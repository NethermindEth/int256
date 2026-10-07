// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System.Text.Json.Nodes;

namespace UInt256Verification;

internal static class SafetyGates
{
    private static string Bool(bool value) => value ? "true" : "false";
    private static string Family(string contract) => contract.Replace("Extracted.program", "(CIL.reprofile Extracted.program profile)", StringComparison.Ordinal);
    internal static string Module(Catalog catalog, string method, string profile)
    {
        JsonObject gate = SafetyCatalog.Gate(method, profile);
        if (gate["generatedAudit"]?.GetValue<bool>() != true)
            throw new InvalidOperationException($"Safety gate uses a static audit module: {method}/{profile}");
        string text = SafetyCatalog.ClassifiedMethods.Contains(method) ? Classified(method, profile)
            : SafetyCatalog.MultiplyMethods.Contains(method) ? Multiply(catalog, method, profile)
            : SafetyCatalog.PrimitiveComparisons.ContainsKey(method) ? PrimitiveComparison(method)
            : SafetyCatalog.Operators.ContainsKey(method) ? Operator(method, profile) : Bitwise(method, profile);
        return text.ReplaceLineEndings("\n") + "\n";
    }

    private static string Classified(string method, string profile)
    {
        JsonObject gate = SafetyCatalog.Representative(method, profile);
        string module = Catalog.Text(gate["target"])[1..].Split(':')[0];
        bool reporting = method is "AddOverflow" or "SubtractUnderflow", adding = method is "Add" or "AddOverflow";
        string kind = reporting ? "ReportingBinaryContract" : "WrappingBinaryContract";
        string contract = $"{kind} (fun left right => left {(adding ? "+" : "-")} right)";
        if (reporting) contract += $"\n      (fun left right => decide ({(adding ? "2^256 ≤ left.toNat + right.toNat" : "left.toNat < right.toNat")}))";
        return $"""
            import {module}
            import UInt256.Safety.ReportingContract

            namespace UInt256Proof.SafetySelected
            open UInt256Model.Safety

            theorem checked_family_contract (profile : CIL.FeatureProfile) (valid : profile.Valid)
                (same : profile.classify = Extracted.profile.classify) :
                {contract} (CIL.reprofile Extracted.program profile) Extracted.entryIndex :=
              {kind}.reprofile (CIL.uniform_of_profile_map _ _ Extracted.programProfiles)
                (CIL.Program.same_family_profile_agreement _ _ _ valid Extracted.profileValid same
                  (CIL.Program.classified_of_check _ _ (by decide)))
                {Catalog.Text(gate["theorems"]!.AsArray().Last())}

            #print axioms checked_family_contract
            end UInt256Proof.SafetySelected
            """;
    }

    private static string Multiply(Catalog catalog, string method, string profile)
    {
        JsonObject flags = catalog.Profile(profile);
        bool Flag(string name) => flags[name]!.GetValue<bool>();
        string top = Flag("Avx512DQVL") ? "Avx512" : Flag("Avx2") ? "Avx2" : "Scalar";
        bool hardware = Flag("Bmi2") || Flag("ArmBase64");
        string wordImport = hardware ? "WordHardwareAudit" : "WordSoftwareSafety";
        string word = hardware ? "(fun memory a b output wf writable => hardware_word_invoke memory a b output wf writable hardware_profile_supported)" : "software_word_invoke";
        bool primitive = SafetyCatalog.MultiplyPrimitives.TryGetValue(method, out var scalar);
        (string module, string theorem) = primitive ? ($"Primitive{scalar.Width}Safety", $"multiply_primitive{scalar.Width}_contract") : method switch
        {
            "Multiply" => ("EntrySafetyContract", "multiply_checked_contract"),
            "MultiplyInstance" => ("InstanceSafety", "multiply_instance_contract"),
            "OperatorMultiplyUInt256UInt256" => ("ReturnSafety", "multiply_return_contract"),
            _ => throw new InvalidOperationException("Unsupported multiplication safety method")
        };
        bool returning = method == "OperatorMultiplyUInt256UInt256";
        string contract = returning ? "ReadOnlyContract (fun values => .v256 ((values[0]?.getD 0) * (values[1]?.getD 0)))"
            : "WrappingBinaryContract (fun left right => left * right)";
        string arity = returning ? " 2" : "";
        string index = method == "Multiply" ? "multiplyIndex" : "Extracted.entryIndex";
        string binding = method == "Multiply" ? "by\n  simpa only [show multiplyIndex = Extracted.entryIndex from rfl] using checked_contract" : "checked_contract";
        string reprofile = returning ? "ReadOnlyContract" : "WrappingBinaryContract";
        string extraImport = "";
        if (primitive)
        {
            contract = $"OrderedScalarContract {Bool(scalar.First)} CIL.Value.i{scalar.Width}\n      (fun input scalar => .v256 (input * BitVec.ofNat 256 scalar.toNat))";
            reprofile = "OrderedScalarContract";
            extraImport = "import UInt256.Safety.OrderedScalarProfiles\n";
        }
        return $"""
            import UInt256.Methods.Multiply.{module}
            {extraImport}import UInt256.Methods.Multiply.SafetyProfiles
            import UInt256.Methods.Multiply.FullSafety{top}Top
            import UInt256.Methods.Multiply.{wordImport}

            namespace UInt256Proof.SafetySelected
            open UInt256Model.Safety UInt256Proof.Multiply.Safety

            theorem checked_contract :
                {contract} Extracted.program {index}{arity} :=
              {theorem} {word} full_{top.ToLowerInvariant()}_top

            theorem checked_binding :
                {contract} Extracted.program Extracted.entryIndex{arity} := {binding}

            theorem checked_family_contract (profile : CIL.FeatureProfile) (valid : profile.Valid)
                (same : Extracted.profile.classifyMultiply = profile.classifyMultiply)
                (storage : Extracted.profile.vector256Accelerated = profile.vector256Accelerated) :
                {contract} (CIL.reprofile Extracted.program profile) Extracted.entryIndex{arity} :=
              {reprofile}.reprofile (CIL.uniform_of_profile_map _ _ Extracted.programProfiles)
                (selected_profile_agreement profile valid same storage) checked_binding

            #print axioms checked_contract
            #print axioms checked_binding
            #print axioms checked_family_contract
            end UInt256Proof.SafetySelected
            """;
    }

    private static string PrimitiveComparison(string method)
    {
        var s = SafetyCatalog.PrimitiveComparisons[method];
        string number = s.Signed ? "word.toInt" : "(word.toNat : Int)";
        string left = s.First ? number : "(input.toNat : Int)", right = s.First ? "(input.toNat : Int)" : number;
        string symbol = s.Relation switch { "Lt" => "<", "Le" => "≤", "Gt" => ">", "Ge" => "≥", _ => throw new InvalidOperationException("Unknown comparison") };
        string comparison = $"{left} {symbol} {right}";
        string contract = $"ScalarOperatorContract {Bool(s.First)} false CIL.Value.i{s.Width}\n      (fun input word => decide ({comparison})) Extracted.program Extracted.entryIndex";
        bool leafFirst = s.First != (s.Relation is "Gt" or "Le"), negate = s.Relation is "Le" or "Ge";
        string argument = s.Width == 32 ? "(widen32 word)" : "word";
        string widening = s.Width == 32 ? $", show wrapperSigned32 = {Bool(s.Signed)} from rfl, widen32, "
            + (s.Signed ? "BitVec.toInt_signExtend_of_le (by decide : 32 ≤ 64)" : "UInt256Proof.Compare.zeroExtend32_toInt") : "";
        return $"""
            import UInt256.Methods.Compare.PrimitiveSafetyWrapper{s.Width}
            import UInt256.Safety.ScalarOperatorResult
            import UInt256.Safety.ProfileContracts

            namespace UInt256Proof.SafetySelected
            open UInt256Model.Safety UInt256Proof.Compare.PrimitiveSafety

            theorem checked_contract :
                {contract} := by
              have meaning (input : BitVec 256) (word : BitVec {s.Width}) :
                  (predicate leafSigned leafScalarFirst input {argument} != wrapperNegate) =
                    decide ({comparison}) := by
                simp [show leafSigned = {Bool(s.Signed || s.Width == 32)} from rfl,
                  show leafScalarFirst = {Bool(leafFirst)} from rfl,
                  show wrapperNegate = {Bool(negate)} from rfl, predicate{widening}] <;>
                  (by_cases ordered : {comparison} <;> simp_all <;> omega)
              simpa only [show wrapperScalarFirst = {Bool(s.First)} from rfl] using
                ScalarOperatorContract.result_congr meaning checked{s.Width}

            theorem checked_binding :
                {contract} := checked_contract

            theorem checked_family_contract (profile : CIL.FeatureProfile) (_valid : profile.Valid) :
                {Family(contract)} :=
              ScalarOperatorContract.reprofile (CIL.uniform_of_profile_map _ _ Extracted.programProfiles)
                (Extracted.program.profile_independent_agreement (by decide) _ _) checked_contract

            #print axioms checked_contract
            #print axioms checked_binding
            #print axioms checked_family_contract
            end UInt256Proof.SafetySelected
            """;
    }

    private static string Operator(string method, string profile)
    {
        var s = SafetyCatalog.Operators[method];
        string prefix = profile == "x64-vector256" ? "Vector" : "Scalar";
        string kind = (s.Signed ? "S" : "U") + s.Width;
        string number = s.Signed ? "right.toInt" : "(right.toNat : Int)";
        string predicate = $"(fun left right => decide ((left.toNat : Int) = {number}))";
        string contract = $"ScalarOperatorContract {Bool(s.First)} {Bool(s.Negate)} CIL.Value.i{s.Width}\n      {predicate} Extracted.program Extracted.entryIndex";
        return $"""
            import UInt256.Methods.Equality.{prefix}OperatorChild{kind}
            import UInt256.Safety.ProfileContracts
            import CIL.StorageProfileCoverage

            namespace UInt256Proof.SafetySelected
            open UInt256Model.Safety UInt256Proof.Equality.Safety

            theorem checked_contract :
                {contract} :=
              scalar_operator_checked CIL.Value.i{s.Width} {predicate} (fun _ => rfl) operator_child_checked

            theorem checked_binding :
                {contract} := checked_contract

            theorem checked_family_contract (profile : CIL.FeatureProfile) (_valid : profile.Valid)
                (same : Extracted.profile.vector256Accelerated = profile.vector256Accelerated) :
                {Family(contract)} := by
              apply ScalarOperatorContract.reprofile
                (CIL.uniform_of_profile_map _ _ Extracted.programProfiles)
                (CIL.storage_profile_agreement Extracted.program (by decide) _ _ same)
              exact checked_contract

            #print axioms checked_contract
            #print axioms checked_binding
            #print axioms checked_family_contract
            end UInt256Proof.SafetySelected
            """;
    }

    private static string Bitwise(string method, string profile)
    {
        bool returned = method.StartsWith("Operator", StringComparison.Ordinal), unary = SafetyCatalog.Unary.Contains(method), scalar = profile == "scalar";
        string ns = scalar ? "ScalarSafety" : unary ? "NotSafety" : "Safety";
        string kind = returned ? "ReadOnlyContract" : unary ? "InitializedUnaryContract" : "WrappingBinaryContract";
        string contract, module, theorem, proof;
        if (unary)
        {
            contract = returned ? "ReadOnlyContract (fun values => .v256 (~~~(values[0]?.getD 0))) Extracted.program Extracted.entryIndex 1"
                : "InitializedUnaryContract (fun input => ~~~input) Extracted.program Extracted.entryIndex";
            module = scalar ? (returned ? "NotScalarReturnSafetyContract" : "NotScalarSafetyContract") : (returned ? "NotReturnSafetyContract" : "NotEntrySafety");
            theorem = returned ? (scalar ? "not_return_contract" : "return_contract") : (scalar ? "not_initialized" : "vector_entry_initialized");
            string index = scalar ? "scalarIndex" : "unaryIndex";
            proof = returned ? $"  exact {theorem}" : $"  simpa only [show {index} = Extracted.entryIndex from rfl] using {theorem}";
        }
        else
        {
            var b = SafetyCatalog.Bitwise[method];
            contract = returned ? $"ReadOnlyContract (fun values => .v256 ((values[0]?.getD 0) {b.Symbol} (values[1]?.getD 0))) Extracted.program Extracted.entryIndex 2"
                : $"WrappingBinaryContract (fun left right => left {b.Symbol} right) Extracted.program Extracted.entryIndex";
            module = scalar ? (returned ? "ScalarReturnSafetyContract" : "ScalarSafetyContract") : (returned ? "ReturnSafetyContract" : "VectorEntrySafety");
            theorem = returned ? "return_contract" : scalar ? "scalar_checked" : "vector_entry_checked";
            string index = returned ? "" : $", show {(scalar ? "scalarIndex" : "binaryIndex")} = Extracted.entryIndex from rfl";
            string operation = scalar ? "scalarOperation" : "vectorOperation";
            proof = $"""
                  have selected : UInt256Model.Bitwise.applyBinary {operation} =
                      (fun left right : BitVec 256 => left {b.Symbol} right) := by
                    funext left right
                    simp only [show {operation} = .{b.Operation} from rfl, UInt256Model.Bitwise.applyBinary]
                  simpa only [selected{index}] using {theorem}
                """;
        }
        return $"""
            import UInt256.Methods.Bitwise.{module}
            import UInt256.Safety.ProfileContracts
            import CIL.StorageProfileCoverage

            namespace UInt256Proof.SafetySelected
            open UInt256Model.Safety UInt256Proof.Bitwise.{ns}

            theorem checked_contract : {contract} := by
            {proof}

            theorem checked_binding : {contract} := checked_contract

            theorem checked_family_contract (profile : CIL.FeatureProfile) (_valid : profile.Valid)
                (same : Extracted.profile.vector256Accelerated = profile.vector256Accelerated) :
                {Family(contract)} :=
              {kind}.reprofile (CIL.uniform_of_profile_map _ _ Extracted.programProfiles)
                (CIL.storage_profile_agreement Extracted.program (by decide) _ _ same) checked_contract

            #print axioms checked_contract
            #print axioms checked_binding
            #print axioms checked_family_contract
            end UInt256Proof.SafetySelected
            """;
    }
}
