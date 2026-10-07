// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System.Text.Json.Nodes;
using System.Text.RegularExpressions;

namespace UInt256Verification;

internal static class AuditGates
{
    private const string Identifier = @"[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*";
    private static string Text(JsonNode? node) => Catalog.Text(node);
    private static bool Boolean(JsonNode? node) => node is JsonValue value && value.TryGetValue(out bool flag)
        ? flag : throw new InvalidOperationException("Expected a Boolean contract descriptor");
    private static bool All(JsonObject gate) => gate.ContainsKey("allProfiles") && Boolean(gate["allProfiles"]);
    private static string Bool(bool value) => value ? "true" : "false";
    private static string Bind(string contract, string program) => contract.Replace("{program}", program, StringComparison.Ordinal);
    private static bool Shift(string name) => name is "Lsh" or "Rsh" or "LeftShift" or "RightShift" or "OperatorLsh" or "OperatorRsh";
    private static void Keys(JsonObject descriptor, params string[] keys)
    {
        if (!keys.ToHashSet().SetEquals(descriptor.Select(pair => pair.Key)))
            throw new InvalidOperationException("Invalid typed contract descriptor fields");
    }

    internal static string Module(JsonObject entry)
    {
        JsonObject gate = entry["verification"]!.AsObject();
        if (!gate.ContainsKey("template")) return HandwrittenGate(entry);
        JsonObject descriptor = gate["template"]?.AsObject()
            ?? throw new InvalidOperationException("Invalid typed audit descriptor");
        string result = Text(descriptor["kind"]) switch
        {
            "scalar-comparison" => ScalarComparison(entry, descriptor),
            "scalar-equality" => ScalarEquality(entry, descriptor),
            "binary-bitwise" or "returning-bitwise" => Bitwise(entry, descriptor),
            _ => throw new InvalidOperationException("Unsupported typed audit template")
        };
        return result.ReplaceLineEndings("\n");
    }

    private static (string Variables, string Contract) HandwrittenContract(string name)
    {
        string variables = "(initial : Bytes) (left right : Nat)";
        string contract;
        if (name is "EqUInt256UInt256" or "EqualsUInt256Ref" or "NeUInt256UInt256")
            contract = $"UInt256Model.Equality.{(name.StartsWith("Ne", StringComparison.Ordinal) ? "InequalityContract" : "Contract")} {{program}} Extracted.entryIndex initial left right";
        else if (name == "EqualsUInt256Value")
        {
            variables = "(initial : Bytes) (left : Nat) (right : BitVec 256)";
            contract = "UInt256Model.Equality.SnapshotContract {program} Extracted.entryIndex initial left right";
        }
        else if (name is "CompareToUInt256Ref" or "CompareToUInt256Value")
        {
            bool snapshot = name == "CompareToUInt256Value";
            if (snapshot) variables = "(initial : Bytes) (left : Nat) (right : BitVec 256)";
            contract = $"UInt256Model.Compare.{(snapshot ? "ThreeWaySnapshotContract" : "ThreeWayContract")} {{program}} Extracted.entryIndex initial left right";
        }
        else if (name is "LtUInt256UInt256" or "LeUInt256UInt256" or "GtUInt256UInt256" or "GeUInt256UInt256")
        {
            string relation = name[..2] switch { "Lt" => "less", "Le" => "lessEqual", "Gt" => "greater", _ => "greaterEqual" };
            contract = $"UInt256Model.Compare.Contract {{program}} Extracted.entryIndex .{relation} initial left right";
        }
        else if (name == "LeUInt64UInt256")
        {
            variables = "(initial : Bytes) (word : W64) (right : BitVec 256)";
            contract = "UInt256Model.Compare.ScalarSnapshotContract {program} Extracted.entryIndex .lessEqual initial (.u64 word) right";
        }
        else if (name is "Not" or "Xor")
        {
            variables = name == "Not" ? "(initial : Bytes) (input out : Nat)" : "(initial : Bytes) (left right out : Nat)";
            contract = name == "Not" ? "UInt256Model.Bitwise.NotContract {program} Extracted.entryIndex initial input out"
                : "UInt256Model.Bitwise.Contract {program} Extracted.entryIndex .xor initial left right out";
        }
        else if (Shift(name))
        {
            string direction = name is "Lsh" or "LeftShift" or "OperatorLsh" ? "left" : "right";
            bool returning = name.StartsWith("Operator", StringComparison.Ordinal);
            variables = returning ? "(initial : Bytes) (input : Nat) (count : W32)" : "(initial : Bytes) (input out : Nat) (count : W32)";
            contract = $"UInt256Proof.Shift.{(returning ? "OperatorContract" : "Contract")} .{direction} {{program}} Extracted.entryIndex "
                + (returning ? "initial input count" : "initial input out count");
        }
        else if (name is "AddOverflow" or "SubtractUnderflow")
        {
            variables = "(initial : Bytes) (left right out : Nat)";
            contract = $"UInt256Proof.Reporting.Contract .{(name == "AddOverflow" ? "add" : "subtract")} {{program}} Extracted.entryIndex initial left right out";
        }
        else if (name is "Multiply" or "MultiplyInstance")
        {
            variables = "(initial : Bytes) (left right out : Nat)";
            contract = "UInt256Proof.Multiply.Contract {program} Extracted.entryIndex initial left right out";
        }
        else if (name == "OperatorMultiplyUInt256UInt256")
            contract = "UInt256Proof.Multiply.ReturnContract {program} Extracted.entryIndex initial left right";
        else if (name is "OperatorMultiplyUInt256UInt32" or "OperatorMultiplyUInt32UInt256" or "OperatorMultiplyUInt256UInt64" or "OperatorMultiplyUInt64UInt256")
        {
            int width = name.Contains("UInt32", StringComparison.Ordinal) ? 32 : 64;
            variables = $"(initial : Bytes) (input : Nat) (word : W{width})";
            contract = $"UInt256Proof.Multiply.ScalarReturnContract {{program}} Extracted.entryIndex {width} "
                + $"{Bool(name.StartsWith($"OperatorMultiplyUInt{width}UInt256", StringComparison.Ordinal))} initial input word";
        }
        else throw new InvalidOperationException($"No independent typed binding for handwritten API: {name}");
        return (variables, contract);
    }

    private static List<(string Name, string Type, string Proof)> Bindings(JsonObject entry)
    {
        JsonObject gate = entry["verification"]!.AsObject();
        (string variables, string contract) = HandwrittenContract(Text(entry["id"]));
        string[] sources = gate["auditedTheorems"]!.AsArray().Select(Text).ToArray();
        if (sources.Length == 0 || sources.Any(name => !Regex.IsMatch(name, @"\A" + Identifier + @"\z")))
            throw new InvalidOperationException("Invalid handwritten theorem identifier");
        List<(string, string, string)> result = [("bound_contract", $"∀ {variables}, {Bind(contract, "Extracted.program")}", sources[0])];
        string profiled = $"∀ {variables}, {Bind(contract, "(reprofile Extracted.program profile)")}";
        const string header = "∀ profile : FeatureProfile, profile.Valid → ";
        if (All(gate)) result.Add(("bound_all_profiles_contract", header + profiled, Text(gate["allProfilesTheorem"])));
        else
        {
            JsonObject? family = gate["familyCoverage"]?.AsObject();
            string[] conditional = sources.Skip(1).Where(name => family is null || name != Text(family["theorem"])).ToArray();
            if (conditional.Length > 1) throw new InvalidOperationException("Ambiguous handwritten profile binding");
            bool shift = Shift(Text(entry["id"]));
            if (conditional.Length != 0)
                result.Add(("bound_profile_contract", header + "Extracted.program.ProfileAgreement Extracted.profile profile → " + profiled,
                    $"by\n  intro profile {(shift ? "_" : "valid")} agreement\n  exact {conditional[0]} profile {(shift ? "agreement" : "valid agreement")}"));
            if (family is not null)
            {
                string guards = Text(family["kind"]) switch
                {
                    "vector256-storage" => "Extracted.profile.vector256Accelerated = profile.vector256Accelerated → ",
                    "vector-reduction" => "Extracted.profile.vector256Accelerated = profile.vector256Accelerated → (Extracted.profile.vector256Accelerated = false → Extracted.profile.sse41 = profile.sse41) → ",
                    "relational-dispatch" => "Extracted.profile.avx512FVL = profile.avx512FVL → (Extracted.profile.avx512FVL = false → Extracted.profile.avx2 = profile.avx2) → (Extracted.profile.avx512FVL = false → Extracted.profile.avx2 = false → Extracted.profile.vector256Accelerated = profile.vector256Accelerated) → ",
                    "multiply-dispatch-storage" => "Extracted.profile.classifyMultiply = profile.classifyMultiply → Extracted.profile.vector256Accelerated = profile.vector256Accelerated → ",
                    "feature-class" => "profile.classify = Extracted.profile.classify → ",
                    _ => throw new InvalidOperationException("Unknown handwritten feature family")
                };
                string theorem = Text(family["theorem"]);
                result.Add(("bound_family_contract", header + guards + profiled,
                    shift ? $"by\n  intro profile _ same\n  exact {theorem} profile same" : theorem));
            }
        }
        return result;
    }

    internal static string[] BoundAuditNames(JsonObject entry) => Bindings(entry).Select(binding => "UInt256Proof.Selected." + binding.Name).ToArray();

    private static string HandwrittenGate(JsonObject entry)
    {
        string target = Text(entry["verification"]!["auditTarget"]);
        if (!Regex.IsMatch(target, @"\A\+" + Identifier + @":olean\z"))
            throw new InvalidOperationException("Invalid handwritten audit module");
        string declarations = string.Join("\n\n", Bindings(entry).Select(binding =>
            $"theorem {binding.Name} : {binding.Type} := {binding.Proof}\n#print axioms {binding.Name}"));
        return $"import {target[1..^6]}\n\nopen CIL UInt256Model\nnamespace UInt256Proof.Selected\n\n{declarations}\n\nend UInt256Proof.Selected\n";
    }

    private static string Typed(string module, string variables, string arguments, string contract, string execution, bool all = false, bool family = false)
    {
        string imports = $"import {module}\n" + (family ? "import CIL.StorageProfileCoverage\n" : "");
        string universal = "";
        if (all) universal = "\n" + $$"""
            theorem checked_all_profiles_contract : ∀ (profile : FeatureProfile), profile.Valid →
                ∀ {{variables}},
                {{Bind(contract, "(reprofile Extracted.program profile)")}} := by
              intro profile valid
              apply checked_profile_contract profile valid
              exact Program.profile_independent_agreement Extracted.program (by decide) _ _

            #print axioms checked_all_profiles_contract
            """ + "\n";
        if (family) universal = "\n" + $$"""
            theorem checked_family_contract : ∀ (profile : FeatureProfile), profile.Valid →
                Extracted.profile.vector256Accelerated = profile.vector256Accelerated →
                ∀ {{variables}},
                {{Bind(contract, "(reprofile Extracted.program profile)")}} := by
              intro profile valid same
              apply checked_profile_contract profile valid
              exact CIL.storage_profile_agreement Extracted.program (by decide) _ _ same

            #print axioms checked_family_contract
            """ + "\n";
        return $$"""
            {{imports}}

            open CIL UInt256Model UInt256Proof
            set_option maxRecDepth 8192
            set_option maxHeartbeats 2000000
            namespace UInt256Proof.Selected

            theorem checked_contract : ∀ {{variables}},
                {{Bind(contract, "Extracted.program")}} := by
              intro {{arguments}}
              {{execution}}

            theorem checked_profile_contract : ∀ (profile : FeatureProfile), profile.Valid →
                Extracted.program.ProfileAgreement Extracted.profile profile →
                ∀ {{variables}},
                {{Bind(contract, "(reprofile Extracted.program profile)")}} := by
              intro profile _ agreement {{arguments}}
              obtain ⟨fuel, final, execution, bytes⟩ := checked_contract {{arguments}}
              refine ⟨fuel, final, ?_, bytes⟩
              rw [← invoke_uniform_reprofile_eq Extracted.program Extracted.profile profile
                (uniform_of_profile_map _ _ Extracted.programProfiles) agreement]
              exact execution

            #print axioms checked_contract
            #print axioms checked_profile_contract
            {{universal}}
            end UInt256Proof.Selected
            """ + "\n";
    }

    private static (string Width, string Type) Scalar(string kind) => kind switch
    {
        "u32" => ("W32", "System.UInt32"), "u64" => ("W64", "System.UInt64"),
        "s32" => ("W32", "System.Int32"), "s64" => ("W64", "System.Int64"),
        _ => throw new InvalidOperationException("Invalid scalar contract kind")
    };
    private sealed record Parameter(string Type, bool IsIn, bool IsOut);
    private static readonly Parameter Reference = new("Nethermind.Int256.UInt256&", true, false);

    private static void Convention(JsonObject entry, bool instance, string returns, params Parameter[] parameters)
    {
        JsonObject expected = entry["callingConvention"]!.AsObject();
        if (Boolean(expected["static"]) == instance || Text(expected["returns"]) != returns)
            throw new InvalidOperationException("Extracted entry static/return convention differs from its selected contract");
        JsonArray selected = expected["parameters"]!.AsArray();
        if (selected.Count != parameters.Length) throw new InvalidOperationException("Extracted entry parameter count changed");
        for (int i = 0; i < parameters.Length; i++)
            if (Text(selected[i]!["type"]) != parameters[i].Type || Boolean(selected[i]!["isIn"]) != parameters[i].IsIn
                || Boolean(selected[i]!["isOut"]) != parameters[i].IsOut)
                throw new InvalidOperationException("Extracted entry parameter type/direction changed");
    }

    private static void Signature(JsonObject entry, string returns, string method, IEnumerable<Parameter> parameters, string error)
    {
        if (Text(entry["signature"]) != $"{returns} Nethermind.Int256.UInt256::{method}({string.Join(",", parameters.Select(p => p.Type))})")
            throw new InvalidOperationException(error);
    }

    private static string ScalarComparison(JsonObject entry, JsonObject descriptor)
    {
        Keys(descriptor, "kind", "relation", "scalarKind", "scalarFirst");
        string relation = Text(descriptor["relation"]), kind = Text(descriptor["scalarKind"]);
        string method = relation switch
        {
            "less" => "op_LessThan", "lessEqual" => "op_LessThanOrEqual", "greater" => "op_GreaterThan",
            "greaterEqual" => "op_GreaterThanOrEqual", _ => throw new InvalidOperationException("Invalid scalar comparison relation")
        };
        bool first = Boolean(descriptor["scalarFirst"]);
        (string width, string type) = Scalar(kind);
        Parameter scalar = new(type, false, false);
        Parameter[] parameters = first ? [scalar, Reference] : [Reference, scalar];
        Convention(entry, false, "System.Boolean", parameters);
        Signature(entry, "System.Boolean", method, parameters, "Scalar comparison descriptor differs from selected operator");
        string contract = $"UInt256Model.Compare.ScalarContract {{program}} Extracted.entryIndex .{relation}\n      initial input (.{kind} word) {Bool(first)}";
        return Typed("UInt256.Methods.Compare.Automation", $"(initial : Bytes) (input : Nat) (word : {width})",
            "initial input word", contract, "scalar_comparison_execute initial, input", All(entry["verification"]!.AsObject()));
    }

    private static string ScalarEquality(JsonObject entry, JsonObject descriptor)
    {
        Keys(descriptor, "kind", "scalarKind", "scalarFirst", "instance", "negateResult");
        JsonObject gate = entry["verification"]!.AsObject();
        if (All(gate)) throw new InvalidOperationException("Invalid scalar equality contract descriptor");
        string kind = Text(descriptor["scalarKind"]);
        bool first = Boolean(descriptor["scalarFirst"]), instance = Boolean(descriptor["instance"]), negate = Boolean(descriptor["negateResult"]);
        if (instance && (first || negate)) throw new InvalidOperationException("Instance equality descriptor differs from Equals");
        (string width, string type) = Scalar(kind);
        Parameter scalar = new(type, false, false);
        Parameter[] parameters = instance ? [scalar] : first ? [scalar, Reference] : [Reference, scalar];
        Convention(entry, instance, "System.Boolean", parameters);
        Signature(entry, "System.Boolean", instance ? "Equals" : negate ? "op_Inequality" : "op_Equality", parameters,
            "Scalar equality descriptor differs from selected API");
        string contract = $"UInt256Model.Equality.ScalarContract {{program}} Extracted.entryIndex\n      initial input (.{kind} word) {Bool(first)} {Bool(negate)}";
        return Typed("UInt256.Methods.Equality.Automation", $"(initial : Bytes) (input : Nat) (word : {width})",
            "initial input word", contract, "scalar_equality_execute initial, input", family: gate["familyCoverage"] is not null);
    }

    private static string Bitwise(JsonObject entry, JsonObject descriptor)
    {
        Keys(descriptor, "kind", "operation");
        JsonObject gate = entry["verification"]!.AsObject();
        bool returning = Text(descriptor["kind"]) == "returning-bitwise";
        string operation = Text(descriptor["operation"]);
        if (All(gate) || operation is not ("and" or "or" or "xor" or "not") || (!returning && operation == "not"))
            throw new InvalidOperationException("Invalid bitwise contract descriptor");
        bool unary = operation == "not";
        List<Parameter> parameters = unary ? [Reference] : [Reference, Reference];
        string returns = returning ? "Nethermind.Int256.UInt256" : "System.Void";
        if (!returning) parameters.Add(new("Nethermind.Int256.UInt256&", false, true));
        Convention(entry, false, returns, [.. parameters]);
        string method = returning ? operation switch
        {
            "and" => "op_BitwiseAnd", "or" => "op_BitwiseOr", "xor" => "op_ExclusiveOr", _ => "op_OnesComplement"
        } : char.ToUpperInvariant(operation[0]) + operation[1..];
        Signature(entry, returns, method, parameters, "Binary bitwise descriptor differs from selected operation");
        bool family = gate["familyCoverage"] is not null;
        if (returning)
        {
            string contract = unary ? "UInt256Model.Bitwise.NotReturnContract {program} Extracted.entryIndex initial input"
                : $"UInt256Model.Bitwise.ReturnContract {{program}} Extracted.entryIndex .{operation}\n      initial left right";
            return Typed("UInt256.Methods.Bitwise.ReturnAutomation", unary ? "(initial : Bytes) (input : Nat)" : "(initial : Bytes) (left right : Nat)",
                unary ? "initial input" : "initial left right", contract, unary ? "not_bitwise_return_execute initial, input"
                    : $"binary_bitwise_return_execute initial, left, right, UInt256Proof.Bitwise.value_{operation}", family: family);
        }
        return Typed("UInt256.Methods.Bitwise.Automation", "(initial : Bytes) (left right out : Nat)", "initial left right out",
            $"UInt256Model.Bitwise.Contract {{program}} Extracted.entryIndex .{operation}\n      initial left right out",
            $"binary_bitwise_execute initial, left, right, out, UInt256Proof.Bitwise.value_{operation}", family: family);
    }
}
