// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT

internal static class ProofBindings
{
    // These dimensions describe one shared checked operator theorem, not independent proof bodies.
    internal static Dictionary<string, string> Sources(Gate[] gates)
    {
        Dictionary<string, string> sources = new(StringComparer.Ordinal);
        HashSet<Gate> expected = [];
        foreach (int width in new[] { 32, 64 })
        foreach (bool signed in new[] { false, true })
        foreach (bool scalarFirst in new[] { false, true })
        foreach (bool negate in new[] { false, true })
        foreach (bool vector in new[] { false, true })
        {
            string primitive = (signed ? "Int" : "UInt") + width;
            string method = (negate ? "Ne" : "Eq") + (scalarFirst ? primitive + "UInt256" : "UInt256" + primitive);
            string family = vector ? "vector" : "scalar";
            string theorem = "UInt256Proof.Equality." + method + "." + family;
            string path = "proofs/" + method + (vector ? "Vector" : "Scalar") + ".lean";
            Gate gate = new(method, vector ? "x64-v3" : "scalar", path, theorem + "_correctness");
            if (gates.Count(candidate => candidate == gate) != 1)
                throw new InvalidOperationException($"Expected exactly one generated binding gate: {method}/{gate.Profile}");
            expected.Add(gate);
            sources.Add(path, Equality(width, signed, scalarFirst, negate, vector, theorem));
        }
        foreach (int width in new[] { 32, 64 })
        foreach (bool signed in new[] { false, true })
        foreach (bool scalarFirst in new[] { false, true })
        foreach (var (name, operation) in new[] { ("Lt", "<"), ("Le", "≤"), ("Gt", ">"), ("Ge", "≥") })
        {
            string primitive = (signed ? "Int" : "UInt") + width;
            string method = name + (scalarFirst ? primitive + "UInt256" : "UInt256" + primitive);
            // This overload takes UInt256 by value and has its own aggregate contract.
            if (method == "LeUInt64UInt256") continue;
            string path = "proofs/" + method + "Scalar.lean";
            Gate gate = new(method, "scalar", path, "UInt256Proof.Compare." + method + ".scalar_correctness");
            if (gates.Count(candidate => candidate == gate) != 1)
                throw new InvalidOperationException($"Expected exactly one generated binding gate: {method}/scalar");
            expected.Add(gate);
            sources.Add(path, Comparison(method, width, signed, scalarFirst, name, operation));
        }
        HashSet<string> methods = [.. expected.Select(gate => gate.Method)];
        if (gates.Any(gate => methods.Contains(gate.Method) && !expected.Contains(gate)))
            throw new InvalidOperationException("Unexpected profile, proof or theorem for a generated binding");
        return sources;
    }

    internal static void Write(string root, Gate[] gates, bool check = false)
    {
        foreach (var (relative, source) in Sources(gates))
        {
            string path = Path.Combine(root, relative);
            bool same = File.Exists(path) && File.ReadAllText(path).ReplaceLineEndings("\n") == source;
            if (check && !same) throw new InvalidOperationException("Generated binding differs: " + relative);
            if (same || check) continue;
            Directory.CreateDirectory(Path.GetDirectoryName(path)!);
            File.WriteAllText(path, source);
        }
    }

    private static string Comparison(string method, int width, bool signed, bool scalarFirst,
        string name, string operation)
    {
        string first = scalarFirst ? "true" : "false";
        string scalar = signed ? "word.toInt" : "(word.toNat : Int)";
        string predicate = scalarFirst ? $"{scalar} {operation} (input.toNat : Int)" :
            $"(input.toNat : Int) {operation} {scalar}";
        string widened = width == 32 ? "(widen32 word)" : "word";
        string leafSigned = signed || width == 32 ? "true" : "false";
        string leafFirst = (name is "Gt" or "Le" ? !scalarFirst : scalarFirst) ? "true" : "false";
        string negated = name is "Le" or "Ge" ? "true" : "false";
        string widenProof = width == 64 ? "" :
            $", show wrapperSigned32 = {(signed ? "true" : "false")} from rfl, widen32, " +
            (signed ? "BitVec.toInt_signExtend_of_le (by decide : 32 ≤ 64)" : "UInt256Proof.Compare.zeroExtend32_toInt");
        return $$"""
            import UInt256.Methods.Compare.PrimitiveSafetyWrapper{{width}}
            import UInt256.Safety.ScalarOperatorResult

            namespace UInt256Proof.Compare.{{method}}
            open UInt256Model.Safety UInt256Proof.Compare.PrimitiveSafety

            /-- Exact comparison of the initial UInt256 and scalar values, with checked
                finite return and preservation of caller memory. -/
            theorem scalar_correctness : ScalarOperatorContract {{first}} false CIL.Value.i{{width}}
                (fun input word => decide ({{predicate}}))
                Extracted.program Extracted.entryIndex := by
              have meaning (input : BitVec 256) (word : BitVec {{width}}) :
                  (predicate leafSigned leafScalarFirst input {{widened}} != wrapperNegate) =
                    decide ({{predicate}}) := by
                simp [show leafSigned = {{leafSigned}} from rfl,
                  show leafScalarFirst = {{leafFirst}} from rfl,
                  show wrapperNegate = {{negated}} from rfl, predicate{{widenProof}}]
                <;> (by_cases ordered : {{predicate}} <;> simp_all <;> omega)
              simpa only [show wrapperScalarFirst = {{first}} from rfl] using
                ScalarOperatorContract.result_congr meaning checked{{width}}

            end UInt256Proof.Compare.{{method}}
            """ + "\n";
    }

    // Synthetic runner tests have their own tiny registry and no UInt256 proof library.
    internal static void Prepare(string root)
    {
        if (File.Exists(Path.Combine(root, "UInt256/Methods/Equality/PrimitiveOperator.lean")))
            Write(root, VerificationSupport.Gates(root));
    }

    private static string Equality(int width, bool signed, bool scalarFirst, bool negate, bool vector,
        string theorem)
    {
        string first = scalarFirst ? "true" : "false", negated = negate ? "true" : "false";
        string operation = (signed ? "!decide (word.toInt < 0) && " : "") +
            "decide (input = BitVec.ofNat 256 word.toNat)";
        string contract = $"UInt256Model.Safety.ScalarOperatorContract {first} {negated} CIL.Value.i{width}";
        string imports = "import UInt256.Methods.Equality.PrimitiveProfileBindings\n" +
            (vector ? "import UInt256.Methods.Equality.VectorPrimitiveWrapper\n" : "") +
            "import Extracted\nimport UInt256.Methods.Equality.PrimitiveOperator\n" +
            (signed ? "import UInt256.Methods.Equality.SignedPrimitive\n" : "");
        string helper = $"UInt256Proof.Equality.{(vector ? "VectorPrimitiveWrapper" : "UnsignedPrimitive")}.checked{width}" +
            " Extracted.profile Extracted.program " + (signed ? "2 3" : "1 2") +
            (vector ? " rfl rfl rfl" : (signed ? " 4" : " 3") + " rfl rfl rfl rfl");
        string checkedHelper = signed
            ? $"    (UInt256Proof.Equality.SignedPrimitive.checked{width} Extracted.profile Extracted.program 1 2 rfl\n" +
              $"      ({helper}))"
            : $"    ({helper})";
        return imports + "\n" + $$"""
            /-- Primitive equality operator with checked argument order, polarity and caller-memory preservation. -/
            theorem {{theorem}}_correctness :
                {{contract}}
                  (fun input word => {{operation}}) Extracted.program 0 :=
              UInt256Proof.Equality.PrimitiveOperator.checked CIL.Value.i{{width}} _
                Extracted.profile {{first}} {{negated}} Extracted.program 0 1 rfl (fun _ => rfl)
            {{checkedHelper}}

            """ + (vector ? "\n\n" : "\n") + $$"""
            theorem {{theorem}}_family (profile : CIL.FeatureProfile)
                (vector : Extracted.profile.vector256Accelerated = profile.vector256Accelerated) :
                {{contract}}
                  (fun input word => {{operation}}) (CIL.reprofile Extracted.program profile) 0 :=
              UInt256Model.Safety.ScalarOperatorContract.reprofile UInt256Proof.Equality.ProfileBindings.uniform
                (UInt256Proof.Equality.ProfileBindings.primitive_agreement profile vector) {{theorem}}_correctness

            """ + "\n";
    }
}
