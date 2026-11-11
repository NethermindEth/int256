// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT

internal static class ProofBindings
{
    // These dimensions describe one shared checked operator theorem, not independent proof bodies.
    internal static Dictionary<string, string> Sources(Gate[] gates)
    {
        Dictionary<string, string> sources = new(StringComparer.Ordinal);
        HashSet<Gate> expected = [];
        void Add(string method, string profile, string file, string theorem, string? source)
        {
            Gate gate = new(method, profile, "proofs/" + file + ".lean", theorem);
            if (gates.Count(candidate => candidate == gate) != 1)
                throw new InvalidOperationException($"Expected exactly one generated binding gate: {method}/{profile}");
            expected.Add(gate);
            if (source is null) return;
            if (sources.TryGetValue(gate.Proof, out string? previous) && previous != source)
                throw new InvalidOperationException("Conflicting generated binding: " + gate.Proof);
            sources[gate.Proof] = source;
        }
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
        foreach (bool vector in new[] { false, true })
        {
            string suffix = vector ? "Vector" : "Scalar", family = vector ? "vector" : "scalar";
            string profile = vector ? "x64-v3" : "scalar";
            foreach (string operation in new[] { "And", "Or", "Xor", "Not" })
            foreach (bool aggregate in new[] { false, true })
            {
                string method = (aggregate ? "Operator" : "") + operation;
                Add(method, profile, method + suffix, $"UInt256Proof.{method}.{family}_correctness",
                    Bitwise(operation, aggregate, vector));
            }
            foreach (bool left in new[] { true, false })
            foreach (int wrappers in new[] { 0, 1, 2 })
            {
                string method = wrappers == 1 ? (left ? "LeftShift" : "RightShift") :
                    (wrappers == 2 ? "Operator" : "") + (left ? "Lsh" : "Rsh");
                Add(method, profile, method + suffix, $"UInt256Proof.{method}.{family}_correctness",
                    Shift(method, left, wrappers, vector));
            }
            foreach (int width in new[] { 32, 64 })
            foreach (bool signed in new[] { false, true })
            {
                string method = "Equals" + (signed ? "Int" : "UInt") + width;
                Add(method, profile, method + suffix, $"UInt256Proof.Equality.{method}.{family}_correctness",
                    PrimitiveEquals(method, width, signed, vector));
            }
        }
        foreach (var (name, operation, audit, binding) in new[]
        {
            ("Lt", "<", "", "less"), ("Le", "≤", "LessEqual", "less_equal"),
            ("Gt", ">", "Greater", "greater"), ("Ge", "≥", "GreaterEqual", "greater_equal")
        })
        foreach (var (profile, suffix, family) in new[]
            { ("scalar", "Scalar", "scalar"), ("x64-v3", "Avx2", "avx2"), ("x64-v4", "Avx512", "avx512") })
        {
            string method = name + "UInt256UInt256";
            Add(method, profile, method + suffix, $"UInt256Proof.Compare.{method}.{family}_correctness",
                FullComparison(name, operation, audit, binding, family));
        }
        foreach (bool subtract in new[] { false, true })
        foreach (bool reporting in new[] { false, true })
        {
            string name = subtract ? "Subtract" : "Add", flag = subtract ? "underflow_" : "overflow_";
            string method = name + (reporting ? subtract ? "Underflow" : "Overflow" : "");
            Add(method, "scalar", method + "Scalar",
                $"UInt256Proof.{name}.{(reporting ? flag : "")}scalar_correctness", null);
            foreach (string profile in new[] { "arm64-advsimd", "x64-sse42", "x64-v3", "x64-v4" })
            {
                string theorem = (profile == "x64-sse42" ? "sse_" : "") + (reporting ? flag : "");
                Add(method, profile, method + "Profile_" + profile.Replace('-', '_'),
                    $"UInt256Proof.{name}.{theorem}profile_correctness", AddSubtract(subtract, reporting, profile));
            }
        }
        foreach (string method in new[] { "Multiply", "MultiplyInstance", "OperatorMultiplyUInt256UInt256",
            "OperatorMultiplyUInt256UInt32", "OperatorMultiplyUInt256UInt64",
            "OperatorMultiplyUInt32UInt256", "OperatorMultiplyUInt64UInt256" })
        foreach (string profile in new[]
            { "scalar", "arm64-advsimd", "x64-v3", "x64-v3-v128", "x64-v4", "x64-v4-v128" })
            Add(method, profile, method + "Profile", $"UInt256Proof.{method}.profile_correctness", Multiply(method));
        foreach (string method in new[]
            { "EqUInt256UInt256", "NeUInt256UInt256", "EqualsUInt256Ref", "EqualsUInt256Value" })
        {
            string scalarFile = method == "NeUInt256UInt256" ? "InequalityScalar" :
                method == "EqualsUInt256Value" ? method + "Scalar" : "EqualityScalar";
            string scalarTheorem = method == "NeUInt256UInt256" ? "scalar_inequality_correctness" :
                method == "EqualsUInt256Value" ? method + ".scalar_correctness" : "scalar_correctness";
            Add(method, "scalar", scalarFile, "UInt256Proof.Equality." + scalarTheorem, null);
            foreach (bool vector in new[] { false, true })
                Add(method, vector ? "x64-v3" : "x64-sse42", method + (vector ? "Vector" : "Sse"),
                    $"UInt256Proof.Equality.{method}.{(vector ? "vector" : "sse")}_correctness",
                    ReferenceEquality(method, vector));
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

    private static string ReferenceEquality(string method, bool vector)
    {
        bool value = method == "EqualsUInt256Value", negate = method == "NeUInt256UInt256";
        string family = vector ? "vector" : "sse", wrapper = vector ? "Vector" : "Sse";
        string name = $"UInt256Proof.Equality.{method}.{family}";
        string helper = $"UInt256Proof.Equality.Reference{wrapper}Wrapper.checked Extracted.profile Extracted.program ";
        string checks = vector ? "rfl rfl rfl" : "rfl rfl rfl rfl";
        string operation = negate ? "≠" : "=";
        string contractName = value ? "ReadOnlyScalarContract" : "ReadOnlyContract";
        string contract = "UInt256Model.Safety." + contractName + (value ?
            " UInt256Proof.ValueForwarder32.encode\n      (fun left right => .i32 (if left = right then 1 else 0))" :
            $" (fun values => .i32 (if values[0]?.getD 0 {operation} values[1]?.getD 0 then 1 else 0))");
        string proof = value ?
            "  apply UInt256Proof.ValueForwarder32.checked Extracted.profile Extracted.program 0 1 true\n" +
            "    (fun left right => if left = right then 1 else 0)\n" +
            "  · intro left right _; split <;> simp\n  · rfl\n  · exact " + helper + "1 2 " + checks :
            (negate ? "  simp only [ne_eq, ite_not]\n" : "") +
            "  apply (by simpa using UInt256Proof.Equality.ReferenceOperator.readOnly_contract " +
            $"(fun a b => decide (a {operation} b)) Extracted.program 0)\n  intro memory left right call\n";
        string equality = "UInt256Proof.Equality.ReferenceOperator.checked " +
            "(fun a b => decide (a = b)) Extracted.profile ";
        if (!value)
            proof += method == "EqualsUInt256Ref" ?
                "  simpa using " + helper + "0 1 " + checks + " memory left right call" : negate ?
                "  simpa using " + equality + "true Extracted.program 0 1 rfl (by\n    intro m l r c\n" +
                "    simpa using " + equality + "false Extracted.program 1 2 rfl (by\n      intro m2 l2 r2 c2\n" +
                "      simpa using " + helper + "2 3 " + checks + " m2 l2 r2 c2) m l r c) memory left right call" :
                "  simpa using " + equality + "false Extracted.program 0 1 rfl\n" +
                "    (fun m l r c => by simpa using " + helper + "1 2 " + checks + " m l r c) memory left right call";
        string suffix = value ? "" : " 2";
        string spacing = new('\n', (value ? 2 : 3) + (vector ? 0 : 1));
        string imports = value ? "ValueForwarder32" : "Equality.ReferenceOperator";
        return $$"""
            import UInt256.Methods.Equality.ReferenceProfileBindings
            import Extracted
            import UInt256.Methods.Equality.Reference{{wrapper}}Wrapper
            import UInt256.Methods.{{imports}}

             theorem {{name}}_correctness :
                {{contract}} Extracted.program 0{{suffix}} := by
            {{proof}}{{spacing}}theorem {{name}}_family (profile : CIL.FeatureProfile)
                (vector : Extracted.profile.vector256Accelerated = profile.vector256Accelerated)
                (sse : Extracted.profile.vector256Accelerated = false → Extracted.profile.sse41 = profile.sse41) :
                {{contract}} (CIL.reprofile Extracted.program profile) 0{{suffix}} :=
              UInt256Model.Safety.{{contractName}}.reprofile UInt256Proof.Equality.ProfileBindings.uniform
                (UInt256Proof.Equality.ProfileBindings.reference_agreement profile vector sse) {{name}}_correctness
            """ + "\n";
    }

    private static string Bitwise(string operation, bool aggregate, bool vector)
    {
        bool unary = operation == "Not";
        string method = (aggregate ? "Operator" : "") + operation;
        string argument = unary ? "" : "." + operation.ToLowerInvariant() + " ";
        string contract = (aggregate ? "UInt256Proof.Bitwise.ReturnSafety." : "UInt256Model.Safety.Wrapping") +
            (unary ? "UnaryContract (~~~·)" :
                $"BinaryContract (UInt256Model.Bitwise.applyBinary .{operation.ToLowerInvariant()})");
        string module = vector ? (aggregate ? "VectorReturn" : unary ? "NotVectorSafety" : "VectorSafety") :
            aggregate ? (unary ? "NotReturn" : "ScalarReturn") : unary ? "NotScalar" : "ScalarSafetyContract";
        string proof = "UInt256Proof.Bitwise." + (aggregate ?
            (vector ? "VectorReturn." : "ReturnSafety.") + (unary ? "unary" : "binary") + "_correctness " + argument :
            vector ? module + ".correctness " : unary ? "not_correctness " : "scalar_correctness " + argument);
        string vectorArgument = vector && !aggregate ? argument : "";
        string indices = aggregate ? "0 1 2 (by rfl) (by rfl) (by rfl)" : "0 1 (by rfl) (by rfl)";
        string reprofile = "(CIL.reprofile Extracted.program profile)";
        if (vector)
            return $$"""
                import Extracted
                import CIL.ProfileEquivalence
                import UInt256.Methods.Bitwise.{{module}}

                namespace UInt256Proof.{{method}}

                theorem vector_correctness : {{contract}} Extracted.program 0 :=
                  {{proof}}Extracted.profile (by rfl) {{vectorArgument}}Extracted.program {{indices}}

                theorem vector_family_correctness (profile : CIL.FeatureProfile)
                    (enabled : profile.vector256Accelerated = true) :
                    {{contract}} {{reprofile}} 0 :=
                  {{proof}}profile enabled {{vectorArgument}}{{reprofile}} {{indices}}

                end UInt256Proof.{{method}}
                """ + "\n";
        string contractBreak = unary ? " " : "\n      ";
        string familyHeader = $"theorem UInt256Proof.{method}.scalar_family_correctness " +
            "(profile : CIL.FeatureProfile) (disabled : profile.vector256Accelerated = false) :";
        return $$"""
            import CIL.ProfileEquivalence
            import Extracted
            import UInt256.Methods.Bitwise.{{module}}

            namespace UInt256Proof.{{method}}

            theorem scalar_correctness :
                {{contract}}{{contractBreak}}Extracted.program 0 :=
              {{proof}}Extracted.profile (by rfl)
                Extracted.program {{indices}}

            end UInt256Proof.{{method}}

            {{familyHeader}}
                {{contract}} {{reprofile}} 0 :=
              {{proof}}profile disabled {{reprofile}} {{indices}}
            """ + "\n";
    }

    private static string Shift(string method, bool left, int wrappers, bool vector)
    {
        string direction = left ? "left" : "right", family = vector ? "vector" : "scalar";
        string storage = vector ? "Vector" : "Scalar";
        string module = wrappers switch { 0 => "Contract", 1 => "Wrapper", _ => "Operator" };
        string Contract(string program) => wrappers < 2 ?
            $"UInt256Model.Safety.ShiftContract .{direction} {program} 0" :
            "UInt256Model.Safety.ReadOnlyScalarContract CIL.Value.i32\n" +
            "    (fun input count => .aggregate (CIL.Safety.numberBytes " +
            $"(UInt256Proof.Shift.result .{direction} input count).toNat 32))\n    {program} 0";
        string Proof(string profile, string program, string enabled)
        {
            string prefix = "UInt256Proof.Shift.Safety.";
            string proof = $"{prefix}scalar_correctness (profile := {profile}) (direction := .{direction})\n" +
                $"    (storage := {wrappers + 1}) (by rfl) " +
                $"(UInt256Proof.Storage{storage}.store_limbs_readable_contract {profile} {enabled} _ _ (by rfl))";
            if (wrappers > 0)
                proof = $"{prefix}wrapper_correctness {profile} .{direction} {program} " +
                    $"{wrappers - 1} {wrappers} (by rfl)\n    (" + proof.Replace("\n", "\n  ") + ")";
            if (wrappers == 2)
                proof = $"{prefix}operator_correctness {profile} .{direction} {program} 0 1 (by rfl)\n    (" +
                    proof.Replace("\n", "\n  ") + ")";
            return proof;
        }
        return $$"""
            import UInt256.Methods.Storage{{storage}}
            import Extracted
            import UInt256.Methods.Shift.Scalar{{module}}

            namespace UInt256Proof.{{method}}

            theorem {{family}}_correctness : {{Contract("Extracted.program")}} :=
              {{Proof("Extracted.profile", "Extracted.program", "(by rfl)")}}

            theorem {{family}}_family_correctness (profile : CIL.FeatureProfile)
                (storageProfile : profile.vector256Accelerated = {{(vector ? "true" : "false")}}) : {{
                    Contract("(CIL.reprofile Extracted.program profile)")}} :=
              {{Proof("profile", "(CIL.reprofile Extracted.program profile)", "storageProfile")}}


            end UInt256Proof.{{method}}
            """ + "\n";
    }

    private static string AddSubtract(bool subtract, bool reporting, string profile)
    {
        bool vector = profile is "x64-v3" or "x64-v4", sse = profile == "x64-sse42";
        string name = subtract ? "Subtract" : "Add", operation = subtract ? "-" : "+";
        string flag = subtract ? "underflow" : "overflow";
        string method = name + (reporting ? subtract ? "Underflow" : "Overflow" : "");
        string theorem = (sse ? "sse_" : "") + (reporting ? flag + "_" : "") + "profile_correctness";
        string module = vector ? "Vector256Entry" : subtract ? "AcceleratedContract" :
            sse ? "SSEContract" : reporting ? "ARMOverflowContract" : "ARMContract";
        string prefix = vector ? "AVX2" : sse ? "SSE4.2" : "AdvSimd";
        string meaning = subtract ? "difference" : "sum";
        string documentation = !reporting ? $"wrapping {meaning} of the initial operands, checked " +
            (vector ? "return" : "finite return") + ", writable output, caller bytes kept." :
            vector ? $"exact initial-operand {(subtract ? "borrow" : "carry")}, wrapping {meaning}, " +
                "writable output, caller bytes kept." :
            subtract ? "exact underflow flag and wrapping difference through the same certified call graph." :
                "exact unsigned carry and wrapping sum of the initial operands, checked return, caller bytes kept.";
        string contract = !reporting ? $"WrappingBinaryContract (· {operation} ·)" :
            subtract ? "ReportingBinaryContract (· - ·) " + (vector ?
                "(fun left right => decide (left.toNat < right.toNat))\n     " :
                "(fun a b => decide (a.toNat < b.toNat))") :
            "ReportingBinaryContract " + (vector ? "(· + ·)" : "(fun left right => left + right)") +
                "\n      (fun left right => decide (2^256 ≤ left.toNat + right.toNat))";
        string signature = (reporting || subtract && !vector ? "\n    " : " ") +
            "UInt256Model.Safety." + contract + " Extracted.program 0 :=";
        string call;
        if (vector)
            call = $"Vector256.{name.ToLowerInvariant()}{(reporting ? "_" + flag : "")}_contract " +
                $"Extracted.program Extracted.profile {(profile == "x64-v4" ? "true" : "false")}" +
                (subtract ? " true rfl rfl rfl\n    ⟨rfl, rfl, rfl, rfl, rfl⟩" :
                    " rfl rfl rfl rfl\n    ⟨rfl, rfl, rfl, rfl⟩");
        else if (subtract)
            call = $"checked_accelerated_{(reporting ? "underflow" : "subtract")}_contract " +
                "Extracted.program 0 1 2 3 4 5 6 Extracted.profile rfl (by decide) (by decide) (by decide)\n" +
                "    rfl rfl rfl rfl rfl rfl rfl";
        else
            call = $"checked_{(sse ? "sse" : "arm")}_add{(reporting ? "_overflow" : "")}_contract " +
                "Extracted.program 0 1 2 3 4 " + (sse ? "5 " : "") + "Extracted.profile " +
                string.Join(' ', Enumerable.Repeat("rfl", sse ? 11 : 7));
        string opened = vector ? "" : "open " + (subtract ? "Profile" : "Safety") + "\n";
        return $$"""
            import Extracted
            import UInt256.Methods.{{name}}.{{module}}

            namespace UInt256Proof.{{name}}
            {{opened}}
            /-- {{prefix}} {{method}}: {{documentation}} -/
            theorem {{theorem}} :{{signature}}
              {{call}}
            end UInt256Proof.{{name}}
            """ + (subtract && !vector ? "" : "\n");
    }

    private static string Multiply(string method)
    {
        bool direct = method == "Multiply", instance = method == "MultiplyInstance";
        bool primitive = !direct && !instance && method != "OperatorMultiplyUInt256UInt256";
        bool narrow = method.Contains("UInt32", StringComparison.Ordinal);
        string first = method.EndsWith("UInt256", StringComparison.Ordinal) ? "true" : "false";
        string width = narrow ? "32" : "64", offset = direct ? "0" : "1";
        string full = $"(Full.fullBody Extracted.profile (profileIndices Extracted.profile {offset}).word " +
            (direct ? "4 6)" : "5 7)");
        string imports = primitive ? "import UInt256.Methods.Multiply.EntryPrimitiveSafety\n" :
            instance ? "import UInt256.Safety.BinaryForwarder\n" : "";
        string contract = primitive ? $"OrderedScalarContract {first} CIL.Value.i{width} " +
            "(fun input word => encoded (input * BitVec.ofNat 256 word.toNat))" :
            (direct || instance ? "WrappingBinaryContract" : "AggregateReturn.BinaryContract") + " (· * ·)";
        string adaptation = primitive ? "OrderedScalarContract" : direct || instance ? "WrappingBinaryContract" :
            "AggregateReturn.BinaryContract";
        string contracts = "(profile_word_contract context rfl) (profile_top_contract context rfl)";
        string arguments = "context " + contracts;
        string proof = primitive ? $"primitive{width}_with_contracts primitiveContext rfl " + contracts :
            instance ? "UInt256Model.Safety.forward_wrapping_binary embedded 0 1 Extracted.method0 (· * ·)\n" +
                "    rfl rfl rfl rfl rfl rfl rfl\n    (multiply_checked_contract " + arguments + ")" :
            direct ? "multiply_checked_contract " + arguments :
                "UInt256Model.Safety.AggregateReturn.binary_checked (· * ·) Extracted.profile embedded 0 1 rfl\n" +
                "    (initialized_result " + arguments + ")";
        string extra = primitive ? "private def primitiveContext : PrimitiveContext := ⟨context, 0, " +
            "(profileIndices Extracted.profile 1).word + 1, (profileIndices Extracted.profile 1).word + 2, " +
            $"{(narrow ? "true" : "false")}, {first}, rfl, rfl, rfl⟩\n" : "";
        string embedded = $"private abbrev embedded : CIL.Program := Extracted.program.set {(direct ? 1 : 2)} {full}";
        string embedding = $"private theorem fullEmbeds : CIL.MethodEmbeds Extracted.program " +
            $"{(direct ? 1 : 2)} {full} := by cil_embed";
        return $$"""
            import Extracted
            import UInt256.Safety.EmbeddingTransport
            import UInt256.Methods.Multiply.ProfileLayout
            {{imports}}
            namespace UInt256Proof.{{method}}
            open {{(direct ? "Entry" : "UInt256Proof.Multiply UInt256Proof.Multiply.Entry")}}
            -- The extraction may add dead blocks to the full-width body; `fullEmbeds` checks every live instruction.
            {{embedded}}
            {{embedding}}
            private def context : Context :=
              profileContext (profileIndices Extracted.profile {{offset}}) Extracted.profile embedded {{
                string.Join(' ', Enumerable.Repeat("rfl", 8))}}
            {{extra}}theorem profile_correctness : UInt256Model.Safety.{{contract}} Extracted.program 0 :=
              UInt256Model.Safety.{{adaptation}}.of_embeds fullEmbeds <|
              {{proof}}
            end UInt256Proof.{{method}}
            """ + "\n";
    }

    private static string PrimitiveEquals(string method, int width, bool signed, bool vector)
    {
        string family = vector ? "vector" : "scalar";
        string helper = vector ? "VectorPrimitiveWrapper" : "UnsignedPrimitive";
        string imports = "import UInt256.Methods.Equality.PrimitiveProfileBindings\n" +
            (signed && vector ? "import UInt256.Methods.Equality.VectorPrimitiveWrapper\n" : "") +
            "import Extracted\nimport UInt256.Methods.Equality." + (signed ? "SignedPrimitive" : helper);
        string documentation = signed ?
            "Signed primitive equality rejects negative inputs and preserves caller bytes." :
            "Primitive equality with finite checked return and preservation of all caller bytes.";
        string predicate = (signed ? "!decide (word.toInt < 0) && " : "") +
            "decide (input = BitVec.ofNat 256 word.toNat)";
        string gap = signed ? "\n      " : " ";
        string proof = signed ?
            $"UInt256Proof.Equality.SignedPrimitive.checked{width} Extracted.profile Extracted.program 0 1 rfl\n" +
            $"    (UInt256Proof.Equality.{helper}.checked{width} Extracted.profile Extracted.program 1 2" +
            (vector ? " rfl rfl rfl)" : " 3 rfl rfl rfl rfl)") :
            $"UInt256Proof.Equality.{helper}.checked{width}\n    Extracted.profile Extracted.program 0 1" +
            (vector ? " rfl rfl rfl" : " 2 rfl rfl rfl rfl");
        string theorem = $"UInt256Proof.Equality.{method}.{family}";
        string transport = "(UInt256Proof.Equality.ProfileBindings.primitive_agreement profile vector) " +
            theorem + "_correctness";
        return $$"""
            {{imports}}

            /-- {{documentation}} -/
            theorem {{theorem}}_correctness :
                UInt256Model.Safety.ScalarOperatorContract false false CIL.Value.i{{width}}
                  (fun input word => {{predicate}}){{gap}}Extracted.program 0 :=
              {{proof}}
            {{(vector ? "\n" : "")}}
            theorem {{theorem}}_family (profile : CIL.FeatureProfile)
                (vector : Extracted.profile.vector256Accelerated = profile.vector256Accelerated) :
                UInt256Model.Safety.ScalarOperatorContract false false CIL.Value.i{{width}}
                  (fun input word => {{predicate}}){{gap}}(CIL.reprofile Extracted.program profile) 0 :=
              UInt256Model.Safety.ScalarOperatorContract.reprofile UInt256Proof.Equality.ProfileBindings.uniform
                {{transport}}
            """ + "\n";
    }

    private static string FullComparison(string name, string operation, string audit, string binding, string family)
    {
        bool native = family == "avx512";
        string theorem = $"UInt256Proof.Compare.{name}UInt256UInt256.{family}";
        string entry = native ? "0" : "Extracted.entryIndex";
        string imports = native ? "import Extracted\nimport UInt256.Methods.Compare.NativeEntrySafety" :
            (family == "avx2" && name is "Lt" or "Le" ? "\n" : "") +
            $"import UInt256.Methods.Compare.{audit}FamilySafetyAudit";
        string documentation = native ? "" :
            "/-- Unsigned ordering of the initial UInt256 values, checked finite return,\n" +
            "    and preservation of caller memory. -/\n";
        string proof = native ? " by\n  have proof := UInt256Proof.Compare.Safety.native_entry_checked " +
            $"Extracted.profile {(name is "Lt" or "Le" ? "true" : "false")} " +
            $"{(name is "Le" or "Ge" ? "true" : "false")} Extracted.program 0 1 rfl rfl rfl rfl rfl rfl\n" +
            "  simpa [UInt256Proof.Compare.Safety.nativePredicate] using proof.to_contract" :
            "\n  UInt256Proof.Compare.Safety.checked_" + binding + "_binding";
        string predicate = "(fun values => .i32 (if (values[0]?.getD 0).toNat " + operation +
            " (values[1]?.getD 0).toNat then 1 else 0))";
        string vector = "(vector : Extracted.profile.avx512FVL = false → Extracted.profile.avx2 = false → " +
            "Extracted.profile.vector256Accelerated = profile.vector256Accelerated) :";
        string transport = "UInt256Model.Safety.ReadOnlyContract.reprofile " +
            "UInt256Proof.Compare.ProfileBindings.uniform " +
            "(UInt256Proof.Compare.ProfileBindings.agreement profile valid native avx2 vector) " +
            theorem + "_correctness";
        return $$"""
            import UInt256.Methods.Compare.ProfileBindings
            {{imports}}

            {{documentation}}theorem {{theorem}}_correctness :
                UInt256Model.Safety.ReadOnlyContract
                  {{predicate}}
                  Extracted.program {{entry}} 2 :={{proof}}


            theorem {{theorem}}_family (profile : CIL.FeatureProfile) (valid : profile.Valid)
                (native : Extracted.profile.avx512FVL = profile.avx512FVL)
                (avx2 : Extracted.profile.avx512FVL = false → Extracted.profile.avx2 = profile.avx2)
                {{vector}}
                UInt256Model.Safety.ReadOnlyContract
                  {{predicate}}
                  (CIL.reprofile Extracted.program profile) {{entry}} 2 :=
              {{transport}}
            """ + "\n";
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
