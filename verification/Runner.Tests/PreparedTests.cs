// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System.Text.Json.Nodes;
using System.Text.RegularExpressions;
using UInt256Verification;

namespace UInt256VerificationTests;

internal static class PreparedTests
{
    internal static void Register(Action<string, Action<Catalog, string>> check)
    {
        check("bitwise gates bind each operation, returned value and scalar constructor path", (catalog, _) =>
        {
            foreach (var (method, operation, symbol) in new[] { ("Xor", "xor", "^^^"), ("And", "and", "&&&"), ("Or", "or", "|||") })
            {
                var gate = SafetyCatalog.Gate(method, "x64-vector256"); string source = SafetyGates.Module(catalog, method, "x64-vector256");
                Contract(gate, "WrappingBinaryContract"); Family(gate, true);
                Program.Require(gate["generatedAudit"]!.GetValue<bool>(), "Bitwise audit not generated");
                Contains(source, $"left {symbol} right", $"vectorOperation = .{operation} from rfl");
                string returned = "Operator" + method;
                Contract(SafetyCatalog.Gate(returned, "x64-vector256"), "ReadOnlyContract");
                source = SafetyGates.Module(catalog, returned, "x64-vector256");
                Contains(source, "import UInt256.Methods.Bitwise.ReturnSafetyContract", $".v256 ((values[0]?.getD 0) {symbol} (values[1]?.getD 0))", "using return_contract");
                Absent(source, "binaryIndex = Extracted.entryIndex");
            }
            foreach (var (method, contract, expression) in new[] { ("Not", "InitializedUnaryContract", "fun input => ~~~input"), ("OperatorNot", "ReadOnlyContract", ".v256 (~~~(values[0]?.getD 0))") })
            {
                var gate = SafetyCatalog.Gate(method, "x64-vector256"); Contract(gate, contract); Family(gate, true);
                string source = SafetyGates.Module(catalog, method, "x64-vector256"); Contains(source, expression, $"{contract}.reprofile"); Absent(source, "vectorOperation");
            }
            foreach (string method in new[] { "Xor", "And", "Or", "Not", "OperatorXor", "OperatorAnd", "OperatorOr", "OperatorNot" })
            {
                Family(SafetyCatalog.Gate(method, "scalar"), false);
                string source = SafetyGates.Module(catalog, method, "scalar"); Contains(source, "UInt256Proof.Bitwise.ScalarSafety"); Absent(source, "vectorOperation", "vector_entry");
                if (!method.StartsWith("Operator", StringComparison.Ordinal)) Contains(source, "scalarIndex = Extracted.entryIndex from rfl");
                if (!method.Contains("Not", StringComparison.Ordinal)) Contains(source, $"scalarOperation = .{method.Replace("Operator", "", StringComparison.Ordinal).ToLowerInvariant()} from rfl");
                Program.Reject(() => SafetyCatalog.Gate(method, "arm64"));
            }
        });
        check("scalar equality operator gates bind order, signedness, polarity and profile transfer", (catalog, _) =>
        {
            Program.Require(SafetyCatalog.Operators.Count == 16, "Equality operator inventory changed");
            foreach (var (method, scalar) in SafetyCatalog.Operators)
            {
                foreach (string profile in new[] { "scalar", "x64-vector256" })
                {
                    var gate = SafetyCatalog.Gate(method, profile); Family(gate, profile == "x64-vector256");
                    Program.Require(gate["generatedAudit"]!.GetValue<bool>() && gate["theorems"]!.AsArray().Select(Catalog.Text).Contains("UInt256Proof.SafetySelected.checked_family_contract"), "Operator family audit missing");
                    string source = SafetyGates.Module(catalog, method, profile);
                    Contains(source, $"ScalarOperatorContract {scalar.First.ToString().ToLowerInvariant()} {scalar.Negate.ToString().ToLowerInvariant()} CIL.Value.i{scalar.Width}",
                        scalar.Signed ? "right.toInt" : "right.toNat : Int", "CIL.storage_profile_agreement Extracted.program (by decide)", "(CIL.reprofile Extracted.program profile)");
                    Program.Require(source.Split("#print axioms", StringSplitOptions.None).Length == 4, "Operator audit count changed");
                }
                Program.Reject(() => SafetyCatalog.Gate(method, "x64-sse41"));
            }
        });
        check("equality reference, snapshot and primitive gates retain exact independent contracts", (_, _) =>
        {
            var equality = SafetyCatalog.Gate("EqUInt256UInt256", "scalar"); Contract(equality, "ReadOnlyContract"); EqualityAudits(equality, "equality");
            foreach (string method in new[] { "EqUInt256UInt256", "EqualsUInt256Ref", "NeUInt256UInt256", "EqualsUInt256Value" })
            foreach (var (profile, prefix) in new[] { ("scalar", ""), ("x64-sse41", "Sse"), ("x64-vector256", "Vector") })
            {
                var gate = SafetyCatalog.Gate(method, profile);
                JsonObject family = new() { ["vector256Accelerated"] = profile == "x64-vector256" };
                if (profile != "x64-vector256") family["sse41"] = profile == "x64-sse41";
                Program.Require(JsonNode.DeepEquals(gate["coverage"]!["family"], family) && gate["theorems"]!.AsArray().Count == 3, "Reference family scope/audits changed");
                if (method == "EqualsUInt256Value") { Contract(gate, "ReadOnlyValueContract"); EqualityTarget(gate, prefix + "Value"); EqualityAudits(gate, "value"); }
                else if (profile != "scalar") EqualityTarget(gate, prefix + (method == "NeUInt256UInt256" ? "Negation" : ""));
                if (method == "EqUInt256UInt256" && profile == "x64-vector256") Program.Require(JsonNode.DeepEquals(gate["theorems"], equality["theorems"]), "Vector equality audits differ");
            }
            foreach (string method in new[] { "EqUInt256UInt256", "EqualsUInt256Value" }) Program.Reject(() => SafetyCatalog.Gate(method, "x64-avx2"));
            foreach (string method in new[] { "Add", "Subtract", "LtUInt256UInt64" }) Program.Reject(() => SafetyCatalog.Gate(method, "x64-vector256"));
            Program.Reject(() => SafetyCatalog.Gate("Add", "x64-sse41"));
            foreach (int width in new[] { 32, 64 })
            foreach (bool signed in new[] { false, true })
            foreach (string profile in new[] { "scalar", "x64-vector256" })
            {
                string method = $"Equals{(signed ? "Int" : "UInt")}{width}";
                var gate = SafetyCatalog.Gate(method, profile); Contract(gate, "ReadOnlyScalarContract"); Family(gate, profile == "x64-vector256");
                string stem = signed ? $"Signed{width}" : $"Primitive{(width == 64 && profile == "scalar" ? "" : width.ToString())}";
                EqualityTarget(gate, (profile == "scalar" ? "" : "Vector") + stem);
                Program.Require(Catalog.Text(gate["profile"]) == profile && gate["theorems"]!.AsArray().Count == 3 && Catalog.Text(gate["theorems"]!.AsArray()[^1]).EndsWith("_family", StringComparison.Ordinal), "Primitive profile/family audit changed");
                if (signed) EqualityAudits(gate, "signed"); else if (width == 64 && profile == "scalar") EqualityAudits(gate, "primitive");
                Program.Reject(() => SafetyCatalog.Gate(method, "x64-sse41"));
            }
        });
        check("all shift APIs retain exact result, binding and profile-family audits", (_, _) =>
        {
            foreach (var (method, prefix, contract, binding) in new[] { ("Lsh", "", "shift", "shift"), ("Rsh", "Right", "shift", "right_shift"),
                ("LeftShift", "Wrapper", "wrapper", "wrapper"), ("RightShift", "RightWrapper", "wrapper", "right_wrapper"), ("OperatorLsh", "Return", "return", "return"), ("OperatorRsh", "RightReturn", "return", "right_return") })
            {
                var gate = SafetyCatalog.Gate(method, "scalar"); Contract(gate, contract == "return" ? "ReadOnlyScalarContract" : "ShiftContract"); Family(gate, false);
                Program.Require(Catalog.Text(gate["target"]) == $"+UInt256.Methods.Shift.{prefix}SafetyAudit:olean", "Shift audit target changed");
                Program.Require(gate["theorems"]!.AsArray().Select(Catalog.Text).SequenceEqual(new[] { $"UInt256Proof.Shift.Safety.checked_{contract}_contract", $"UInt256Proof.Shift.Safety.checked_{binding}_binding", $"UInt256Proof.Shift.Safety.checked_{binding}_family_binding" }), "Shift audit bindings changed");
                var vector = SafetyCatalog.Gate(method, "x64-vector256"); Family(vector, true);
                Program.Require(JsonNode.DeepEquals(vector["theorems"], gate["theorems"]), "Vector shift audits changed");
                foreach (string profile in new[] { "x64-sse41", "arm64-advsimd" }) Program.Reject(() => SafetyCatalog.Gate(method, profile));
            }
        });
        check("comparison safety preserves signed-helper interpretation and three-way value contracts", (catalog, _) =>
        {
            string source = SafetyGates.Module(catalog, "GtUInt256UInt32", "scalar");
            foreach (string fragment in new[] { "decide ((input.toNat : Int) > (word.toNat : Int))", "show wrapperSigned32 = false from rfl", "show leafSigned = true from rfl", "UInt256Proof.Compare.zeroExtend32_toInt" })
                Program.Require(source.Contains(fragment, StringComparison.Ordinal), "Unsigned comparison meaning changed");
            JsonObject reference = SafetyCatalog.Gate("CompareToUInt256Ref", "scalar"), value = SafetyCatalog.Gate("CompareToUInt256Value", "scalar");
            foreach (var (gate, module, theorem) in new[] { (reference, "ThreeWay", "threeWay"), (value, "ThreeWayValue", "threeWayValue") })
            {
                Program.Require(Catalog.Text(gate["target"]) == $"+UInt256.Methods.Compare.{module}SafetyAudit:olean", "Three-way audit target changed");
                Program.Require(gate["theorems"]!.AsArray().Select(Catalog.Text).SequenceEqual(new[] { "contract", "binding", "family" }.Select(kind => $"UInt256Proof.Compare.Safety.checked_{theorem}_{kind}")), "Three-way required audits changed");
                Program.Require(Catalog.Text(gate["coverage"]!["kind"]) == "all-profiles", "Three-way profile independence lost");
            }
            Program.Require(Catalog.Text(value["contract"]) == "UInt256Model.Safety.ReadOnlyValueContract" && JsonNode.DeepEquals(reference["coverage"], value["coverage"]), "By-value three-way contract changed");
        });
        check("relational safety binds each relation and dispatch family to its own audits", (_, _) =>
        {
            foreach (var (method, relation, module) in new[] { ("LtUInt256UInt256", "less", ""), ("GtUInt256UInt256", "greater", "Greater"),
                ("LeUInt256UInt256", "less_equal", "LessEqual"), ("GeUInt256UInt256", "greater_equal", "GreaterEqual") })
            foreach (var (profile, prefix, family) in new[] {
                ("scalar", "", "{\"avx512FVL\":false,\"avx2\":false,\"vector256Accelerated\":false}"),
                ("x64-vector256", "Portable", "{\"avx512FVL\":false,\"avx2\":false,\"vector256Accelerated\":true}"),
                ("x64-avx2", "", "{\"avx512FVL\":false,\"avx2\":true}"),
                ("x64-avx512", "Native", "{\"avx512FVL\":true}") })
            {
                JsonObject gate = SafetyCatalog.Gate(method, profile);
                Program.Require(Catalog.Text(gate["target"]) == $"+UInt256.Methods.Compare.{prefix}{module}FamilySafetyAudit:olean", "Relation/ISA audit target changed");
                Program.Require(Catalog.Text(gate["contract"]) == "UInt256Model.Safety.ReadOnlyContract", "Relational memory/result contract changed");
                Program.Require(gate["theorems"]!.AsArray().Select(Catalog.Text).SequenceEqual(new[] { "contract", "binding", "family" }.Select(kind => $"UInt256Proof.Compare.Safety.checked_{relation}_{kind}")), "Relational audits changed");
                Program.Require(JsonNode.DeepEquals(gate["coverage"]!["family"], JsonNode.Parse(family)), "Comparison dispatch family changed");
                Program.Reject(() => SafetyCatalog.Gate(method, "arm64"));
            }
            Program.Reject(() => SafetyCatalog.Gate("LeUInt64UInt256", "x64-vector256"));
            Program.Require(JsonNode.DeepEquals(SafetyCatalog.Gate("LtUInt256UInt256", "scalar")["coverage"], SafetyCatalog.Gate("GtUInt256UInt256", "scalar")["coverage"]), "Reversed comparison coverage changed");
        });
        check("Add and Subtract representative safety gates retain exact arithmetic and reporting bindings", (_, _) =>
        {
            void Representative(string method, string profile, string contract, string? target, params string[] names)
            {
                JsonObject gate = SafetyCatalog.Representative(method, profile);
                Program.Require(Catalog.Text(gate["contract"]) == "UInt256Model.Safety." + contract && Catalog.Text(gate["profile"]) == profile, "Wrong representative contract/profile");
                if (target is not null) Program.Require(Catalog.Text(gate["target"]) == $"+UInt256.Methods.{target}:olean", "Wrong representative audit module");
                Program.Require(gate["theorems"]!.AsArray().Select(Catalog.Text).SequenceEqual(names) && !gate.ContainsKey("coverage"), "Representative audits changed or gained unconditional coverage");
            }
            foreach (string profile in new[] { "x64-avx2", "x64-avx2-bmi1", "x64-avx512", "x64-avx512-bmi1" })
            {
                Representative("Add", profile, "WrappingBinaryContract", "Add.VectorSafetyAudit", "UInt256Proof.Add.Safety.checked_vector_parent_contract", "UInt256Proof.Add.Safety.checked_vector_add_binding");
                Representative("AddOverflow", profile, "ReportingBinaryContract", "Add.VectorOverflowSafetyAudit", "UInt256Proof.Add.Safety.checked_vector_reporting_contract", "UInt256Proof.Add.Safety.checked_vector_overflow_binding");
                Representative("Subtract", profile, "WrappingBinaryContract", "Subtract.VectorWrappingSafetyAudit", "UInt256Proof.Subtract.Safety.checked_vector_wrapping_contract", "UInt256Proof.Subtract.Safety.checked_vector_wrapping_binding");
                Representative("SubtractUnderflow", profile, "ReportingBinaryContract", "Subtract.VectorUnderflowSafetyAudit", "UInt256Proof.Subtract.Safety.checked_vector_underflow_contract", "UInt256Proof.Subtract.Safety.checked_vector_underflow_binding");
            }
            foreach (var (isa, profile) in new[] { ("arm", "arm64-advsimd"), ("sse", "x64-sse42") })
            {
                Representative("Add", profile, "WrappingBinaryContract", $"Add.{isa.ToUpperInvariant()}SafetyAudit", $"UInt256Proof.Add.Safety.checked_{isa}_add_contract", $"UInt256Proof.Add.Safety.checked_{isa}_add_binding");
                Representative("AddOverflow", profile, "ReportingBinaryContract", $"Add.{isa.ToUpperInvariant()}OverflowSafetyAudit", $"UInt256Proof.Add.Safety.checked_{isa}_overflow_contract", $"UInt256Proof.Add.Safety.checked_{isa}_overflow_binding");
                Representative("Subtract", profile, "WrappingBinaryContract", "Subtract.Vector128SafetyAudit", "UInt256Proof.Subtract.Safety.checked_vector128_wrapping_contract", "UInt256Proof.Subtract.Safety.checked_vector128_wrapping_binding");
                Representative("SubtractUnderflow", profile, "ReportingBinaryContract", "Subtract.Vector128UnderflowSafetyAudit", "UInt256Proof.Subtract.Safety.checked_vector128_underflow_contract", "UInt256Proof.Subtract.Safety.checked_vector128_underflow_binding");
            }
            Representative("Subtract", "scalar", "WrappingBinaryContract", "Subtract.SafetyAudit", "UInt256Proof.Subtract.Safety.checked_wrapping_contract", "UInt256Proof.Subtract.Safety.checked_wrapping_binding");
            Representative("AddOverflow", "scalar", "ReportingBinaryContract", null, "UInt256Proof.Safety.checked_overflow_contract", "UInt256Proof.Safety.checked_overflow_binding");
            Representative("SubtractUnderflow", "scalar", "ReportingBinaryContract", null, "UInt256Proof.Subtract.Safety.checked_underflow_contract", "UInt256Proof.Subtract.Safety.checked_underflow_binding");
            foreach (string method in new[] { "Add", "Subtract" })
                foreach (string profile in new[] { "x64-sse41", "x64-vector256" }) Program.Reject(() => SafetyCatalog.Representative(method, profile));
            Program.Reject(() => SafetyCatalog.Representative("AddOverflow", "arm64"));
        });
        check("every production arithmetic and safety gate has a complete import closure", (catalog, _) =>
        {
            string verification = Path.Combine(Directory.GetCurrentDirectory(), "verification"); HashSet<string> seen = [];
            void Visit(string module, string? source = null)
            {
                if (module == "Extracted" || module.Split('.')[0] is "Lean" or "Std" or "Init") return;
                if (source is null)
                {
                    if (!seen.Add(module)) return;
                    string path = Path.Combine(verification, module.Replace('.', '/') + ".lean");
                    Program.Require(File.Exists(path), $"Missing production import: {module}"); source = File.ReadAllText(path);
                }
                foreach (Match match in Regex.Matches(source, @"^import (\S+)", RegexOptions.Multiline)) Visit(match.Groups[1].Value);
            }
            foreach (JsonNode? job in catalog.Plan(catalog.MethodNames, safety: true)["include"]!.AsArray())
            {
                string method = Catalog.Text(job!["method"]), profile = Catalog.Text(job["profile"]);
                if (Catalog.Legacy.Contains(method)) Visit(method == "Add" ? "Audit" : "SubtractAudit");
                else Visit("SelectedGate", AuditGates.Module(catalog.Entries()[method]));
                JsonObject gate = SafetyCatalog.Gate(method, profile);
                if (gate["generatedAudit"]?.GetValue<bool>() == true) Visit("SelectedSafetyGate", SafetyGates.Module(catalog, method, profile));
                else Visit(Catalog.Text(gate["target"]).TrimStart('+').Replace(":olean", "", StringComparison.Ordinal));
            }
        });
        check("CIL imports stay independent of consumers and editor files are excluded", (_, manifests) =>
        {
            foreach (string path in Workspace.SourceFiles(Path.Combine(Directory.GetCurrentDirectory(), "verification/CIL"), [".lean"]))
                foreach (Match match in Regex.Matches(File.ReadAllText(path), @"^import (\S+)", RegexOptions.Multiline))
                    Program.Require(!match.Groups[1].Value.StartsWith("UInt256", StringComparison.Ordinal) && !match.Groups[1].Value.StartsWith("Extracted", StringComparison.Ordinal), $"Consumer import in {path}");
            string root = Path.Combine(Path.GetDirectoryName(manifests)!, "editor");
            foreach (string name in new[] { "Code.cs", "manifest.json", ".vs/v17/DocumentLayout.json", ".vs/Generated.cs" })
            {
                string path = Path.Combine(root, name); Directory.CreateDirectory(Path.GetDirectoryName(path)!); File.WriteAllText(path, "test input");
            }
            Program.Require(Workspace.SourceFiles(root, [".cs", ".json"]).Select(p => Workspace.Relative(root, p)).ToHashSet().SetEquals(["Code.cs", "manifest.json"]), "Editor state became a verification input");
        });
        check("all safety gates expose runtime alignment assumptions and require every named audit", (catalog, _) =>
        {
            foreach (JsonNode? job in catalog.Plan(catalog.MethodNames, safety: true)["include"]!.AsArray())
            {
                JsonObject gate = SafetyCatalog.Gate(Catalog.Text(job!["method"]), Catalog.Text(job["profile"]));
                JsonNode policy = gate["alignmentPolicy"]!, limitation = gate["modelLimitations"]![0]!;
                Program.Require(Catalog.Text(limitation["kind"]) == "instruction-alignment" && Catalog.Text(limitation["status"]) == "target-runtime-assumption", "Alignment boundary missing");
                Program.Require(policy["ordinaryAccessBytes"]!.GetValue<int>() == 1 && !policy["portableCliGuarantee"]!.GetValue<bool>()
                    && policy["targetArchitectures"]!.AsArray().Select(Catalog.Text).SequenceEqual(new[] { "x64", "arm64" })
                    && policy["excluded"]!.AsArray().Select(Catalog.Text).Contains("aligned memory APIs"), "Alignment scope changed");
                string[] names = gate["theorems"]!.AsArray().Select(Catalog.Text).ToArray();
                foreach (string omitted in names)
                    Program.Reject(() => ProofAudits.Check(string.Join('\n', names.Where(n => n != omitted).Select(n => $"'{n}' depends on axioms: []")), names, []));
            }
        });
        check("classified and multiplication gates retain exact contracts and family transfer", (catalog, _) =>
        {
            foreach (string method in new[] { "Add", "Subtract", "AddOverflow", "SubtractUnderflow" })
            foreach (string profile in Catalog.Profiles)
            {
                JsonObject gate = SafetyCatalog.Gate(method, profile), representative = SafetyCatalog.Representative(method, profile);
                Program.Require(Catalog.Text(gate["target"]) == "+UInt256.Methods.SelectedSafetyGate:olean" && gate["generatedAudit"]!.GetValue<bool>()
                    && Catalog.Text(gate["coverage"]!["kind"]) == "feature-family", "Classified family gate changed");
                Program.Require(gate["theorems"]!.AsArray().Select(Catalog.Text).SequenceEqual(representative["theorems"]!.AsArray().Select(Catalog.Text).Append("UInt256Proof.SafetySelected.checked_family_contract")), "Classified audits changed");
                string source = SafetyGates.Module(catalog, method, profile);
                foreach (string expected in new[] { "import " + Catalog.Text(representative["target"])[1..].Split(':')[0], Catalog.Text(representative["theorems"]!.AsArray()[^1]), "same_family_profile_agreement", "profile.classify = Extracted.profile.classify" })
                    Program.Require(source.Contains(expected, StringComparison.Ordinal), "Family transfer binding missing");
            }
            foreach (string method in new[] { "Multiply", "MultiplyInstance", "OperatorMultiplyUInt256UInt256", "OperatorMultiplyUInt256UInt32", "OperatorMultiplyUInt32UInt256", "OperatorMultiplyUInt256UInt64", "OperatorMultiplyUInt64UInt256" })
            foreach (string profile in Catalog.MultiplyProfiles)
            {
                JsonObject gate = SafetyCatalog.Gate(method, profile);
                string contract = method.Contains("UInt32", StringComparison.Ordinal) || method.Contains("UInt64", StringComparison.Ordinal) ? "OrderedScalarContract"
                    : method.StartsWith("Operator", StringComparison.Ordinal) ? "ReadOnlyContract" : "WrappingBinaryContract";
                Program.Require(Catalog.Text(gate["contract"]) == "UInt256Model.Safety." + contract && gate["generatedAudit"]!.GetValue<bool>(), "Multiplication contract changed");
                if (contract == "OrderedScalarContract")
                {
                    int width = method.Contains("UInt32", StringComparison.Ordinal) ? 32 : 64; string first = method.StartsWith($"OperatorMultiplyUInt{width}", StringComparison.Ordinal) ? "true" : "false";
                    string source = SafetyGates.Module(catalog, method, profile);
                    foreach (string expected in new[] { $"OrderedScalarContract {first} CIL.Value.i{width}", "input * BitVec.ofNat 256 scalar.toNat", "OrderedScalarContract.reprofile" })
                        Program.Require(source.Contains(expected, StringComparison.Ordinal), "Scalar multiplication binding missing");
                }
            }
            foreach (string method in new[] { "OperatorMultiplyUInt256UInt64", "Multiply" }) Program.Reject(() => SafetyCatalog.Gate(method, "x64-sse41"));
        });
        check("primitive comparison registry distinguishes scalar references from value arguments", (_, _) =>
        {
            var expected = (from scalar in new[] { "Int32", "UInt32", "Int64", "UInt64" } from operands in new[] { scalar + "UInt256", "UInt256" + scalar }
                from relation in new[] { "Lt", "Le", "Gt", "Ge" } select relation + operands).Where(name => name != "LeUInt64UInt256").ToHashSet();
            Program.Require(expected.SetEquals(SafetyCatalog.PrimitiveComparisons.Keys), "Primitive comparison inventory changed");
            foreach (string method in expected)
            {
                var gate = SafetyCatalog.Gate(method, "scalar");
                Program.Require(Catalog.Text(gate["contract"]) == "UInt256Model.Safety.ScalarOperatorContract" && Catalog.Text(gate["coverage"]!["kind"]) == "all-profiles" && gate["generatedAudit"]!.GetValue<bool>(), "Scalar reference contract changed");
            }
            var value = SafetyCatalog.Gate("LeUInt64UInt256", "scalar");
            Program.Require(Catalog.Text(value["contract"]) == "UInt256Model.Safety.ScalarValueContract" && Catalog.Text(value["coverage"]!["kind"]) == "all-profiles" && !value.ContainsKey("generatedAudit"), "By-value argument received reference contract");
        });
    }

    private static void Contract(JsonObject gate, string name) => Program.Require(Catalog.Text(gate["contract"]) == "UInt256Model.Safety." + name, "Independent safety contract changed");
    private static void Family(JsonObject gate, bool vector) => Program.Require(JsonNode.DeepEquals(gate["coverage"]!["family"], new JsonObject { ["vector256Accelerated"] = vector }), "Storage family changed");
    private static void Contains(string source, params string[] fragments) { foreach (string fragment in fragments) Program.Require(source.Contains(fragment, StringComparison.Ordinal), "Missing safety binding: " + fragment); }
    private static void Absent(string source, params string[] fragments) { foreach (string fragment in fragments) Program.Require(!source.Contains(fragment, StringComparison.Ordinal), "Unexpected safety binding: " + fragment); }
    private static void EqualityTarget(JsonObject gate, string prefix) => Program.Require(Catalog.Text(gate["target"]) == $"+UInt256.Methods.Equality.{prefix}SafetyAudit:olean", "Equality target changed");
    private static void EqualityAudits(JsonObject gate, string stem) => Program.Require(gate["theorems"]!.AsArray().Select(Catalog.Text).SequenceEqual(new[] { "contract", "binding", "family" }.Select(kind => $"UInt256Proof.Equality.Safety.checked_{stem}_{kind}")), "Equality audits changed");
}
