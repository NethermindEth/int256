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
}
