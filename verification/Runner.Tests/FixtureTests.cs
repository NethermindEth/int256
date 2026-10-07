// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System.Text.Json.Nodes;
using UInt256Verification;

namespace UInt256VerificationTests;

internal static class FixtureTests
{
    internal static void Register(Action<string, Action<Catalog, string>> check)
    {
        check("refutation templates preserve substitution order and require checked theorem audits", (_, manifests) =>
        {
            Program.Require(FixtureChecks.ExpandRefutation("@FIRST@", new Dictionary<string, string> { ["FIRST"] = "@SECOND@", ["SECOND"] = "value" }) == "value", "Substitution order changed");
            Program.Reject(() => FixtureChecks.ExpandRefutation("@UNBOUND@", []));
            string proof = Path.GetDirectoryName(manifests)!, template = Path.Combine(proof, "Refutation.lean.in");
            File.WriteAllText(template, "theorem @NAME@ : @VALUE@ = @VALUE@ := rfl\n#print axioms @NAME@\n");
            string output = "'checked' does not depend on any axioms";
            bool failed = false;
            Workspace workspace = new(proof, (command, cwd, stage) =>
            {
                Program.Require(command.SequenceEqual(new[] { "lake", "build", "+Refutation:olean" }) && cwd == proof && stage == "Refutation checking", "Refutation command changed");
                if (failed) throw new InvalidOperationException("Kernel rejection");
                return output;
            });
            void Run(bool register = false) => FixtureChecks.Refutation(workspace, proof, "lake", template,
                new Dictionary<string, string> { ["NAME"] = "checked", ["VALUE"] = "18446744073709551615" }, "Refutation", "checked", ["propext"], register);
            Run(true);
            Program.Require(File.ReadAllText(Path.Combine(proof, "Refutation.lean")).Contains("18446744073709551615", StringComparison.Ordinal), "Large numeral changed");
            string configuration = File.ReadAllText(Path.Combine(proof, "lakefile.toml"));
            Run();
            Program.Require(File.ReadAllText(Path.Combine(proof, "lakefile.toml")) == configuration, "Unrequested library registration");
            foreach (string invalid in new[] { "", "'other' does not depend on any axioms", "'checked' depends on axioms: [sorryAx]", output + "\n" + output })
            {
                output = invalid;
                Program.Reject(() => Run());
            }
            failed = true;
            Program.Reject(() => Run());
        });
        check("SIMD fixture changes target the selected helper and reachable feature expressions", (_, _) =>
        {
            JsonObject Artifact(params string[] signatures) => new()
            {
                ["methods"] = new JsonArray(signatures.Select(signature => (JsonNode)new JsonObject { ["signature"] = signature,
                    ["instructions"] = new JsonArray(new JsonObject { ["opcode"] = "call", ["operand"] = "Feature::get_IsSupported()", ["Offset"] = 0 }) }).ToArray()),
                ["coverage"] = new JsonArray(signatures.Select(signature => (JsonNode)new JsonObject { ["method"] = signature, ["reachable"] = new JsonArray(0) }).ToArray())
            };
            foreach (string method in new[] { "Add", "Subtract" })
                foreach (string profile in new[] { "arm64-advsimd", "x64-sse42", "x64-avx2", "x64-avx512" })
                    foreach (string name in new[] { "LaneLocals", "InlineCarry", "EquivalentMask", "ExtractedHelper", "ReversedStore" })
                    {
                        string target = name == "ReversedStore" ? "StoreLimbs" : name == "EquivalentMask" ? (method == "Add" ? "PrepareAdd" : "SubtractImpl")
                            : name == "ExtractedHelper" && profile.StartsWith("x64-avx", StringComparison.Ordinal) ? (method == "Add" ? "FinishAdd" : "SubtractImpl")
                            : method == "Add" ? "AddVector128" : "SubtractVector128";
                        JsonObject before = Artifact($"::{target}(", "::Other(");
                        JsonObject after = before.DeepClone().AsObject();
                        after["methods"]![0]!["instructions"]![0]!["operand"] = "changed";
                        SimdFixtures.TargetChanged(name, method, profile, before, after);
                        Program.Reject(() => SimdFixtures.TargetChanged(name, method, profile, before, before));
                        after = before.DeepClone().AsObject(); after["methods"]![1]!["instructions"]![0]!["operand"] = "changed";
                        Program.Reject(() => SimdFixtures.TargetChanged(name, method, profile, before, after));
                        Program.Reject(() => SimdFixtures.TargetChanged(name, method, profile, before, Artifact("::Other(")));
                        Program.Reject(() => SimdFixtures.TargetChanged(name, method, profile, before, Artifact($"::{target}(", $"::{target}(")));
                    }
            JsonObject baseline = Artifact("::Entry("), changed = baseline.DeepClone().AsObject();
            changed["methods"]![0]!["signature"] = "::Renamed(";
            Program.Reject(() => SimdFixtures.TargetChanged("Renamed", "Add", "x64-avx2", baseline, changed));
            changed["methods"]![0]!["instructions"]![0]!["operand"] = "::NewCall(";
            SimdFixtures.TargetChanged("Renamed", "Add", "x64-avx2", baseline, changed);
            changed = baseline.DeepClone().AsObject();
            changed["methods"]![0]!["instructions"]!.AsArray().Add(new JsonObject { ["opcode"] = "call", ["operand"] = "Other::get_IsSupported()", ["Offset"] = 1 });
            Program.Reject(() => SimdFixtures.TargetChanged("FeatureExpressions", "Add", "x64-avx2", baseline, changed));
            changed["coverage"]![0]!["reachable"]!.AsArray().Add(1);
            SimdFixtures.TargetChanged("FeatureExpressions", "Add", "x64-avx2", baseline, changed);
            Program.Reject(() => SimdFixtures.TargetChanged("FeatureExpressions", "Add", "x64-avx2", changed, baseline));
        });
        check("fixture changes require instructions in the intended reachable method", (_, _) =>
        {
            JsonObject baseline = JsonNode.Parse("""
                {"methods":[{"signature":"target","instructions":[{"opcode":"ldc.i4","operand":0}]},{"signature":"unrelated","instructions":[]}]}
                """)!.AsObject();
            foreach (string field in new[] { "opcode", "operand", "scope" })
            {
                JsonObject changed = baseline.DeepClone().AsObject();
                changed["methods"]![0]!["instructions"]![0]![field] = "changed";
                FixtureChecks.ChangedMethod(changed, baseline, "target");
            }
            foreach (string mutation in new[] { "metadata", "offset", "unrelated", "missing-target", "missing-baseline" })
            {
                JsonObject actual = baseline.DeepClone().AsObject(), original = baseline.DeepClone().AsObject();
                switch (mutation)
                {
                    case "metadata": actual["methods"]![0]!["token"] = 123; break;
                    case "offset": actual["methods"]![0]!["instructions"]![0]!["Offset"] = 123; break;
                    case "unrelated": actual["methods"]![1]!["instructions"]!.AsArray().Add(new JsonObject { ["opcode"] = "ret" }); break;
                    case "missing-target": actual["methods"]!.AsArray().RemoveAt(0); break;
                    case "missing-baseline": original["methods"]!.AsArray().RemoveAt(0); break;
                }
                Program.Reject(() => FixtureChecks.ChangedMethod(actual, original, "target"));
            }
        });
        check("fixture prerequisites bind production freshness, safety and unchanged proofs", (_, _) =>
        {
            JsonObject inputs = new() { ["source"] = "current" };
            JsonObject production = new() { ["source"] = new JsonObject { ["kind"] = "production" }, ["sourceInputs"] = inputs.DeepClone(),
                ["leanSourceSha256"] = new JsonObject { ["proof"] = "same" }, ["evidenceKind"] = "arithmetic-and-memory-safety", ["safety"] = SafetyCatalog.Gate("Lsh", "scalar") };
            JsonObject baseline = production.DeepClone().AsObject();
            baseline["source"]!["kind"] = "fixture";
            baseline["generatedProgramSha256"] = "baseline";
            JsonObject alternate = baseline.DeepClone().AsObject(); alternate["generatedProgramSha256"] = "alternate";
            FixtureChecks.Baseline(production, baseline, inputs);
            FixtureChecks.Alternative(baseline, alternate);
            FixtureChecks.SafetyReport(production, "Lsh", "scalar");
            Program.Reject(() => FixtureChecks.Production(baseline, inputs));
            Program.Reject(() => FixtureChecks.Production(production, new() { ["source"] = "stale" }));
            Program.Reject(() => FixtureChecks.SafetyReport(production, "Rsh", "scalar"));
            production.Remove("evidenceKind");
            Program.Reject(() => FixtureChecks.SafetyReport(production, "Lsh", "scalar"));
            Program.Reject(() => FixtureChecks.Alternative(baseline, baseline));
            baseline["leanSourceSha256"]!["proof"] = "different";
            Program.Reject(() => FixtureChecks.Baseline(production, baseline, inputs));
            Program.Reject(() => FixtureChecks.Alternative(baseline, alternate));
        });
    }
}
