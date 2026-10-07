// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System.Text.Json.Nodes;
using UInt256Verification;

namespace UInt256VerificationTests;

internal static class FixtureTests
{
    internal static void Register(Action<string, Action<Catalog, string>> check)
    {
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
