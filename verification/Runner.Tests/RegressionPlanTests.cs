// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System.Text.Json.Nodes;
using UInt256Verification;

namespace UInt256VerificationTests;

internal static class RegressionPlanTests
{
    internal static void Register(Action<string, Action<Catalog, string>> check)
    {
        check("regression CI batching retains ordered jobs within the Actions limit", (_, _) =>
        {
            foreach (int count in new[] { 1, 256, 257, 387, 1537 })
            {
                string[] ids = Enumerable.Range(0, count).Select(i => $"job-{i}").ToArray();
                var batches = RegressionPlan.Matrix(ids)["include"]!.AsArray();
                Program.Require(batches.Count <= 256 && batches.SelectMany(batch => batch!["jobs"]!.AsArray().Select(Catalog.Text)).SequenceEqual(ids), "CI batching omitted or reordered jobs");
                for (int i = 0; i < batches.Count; i++)
                {
                    var batch = batches[i]!;
                    int length = batch["jobs"]!.AsArray().Count;
                    Program.Require(length > 0 && batch["batch"]!.GetValue<int>() == i && batch["timeoutMinutes"]!.GetValue<int>() == Math.Min(360, 60 * length), "CI batch identity or timeout changed");
                }
            }
            Program.Reject(() => RegressionPlan.Matrix([]));
        });
        check("regression selection rejects missing equality and multiplication coverage", (catalog, directory) =>
        {
            string path = Path.Combine(directory, "api-coverage.json"), original = File.ReadAllText(path);
            var document = JsonNode.Parse(original)!;
            JsonObject Entry(string method) => document["entries"]!.AsArray()
                .Select(node => node!.AsObject()).Single(entry => entry["id"]?.GetValue<string>() == method);
            Entry("EqualsUInt64")["verification"]!["fixtureGroup"] = "Other";
            File.WriteAllText(path, document.ToJsonString());
            Program.Reject(() => RegressionPlan.Create(catalog));
            document = JsonNode.Parse(original)!;
            Entry("Multiply")["verification"]!["familyCoverage"]!["representatives"]!.AsArray().RemoveAt(0);
            File.WriteAllText(path, document.ToJsonString());
            Program.Reject(() => RegressionPlan.Create(catalog));
        });
    }
}
