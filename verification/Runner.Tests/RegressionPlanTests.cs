// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System.Text.Json.Nodes;
using UInt256Verification;

namespace UInt256VerificationTests;

internal static class RegressionPlanTests
{
    internal static void Register(Action<string, Action<Catalog, string>> check)
    {
        check("regression matrix retains every production safety job and complete fixture command", (catalog, _) =>
        {
            var actual = RegressionPlan.Create(catalog).ToDictionary(job => job.Id, StringComparer.Ordinal);
            Dictionary<string, string[][]> expected = [];
            void Test(string id, params string[] args) => expected.Add(id, [[RegressionPlan.Tests, .. args]]);
            foreach (var job in catalog.Plan(catalog.MethodNames, safety: true)["include"]!.AsArray())
            {
                string method = Catalog.Text(job!["method"]), profile = Catalog.Text(job["profile"]), suffix = profile;
                if (method is "EqUInt256UInt256" or "EqualsUInt256Ref" or "NeUInt256UInt256")
                    suffix = profile == "x64-vector256" ? "vector256" : profile == "x64-sse41" ? "sse41" : profile;
                expected.Add($"safety-{method}-{suffix}", [[RegressionPlan.Runner, "verify", "--method", method, "--profile", profile, "--safety"]]);
            }
            Program.Require(expected.Count == 256, "Production safety inventory changed");
            foreach (string name in new[] { "foundation", "safety-foundation", "safety-fixtures", "profile-extractor" }) Test(name, name);
            Test("safety-robustness-Add", "robustness", "--method", "Add", "--case", "Renamed", "--case", "ReversedStore", "--safety");
            Test("csharp-runner");
            foreach (string name in new[] { "change", "method", "prepared", "regression" }) Test("csharp-" + name, name + "-checks");
            Test("gate-binding", "gate-binding", "--workspace");
            foreach (string method in new[] { "Add", "Subtract" })
            {
                expected.Add("legacy-" + method, [[RegressionPlan.Runner, "verify", "--method", method, "--profile", "scalar"], [RegressionPlan.Tests, method.ToLowerInvariant() + "-negative"]]);
                Test("robustness-" + method, "robustness", "--method", method);
                foreach (string profile in Catalog.Profiles.Skip(1)) Test($"simd-{method}-{profile}", "simd-fixtures", "--method", method, "--profile", profile, "--suite", "all");
            }
            foreach (string operation in new[] { "Compare", "Bitwise", "OperatorXor", "OperatorAnd", "OperatorOr", "OperatorNot", "Lsh", "Rsh", "LeftShift", "RightShift", "OperatorLsh", "OperatorRsh" })
                foreach (string profile in new[] { "scalar", "x64-vector256" })
                {
                    string id = $"operation-{operation}-{profile}";
                    if (operation is "Compare" or "Bitwise") Test(id, operation.ToLowerInvariant() + "-fixtures", "--profile", profile, "--workspace");
                    else if (operation is "OperatorXor" or "OperatorAnd" or "OperatorOr" or "OperatorNot") Test(id, "bitwise-operator-fixtures", "--method", operation, "--profile", profile, "--workspace");
                    else Test(id, "shift-fixtures", "--method", operation, "--safety", "--profile", profile, "--workspace");
                }
            string[] equality = catalog.Entries().Where(pair => pair.Value["verification"]?["fixtureGroup"]?.GetValue<string>() == "Equality").Select(pair => pair.Key).ToArray();
            var equalityPlan = catalog.Plan(equality)["include"]!.AsArray();
            Program.Require(equality.Length == 24 && equalityPlan.Count == 52, "Equality fixture coverage changed");
            foreach (var job in equalityPlan)
            {
                string method = Catalog.Text(job!["method"]), profile = Catalog.Text(job["profile"]);
                Test($"equality-{method}-{profile}", "equality-fixtures", "--method", method, "--profile", profile, "--workspace");
            }
            foreach (string profile in Catalog.MultiplyProfiles) Test("multiply-" + profile, "multiply-fixtures", "--profile", profile, "--workspace");
            foreach (string method in new[] { "AddOverflow", "SubtractUnderflow" })
                foreach (string profile in Catalog.Profiles) Test($"reporting-{method}-{profile}", "reporting", "--method", method, "--profile", profile);
            Program.Require(actual.Count == 387 && actual.Keys.ToHashSet().SetEquals(expected.Keys), "Missing or unexpected regression jobs");
            foreach (var (id, commands) in expected)
            {
                Program.Require(actual[id].Commands.Length == commands.Length && actual[id].Commands.Zip(commands).All(pair => pair.First.SequenceEqual(pair.Second)), "Changed command or incomplete suite: " + id);
                foreach (var command in commands) Program.Require(File.Exists(Path.Combine(Directory.GetCurrentDirectory(), command[0])), "Missing regression project: " + command[0]);
            }
        });
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
