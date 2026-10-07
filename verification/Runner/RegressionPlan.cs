// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System.Text.Json.Nodes;
using System.Text.Json.Serialization;

namespace UInt256Verification;

internal static class RegressionPlan
{
    internal sealed record Job([property: JsonPropertyName("id")] string Id,
        [property: JsonPropertyName("commands")] string[][] Commands);

    internal const string Tests = "verification/Runner.Tests/Verification.Tests.csproj";
    internal const string Runner = "verification/Runner/Verification.csproj";

    internal static Job[] Create(Catalog catalog)
    {
        List<Job> jobs = [];
        void Test(string id, params string[] arguments) => jobs.Add(new(id, [[Tests, .. arguments]]));
        void Safety(string method, string profile, string? suffix = null) => jobs.Add(new($"safety-{method}-{suffix ?? profile}",
            [[Runner, "verify", "--method", method, "--profile", profile, "--safety"]]));
        string[] storage = ["scalar", "x64-vector256"];
        string[] avx = ["x64-avx2", "x64-avx2-bmi1", "x64-avx512", "x64-avx512-bmi1"];
        string[] shifts = ["Lsh", "Rsh", "LeftShift", "RightShift", "OperatorLsh", "OperatorRsh"];
        foreach (string name in new[] { "foundation", "safety-foundation", "safety-fixtures" }) Test(name, name);
        Test("safety-robustness-Add", "robustness", "--method", "Add", "--case", "Renamed", "--case", "ReversedStore", "--safety");
        foreach (string method in SafetyCatalog.MultiplyMethods.Order(StringComparer.Ordinal))
            foreach (string profile in Catalog.MultiplyProfiles) Safety(method, profile);
        foreach (string profile in avx)
            foreach (string method in new[] { "Add", "AddOverflow" }) Safety(method, profile);
        foreach (string profile in new[] { "scalar", "x64-sse42", "arm64-advsimd" }) Safety("Add", profile);
        foreach (string method in new[] { "AddOverflow", "Subtract", "SubtractUnderflow" })
            foreach (string profile in new[] { "x64-sse42", "arm64-advsimd" }) Safety(method, profile);
        Safety("EqUInt256UInt256", "scalar");
        Safety("EqUInt256UInt256", "x64-vector256", "vector256");
        foreach (string profile in storage)
            foreach (string method in new[] { "EqualsUInt256Ref", "NeUInt256UInt256" })
                Safety(method, profile, profile == "scalar" ? profile : "vector256");
        foreach (string method in new[] { "EqUInt256UInt256", "EqualsUInt256Ref", "NeUInt256UInt256" }) Safety(method, "x64-sse41", "sse41");
        Safety("EqualsUInt256Value", "scalar");
        foreach (string sign in new[] { "UInt", "Int" })
            foreach (string profile in storage)
                foreach (int width in new[] { 64, 32 }) Safety($"Equals{sign}{width}", profile);
        foreach (string profile in new[] { "x64-sse41", "x64-vector256" }) Safety("EqualsUInt256Value", profile);
        foreach (string method in SafetyCatalog.Operators.Keys.Order(StringComparer.Ordinal))
            foreach (string profile in storage) Safety(method, profile);
        foreach (string method in SafetyCatalog.PrimitiveComparisons.Keys.Order(StringComparer.Ordinal)) Safety(method, "scalar");
        foreach (string method in new[] { "LeUInt64UInt256", "AddOverflow", "SubtractUnderflow", "Subtract" }) Safety(method, "scalar");
        foreach (string method in shifts)
            foreach (string profile in storage) Safety(method, profile);
        foreach (string method in new[] { "Subtract", "SubtractUnderflow" })
            foreach (string profile in avx) Safety(method, profile);
        foreach (string method in SafetyCatalog.Bitwise.Keys.Union(SafetyCatalog.Unary).Order(StringComparer.Ordinal))
            foreach (string profile in storage) Safety(method, profile);
        foreach (string method in SafetyCatalog.Comparisons.Keys.Order(StringComparer.Ordinal))
            foreach (string profile in new[] { "scalar", "x64-vector256", "x64-avx2", "x64-avx512" }) Safety(method, profile);
        foreach (string method in new[] { "CompareToUInt256Ref", "CompareToUInt256Value" }) Safety(method, "scalar");
        Test("profile-extractor", "profile-extractor");
        Test("csharp-runner");
        foreach (string name in new[] { "change", "method", "prepared" }) Test("csharp-" + name, name + "-checks");
        Test("csharp-regression", "regression-checks");
        Test("gate-binding", "gate-binding", "--workspace");
        foreach (string method in Catalog.Legacy)
        {
            jobs.Add(new("legacy-" + method, [[Runner, "verify", "--method", method, "--profile", "scalar"], [Tests, method.ToLowerInvariant() + "-negative"]]));
            Test("robustness-" + method, "robustness", "--method", method);
            foreach (string profile in Catalog.Profiles.Skip(1)) Test($"simd-{method}-{profile}", "simd-fixtures", "--method", method, "--profile", profile, "--suite", "all");
        }
        foreach (string operation in new[] { "Compare", "Bitwise", "OperatorXor", "OperatorAnd", "OperatorOr", "OperatorNot" }.Concat(shifts))
            foreach (string profile in storage)
            {
                string id = $"operation-{operation}-{profile}";
                if (operation is "Compare" or "Bitwise") Test(id, operation.ToLowerInvariant() + "-fixtures", "--profile", profile, "--workspace");
                else if (!shifts.Contains(operation)) Test(id, "bitwise-operator-fixtures", "--method", operation, "--profile", profile, "--workspace");
                else Test(id, "shift-fixtures", "--method", operation, "--safety", "--profile", profile, "--workspace");
            }
        string[] equality = catalog.Entries().Where(pair => pair.Value["verification"]?["fixtureGroup"]?.GetValue<string>() == "Equality").Select(pair => pair.Key).ToArray();
        (string Method, string Profile)[] Profiles(string[] methods) => catalog.Plan(methods)["include"]!.AsArray()
            .Select(job => (Catalog.Text(job!["method"]), Catalog.Text(job["profile"]))).ToArray();
        var equalProfiles = Profiles(equality);
        var multiplyProfiles = Profiles(["Multiply"]);
        if (equality.Length != 24 || equalProfiles.Length != 52 || equalProfiles.Distinct().Count() != 52
            || !multiplyProfiles.SequenceEqual(Catalog.MultiplyProfiles.Select(profile => ("Multiply", profile))))
            throw new InvalidOperationException("Incomplete equality or multiplication regression selection");
        foreach (var (method, profile) in equalProfiles) Test($"equality-{method}-{profile}", "equality-fixtures", "--method", method, "--profile", profile, "--workspace");
        foreach (var (_, profile) in multiplyProfiles) Test("multiply-" + profile, "multiply-fixtures", "--profile", profile, "--workspace");
        foreach (string method in new[] { "AddOverflow", "SubtractUnderflow" })
            foreach (string profile in Catalog.Profiles) Test($"reporting-{method}-{profile}", "reporting", "--method", method, "--profile", profile);
        if (jobs.Count != 387 || jobs.Select(job => job.Id).Distinct(StringComparer.Ordinal).Count() != 387)
            throw new InvalidOperationException("Incomplete or duplicate regression matrix");
        return jobs.ToArray();
    }

    internal static JsonObject Matrix(IReadOnlyList<string> ids)
    {
        if (ids.Count == 0) throw new ArgumentException("Empty regression matrix");
        int width = (ids.Count + 255) / 256;
        JsonArray include = [];
        for (int index = 0; index < ids.Count; index += width)
        {
            string[] batch = ids.Skip(index).Take(width).ToArray();
            include.Add(new JsonObject { ["batch"] = index / width, ["jobs"] = new JsonArray(batch.Select(id => (JsonNode?)JsonValue.Create(id)).ToArray()), ["timeoutMinutes"] = Math.Min(360, 60 * batch.Length) });
        }
        return new JsonObject { ["include"] = include };
    }
}
