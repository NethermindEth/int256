// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System.Globalization;
using System.Numerics;
using System.Text.Json.Nodes;
using UInt256Verification;

namespace UInt256VerificationTests;

internal static class SimdFixtureChecks
{
    internal static (string Initial, int Expected) Witness(string name, string method)
    {
        var witness = SimdFixtures.Witness(name, method);
        BigInteger Number(ulong[] words) => words.Select((word, i) => new BigInteger(word) << (64 * i)).Aggregate(BigInteger.Zero, (a, b) => a + b);
        BigInteger value = method == "Add" ? Number(witness.Left) + Number(witness.Right) : Number(witness.Left) - Number(witness.Right);
        int expected = (int)((value >> (8 * (witness.Address - witness.Output))) & 255);
        if (witness.Actual == expected) throw new InvalidOperationException("Fixture witness does not distinguish the contract");
        string Words(ulong[] words) => "[" + string.Join(", ", words.Select(word => word.ToString(CultureInfo.InvariantCulture))) + "]";
        string initial = $"if address < 32 then BitVec.ofNat 8 ((({Words(witness.Left)} : List Nat)[address / 8]!) / 256^(address % 8)) "
            + $"else if 64 ≤ address ∧ address < 96 then BitVec.ofNat 8 ((({Words(witness.Right)} : List Nat)[(address-64) / 8]!) / 256^(address % 8)) else 0";
        return (initial, expected);
    }

    internal static void CheckReport(JsonObject report, string name, string profile)
    {
        Program.Require(Catalog.Text(report["status"]) == "verified" && Catalog.Text(report["source"]!["kind"]) == "fixture"
            && Catalog.Text(report["source"]!["fixture"]) == "verification/Tests/Fixtures/SIMD/Cases.props"
            && Catalog.Text(report["source"]!["case"]) == name && Catalog.Text(report["executionProfile"]!["Name"]) == profile,
            "Fixture report does not identify the selected artifact/profile");
        var rejections = report["summaryRejections"]!.AsArray();
        Program.Require(!rejections.Any(item => Catalog.Text(item![1]) == "resource limit"), "A fixture summary exhausted proof resources");
        if (name == "ReversedStore") Program.Require(rejections.Any(item => Catalog.Text(item![0]).Contains("storeLimbsIndex", StringComparison.Ordinal)), "Storage mismatch did not exercise transactional raw fallback");
        if (name == "Renamed") Program.Require(!report["artifact"]!["methods"]!.AsArray().Any(body =>
            new[] { "AddVector128", "SubtractVector128", "PrepareAdd", "FinishAdd", "SubtractImpl" }.Any(old => Catalog.Text(body!["signature"]).Contains($"::{old}(", StringComparison.Ordinal))), "Renamed fixture retained an old vector helper name");
    }

    internal static void Register(Action<string, Action<Catalog, string>> check)
    {
        check("SIMD runner rejects invalid selections and nondistinguishing witnesses", (_, _) =>
        {
            Workspace workspace = new(Directory.GetCurrentDirectory());
            foreach (string method in Catalog.Legacy)
            foreach (string name in Verifier.SimdRegistry(workspace.Verification)["SIMD_NEGATIVES"])
            {
                var witness = Witness(name, method);
                Program.Require(witness.Initial.Contains("64 ≤ address", StringComparison.Ordinal) && witness.Expected is >= 0 and <= 255, "Invalid byte witness");
            }
            foreach (string[] args in new[] { new[] { "--profile", "scalar" }, ["--method", "missing"], ["--case", "missing"],
                ["--case", "WrongAlignment", "--suite", "positive"], ["--case", "Renamed", "--suite", "negative"],
                ["--case", "WrongTernary", "--profile", "x64-sse42"], ["--case", "EquivalentMask", "--profile", "arm64-advsimd"] })
                Program.Reject(() => Run(workspace, args));
        });
        check("SIMD report checks retain artifact binding and transactional fallback", (_, _) =>
        {
            JsonObject report = JsonNode.Parse("""{"status":"verified","source":{"kind":"fixture","fixture":"verification/Tests/Fixtures/SIMD/Cases.props","case":"ReversedStore"},"executionProfile":{"Name":"x64-sse42"},"summaryRejections":[["storeLimbsIndex","proof failure"]],"artifact":{"methods":[]}}""")!.AsObject();
            CheckReport(report, "ReversedStore", "x64-sse42");
            Program.Reject(() => CheckReport(report, "ReversedStore", "arm64-advsimd"));
            report["summaryRejections"]![0]![1] = "resource limit";
            Program.Reject(() => CheckReport(report, "ReversedStore", "x64-sse42"));
            report["summaryRejections"] = new JsonArray();
            Program.Reject(() => CheckReport(report, "ReversedStore", "x64-sse42"));
            report["source"]!["case"] = "Renamed";
            CheckReport(report, "Renamed", "x64-sse42");
            report["artifact"]!["methods"]!.AsArray().Add(new JsonObject { ["signature"] = "void T::PrepareAdd()" });
            Program.Reject(() => CheckReport(report, "Renamed", "x64-sse42"));
        });
    }

    internal static void Run(Workspace workspace, string[] arguments)
    {
        string method = "all", profile = "all", selected = "all", suite = "all";
        for (int i = 0; i < arguments.Length; i++)
        {
            if (i + 1 >= arguments.Length) throw new ArgumentException("Incomplete SIMD fixture option");
            switch (arguments[i])
            {
                case "--method": method = arguments[++i]; break;
                case "--profile": profile = arguments[++i]; break;
                case "--case": selected = arguments[++i]; break;
                case "--suite": suite = arguments[++i]; break;
                default: throw new ArgumentException("Unknown SIMD fixture option");
            }
        }
        var registry = Verifier.SimdRegistry(workspace.Verification);
        string[] positives = registry["SIMD_POSITIVES"], negatives = registry["SIMD_NEGATIVES"];
        if (method != "all" && !Catalog.Legacy.Contains(method) || profile != "all" && !Catalog.Profiles.Skip(1).Contains(profile)
            || selected != "all" && !registry["SIMD_CASES"].Contains(selected) || suite is not ("all" or "positive" or "negative"))
            throw new ArgumentException("Unknown SIMD fixture selection");
        if (negatives.Contains(selected) && suite == "positive" || positives.Contains(selected) && suite == "negative")
            throw new ArgumentException("Case does not belong to selected suite");
        string[] methods = method == "all" ? Catalog.Legacy : [method], profiles = profile == "all" ? Catalog.Profiles[1..] : [profile];
        if (positives.Skip(1).Contains(selected) && !methods.Any(m => profiles.Any(p => SimdFixtures.Positive(selected, m, p)))
            || negatives.Contains(selected) && !methods.Any(m => profiles.Any(p => SimdFixtures.Negative(selected, m, p))))
            throw new ArgumentException("Selected fixture is inapplicable to these profiles");
        BinaryFixtureChecks.Isolate(workspace, child => RunSelected(child, methods, profiles, selected, suite, positives, negatives));
    }

    private static string[] Command(Workspace workspace, string method, string profile) => ["dotnet", "run", "--project", Path.Combine(workspace.Verification, "Runner/Verification.csproj"), "-c", "Release", "--", "verify", "--method", method, "--profile", profile];
    private static string ReportPath(Workspace workspace, string method, string profile) => Path.Combine(new Verifier(workspace).OutputDirectory(method, profile), "report.json");
    private static JsonObject Positive(Workspace workspace, string name, string method, string profile)
    {
        workspace.Run([.. Command(workspace, method, profile), "--simd-fixture", name], workspace.Root);
        JsonObject report = JsonNode.Parse(File.ReadAllText(ReportPath(workspace, method, profile)))!.AsObject();
        CheckReport(report, name, profile);
        Console.WriteLine($"PASS: {method}/{profile}/{name}, complete public proof");
        return report;
    }

    private static void RunSelected(Workspace workspace, string[] methods, string[] profiles, string selected, string suite, string[] positives, string[] negatives)
    {
        JsonNode? hashes = null;
        List<(string Name, string Method, string Profile, JsonObject Baseline)> jobs = [];
        foreach (string method in methods)
        foreach (string profile in profiles)
        {
            if (suite != "positive")
            {
                workspace.Run(Command(workspace, method, profile), workspace.Root);
                JsonNode production = JsonNode.Parse(File.ReadAllText(ReportPath(workspace, method, profile)))!;
                Program.Require(Catalog.Text(production["source"]!["kind"]) == "production", "Production baseline required");
            }
            JsonObject baseline = Positive(workspace, "Baseline", method, profile);
            hashes ??= baseline["leanSourceSha256"];
            Program.Require(JsonNode.DeepEquals(baseline["leanSourceSha256"], hashes), "Handwritten proofs changed");
            if (suite != "negative")
                foreach (string name in positives.Skip(1).Where(name => (selected == "all" || selected == name) && SimdFixtures.Positive(name, method, profile)))
                {
                    JsonObject report = Positive(workspace, name, method, profile);
                    Program.Require(JsonNode.DeepEquals(report["leanSourceSha256"], hashes), "Fixture used different handwritten proofs");
                    SimdFixtures.TargetChanged(name, method, profile, baseline["artifact"]!.AsObject(), report["artifact"]!.AsObject());
                }
            if (suite != "positive")
                foreach (string name in negatives.Where(name => (selected == "all" || selected == name) && SimdFixtures.Negative(name, method, profile)))
                    jobs.Add((name, method, profile, baseline));
        }
        foreach (var job in jobs) Negative(workspace, job.Name, job.Method, job.Profile, job.Baseline);
    }

    private static void Negative(Workspace workspace, string name, string method, string profile, JsonObject baseline)
    {
        string proof = workspace.Verification, project = Path.Combine(proof, "Tests/Fixtures/SIMD/Nethermind.Int256.csproj");
        workspace.Run(["dotnet", "build", project, "-c", "Release", "--no-incremental", $"-p:FixtureCase={name}", $"-p:FixtureMethod={method}",
            "-p:EnforceCodeStyleInBuild=true", "-p:GenerateDocumentationFile=true"], workspace.Root);
        string assembly = Path.Combine(Path.GetDirectoryName(project)!, "bin/Release/net10.0/Nethermind.Int256.dll"), generated = Path.Combine(proof, "generated");
        workspace.Run(["dotnet", "run", "--project", Path.Combine(proof, "Extractor"), "-c", "Release", "--", assembly, generated, method, profile], workspace.Root);
        JsonObject artifact = JsonNode.Parse(File.ReadAllText(Path.Combine(generated, "artifact.json")))!.AsObject();
        Program.Require(Catalog.Text(artifact["profile"]!["Name"]) == profile, "Wrong counterexample extraction profile");
        JsonArray Target(JsonNode source)
        {
            if (name == "WrongTable") return new JsonArray(source["staticData"]!.AsArray().Select(item => item!["bytes"]!.DeepClone()).ToArray());
            string target = name switch
            {
                "WrongAvxAlignment" or "WrongBlend" or "WrongTernary" or "WrongPredicate" or "EarlyReread" => method == "Add" ? "PrepareAdd" : "SubtractImpl",
                "WrongScale" => method == "Add" ? "FinishAdd" : "SubtractImpl",
                _ => method == "Add" ? "AddVector128" : "SubtractVector128"
            };
            return new JsonArray(source["methods"]!.AsArray().Where(body => Catalog.Text(body!["signature"]).Contains($"::{target}(", StringComparison.Ordinal))
                .Select(body => (JsonNode)new JsonArray(body!["instructions"]!.AsArray().Select(op => (JsonNode)new JsonArray(op!["opcode"]!.DeepClone(), op["operand"]?.DeepClone())).ToArray())).ToArray());
        }
        JsonArray changed = Target(artifact);
        Program.Require((name == "WrongTable" || changed.Count > 0) && !JsonNode.DeepEquals(changed, Target(baseline["artifact"]!)), "Targeted negative fixture CIL/table did not change");
        foreach (var pair in baseline["leanSourceSha256"]!.AsObject())
            Program.Require(Workspace.Hash(Path.Combine(proof, pair.Key)) == Catalog.Text(pair.Value), "Negative fixture changed handwritten proof sources");
        var witness = SimdFixtures.Witness(name, method);
        var (initial, expected) = Witness(name, method);
        string configuration = Path.Combine(proof, "lakefile.toml");
        string original = File.ReadAllText(configuration).Replace("\r\n", "\n", StringComparison.Ordinal).Split("\n[[lean_lib]]\nname = \"Refutation\"", StringSplitOptions.None)[0];
        File.WriteAllText(configuration, original.TrimEnd() + "\n");
        FixtureChecks.ModelRefutation(workspace, proof, "lake", initial, "0", "64", witness.Output.ToString(CultureInfo.InvariantCulture), witness.Address.ToString(CultureInfo.InvariantCulture),
            witness.Actual.ToString(CultureInfo.InvariantCulture), expected.ToString(CultureInfo.InvariantCulture), method);
        string module = $"UInt256/Methods/{method}/Entry.lean";
        RejectionChecks.Semantic(workspace.RunRejected(["lake", "build", method == "Add" ? "Audit" : "SubtractAudit"], proof, "Direct SIMD rejection"), module);
        RejectionChecks.Semantic(workspace.RunRejected([.. Command(workspace, method, profile), "--simd-fixture", name], workspace.Root, "Public SIMD rejection"), module);
        Program.Require(!File.Exists(ReportPath(workspace, method, profile)), "A negative fixture retained stale successful evidence");
        Console.WriteLine($"PASS: {method}/{profile}/{name}, independently refuted full contract");
    }
}
