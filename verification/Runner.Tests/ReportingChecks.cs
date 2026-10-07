// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System.Numerics;
using System.Text.Json.Nodes;
using System.Xml.Linq;
using UInt256Verification;

namespace UInt256VerificationTests;

internal static class ReportingChecks
{
    internal static void Register(Action<string, Action<Catalog, string>> check)
    {
        check("reporting suite retains method/profile selections and exact fixture provenance", (_, _) =>
        {
            var cases = Cases(new Workspace(Directory.GetCurrentDirectory()));
            Program.Require(cases.Positive.SequenceEqual(new[] { "Baseline", "Renamed", "EquivalentMask", "ExtractedHelper", "ReversedStore" })
                && cases.Negative.SequenceEqual(new[] { "WrongFlag", "WrongAlignment", "WrongTop", "EarlyReread" }), "Reporting registry changed");
            string[] names = [.. cases.Positive, .. cases.Negative];
            Program.Require(Options([], names) == ("all", "all", "all"), "Default reporting coverage narrowed");
            foreach (string[] invalid in new[] { new[] { "--method", "Add" }, new[] { "--profile", "missing" }, new[] { "--case", "missing" }, new[] { "--method" }, new[] { "--unknown", "value" } })
                Program.Reject(() => Options(invalid, names));
            foreach (string profile in Catalog.Profiles)
            foreach (string name in cases.Positive)
            {
                JsonObject report = new() { ["source"] = new JsonObject { ["kind"] = "fixture", ["case"] = name, ["fixture"] = "verification/Tests/Fixtures/Reporting/Public.cs" },
                    ["executionProfile"] = new JsonObject { ["Name"] = profile }, ["summaryRejections"] = name == "ReversedStore" ? new JsonArray(new JsonArray("storeLimbsIndex", "proof failure")) : new JsonArray() };
                CheckReport(report, profile, name);
                foreach (string failure in new[] { "kind", "case", "fixture", "profile", "resources" })
                {
                    var invalid = report.DeepClone().AsObject();
                    if (failure == "profile") invalid["executionProfile"]!["Name"] = "wrong";
                    else if (failure == "resources") invalid["summaryRejections"]!.AsArray().Add(new JsonArray("helper", "resource limit"));
                    else invalid["source"]![failure] = "wrong";
                    Program.Reject(() => CheckReport(invalid, profile, name));
                }
                if (name == "ReversedStore") { report["summaryRejections"] = new JsonArray(); Program.Reject(() => CheckReport(report, profile, name)); }
            }
        });
        check("reporting witnesses refute both flags and byte results of full contracts", (_, _) =>
        {
            string template = File.ReadAllText(Path.Combine(Directory.GetCurrentDirectory(), "verification/Tests/Fixtures/Reporting/RefutationTemplate.lean.in"));
            foreach (string method in Methods)
            foreach (string name in new[] { "WrongFlag", "WrongAlignment", "WrongTop", "EarlyReread" })
            {
                var data = Witness(method, name);
                string source = FixtureChecks.ExpandRefutation(template, data);
                Program.Require(source.Contains(method == "AddOverflow" ? "¬ Contract .add" : "¬ Contract .subtract", StringComparison.Ordinal)
                    && source.Contains("#print axioms model_not_correct", StringComparison.Ordinal), "Complete contract or axiom audit lost");
                Program.Require(data["LEMMA"] == (name == "WrongFlag" ? "flag_observation_refuted" : "byte_observation_refuted"), "Wrong observation refutation");
                if (name == "WrongFlag") Program.Require(data["OBSERVED"] == "[.i32 1]" && data["EXPECTED_VALUE"] == "0", "Flag counterexample changed");
            }
        });
    }
    internal static readonly string[] Methods = ["AddOverflow", "SubtractUnderflow"];
    internal static string Legacy(string method) => method == "AddOverflow" ? "Add" : "Subtract";
    internal static (string[] Positive, string[] Negative) Cases(Workspace workspace)
    {
        var cases = XDocument.Load(Path.Combine(workspace.Verification, "Tests/Fixtures/Reporting/Cases.props")).Descendants("ReportingCase").ToArray();
        string[] Suite(string name) => cases.Where(item => (string?)item.Attribute("Suite") == name).Select(item => (string)item.Attribute("Include")!).ToArray();
        return (Suite("positive"), Suite("negative"));
    }
    internal static (string Method, string Profile, string Case) Options(string[] arguments, IEnumerable<string> cases)
    {
        Dictionary<string, string> values = new() { ["--method"] = "all", ["--profile"] = "all", ["--case"] = "all" };
        for (int i = 0; i < arguments.Length; i += 2)
        {
            if (!values.ContainsKey(arguments[i]) || i + 1 == arguments.Length) throw new ArgumentException("Unknown or incomplete reporting option");
            values[arguments[i]] = arguments[i + 1];
        }
        string method = values["--method"], profile = values["--profile"], name = values["--case"];
        if (method != "all" && !Methods.Contains(method) || profile != "all" && !Catalog.Profiles.Contains(profile) || name != "all" && !cases.Contains(name))
            throw new ArgumentException("Unknown reporting selection");
        return (method, profile, name);
    }
    internal static void CheckReport(JsonObject report, string profile, string name)
    {
        if (Catalog.Text(report["source"]?["kind"]) != "fixture" || Catalog.Text(report["source"]?["case"]) != name
            || Catalog.Text(report["source"]?["fixture"]) != "verification/Tests/Fixtures/Reporting/Public.cs" || Catalog.Text(report["executionProfile"]?["Name"]) != profile)
            throw new InvalidOperationException("Reporting fixture provenance mismatch");
        JsonArray rejections = report["summaryRejections"]!.AsArray();
        if (rejections.Any(item => Catalog.Text(item![1]) == "resource limit")) throw new InvalidOperationException("Reporting fixture exhausted optional proof resources");
        if (name == "ReversedStore" && !rejections.Any(item => Catalog.Text(item![0]).Contains("storeLimbsIndex", StringComparison.Ordinal)))
            throw new InvalidOperationException("Reversed storage did not exercise transactional raw fallback");
    }
    internal static Dictionary<string, string> RefutationData(string method, string initial, int output, int? address = null, int actual = 1, int expected = 0)
    {
        string operation = method == "AddOverflow" ? ".add" : ".subtract";
        return new()
        {
            ["INITIAL"] = initial, ["OUT"] = output.ToString(), ["OPERATION"] = operation,
            ["OBSERVATION"] = address is null ? "outcome.2" : $"outcome.1 (.byte {address})",
            ["OBSERVED"] = address is null ? $"[.i32 {actual}]" : $"some (.i8 {actual})",
            ["COMPARISON"] = address is null ? $"((if flag {operation} (byteValue witnessBytes 0) (byteValue witnessBytes 64) then 1 else 0) : W32)"
                : $"writeBytes (byteMemory witnessBytes) {output} (result {operation} (byteValue witnessBytes 0) (byteValue witnessBytes 64)).toNat 32 (.byte {address})",
            ["EXPECTED_VALUE"] = address is null ? expected.ToString() : $"some (.i8 {expected})",
            ["LEMMA"] = address is null ? "flag_observation_refuted" : "byte_observation_refuted",
            ["ARGUMENTS"] = address is null ? actual.ToString() : $"{address} (some (.i8 {actual}))"
        };
    }
    internal static Dictionary<string, string> Witness(string method, string name)
    {
        if (name == "WrongFlag") return RefutationData(method, "0", 128);
        var witness = SimdFixtures.Witness(name, Legacy(method));
        BigInteger Number(ulong[] words) => words.Select((word, i) => (BigInteger)word << (64 * i)).Aggregate(BigInteger.Zero, (a, b) => a + b);
        BigInteger value = method == "AddOverflow" ? Number(witness.Left) + Number(witness.Right) : Number(witness.Left) - Number(witness.Right);
        int expected = (int)((value >> (8 * (witness.Address - witness.Output))) & 255);
        if (expected == witness.Actual) throw new InvalidOperationException("Witness fails to distinguish full contract");
        string Words(ulong[] words) => "[" + string.Join(", ", words) + "]";
        string initial = $"if address < 32 then BitVec.ofNat 8 (({Words(witness.Left)} : List Nat)[address / 8]! / 256^(address % 8)) "
            + $"else if 64 ≤ address ∧ address < 96 then BitVec.ofNat 8 (({Words(witness.Right)} : List Nat)[(address-64) / 8]! / 256^(address % 8)) else 0";
        return RefutationData(method, initial, witness.Output, witness.Address, witness.Actual, expected);
    }
    internal static void Run(Workspace workspace, string[] arguments)
    {
        var cases = Cases(workspace);
        var options = Options(arguments, [.. cases.Positive, .. cases.Negative]);
        string destination = Path.Combine(Path.GetTempPath(), "int256-reporting-" + Guid.NewGuid().ToString("N"));
        try
        {
            workspace.Run(["git", "clone", "--shared", "--no-checkout", "--quiet", workspace.Root, destination], workspace.Root);
            string proof = workspace.CopyRegressionSource(destination);
            Workspace isolated = new(destination);
            foreach (string method in options.Method == "all" ? Methods : [options.Method])
            foreach (string profile in options.Profile == "all" ? Catalog.Profiles : [options.Profile])
            {
                string reportPath = Path.Combine(new Verifier(isolated).OutputDirectory(method, profile), "report.json");
                string[] command = ["dotnet", "run", "--project", Path.Combine(proof, "Runner/Verification.csproj"), "-c", "Release", "--", "--root", destination,
                    "verify", "--method", method, "--profile", profile];
                JsonObject Report() => JsonNode.Parse(File.ReadAllText(reportPath))!.AsObject();
                JsonObject Checked(string name)
                {
                    isolated.Run([.. command, "--fixture", name], destination);
                    JsonObject report = Report(); CheckReport(report, profile, name); return report;
                }
                isolated.Run(command, destination);
                if (Catalog.Text(Report()["source"]?["kind"]) != "production") throw new InvalidOperationException("Fresh production baseline required");
                JsonObject baseline = Checked("Baseline");
                foreach (string name in cases.Positive.Skip(1))
                {
                    if (options.Case != "all" && options.Case != name || profile == "scalar" && name == "ExtractedHelper" || !SimdFixtures.Positive(name, Legacy(method), profile)) continue;
                    JsonObject report = Checked(name);
                    if (!JsonNode.DeepEquals(report["leanSourceSha256"], baseline["leanSourceSha256"])) throw new InvalidOperationException("Positive changed handwritten proofs");
                    SimdFixtures.TargetChanged(name, Legacy(method), profile, baseline["artifact"]!.AsObject(), report["artifact"]!.AsObject());
                }
                foreach (string name in cases.Negative)
                {
                    if (options.Case != "all" && options.Case != name || name != "WrongFlag" && !SimdFixtures.Negative(name, Legacy(method), profile)) continue;
                    string project = Path.Combine(proof, "Tests/Fixtures/Reporting/Nethermind.Int256.csproj");
                    isolated.Run(["dotnet", "build", project, "-c", "Release", "--no-incremental", $"-p:FixtureCase={name}", "-p:EnforceCodeStyleInBuild=true", "-p:GenerateDocumentationFile=true"], destination);
                    isolated.Run(["dotnet", "run", "--project", Path.Combine(proof, "Extractor"), "-c", "Release", "--",
                        Path.Combine(Path.GetDirectoryName(project)!, "bin/Release/net10.0/Nethermind.Int256.dll"), Path.Combine(proof, "generated"), method, profile], destination);
                    JsonObject artifact = JsonNode.Parse(File.ReadAllText(Path.Combine(proof, "generated/artifact.json")))!.AsObject();
                    if (Catalog.Text(artifact["profile"]?["Name"]) != profile) throw new InvalidOperationException("Counterexample profile mismatch");
                    SimdFixtures.TargetChanged("Renamed", Legacy(method), profile, baseline["artifact"]!.AsObject(), artifact);
                    foreach (var pair in baseline["leanSourceSha256"]!.AsObject())
                        if (Workspace.Hash(Path.Combine(proof, pair.Key)) != Catalog.Text(pair.Value)) throw new InvalidOperationException("Semantic negative changed handwritten proofs");
                    bool register = !File.ReadAllText(Path.Combine(proof, "lakefile.toml")).Contains("name = \"ReportingWitness\"", StringComparison.Ordinal);
                    FixtureChecks.Refutation(isolated, proof, "lake", Path.Combine(proof, "Tests/Fixtures/Reporting/RefutationTemplate.lean.in"), Witness(method, name),
                        "ReportingWitness", "ReportingWitness.model_not_correct", ["propext", "Classical.choice", "Quot.sound"], register);
                    string rejected = isolated.RunRejected([.. command, "--fixture", name], destination, "Reporting negative public verifier");
                    string entry = method == "AddOverflow" ? "AddEntry" : "SubtractEntry";
                    RejectionChecks.Semantic(rejected, $"UInt256/Methods/Reporting/{entry}.lean");
                    if (File.Exists(reportPath)) throw new InvalidOperationException("Rejected reporting fixture retained a success report");
                    Console.WriteLine($"PASS: {method}/{profile}/{name}, full contract independently refuted");
                }
            }
        }
        finally { if (Directory.Exists(destination)) Directory.Delete(destination, true); }
    }
}
