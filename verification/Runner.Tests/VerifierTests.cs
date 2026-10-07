// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System.Text.Json.Nodes;
using UInt256Verification;

namespace UInt256VerificationTests;

internal static class VerifierTests
{
    private const string Method = "EqInt64UInt256";
    private static void Write(string root, string relative, string text)
    {
        string target = Path.Combine(root, relative);
        Directory.CreateDirectory(Path.GetDirectoryName(target)!);
        File.WriteAllText(target, text);
    }

    internal static Workspace Setup(Catalog catalog, string manifests, string failure = "", Action<string, string>? during = null, string method = Method)
    {
        string root = Path.Combine(Path.GetDirectoryName(manifests)!, "source");
        foreach (string source in Directory.EnumerateFiles(manifests, "*", SearchOption.AllDirectories))
            Write(root, "verification/manifests/" + Path.GetRelativePath(manifests, source), File.ReadAllText(source));
        foreach (string path in new[] { "global.json", ".editorconfig", "verification/lean-toolchain", "verification/lakefile.toml", "verification/Proof.lean" }) Write(root, path, "source");
        JsonObject manifest = catalog.Manifest(method), abi = manifest["callingConvention"]!.AsObject();
        JsonArray parameters = [];
        foreach (JsonNode? p in abi["parameters"]!.AsArray()) parameters.Add(new JsonObject
        {
            ["type"] = p!["type"]!.DeepClone(), ["IsIn"] = p["isIn"]!.DeepClone(), ["IsOut"] = p["isOut"]!.DeepClone()
        });
        JsonObject entry = new() { ["signature"] = manifest["entry"]!.DeepClone(), ["isStatic"] = true, ["hasThis"] = false,
            ["returnType"] = abi["returns"]!.DeepClone(), ["parameters"] = parameters };
        return new(root, (command, cwd, stage) =>
        {
            during?.Invoke(stage, cwd);
            if (command.SequenceEqual(new[] { "dotnet", "--version" })) return failure == "sdk" ? "0.0.0" : Catalog.Text(manifest["sdk"]);
            if (command.SequenceEqual(new[] { "lake", "env", "lean", "--version" })) return failure == "lean" ? "Lean (version 4.35.0)" : "Lean (version 4.34.1)";
            if (command[0] == "git") return command[1] == "rev-parse" ? "commit\n" : " M source.cs\n";
            if (command[0] == "dotnet" && command[1] == "build")
            {
                if (command.Any(arg => arg.StartsWith("-p:FixtureMethod=", StringComparison.Ordinal)))
                    Program.Require(command.Contains("-p:FixtureCase=Renamed") && command.Contains("-p:EnforceCodeStyleInBuild=true"), "Fixture case or analyzer selection lost");
                string artifacts = command.Single(arg => arg.StartsWith("-p:ArtifactsPath=", StringComparison.Ordinal))[17..];
                Write(artifacts, command[2].EndsWith("Extractor.csproj", StringComparison.Ordinal) ? "bin/Extractor/release/Extractor.dll" : "bin/Nethermind.Int256/release/Nethermind.Int256.dll", "binary");
                return "built";
            }
            if (command[0] == "dotnet")
            {
                JsonObject artifact = new() { ["sha256"] = Workspace.Hash(command[2]), ["entryIndex"] = 0,
                    ["methods"] = new JsonArray(entry.DeepClone()), ["profile"] = catalog.Profile(command[5].StartsWith('@')
                        ? Path.GetFileNameWithoutExtension(command[5][1..]) : command[5]) };
                Write(command[3], "artifact.json", artifact.ToJsonString()); Write(command[3], "Extracted.lean", "extracted");
                return "extracted";
            }
            if (command[0] == "lake")
            {
                if (stage == "Coverage checking")
                {
                    IEnumerable<string> compositionNames = command.Contains("+UInt256.OperationCoverage:olean")
                        ? Coverage.Theorems.Concat(Coverage.OperationTheorems) : Coverage.Theorems;
                    return string.Join('\n', compositionNames.Select(name => $"'{name}' depends on axioms: [propext]"));
                }
                bool safety = stage == "Safety proof checking";
                string[] names = safety ? SafetyCatalog.Gate(method, "scalar")["theorems"]!.AsArray().Select(Catalog.Text).ToArray() : ProofAudits.Names(catalog, method);
                if (failure == "source" && safety) Write(root, "verification/Proof.lean", "changed");
                if (failure == "snapshot" && safety) Write(cwd, "Proof.lean", "changed");
                if (failure == "gate" && safety) Write(cwd, "UInt256/Methods/SelectedGate.lean", "changed");
                if (failure == "safety-gate" && safety) Write(cwd, "UInt256/Methods/SelectedSafetyGate.lean", "changed");
                if (failure == "missing-audit" && safety) names = names[..^1];
                if (failure == "proof") throw new InvalidOperationException("Proof checking failure: simulated kernel rejection");
                string output = string.Join('\n', names.Select(name => $"'{name}' depends on axioms: [{(failure == "axiom" ? "sorryAx" : "propext")}]"));
                return failure == "duplicate-audit" ? output + "\n" + output : output;
            }
            throw new InvalidOperationException("Unexpected command: " + string.Join(' ', command));
        });
    }

    internal static void Register(Action<string, Action<Catalog, string>> check)
    {
        check("SIMD registry preserves case and suite selection", (_, manifests) =>
        {
            string directory = Path.GetDirectoryName(manifests)!;
            const string path = "Tests/Fixtures/SIMD/Cases.props";
            Write(directory, path, "<Project><ItemGroup><SimdCase Include='Baseline' Suite='positive'/><SimdCase Include='WrongAlignment' Suite='negative'/></ItemGroup></Project>");
            var registry = Verifier.SimdRegistry(directory);
            Program.Require(registry["SIMD_CASES"].SequenceEqual(new[] { "Baseline", "WrongAlignment" }), "Case order changed");
            Program.Require(registry["SIMD_POSITIVES"].SequenceEqual(new[] { "Baseline" }) && registry["SIMD_NEGATIVES"].SequenceEqual(new[] { "WrongAlignment" }), "Suite selection changed");
            Write(directory, path, "<Project><ItemGroup><SimdCase Include='Baseline'/></ItemGroup></Project>");
            Program.Reject(() => Verifier.SimdRegistry(directory));
        });
        check("verification options reject ambiguity and unknown switches", (_, _) =>
        {
            Program.Require(VerifyOptions.Parse([]) == new VerifyOptions(), "Defaults changed");
            foreach (string[] args in new[] { new[] { "--method" }, new[] { "--unknown", "value" }, new[] { "--safety", "--safety" }, new[] { "--fixture", "A", "--simd-fixture", "B" } })
                Program.Reject(() => VerifyOptions.Parse(args));
        });
        check("complete combined verifier publishes only bound evidence", (catalog, manifests) =>
        {
            Workspace workspace = Setup(catalog, manifests);
            Verifier verifier = new(workspace);
            JsonObject report = verifier.Verify(new(Method, Safety: true));
            string directory = Path.Combine(verifier.OutputDirectory(Method), "safety");
            Program.Require(File.Exists(Path.Combine(directory, "report.json")), "Report missing");
            Program.Require(Catalog.Text(report["evidenceKind"]) == "arithmetic-and-memory-safety", "Combined scope missing");
            Program.Require(JsonNode.DeepEquals(report["safety"], SafetyCatalog.Gate(Method, "scalar")), "Wrong safety binding");
            Program.Require(Catalog.Text(report["generatedGateSha256"]) == Workspace.Hash(Path.Combine(directory, "SelectedGate.lean")), "Typed gate hash lost");
            Program.Require(Catalog.Text(report["generatedSafetyGateSha256"]) == Workspace.Hash(Path.Combine(directory, "SelectedSafetyGate.lean")), "Safety gate hash lost");
            Program.Require(report["auditedTheorems"]!.AsArray().Count == ProofAudits.Names(catalog, Method).Length + 3, "Missing audited contracts");
            Program.Require(!report["coverage"]!["aggregateChecked"]!.GetValue<bool>(), "Single proof claimed aggregate coverage");
            Program.Require(report["leanSourceSha256"]!.AsObject().Count == 1, "Generated files entered handwritten hashes");
            Program.Require(!File.Exists(Path.Combine(directory, "report.json.tmp")), "Report not atomically published");
        });
        check("missing public proof invalidates prior success before failing", (catalog, manifests) =>
        {
            Workspace workspace = Setup(catalog, manifests);
            Verifier verifier = new(workspace);
            string output = verifier.OutputDirectory(Method);
            Write(output, "report.json", "old success");
            string path = Path.Combine(workspace.Verification, "manifests/api-coverage.json");
            JsonObject document = JsonNode.Parse(File.ReadAllText(path))!.AsObject();
            document["entries"]!.AsArray().Single(entry => entry?["id"]?.GetValue<string>() == Method)!.AsObject().Remove("verification");
            File.WriteAllText(path, document.ToJsonString());
            Program.Reject(() => verifier.Verify(new(Method)));
            Program.Require(!File.Exists(Path.Combine(output, "report.json")), "Unimplemented proof retained old success");
        });
        foreach (string failure in new[] { "sdk", "lean", "proof", "axiom", "duplicate-audit", "missing-audit", "source", "snapshot", "gate", "safety-gate" })
            check("verifier invalidates prior success on " + failure, (catalog, manifests) =>
            {
                Workspace workspace = Setup(catalog, manifests, failure);
                Verifier verifier = new(workspace);
                string output = Path.Combine(verifier.OutputDirectory(Method), "safety");
                Write(output, "report.json", "old success");
                Write(verifier.OutputDirectory(Method), "coverage.json", "old aggregate");
                Write(workspace.Verification, "generated/safety/coverage.json", "old aggregate");
                Program.Reject(() => verifier.Verify(new(Method, Safety: true)));
                Program.Require(!File.Exists(Path.Combine(output, "report.json")), "Stale success survived");
                Program.Require(!File.Exists(Path.Combine(verifier.OutputDirectory(Method), "coverage.json")), "Stale arithmetic aggregate survived");
                Program.Require(!File.Exists(Path.Combine(workspace.Verification, "generated/safety/coverage.json")), "Stale safety aggregate survived");
            });
        check("shared worker reuse retains exact report bindings", (catalog, manifests) =>
        {
            Workspace workspace = Setup(catalog, manifests);
            Verifier verifier = new(workspace);
            ArtifactBundle bundle = workspace.BuildArtifact(workspace.ProductionProject, Path.Combine(workspace.Root, "build"), Method);
            using ProofSession session = new(workspace);
            JsonObject first = verifier.Verify(new(Method, Safety: true), bundle, session);
            JsonObject second = verifier.Verify(new(Method, Safety: true), bundle, session);
            Program.Require(!first["timings"]!["sessionProofReuse"]!.GetValue<bool>() && second["timings"]!["sessionProofReuse"]!.GetValue<bool>(), "Reuse marker incorrect");
            Program.Require(JsonNode.DeepEquals(first["axiomAudits"], second["axiomAudits"]), "Reuse changed theorem audits");
            Program.Require(JsonNode.DeepEquals(first["sourceInputs"], second["sourceInputs"]), "Reuse changed source binding");
        });
        check("registered fixture report preserves its project, case and shared source", (catalog, manifests) =>
        {
            Workspace workspace = Setup(catalog, manifests);
            Write(workspace.Verification, "Tests/Fixtures/Equality/Public.cs", "fixture");
            Verifier verifier = new(workspace);
            JsonObject report = verifier.Verify(new(Method, Fixture: "Renamed"));
            Program.Require(Catalog.Text(report["source"]!["kind"]) == "fixture", "Fixture claimed production identity");
            Program.Require(Catalog.Text(report["source"]!["case"]) == "Renamed", "Case identity lost");
            Program.Require(Catalog.Text(report["source"]!["fixture"]) == "verification/Tests/Fixtures/Equality/Public.cs", "Shared fixture source lost");
            Program.Require(Catalog.Text(report["source"]!["project"]) == "verification/Tests/Fixtures/Equality/Nethermind.Int256.csproj", "Wrong fixture project");
            Program.Reject(() => verifier.Verify(new(Method, Fixture: "../Renamed")));
            Program.Require(!File.Exists(Path.Combine(verifier.OutputDirectory(Method), "report.json")), "Unknown fixture retained success");
        });
    }
}
