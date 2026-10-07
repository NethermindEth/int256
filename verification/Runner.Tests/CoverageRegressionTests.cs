// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System.Collections.Concurrent;
using System.Text.Json.Nodes;
using UInt256Verification;

namespace UInt256VerificationTests;

internal static class CoverageRegressionTests
{
    internal static void Register(Action<string, Action<Catalog, string>> check)
    {
        foreach (var item in new[] { ("Lsh", "x64-vector256", "vector256Accelerated"), ("EqUInt256UInt256", "x64-sse41", "sse41"),
            ("LtUInt256UInt256", "x64-vector256", "vector256Accelerated"), ("Multiply", "arm64-armbase-vector256", "armBase64") })
            check("family rejects duplicate profile flags: " + item.Item1, (catalog, manifests) =>
            {
                string path = Path.Combine(manifests, "profiles", item.Item2 + ".json");
                JsonObject profile = JsonNode.Parse(File.ReadAllText(path))!.AsObject();
                profile[item.Item3] = false;
                File.WriteAllText(path, profile.ToJsonString());
                Program.Reject(() => catalog.Plan([item.Item1]));
            });
        check("coverage plans retain independent dispatch and storage representatives", (catalog, _) =>
        {
            foreach (var item in new[] {
                ("LtUInt256UInt64", new[] { "scalar" }), ("Lsh", new[] { "scalar", "x64-vector256" }),
                ("EqUInt256UInt256", new[] { "scalar", "x64-sse41", "x64-vector256" }),
                ("LtUInt256UInt256", new[] { "scalar", "x64-vector256", "x64-avx2", "x64-avx512" }) })
                Program.Require(catalog.Plan([item.Item1])["include"]!.AsArray().Select(job => Catalog.Text(job!["profile"])).SequenceEqual(item.Item2), item.Item1);
            var flags = catalog.Plan(["Multiply"])["include"]!.AsArray().Select(job => catalog.Profile(Catalog.Text(job!["profile"])))
                .Select(profile => (profile["Bmi2"]!.GetValue<bool>(), profile["ArmBase64"]!.GetValue<bool>(), profile["Avx512DQVL"]!.GetValue<bool>(),
                    profile["Avx2"]!.GetValue<bool>(), profile["Vector256Accelerated"]!.GetValue<bool>())).ToHashSet();
            var arithmetic = new[] { (false, false, false, false), (false, false, false, true), (false, false, true, true), (true, false, false, false),
                (true, false, false, true), (true, false, true, true), (false, true, false, false) };
            Program.Require(flags.SetEquals(from combination in arithmetic from storage in new[] { false, true } select (combination.Item1, combination.Item2, combination.Item3, combination.Item4, storage)), "Multiplication classes incomplete");
            Program.Reject(() => catalog.Profile("x64-new-isa"));
            Program.Require(Catalog.Profiles.Select(name => catalog.Profile(name).ToJsonString()).Distinct().Count() == 7, "Legacy representatives collapsed");
        });
        foreach (string method in new[] { "EqInt64UInt256", "Lsh" })
            foreach (string mutation in new[] { "project", "fixture", "provenance", "proof-file", "program-file", "table-file", "gate-file", "safety-file", "matched-abi" })
                check($"coverage retained evidence: {method}/{mutation}", (catalog, manifests) =>
                {
                    Workspace workspace = VerifierTests.Setup(catalog, manifests, method: method);
                    Verifier verifier = new(workspace);
                    JsonObject report = verifier.Verify(new(method, Safety: true));
                    string directory = Path.Combine(verifier.OutputDirectory(method), "safety");
                    string artifactPath = Path.Combine(directory, "artifact.json");
                    switch (mutation)
                    {
                        case "project": report["source"]!["project"] = "fixture.csproj"; break;
                        case "fixture": report["source"]!["fixture"] = "Fixture.cs"; break;
                        case "provenance": report["source"] = new JsonObject { ["kind"] = "production" }; break;
                        case "proof-file": File.WriteAllText(Path.Combine(workspace.Verification, "Proof.lean"), "changed"); break;
                        case "program-file": File.AppendAllText(Path.Combine(directory, "Extracted.lean"), "changed"); break;
                        case "table-file":
                            JsonObject artifact = JsonNode.Parse(File.ReadAllText(artifactPath))!.AsObject();
                            artifact["staticData"] = new JsonArray(new JsonObject { ["bytes"] = "00010204" });
                            File.WriteAllText(artifactPath, artifact.ToJsonString()); break;
                        case "gate-file": File.AppendAllText(Path.Combine(directory, "SelectedGate.lean"), "changed"); break;
                        case "safety-file":
                            if (File.Exists(Path.Combine(directory, "SelectedSafetyGate.lean"))) File.AppendAllText(Path.Combine(directory, "SelectedSafetyGate.lean"), "changed");
                            else report["safety"]!["target"] = "+Wrong:olean";
                            break;
                        case "matched-abi":
                            report["artifact"]!["methods"]![0]!["parameters"]![0]!["IsIn"] = !report["artifact"]!["methods"]![0]!["parameters"]![0]!["IsIn"]!.GetValue<bool>();
                            File.WriteAllText(artifactPath, report["artifact"]!.ToJsonString()); break;
                    }
                    File.WriteAllText(Path.Combine(directory, "report.json"), report.ToJsonString());
                    Program.Reject(() => new Coverage(workspace).Certificate(method, "scalar", workspace.Inputs(), safety: true));
                });
        foreach (string mutation in new[] { "program", "table", "proof-copy" })
            check("composition detects changed " + mutation, (catalog, manifests) =>
            {
                const string method = "LtUInt256UInt64";
                string directory = Path.Combine(Path.GetDirectoryName(manifests)!, $"source/verification/generated/operations/{method}/scalar/safety");
                Workspace workspace = VerifierTests.Setup(catalog, manifests, method: method, during: (stage, proof) =>
                {
                    if (stage != "Coverage checking") return;
                    if (mutation == "proof-copy") File.WriteAllText(Path.Combine(proof, "Proof.lean"), "transient copied source");
                    else if (mutation == "program") File.AppendAllText(Path.Combine(directory, "Extracted.lean"), "changed");
                    else
                    {
                        string path = Path.Combine(directory, "artifact.json");
                        JsonObject artifact = JsonNode.Parse(File.ReadAllText(path))!.AsObject();
                        artifact["staticData"] = new JsonArray(new JsonObject { ["bytes"] = "ff" });
                        File.WriteAllText(path, artifact.ToJsonString());
                    }
                });
                new Verifier(workspace).Verify(new(method, Safety: true));
                File.WriteAllText(Path.Combine(directory, "coverage.json"), "prior success");
                Program.Reject(() => new Coverage(workspace).Run(new(Method: method, Safety: true, CheckReports: true)));
                Program.Require(!File.Exists(Path.Combine(directory, "coverage.json")), "Stale aggregate survived");
            });
        check("parallel workers share binaries but keep separate disposable proof directories", (catalog, manifests) =>
        {
            using Barrier barrier = new(2);
            ConcurrentBag<string> proofs = [];
            Workspace workspace = VerifierTests.Setup(catalog, manifests, during: (stage, directory) =>
            {
                if (stage != "Proof checking") return;
                proofs.Add(directory);
                Program.Require(barrier.SignalAndWait(TimeSpan.FromSeconds(20)), "Workers did not execute concurrently");
            });
            ArtifactBundle bundle = workspace.BuildArtifact(workspace.ProductionProject, Path.Combine(workspace.Root, "build"), "EqInt64UInt256");
            new Coverage(workspace).VerifyProfiles([("EqInt64UInt256", "scalar"), ("EqInt64UInt256", "x64-vector256")], bundle, 2, safety: true);
            Program.Require(proofs.Count == 2 && proofs.Distinct().Count() == 2 && proofs.All(path => !Directory.Exists(path)), "Workers shared or leaked their caches");
            foreach (string profile in new[] { "scalar", "x64-vector256" })
                Program.Require(Catalog.Text(new Coverage(workspace).Certificate("EqInt64UInt256", profile, workspace.Inputs(), true)["assemblySha256"]) == bundle.AssemblySha256, "Worker used another assembly");
        });
        check("coverage failure skips composition and clears aggregate success", (catalog, manifests) =>
        {
            int compositions = 0;
            Workspace workspace = VerifierTests.Setup(catalog, manifests, "proof", (stage, _) => { if (stage == "Coverage checking") compositions++; });
            string directory = new Verifier(workspace).OutputDirectory("EqInt64UInt256");
            Directory.CreateDirectory(directory);
            File.WriteAllText(Path.Combine(directory, "coverage.json"), "old success");
            Program.Reject(() => new Coverage(workspace).Run(new(Method: "EqInt64UInt256", Jobs: 2)));
            Program.Require(compositions == 0 && !File.Exists(Path.Combine(directory, "coverage.json")), "Failed proofs published coverage");
        });
        check("incomplete families fail before builds or partial plan output", (catalog, manifests) =>
        {
            Workspace workspace = VerifierTests.Setup(catalog, manifests, during: (_, _) => throw new InvalidOperationException("Unexpected build"));
            string path = Path.Combine(workspace.Verification, "manifests/api-coverage.json");
            JsonObject document = JsonNode.Parse(File.ReadAllText(path))!.AsObject();
            document["entries"]!.AsArray().Single(entry => entry?["id"]?.GetValue<string>() == "EqInt64UInt256")!["verification"]!.AsObject().Remove("familyCoverage");
            File.WriteAllText(path, document.ToJsonString());
            string directory = new Verifier(workspace).OutputDirectory("EqInt64UInt256");
            Directory.CreateDirectory(directory); File.WriteAllText(Path.Combine(directory, "coverage.json"), "prior");
            Program.Reject(() => new Coverage(workspace).Run(new(Method: "EqInt64UInt256")));
            Program.Require(!File.Exists(Path.Combine(directory, "coverage.json")), "Incomplete plan retained aggregate");
            Program.Reject(() => new Coverage(workspace).Run(new(Method: "EqInt64UInt256", PrintPlan: true)));
        });
    }
}
