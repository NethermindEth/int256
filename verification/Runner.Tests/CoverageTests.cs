// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System.Text.Json.Nodes;
using UInt256Verification;

namespace UInt256VerificationTests;

internal static class CoverageTests
{
    private const string Method = "EqInt64UInt256";

    internal static void Register(Action<string, Action<Catalog, string>> check)
    {
        CoverageRegressionTests.Register(check);
        check("coverage options reject conflicting selections and invalid worker counts", (_, _) =>
        {
            Program.Require(CoverageOptions.Parse([]) == new CoverageOptions(), "Default coverage changed");
            foreach (string[] args in new[] { new[] { "--jobs", "0" }, new[] { "--jobs", "-1" }, new[] { "--jobs", "invalid" }, new[] { "--jobs", "999999999999999999999" }, new[] { "--jobs" }, new[] { "--method", "Add", "--expanded" }, new[] { "--check-reports", "--check-reports" } })
                Program.Reject(() => CoverageOptions.Parse(args));
        });
        check("combined certificate binds report, artifacts and selected contract", (catalog, manifests) =>
        {
            Workspace workspace = VerifierTests.Setup(catalog, manifests);
            JsonObject report = new Verifier(workspace).Verify(new(Method, Safety: true));
            JsonObject certificate = new Coverage(workspace).Certificate(Method, "scalar", workspace.Inputs(), safety: true);
            Program.Require(Catalog.Text(certificate["method"]) == Method, "Wrong method");
            Program.Require(JsonNode.DeepEquals(certificate["safety"], report["safety"]), "Safety binding lost");
            Program.Require(JsonNode.DeepEquals(certificate["axiomAudits"], report["axiomAudits"]), "Axiom audits lost");
            Program.Require(Catalog.Text(certificate["reportSha256"]) == Workspace.Hash(Path.Combine(workspace.Root, Catalog.Text(certificate["report"]))), "Report identity lost");
        });
        check("coverage print-plan preserves existing reports and never builds", (catalog, manifests) =>
        {
            Workspace workspace = VerifierTests.Setup(catalog, manifests, during: (_, _) => throw new InvalidOperationException("Plan invoked a tool"));
            string directory = new Verifier(workspace).OutputDirectory(Method);
            Directory.CreateDirectory(directory);
            string path = Path.Combine(directory, "coverage.json");
            File.WriteAllText(path, "retained");
            JsonObject plan = new Coverage(workspace).Run(new(Method: Method, PrintPlan: true));
            Program.Require(plan["include"]!.AsArray().Count == 2 && File.ReadAllText(path) == "retained", "Plan changed coverage or omitted representatives");
            Program.Reject(() => CoverageOptions.Parse(["--print-plan", "--check-reports"]));
        });
        foreach (string mutation in new[] { "source", "inputs", "lean", "semantics", "artifact", "program", "profile", "scope", "gate", "names", "audits", "axioms", "duplicate-axioms", "evidence", "safety", "coverage", "safety-gate", "arithmetic" })
            check("coverage rejects certificate mutation: " + mutation, (catalog, manifests) =>
            {
                Workspace workspace = VerifierTests.Setup(catalog, manifests);
                Verifier verifier = new(workspace);
                JsonObject report = verifier.Verify(new(Method, Safety: true));
                string path = Path.Combine(verifier.OutputDirectory(Method), "safety/report.json");
                switch (mutation)
                {
                    case "source": report["source"]!["kind"] = "fixture"; break;
                    case "inputs": report["sourceInputs"]!.AsObject().Remove("global.json"); break;
                    case "lean": report["leanSourceSha256"] = new JsonObject(); break;
                    case "semantics": report["semanticsVersion"] = "old"; break;
                    case "artifact": report["artifact"]!["sha256"] = "wrong"; break;
                    case "program": report["generatedProgramSha256"] = "wrong"; break;
                    case "profile": report["executionProfile"]!["Bmi1"] = true; break;
                    case "scope": report["scope"]!["entry"] = "wrong"; break;
                    case "gate": report["generatedGateSha256"] = "wrong"; break;
                    case "names": report["auditedTheorems"]!.AsArray().RemoveAt(0); break;
                    case "audits": report["axiomAudits"]!.AsObject().Remove(Catalog.Text(report["auditedTheorems"]![0])); break;
                    case "axioms": report["axiomAudits"]![Catalog.Text(report["auditedTheorems"]![0])] = new JsonArray("sorryAx"); break;
                    case "duplicate-axioms": report["axiomAudits"]![Catalog.Text(report["auditedTheorems"]![0])] = new JsonArray("propext", "propext"); break;
                    case "evidence": report.Remove("evidenceKind"); break;
                    case "safety": report["safety"]!["alignmentPolicy"]!["ordinaryAccessBytes"] = 8; break;
                    case "coverage": report["coverage"]!["kind"] = "exact-profile"; break;
                    case "safety-gate": report["generatedSafetyGateSha256"] = "wrong"; break;
                    case "arithmetic": report["arithmeticCoverage"]!["aggregateChecked"] = true; break;
                }
                File.WriteAllText(path, report.ToJsonString());
                Program.Reject(() => new Coverage(workspace).Certificate(Method, "scalar", workspace.Inputs(), safety: true));
            });
        check("composition checks source copies and exact toolchain", (catalog, manifests) =>
        {
            Workspace workspace = VerifierTests.Setup(catalog, manifests, during: (stage, directory) =>
            {
                if (stage == "Coverage checking") File.WriteAllText(Path.Combine(directory, "Proof.lean"), "tampered");
            });
            Program.Reject(() => new Coverage(workspace).Compose(workspace.Inputs(), operations: true));
            Workspace wrongLean = VerifierTests.Setup(catalog, manifests, "lean");
            Program.Reject(() => new Coverage(wrongLean).Compose(wrongLean.Inputs(), operations: true));
        });
        check("profile workers reuse a fresh shared build", (catalog, manifests) =>
        {
            Workspace workspace = VerifierTests.Setup(catalog, manifests);
            ArtifactBundle bundle = workspace.BuildArtifact(workspace.ProductionProject, Path.Combine(workspace.Root, "build"), Method);
            Coverage coverage = new(workspace);
            coverage.VerifyProfiles([(Method, "scalar"), (Method, "scalar")], bundle, 1, safety: true);
            JsonObject certificate = coverage.Certificate(Method, "scalar", workspace.Inputs(), safety: true);
            Program.Require(certificate["timings"]!["sessionProofReuse"]!.GetValue<bool>(), "Worker did not reuse checked dependencies");
            coverage.VerifyProfiles([(Method, "scalar")], bundle, 2, safety: true);
        });
        check("worker failure prevents remaining queued jobs", (catalog, manifests) =>
        {
            int proofs = 0;
            Workspace workspace = VerifierTests.Setup(catalog, manifests, "proof", (stage, _) => { if (stage == "Proof checking") proofs++; });
            ArtifactBundle bundle = workspace.BuildArtifact(workspace.ProductionProject, Path.Combine(workspace.Root, "build"), Method);
            Program.Reject(() => new Coverage(workspace).VerifyProfiles([(Method, "scalar"), (Method, "scalar")], bundle, 1, safety: true));
            Program.Require(proofs == 1, "Failed worker continued proving queued jobs");
        });
        check("complete coverage publishes exact combined certificates and composition", (catalog, manifests) =>
        {
            const string method = "LtUInt256UInt64";
            Workspace workspace = VerifierTests.Setup(catalog, manifests, method: method);
            JsonObject report = new Coverage(workspace).Run(new(Method: method, Safety: true, Jobs: 2));
            Program.Require(Catalog.Text(report["status"]) == "verified" && report["certificates"]!.AsArray().Count == 1, "Incomplete total coverage");
            Program.Require(report["axiomAudits"]!.AsObject().Count == Coverage.Theorems.Length + Coverage.OperationTheorems.Length, "Composition audits missing");
            Program.Require(report["sharedBuildTimings"] is JsonObject && report["proofJobs"]!.GetValue<int>() == 2, "Shared build provenance lost");
            string path = Path.Combine(new Verifier(workspace).OutputDirectory(method), "safety/coverage.json");
            Program.Require(File.Exists(path) && !File.Exists(path + ".tmp"), "Aggregate not published atomically");
            JsonObject checkedReport = new Coverage(workspace).Run(new(Method: method, Safety: true, CheckReports: true));
            Program.Require(checkedReport["proofJobs"] is null && checkedReport["sharedBuildTimings"] is null, "Check-only mode claimed a fresh build");
            Program.Require(JsonNode.DeepEquals(checkedReport["certificates"], report["certificates"]), "Certificate changed during check-only composition");
        });
        check("composition cannot publish a report changed after validation", (catalog, manifests) =>
        {
            const string method = "LtUInt256UInt64";
            string root = Path.Combine(Path.GetDirectoryName(manifests)!, "source");
            string directory = Path.Combine(root, $"verification/generated/operations/{method}/scalar/safety");
            Workspace workspace = VerifierTests.Setup(catalog, manifests, method: method, during: (stage, _) =>
            {
                if (stage != "Coverage checking") return;
                string path = Path.Combine(directory, "report.json");
                JsonObject report = JsonNode.Parse(File.ReadAllText(path))!.AsObject();
                report["timings"]!["totalSeconds"] = 123;
                File.WriteAllText(path, report.ToJsonString());
            });
            new Verifier(workspace).Verify(new(method, Safety: true));
            File.WriteAllText(Path.Combine(directory, "coverage.json"), "old aggregate");
            Program.Reject(() => new Coverage(workspace).Run(new(Method: method, Safety: true, CheckReports: true)));
            Program.Require(!File.Exists(Path.Combine(directory, "coverage.json")), "Changed certificate retained aggregate success");
        });
        check("legacy certificates retain family, composition and representative bindings", (catalog, manifests) =>
        {
            Workspace workspace = VerifierTests.Setup(catalog, manifests);
            foreach (string method in Catalog.Legacy)
            {
                string directory = new Verifier(workspace).OutputDirectory(method);
                Directory.CreateDirectory(directory);
                File.WriteAllText(Path.Combine(directory, "Extracted.lean"), "program");
                JsonObject artifact = new() { ["sha256"] = "assembly", ["profile"] = catalog.Profile("scalar"), ["entryIndex"] = 0,
                    ["methods"] = new JsonArray(new JsonObject { ["signature"] = catalog.Manifest(method)["entry"]!.DeepClone() }) };
                File.WriteAllText(Path.Combine(directory, "artifact.json"), artifact.ToJsonString());
                string[] names = ProofAudits.Names(catalog, method);
                JsonObject audits = [];
                foreach (string name in names) audits[name] = new JsonArray("propext");
                JsonObject report = new()
                {
                    ["status"] = "verified", ["source"] = new JsonObject { ["kind"] = "production", ["project"] = "src/Nethermind.Int256/Nethermind.Int256.csproj", ["fixture"] = null },
                    ["sourceInputs"] = System.Text.Json.JsonSerializer.SerializeToNode(workspace.Inputs()),
                    ["leanSourceSha256"] = System.Text.Json.JsonSerializer.SerializeToNode(Workspace.SourceFiles(workspace.Verification, [".lean"]).ToDictionary(p => Workspace.Relative(workspace.Verification, p), Workspace.Hash)),
                    ["artifact"] = artifact, ["executionProfile"] = catalog.Profile("scalar"), ["semanticsVersion"] = Verifier.SemanticsVersion,
                    ["generatedProgramSha256"] = Workspace.Hash(Path.Combine(directory, "Extracted.lean")),
                    ["auditedTheorems"] = System.Text.Json.JsonSerializer.SerializeToNode(names), ["axiomAudits"] = audits,
                    ["coverage"] = new JsonObject { ["kind"] = "feature-family", ["representative"] = "scalar" }
                };
                string path = Path.Combine(directory, "report.json");
                File.WriteAllText(path, report.ToJsonString());
                JsonObject certificate = new Coverage(workspace).Certificate(method, "scalar", workspace.Inputs());
                Program.Require(Catalog.Text(certificate["familyTheorem"]) == names[1] && Catalog.Text(certificate["compositionCertificate"]) == names[2]
                    && Catalog.Text(certificate["representativeTheorem"]) == names[3], "Legacy bindings changed");
                JsonObject combined = report.DeepClone().AsObject(), safety = SafetyCatalog.Gate(method, "scalar");
                combined["evidenceKind"] = "arithmetic-and-memory-safety";
                combined["safety"] = safety;
                combined["arithmeticCoverage"] = combined["coverage"]!.DeepClone();
                JsonObject expectedCoverage = safety["coverage"]!.DeepClone().AsObject();
                expectedCoverage["aggregateChecked"] = false; expectedCoverage["representative"] = "scalar";
                combined["coverage"] = expectedCoverage;
                foreach (JsonNode? name in safety["theorems"]!.AsArray())
                {
                    combined["auditedTheorems"]!.AsArray().Add(name!.DeepClone());
                    combined["axiomAudits"]![Catalog.Text(name)] = new JsonArray("propext");
                }
                string safetyDirectory = Path.Combine(directory, "safety");
                Directory.CreateDirectory(safetyDirectory);
                foreach (string file in new[] { "artifact.json", "Extracted.lean" }) File.Copy(Path.Combine(directory, file), Path.Combine(safetyDirectory, file));
                string safetyTarget = Path.Combine(safetyDirectory, "SelectedSafetyGate.lean");
                File.WriteAllText(safetyTarget, SafetyGates.Module(catalog, method, "scalar"));
                combined["generatedSafetyGateSha256"] = Workspace.Hash(safetyTarget);
                string safetyPath = Path.Combine(safetyDirectory, "report.json");
                File.WriteAllText(safetyPath, combined.ToJsonString());
                new Coverage(workspace).Certificate(method, "scalar", workspace.Inputs(), safety: true);
                foreach (string field in new[] { "evidenceKind", "safety", "arithmeticCoverage" })
                {
                    JsonObject changed = combined.DeepClone().AsObject(); changed.Remove(field);
                    File.WriteAllText(safetyPath, changed.ToJsonString());
                    Program.Reject(() => new Coverage(workspace).Certificate(method, "scalar", workspace.Inputs(), safety: true));
                }
                report["auditedTheorems"]!.AsArray().RemoveAt(1);
                File.WriteAllText(path, report.ToJsonString());
                Program.Reject(() => new Coverage(workspace).Certificate(method, "scalar", workspace.Inputs()));
            }
        });
    }
}
