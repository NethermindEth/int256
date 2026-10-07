// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System.Diagnostics;
using System.Text.Json;
using System.Text.Json.Nodes;
using System.Text.RegularExpressions;
using System.Xml.Linq;

namespace UInt256Verification;

internal sealed record VerifyOptions(string Method = "Add", string Profile = "scalar", bool Safety = false, string? Fixture = null, string? SimdFixture = null)
{
    internal static VerifyOptions Parse(IReadOnlyList<string> arguments)
    {
        VerifyOptions options = new();
        HashSet<string> seen = [];
        for (int i = 0; i < arguments.Count; i++)
        {
            string flag = arguments[i];
            if (!seen.Add(flag)) throw new ArgumentException($"Repeated option: {flag}");
            if (flag == "--safety") { options = options with { Safety = true }; continue; }
            if (i + 1 == arguments.Count) throw new ArgumentException($"Missing value for {flag}");
            string value = arguments[++i];
            options = flag switch
            {
                "--method" => options with { Method = value }, "--profile" => options with { Profile = value },
                "--fixture" => options with { Fixture = value }, "--simd-fixture" => options with { SimdFixture = value },
                _ => throw new ArgumentException($"Unknown verification option: {flag}")
            };
        }
        if (options.Fixture is not null && options.SimdFixture is not null) throw new ArgumentException("Choose one fixture kind");
        return options;
    }
}

internal sealed class Verifier(Workspace workspace)
{
    internal const string SemanticsVersion = "cil-uint256-operations-1";
    internal string OutputDirectory(string method, string profile = "scalar")
    {
        if (!workspace.Catalog.MethodNames.Contains(method) || !workspace.Catalog.ProfileNames.Contains(profile))
            throw new ArgumentException("Unknown verification method or feature profile");
        string path = !Catalog.Legacy.Contains(method) ? $"generated/operations/{method}/{profile}"
            : profile == "scalar" ? (method == "Add" ? "generated" : "generated/subtract")
            : $"generated/profiles/{profile}/{method.ToLowerInvariant()}";
        return Path.Combine(workspace.Verification, path);
    }

    private static void DeleteIfPresent(string path)
    {
        if (Directory.Exists(Path.GetDirectoryName(path))) File.Delete(path);
    }

    private static JsonNode Node<T>(T value) => JsonSerializer.SerializeToNode(value)!;

    internal JsonObject Verify(VerifyOptions options, ArtifactBundle? prepared = null, ProofSession? session = null)
    {
        string method = options.Method, profile = options.Profile;
        string outputDirectory = OutputDirectory(method, profile);
        if (options.Safety) outputDirectory = Path.Combine(outputDirectory, "safety");
        Directory.CreateDirectory(outputDirectory);
        string reportPath = Path.Combine(outputDirectory, "report.json");
        DeleteIfPresent(reportPath);
        foreach (string directory in new[] { Path.Combine(workspace.Verification, "generated"), OutputDirectory(method) })
        {
            DeleteIfPresent(Path.Combine(directory, "coverage.json"));
            DeleteIfPresent(Path.Combine(directory, "safety/coverage.json"));
        }
        Stopwatch total = Stopwatch.StartNew();
        JsonObject stages = [];
        JsonObject? safety = options.Safety ? SafetyCatalog.Gate(method, profile) : null;
        Catalog catalog = workspace.Catalog;
        JsonObject manifest = catalog.Manifest(method);
        JsonObject? gate = manifest["verification"]?.AsObject();
        if (gate is null && !Catalog.Profiles.Contains(profile))
            throw new InvalidOperationException("Additional profiles require an exact API profile-agreement audit gate");
        if (gate is not null && options.SimdFixture is not null)
            throw new InvalidOperationException("Selected API does not use the legacy SIMD fixture project");
        string? fixtureName = options.SimdFixture ?? options.Fixture;
        string group = gate?["fixtureGroup"] is { } selectedGroup ? Catalog.Text(selectedGroup) : method;
        string fixtureDirectory = Path.GetFullPath(Path.Combine(workspace.Verification, "Tests/Fixtures", options.SimdFixture is not null ? "SIMD" : group));
        string? fixture = null;
        if (fixtureName is not null)
        {
            if (options.SimdFixture is not null && !SimdCases(workspace.Verification).Contains(fixtureName))
                throw new InvalidOperationException($"Unknown SIMD fixture: {fixtureName}");
            if (gate is not null && !(gate["fixtureCases"]?.AsArray().Select(Catalog.Text).Contains(fixtureName) ?? false))
                throw new InvalidOperationException($"Unknown fixture for selected API: {fixtureName}");
            string source = options.SimdFixture is not null ? "Cases.props"
                : gate?["fixtureSources"]?[fixtureName] is { } registeredSource ? Catalog.Text(registeredSource) : fixtureName + ".cs";
            fixture = Path.GetFullPath(Path.Combine(fixtureDirectory, source));
            if (Path.GetDirectoryName(fixture) != fixtureDirectory || !File.Exists(fixture))
                throw new InvalidOperationException("Fixture maintenance failure: requested versioned fixture is absent");
        }
        string project = fixture is null ? workspace.ProductionProject : gate is not null || options.SimdFixture is not null
            ? Path.Combine(fixtureDirectory, "Nethermind.Int256.csproj") : Path.Combine(workspace.Verification, "Tests/Fixtures/Nethermind.Int256.csproj");
        Dictionary<string, string> inputs = workspace.Inputs();
        string sdk = workspace.Run(["dotnet", "--version"], workspace.Root).Trim();
        if (sdk != Catalog.Text(manifest["sdk"])) throw new InvalidOperationException($"SDK {manifest["sdk"]} required; got {sdk}");
        string lean = workspace.Run(["lake", "env", "lean", "--version"], workspace.Verification).Trim();
        if (!Regex.IsMatch(lean, @"version 4\.34\.1\b")) throw new InvalidOperationException($"Unexpected Lean toolchain: {lean}");
        if (prepared is not null && fixture is not null) throw new InvalidOperationException("A shared production build cannot verify fixtures");
        if (session is not null && (prepared is null || fixture is not null)) throw new InvalidOperationException("Proof reuse requires a shared production build");

        string work = Directory.CreateTempSubdirectory("int256-verify-").FullName;
        try
        {
            ArtifactBundle bundle = prepared ?? workspace.BuildArtifact(project, work, method, fixture, options.SimdFixture is not null || gate is not null, fixtureName);
            workspace.ValidateBundle(bundle, inputs, production: prepared is not null);
            if (prepared is not null) stages["sharedAssemblyBuild"] = true;
            else foreach ((string name, double duration) in bundle.Timings) stages[name] = duration;
            using ProofSession? ownedSession = session is null ? new(workspace) : null;
            ProofSession worker = session ?? ownedSession!;
            string[] copiedPaths = worker.Prepare(inputs);
            string proof = worker.Directory;
            if (session is not null) stages["sessionProofReuse"] = worker.Uses > 1;
            string generated = Path.Combine(proof, "generated");
            Stopwatch timer = Stopwatch.StartNew();
            JsonObject artifact = workspace.Extract(bundle, generated, method, profile);
            stages["extractionSeconds"] = timer.Elapsed.TotalSeconds;
            string? generatedGateHash = null, generatedSafetyHash = null;
            string target = Path.Combine(proof, "UInt256/Methods/SelectedGate.lean");
            string safetyTarget = Path.Combine(proof, "UInt256/Methods/SelectedSafetyGate.lean");
            string WriteGate(string path, string text)
            {
                if (File.Exists(path)) throw new InvalidOperationException("Generated audit would overwrite handwritten source");
                Directory.CreateDirectory(Path.GetDirectoryName(path)!);
                File.WriteAllText(path, text);
                return Workspace.Hash(path);
            }
            if (gate is not null) generatedGateHash = WriteGate(target, AuditGates.Module(catalog.Entries()[method]));
            if (safety?["generatedAudit"]?.GetValue<bool>() == true) generatedSafetyHash = WriteGate(safetyTarget, SafetyGates.Module(catalog, method, profile));
            string auditTarget = gate is not null ? "+UInt256.Methods.SelectedGate:olean" : method == "Add" ? "Audit" : "SubtractAudit";
            timer.Restart();
            string output = workspace.Run(["lake", "build", auditTarget], proof, "Proof checking");
            stages[session is not null && worker.Uses > 1 ? "kernelBuildSeconds" : "freshKernelBuildSeconds"] = timer.Elapsed.TotalSeconds;
            List<string> auditedNames = [.. ProofAudits.Names(catalog, method)];
            string[] approved = manifest["approvedAxioms"]!.AsArray().Select(Catalog.Text).ToArray();
            Dictionary<string, string[]> audits = ProofAudits.Check(output, auditedNames, approved);
            string[] axioms = audits[auditedNames[0]];
            if (safety is not null)
            {
                timer.Restart();
                string safetyOutput = workspace.Run(["lake", "build", Catalog.Text(safety["target"])], proof, "Safety proof checking");
                stages["safetyKernelBuildSeconds"] = timer.Elapsed.TotalSeconds;
                string[] names = safety["theorems"]!.AsArray().Select(Catalog.Text).ToArray();
                foreach (var pair in ProofAudits.Check(safetyOutput, names, approved)) audits[pair.Key] = pair.Value;
                auditedNames.AddRange(names);
            }
            workspace.ValidateBundle(bundle, inputs, production: prepared is not null);
            Dictionary<string, string> copiedHashes = Workspace.CheckProofSnapshot(proof, copiedPaths, inputs);
            if (generatedGateHash is not null && Workspace.Hash(target) != generatedGateHash)
                throw new InvalidOperationException("Generated typed audit changed during proof checking");
            if (generatedSafetyHash is not null && Workspace.Hash(safetyTarget) != generatedSafetyHash)
                throw new InvalidOperationException("Generated safety audit changed during proof checking");
            string commit = workspace.Run(["git", "rev-parse", "HEAD"], workspace.Root).Trim();
            string[] status = workspace.Run(["git", "status", "--porcelain"], workspace.Root).Split(['\r', '\n'], StringSplitOptions.RemoveEmptyEntries);
            JsonObject scope = manifest.DeepClone().AsObject();
            scope["environment"]!["selectedProfile"] = profile;
            stages["totalSeconds"] = total.Elapsed.TotalSeconds;
            JsonObject source = new() { ["kind"] = fixture is null ? "production" : "fixture", ["project"] = Workspace.Relative(workspace.Root, project),
                ["fixture"] = fixture is null ? null : Workspace.Relative(workspace.Root, fixture) };
            if (options.SimdFixture is not null || (gate is not null && fixture is not null)) source["case"] = fixtureName;
            JsonObject report = new()
            {
                ["status"] = "verified", ["sourceCommit"] = commit, ["sourceStatus"] = Node(status), ["nativeLimitations"] = catalog.NativeLimitations([method]),
                ["sourceInputs"] = Node(inputs), ["artifact"] = artifact, ["scope"] = scope, ["executionProfile"] = artifact["profile"]!.DeepClone(),
                ["semanticsVersion"] = SemanticsVersion, ["extractorSha256"] = bundle.ExtractorSha256,
                ["auditedTheorems"] = Node(auditedNames), ["axiomAudits"] = Node(audits),
                ["coverage"] = new JsonObject { ["kind"] = gate is null ? "feature-family" : Catalog.Text(gate["profileCoverage"]), ["aggregateChecked"] = false,
                    ["representative"] = profile, ["condition"] = gate is null ? "Valid profile with the same checked FeatureClass"
                        : gate["allProfiles"]?.GetValue<bool>() == true ? "Every valid profile; kernel-checked independence of actual program operations"
                        : "Valid profile agreeing on actual program feature queries and operation availability" },
                ["source"] = source, ["sdk"] = sdk, ["lean"] = lean, ["axioms"] = Node(axioms), ["timings"] = stages,
                ["summaryRejections"] = Node(Regex.Matches(output, @"Optional summary candidate (\S+) was not proved; using raw execution \(([^)]+)\)")
                    .Select(match => new[] { match.Groups[1].Value, match.Groups[2].Value }).ToArray()),
                ["generatedProgramSha256"] = Workspace.Hash(Path.Combine(generated, "Extracted.lean")), ["generatedGateSha256"] = generatedGateHash,
                ["leanSourceSha256"] = Node(copiedHashes.Where(pair => pair.Key.EndsWith(".lean", StringComparison.Ordinal)).ToDictionary())
            };
            if (safety is not null)
            {
                report["evidenceKind"] = "arithmetic-and-memory-safety";
                report["safety"] = safety;
                report["generatedSafetyGateSha256"] = generatedSafetyHash;
                report["arithmeticCoverage"] = report["coverage"]!.DeepClone();
                JsonObject coverage = safety["coverage"]?.DeepClone().AsObject() ?? new() { ["kind"] = "exact-profile", ["condition"] = "Exactly the extracted execution profile" };
                coverage["aggregateChecked"] = false; coverage["representative"] = profile;
                report["coverage"] = coverage;
            }
            foreach (string file in new[] { "Extracted.lean", "artifact.json" }) File.Copy(Path.Combine(generated, file), Path.Combine(outputDirectory, file), overwrite: true);
            if (generatedGateHash is not null) File.Copy(target, Path.Combine(outputDirectory, "SelectedGate.lean"), overwrite: true);
            if (generatedSafetyHash is not null) File.Copy(safetyTarget, Path.Combine(outputDirectory, "SelectedSafetyGate.lean"), overwrite: true);
            File.WriteAllText(reportPath + ".tmp", report.ToJsonString(new JsonSerializerOptions { WriteIndented = true }) + "\n");
            File.Move(reportPath + ".tmp", reportPath, overwrite: true);
            Console.WriteLine($"Verified {manifest["entry"]} from SHA256 {bundle.AssemblySha256}");
            return report;
        }
        finally { Directory.Delete(work, recursive: true); }
    }

    internal static Dictionary<string, string[]> SimdRegistry(string verification)
    {
        XElement[] cases = XDocument.Load(Path.Combine(verification, "Tests/Fixtures/SIMD/Cases.props"))
            .Elements("Project").Elements("ItemGroup").Elements("SimdCase").ToArray();
        string Name(XElement element) => (string?)element.Attribute("Include") ?? throw new InvalidOperationException("SIMD case has no name");
        foreach (XElement element in cases)
            if (element.Attribute("Suite") is null) throw new InvalidOperationException("SIMD case has no suite");
        return new() { ["SIMD_CASES"] = cases.Select(Name).ToArray(),
            ["SIMD_POSITIVES"] = cases.Where(element => (string?)element.Attribute("Suite") == "positive").Select(Name).ToArray(),
            ["SIMD_NEGATIVES"] = cases.Where(element => (string?)element.Attribute("Suite") == "negative").Select(Name).ToArray() };
    }

    internal static string[] SimdCases(string verification) => SimdRegistry(verification)["SIMD_CASES"];
}
