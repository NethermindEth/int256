// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System.Collections.Concurrent;
using System.Diagnostics;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using System.Text.Json.Nodes;
using System.Text.RegularExpressions;

namespace UInt256Verification;

internal sealed class Coverage(Workspace workspace)
{
    internal static readonly string[] Theorems = ["CIL.FeatureProfile.classification_total", "UInt256Proof.checked_feature_classes",
        "UInt256Proof.checked_representative_classes", "UInt256Proof.add_complete_coverage", "UInt256Proof.subtract_complete_coverage"];
    internal static readonly string[] OperationTheorems = ["UInt256Proof.vector_storage_complete_coverage", "UInt256Proof.classified_complete_coverage",
        "UInt256Proof.vector_reduction_complete_coverage", "UInt256Proof.relational_complete_coverage", "CIL.FeatureProfile.multiply_classification_flags", "UInt256Proof.multiply_complete_coverage"];
    private static JsonNode Node<T>(T value) => JsonSerializer.SerializeToNode(value)!;
    private static string HashText(string text) => Convert.ToHexStringLower(SHA256.HashData(Encoding.UTF8.GetBytes(text)));
    private static string[] Strings(JsonNode? node) => node!.AsArray().Select(Catalog.Text).ToArray();
    private static JsonObject Read(string path) => JsonNode.Parse(File.ReadAllText(path))!.AsObject();

    internal JsonObject Certificate(string method, string profile, IReadOnlyDictionary<string, string> inputs, bool safety = false)
    {
        Catalog catalog = workspace.Catalog;
        string directory = new Verifier(workspace).OutputDirectory(method, profile);
        if (safety) directory = Path.Combine(directory, "safety");
        string path = Path.Combine(directory, "report.json");
        JsonObject report = Read(path), artifact = Read(Path.Combine(directory, "artifact.json")), manifest = catalog.Manifest(method);
        List<string> names = [.. ProofAudits.Names(catalog, method)];
        JsonObject? safetySpec = safety ? SafetyCatalog.Gate(method, profile) : null;
        if (safetySpec is not null) names.AddRange(Strings(safetySpec["theorems"]));
        JsonNode leanHashes = Node(Workspace.SourceFiles(workspace.Verification, [".lean"]).ToDictionary(p => Workspace.Relative(workspace.Verification, p), Workspace.Hash));
        void Require(bool valid, string reason)
        {
            if (!valid) throw new InvalidOperationException($"{reason}: {method}/{profile}");
        }
        void Equal(JsonNode? actual, JsonNode? expected, string reason) => Require(JsonNode.DeepEquals(actual, expected), reason);
        Require(report["status"]?.GetValue<string>() == "verified", "Missing production certificate");
        Equal(report["source"], new JsonObject { ["kind"] = "production", ["project"] = "src/Nethermind.Int256/Nethermind.Int256.csproj", ["fixture"] = null }, "Missing production certificate");
        Equal(report["sourceInputs"], Node(inputs), "Stale proof inputs");
        Equal(report["leanSourceSha256"], leanHashes, "Stale proof inputs");
        Require(report["semanticsVersion"]?.GetValue<string>() == Verifier.SemanticsVersion, "Semantics version mismatch");
        Equal(report["artifact"], artifact, "Stale extraction");
        Require(report["generatedProgramSha256"]?.GetValue<string>() == Workspace.Hash(Path.Combine(directory, "Extracted.lean")), "Stale extraction");
        Equal(report["executionProfile"], catalog.Profile(profile), "Profile mismatch");
        Equal(artifact["profile"], catalog.Profile(profile), "Profile mismatch");
        JsonObject entry = artifact["methods"]![artifact["entryIndex"]!.GetValue<int>()]!.AsObject();
        Equal(entry["signature"], manifest["entry"], "Public entry mismatch");
        bool legacy = Catalog.Legacy.Contains(method);
        if (!legacy)
        {
            Catalog.CheckCallingConvention(entry, manifest["callingConvention"]!.AsObject());
            JsonObject scope = manifest.DeepClone().AsObject(); scope["environment"]!["selectedProfile"] = profile;
            Equal(report["scope"], scope, "Selected contract scope mismatch");
            string hash = HashText(AuditGates.Module(catalog.Entries()[method]));
            Require(report["generatedGateSha256"]?.GetValue<string>() == hash && Workspace.Hash(Path.Combine(directory, "SelectedGate.lean")) == hash, "Stale typed audit module");
        }
        Equal(report["auditedTheorems"], Node(names), "Missing family gate");
        Require(report["axiomAudits"] is JsonObject audits && audits.Select(pair => pair.Key).ToHashSet().SetEquals(names), "Missing family gate");
        HashSet<string> approved = Strings(manifest["approvedAxioms"]).ToHashSet();
        foreach (string name in names)
        {
            string[] axioms = Strings(report["axiomAudits"]![name]);
            Require(axioms.Distinct().Count() == axioms.Length && axioms.All(approved.Contains), "Unapproved family axioms");
        }
        if (safetySpec is not null)
        {
            Require(report["evidenceKind"]?.GetValue<string>() == "arithmetic-and-memory-safety", "Missing or mismatched combined safety evidence");
            Equal(report["safety"], safetySpec, "Missing or mismatched combined safety evidence");
            JsonObject expected = safetySpec["coverage"]!.DeepClone().AsObject(); expected["aggregateChecked"] = false; expected["representative"] = profile;
            Equal(report["coverage"], expected, "Missing safety family coverage");
            Require(Catalog.Text(expected["kind"]) is "feature-family" or "all-profiles", "Missing safety family coverage");
            string? hash = safetySpec["generatedAudit"]?.GetValue<bool>() == true ? HashText(SafetyGates.Module(catalog, method, profile)) : null;
            Require(report["generatedSafetyGateSha256"]?.GetValue<string>() == hash
                && (hash is null || Workspace.Hash(Path.Combine(directory, "SelectedSafetyGate.lean")) == hash), "Stale typed safety audit module");
        }
        JsonNode? coverage = report[safety ? "arithmeticCoverage" : "coverage"];
        if (legacy) Require(coverage?["kind"]?.GetValue<string>() == "feature-family" && coverage?["representative"]?.GetValue<string>() == profile, "Missing family coverage");
        else Equal(coverage, new JsonObject { ["kind"] = manifest["verification"]!["profileCoverage"]!.DeepClone(), ["aggregateChecked"] = false, ["representative"] = profile,
            ["condition"] = manifest["verification"]!["allProfiles"]?.GetValue<bool>() == true ? "Every valid profile; kernel-checked independence of actual program operations"
                : "Valid profile agreeing on actual program feature queries and operation availability" }, "Missing conditional program coverage");
        JsonObject certificate = new()
        {
            ["method"] = method, ["representative"] = profile, ["report"] = Workspace.Relative(workspace.Root, path), ["reportSha256"] = Workspace.Hash(path),
            ["assemblySha256"] = artifact["sha256"]!.DeepClone(), ["generatedProgramSha256"] = report["generatedProgramSha256"]!.DeepClone(),
            ["axiomAudits"] = report["axiomAudits"]!.DeepClone(), ["timings"] = report["timings"]?.DeepClone()
        };
        if (legacy)
        {
            certificate["familyTheorem"] = names[1]; certificate["compositionCertificate"] = names[2]; certificate["representativeTheorem"] = names[3];
        }
        else
        {
            certificate["contract"] = manifest["verification"]!["contract"]!.DeepClone();
            certificate["allProfilesTheorem"] = manifest["verification"]!["allProfilesTheorem"]?.DeepClone();
            certificate["familyCoverage"] = manifest["verification"]!["familyCoverage"]?.DeepClone();
            certificate["auditedTheorems"] = Node(names);
        }
        if (safetySpec is not null) { certificate["evidenceKind"] = "arithmetic-and-memory-safety"; certificate["safety"] = safetySpec; }
        return certificate;
    }

    internal (Dictionary<string, string[]> Audits, string Lean) Compose(IReadOnlyDictionary<string, string> inputs, bool operations)
    {
        string lean = workspace.Run(["lake", "env", "lean", "--version"], workspace.Verification).Trim();
        if (!Regex.IsMatch(lean, @"version 4\.34\.1\b")) throw new InvalidOperationException($"Unexpected composition Lean toolchain: {lean}");
        string[] approved = Strings(workspace.Catalog.Manifest("Add")["approvedAxioms"]);
        if (!approved.ToHashSet().SetEquals(Strings(workspace.Catalog.Manifest("Subtract")["approvedAxioms"])))
            throw new InvalidOperationException("Method axiom approvals differ");
        using ProofSession proof = new(workspace);
        string[] paths = proof.Prepare(inputs);
        string[] targets = operations ? ["+UInt256.FeatureCoverage:olean", "+UInt256.OperationCoverage:olean", "+UInt256.MultiplyCoverage:olean"] : ["+UInt256.FeatureCoverage:olean"];
        string[] names = operations ? [.. Theorems, .. OperationTheorems] : Theorems;
        string output = workspace.Run(["lake", "build", .. targets], proof.Directory, "Coverage checking");
        Dictionary<string, string[]> audits = ProofAudits.Check(output, names, approved);
        Workspace.CheckProofSnapshot(proof.Directory, paths, inputs);
        if (!Workspace.SameInputs(inputs, workspace.Inputs())) throw new InvalidOperationException("Inputs changed during coverage checking");
        return (audits, lean);
    }

    internal void VerifyProfiles(IEnumerable<(string Method, string Profile)> plan, ArtifactBundle bundle, int jobs, bool safety)
    {
        if (jobs < 1) throw new ArgumentException("jobs must be positive");
        ConcurrentQueue<(string Method, string Profile)> selections = new(plan);
        int failed = 0;
        void Worker()
        {
            using ProofSession session = new(workspace);
            while (Volatile.Read(ref failed) == 0 && selections.TryDequeue(out var selection))
            {
                try { new Verifier(workspace).Verify(new(selection.Method, selection.Profile, safety), bundle, session); }
                catch { Interlocked.Exchange(ref failed, 1); throw; }
            }
        }
        if (jobs == 1) Worker();
        else Task.WhenAll(Enumerable.Range(0, Math.Min(jobs, selections.Count)).Select(_ => Task.Run(Worker))).GetAwaiter().GetResult();
    }

    internal JsonObject Run(CoverageOptions options)
    {
        if (options.Jobs < 1) throw new ArgumentException("jobs must be positive");
        if (options.PrintPlan && options.CheckReports) throw new ArgumentException("--print-plan cannot compose reports");
        string[] methods = options.Expanded ? workspace.Catalog.MethodNames : options.Method is null ? Catalog.Legacy : [options.Method];
        if (options.PrintPlan)
        {
            JsonObject selected = workspace.Catalog.Plan(methods, options.Safety);
            Console.WriteLine(selected.ToJsonString());
            return selected;
        }
        string destination = options.Method is null ? Path.Combine(workspace.Verification, "generated/coverage.json")
            : Path.Combine(new Verifier(workspace).OutputDirectory(options.Method), "coverage.json");
        if (options.Safety) destination = Path.Combine(Path.GetDirectoryName(destination)!, "safety/coverage.json");
        if (Directory.Exists(Path.GetDirectoryName(destination))) File.Delete(destination);
        var plan = workspace.Catalog.Plan(methods, options.Safety)["include"]!.AsArray()
            .Select(job => (Method: Catalog.Text(job!["method"]), Profile: Catalog.Text(job["profile"]))).ToArray();
        Stopwatch timer = Stopwatch.StartNew();
        Dictionary<string, string> inputs = workspace.Inputs();
        Dictionary<string, double>? buildTimings = null;
        if (!options.CheckReports)
        {
            string work = Directory.CreateTempSubdirectory("int256-all-artifact-").FullName;
            try
            {
                ArtifactBundle bundle = workspace.BuildArtifact(workspace.ProductionProject, work, "Add");
                buildTimings = bundle.Timings;
                VerifyProfiles(plan, bundle, options.Jobs, options.Safety);
            }
            finally { Directory.Delete(work, recursive: true); }
        }
        JsonArray Certificates() => new(plan.Select(job => (JsonNode?)Certificate(job.Method, job.Profile, inputs, options.Safety)).ToArray());
        JsonArray certificates = Certificates();
        var composition = Compose(inputs, options.Safety || methods.Any(method => !Catalog.Legacy.Contains(method)));
        if (!Workspace.SameInputs(inputs, workspace.Inputs()) || !JsonNode.DeepEquals(certificates, Certificates()))
            throw new InvalidOperationException("Certificates changed during composition");
        JsonObject report = new()
        {
            ["status"] = "verified", ["evidenceKind"] = options.Safety ? "arithmetic-and-memory-safety" : "arithmetic", ["coverage"] = "all valid FeatureProfile configurations",
            ["nativeLimitations"] = workspace.Catalog.NativeLimitations(methods), ["methods"] = Node(methods), ["selectedApiCoverage"] = options.Expanded,
            ["domain"] = "CIL.FeatureProfile.Valid", ["sourceInputs"] = Node(inputs), ["semanticsVersion"] = Verifier.SemanticsVersion,
            ["compositionToolchain"] = composition.Lean, ["composition"] = "Audited universal or full family gates plus kernel-checked total classification and composition rules",
            ["auditedTheorems"] = Node(composition.Audits.Keys), ["axiomAudits"] = Node(composition.Audits), ["certificates"] = certificates,
            ["sharedBuildTimings"] = buildTimings is null ? null : Node(buildTimings), ["proofJobs"] = options.CheckReports ? null : options.Jobs, ["totalSeconds"] = timer.Elapsed.TotalSeconds
        };
        Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
        File.WriteAllText(destination + ".tmp", report.ToJsonString(new JsonSerializerOptions { WriteIndented = true }) + "\n");
        File.Move(destination + ".tmp", destination, overwrite: true);
        Console.WriteLine($"Verified total profile coverage for {methods.Length} methods from {certificates.Count} certificates");
        return report;
    }
}

internal sealed record CoverageOptions(string? Method = null, bool Expanded = false, bool Safety = false, bool CheckReports = false, int Jobs = 1, bool PrintPlan = false)
{
    internal static CoverageOptions Parse(IReadOnlyList<string> arguments)
    {
        CoverageOptions options = new();
        HashSet<string> seen = [];
        for (int i = 0; i < arguments.Count; i++)
        {
            string flag = arguments[i];
            if (!seen.Add(flag)) throw new ArgumentException($"Repeated option: {flag}");
            string Value() => ++i < arguments.Count ? arguments[i] : throw new ArgumentException($"Missing value for {flag}");
            int Jobs() => int.TryParse(Value(), System.Globalization.NumberStyles.Integer, System.Globalization.CultureInfo.InvariantCulture, out int jobs)
                ? jobs : throw new ArgumentException("jobs must be an integer");
            options = flag switch
            {
                "--method" => options with { Method = Value() }, "--jobs" => options with { Jobs = Jobs() },
                "--expanded" => options with { Expanded = true }, "--safety" => options with { Safety = true }, "--check-reports" => options with { CheckReports = true },
                "--print-plan" => options with { PrintPlan = true },
                _ => throw new ArgumentException($"Unknown coverage option: {flag}")
            };
        }
        if (options.Jobs < 1) throw new ArgumentException("jobs must be positive");
        if (options.Expanded && options.Method is not null) throw new ArgumentException("Choose one method or expanded coverage");
        if (options.PrintPlan && options.CheckReports) throw new ArgumentException("--print-plan cannot compose reports");
        return options;
    }
}
