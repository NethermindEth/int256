// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System.Text.Json.Nodes;

namespace UInt256Verification;

internal static class ChangeDetection
{
    internal static bool ProofInputsChanged(IEnumerable<string> paths) => paths.Any(path => !(path.StartsWith("src/", StringComparison.Ordinal) && path.EndsWith(".cs", StringComparison.Ordinal)));

    private static void Validate(Catalog catalog, string method, string profile)
    {
        if (!catalog.MethodNames.Contains(method)) throw new ArgumentException("Unknown verification method");
        if (!catalog.ProfileNames.Contains(profile) || Catalog.Legacy.Contains(method) && !Catalog.Profiles.Contains(profile)) throw new ArgumentException("Unknown execution profile");
    }

    internal static (bool Required, string Reason) NeedsProof(Workspace workspace, string baseline, string method = "Add", string profile = "scalar",
        Func<string, string, string, bool>? evidence = null,
        Func<string, string, string, string, string, (JsonObject Artifact, byte[] Program)>? extract = null)
    {
        Validate(workspace.Catalog, method, profile);
        JsonObject manifest = workspace.Catalog.Manifest(method);
        if (string.IsNullOrEmpty(baseline) || baseline.All(c => c == '0')) return (true, "No comparison baseline; verifying production");
        string[] paths = workspace.Run(["git", "diff", "--no-renames", "--name-only", "-z", baseline, "HEAD"], workspace.Root).Split('\0', StringSplitOptions.RemoveEmptyEntries);
        if (ProofInputsChanged(paths)) return (true, "Verification or build inputs changed");
        bool verified = evidence is null ? BaselineEvidence.Check(baseline, method, profile, Environment.GetEnvironmentVariable("GITHUB_REPOSITORY") ?? "") : evidence(baseline, method, profile);
        if (!verified) return (true, $"No successful baseline proof evidence for {method}/{profile}; verifying production");
        if (paths.Length == 0) return (false, "No source changes; exact baseline proof passed");
        if (workspace.Run(["dotnet", "--version"], workspace.Root).Trim() != Catalog.Text(manifest["sdk"])) throw new InvalidOperationException("Unexpected .NET SDK for change detection");
        string work = Path.Combine(Path.GetTempPath(), "int256-changes-" + Guid.NewGuid().ToString("N"));
        Directory.CreateDirectory(work);
        try
        {
            string tools = Path.Combine(work, "tools"), beforeSource = Path.Combine(work, "baseline");
            workspace.Run(["dotnet", "build", Path.Combine(workspace.Verification, "Extractor/Extractor.csproj"), "-c", "Release", "--no-incremental", $"-p:ArtifactsPath={tools}",
                "-p:EnforceCodeStyleInBuild=true", "-p:GenerateDocumentationFile=true"], workspace.Root);
            workspace.Run(["git", "clone", "--shared", "--no-checkout", "--quiet", workspace.Root, beforeSource], workspace.Root);
            workspace.Run(["git", "checkout", "--detach", baseline], beforeSource);
            string extractor = Path.Combine(tools, "bin/Extractor/release/Extractor.dll");
            extract ??= (source, destination, tool, selectedMethod, selectedProfile) => Extract(workspace, source, destination, tool, selectedMethod, selectedProfile);
            var before = extract(beforeSource, Path.Combine(work, "before"), extractor, method, profile);
            var after = extract(workspace.Root, Path.Combine(work, "after"), extractor, method, profile);
            bool same = JsonNode.DeepEquals(before.Artifact, after.Artifact) && before.Program.SequenceEqual(after.Program);
            return same ? (false, $"Extracted {method}/{profile}, dependencies, layout and static data are unchanged")
                : (true, $"Extracted {method}/{profile}, dependencies, layout or static data changed");
        }
        finally { Directory.Delete(work, recursive: true); }
    }

    internal static void Run(Workspace workspace, string[] arguments, Func<string, string?>? environment = null,
        Func<string, string, string, (bool Required, string Reason)>? decide = null)
    {
        string method = "Add", profile = "scalar";
        for (int i = 0; i < arguments.Length; i++)
        {
            if (i + 1 == arguments.Length) throw new ArgumentException("Missing change-selection option value");
            switch (arguments[i])
            {
                case "--method": method = arguments[++i]; break;
                case "--profile": profile = arguments[++i]; break;
                default: throw new ArgumentException("Unknown change-selection option");
            }
        }
        Validate(workspace.Catalog, method, profile);
        environment ??= Environment.GetEnvironmentVariable;
        (bool Required, string Reason) decision = environment("VERIFY_EVENT") == "workflow_dispatch" ? (true, "Manual production verification requested")
            : environment("VERIFY_EVENT") == "pull_request" && environment("VERIFY_BASE_BRANCH") != "main" ? (true, "PR baseline is outside the verified main branch")
            : decide is null ? NeedsProof(workspace, environment("VERIFY_BASE") ?? "", method, profile) : decide(environment("VERIFY_BASE") ?? "", method, profile);
        Console.WriteLine(decision.Reason);
        if (environment("GITHUB_OUTPUT") is string output && output.Length != 0) File.AppendAllText(output, $"required={decision.Required.ToString().ToLowerInvariant()}\n");
        if (environment("GITHUB_STEP_SUMMARY") is string summary && summary.Length != 0) File.AppendAllText(summary, $"Production proof {(decision.Required ? "required" : "skipped")}: {decision.Reason}.\n");
    }

    internal static JsonObject ComparisonArtifact(JsonObject artifact)
    {
        JsonObject result = artifact.DeepClone().AsObject();
        result.Remove("sha256");
        result.Remove("assembly");
        foreach (JsonNode? method in result["methods"]!.AsArray()) method!.AsObject().Remove("token");
        return result;
    }

    internal static (JsonObject Artifact, byte[] Program) Extract(Workspace workspace, string source, string work, string extractor, string method, string profile)
    {
        JsonObject manifest = workspace.Catalog.Manifest(method), expectedProfile = workspace.Catalog.Profile(profile);
        if (Catalog.Legacy.Contains(method) && !Catalog.Profiles.Contains(profile)) throw new ArgumentException("Unknown execution profile for legacy selection");
        string artifacts = Path.Combine(work, "artifacts"), output = Path.Combine(work, "generated");
        workspace.Run(["dotnet", "build", Path.Combine(source, "src/Nethermind.Int256/Nethermind.Int256.csproj"), "-c", "Release", "--no-incremental",
            $"-p:ArtifactsPath={artifacts}", "-p:EnableZkEvm=false"], source);
        string profileSelector = Catalog.Profiles.Contains(profile) ? profile : "@" + Path.Combine(workspace.Verification, $"manifests/profiles/{profile}.json");
        string[] selection = Catalog.Legacy.Contains(method) ? [method, profile] : [Catalog.Text(manifest["entry"]), profileSelector, Path.Combine(workspace.Verification, "manifests/api-coverage.json")];
        workspace.Run(["dotnet", extractor, Path.Combine(artifacts, "bin/Nethermind.Int256/release/Nethermind.Int256.dll"), output, .. selection], source);
        JsonObject artifact = JsonNode.Parse(File.ReadAllText(Path.Combine(output, "artifact.json")))!.AsObject();
        if (!JsonNode.DeepEquals(artifact["profile"], expectedProfile)) throw new InvalidOperationException("Change-detection extraction profile mismatch");
        JsonObject entry = artifact["methods"]![artifact["entryIndex"]!.GetValue<int>()]!.AsObject();
        if (Catalog.Text(entry["signature"]) != Catalog.Text(manifest["entry"])) throw new InvalidOperationException("Change-detection extraction method mismatch");
        if (!Catalog.Legacy.Contains(method)) Catalog.CheckCallingConvention(entry, manifest["callingConvention"]!.AsObject());
        return (ComparisonArtifact(artifact), File.ReadAllBytes(Path.Combine(output, "Extracted.lean")));
    }
}
