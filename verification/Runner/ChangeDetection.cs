// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System.Text.Json.Nodes;

namespace UInt256Verification;

internal static class ChangeDetection
{
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
