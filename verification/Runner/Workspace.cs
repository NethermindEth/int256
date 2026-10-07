// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System.Diagnostics;
using System.Security.Cryptography;
using System.Text;
using System.Text.Json.Nodes;

namespace UInt256Verification;

internal sealed class Workspace(string root, Func<string[], string, string, string>? run = null)
{
    internal static readonly HashSet<string> BuildDirectories = ["artifacts", "bin", "obj", "generated", ".lake", ".vs", "__pycache__"];
    internal string Root { get; } = Path.GetFullPath(root);
    internal string Verification => Path.Combine(Root, "verification");
    internal Catalog Catalog => new(Verification);
    internal string ProductionProject => Path.GetFullPath(Path.Combine(Root, "src/Nethermind.Int256/Nethermind.Int256.csproj"));
    internal string Run(string[] command, string cwd, string stage = "Command") => (run ?? RunProcess)(command, cwd, stage);

    internal static string Hash(string path)
    {
        using FileStream stream = File.OpenRead(path);
        return Convert.ToHexStringLower(SHA256.HashData(stream));
    }

    internal static IEnumerable<string> SourceFiles(string directory, HashSet<string> suffixes)
    {
        if (!Directory.Exists(directory)) yield break;
        foreach (string file in Directory.EnumerateFiles(directory))
            if (suffixes.Contains(Path.GetExtension(file))) yield return file;
        foreach (string child in Directory.EnumerateDirectories(directory))
            if (!BuildDirectories.Contains(Path.GetFileName(child)))
                foreach (string file in SourceFiles(child, suffixes)) yield return file;
    }

    internal static string Relative(string rootDirectory, string path) => Path.GetRelativePath(rootDirectory, path).Replace('\\', '/');

    internal string CopyRegressionSource(string destination)
    {
        destination = Path.GetFullPath(destination);
        foreach (string directory in new[] { "src", "verification" })
        {
            string source = Path.Combine(Root, directory), target = Path.Combine(destination, directory);
            string relative = Relative(source, destination);
            if (relative == "." || !relative.StartsWith("../", StringComparison.Ordinal) && !Path.IsPathRooted(relative)
                || Directory.Exists(target) || File.Exists(target))
                throw new ArgumentException("Regression destination must have fresh source directories outside the copied trees");
        }
        var inputs = Inputs();
        void CopyTree(string source, string target, bool sourceTree)
        {
            Directory.CreateDirectory(target);
            foreach (string path in Directory.EnumerateFileSystemEntries(source))
            {
                string name = Path.GetFileName(path);
                if (BuildDirectories.Contains(name) || sourceTree && name == "TestResults") continue;
                if (Directory.Exists(path)) CopyTree(path, Path.Combine(target, name), sourceTree);
                else File.Copy(path, Path.Combine(target, name));
            }
        }
        CopyTree(Path.Combine(Root, "src"), Path.Combine(destination, "src"), true);
        CopyTree(Verification, Path.Combine(destination, "verification"), false);
        foreach (string path in Directory.EnumerateFiles(Root).Where(path => Path.GetFileName(path) is "global.json" or "README.md" or ".editorconfig"
            || Path.GetExtension(path).ToLowerInvariant() is ".props" or ".targets" or ".config"))
            File.Copy(path, Path.Combine(destination, Path.GetFileName(path)), overwrite: true);
        string workflows = Path.Combine(destination, ".github/workflows");
        Directory.CreateDirectory(workflows);
        foreach (string path in Directory.EnumerateFiles(Path.Combine(Root, ".github/workflows"), "verify-uint256*.yml"))
            File.Copy(path, Path.Combine(workflows, Path.GetFileName(path)), overwrite: true);
        if (!SameInputs(inputs, Inputs()) || !SameInputs(inputs, new Workspace(destination).Inputs()))
            throw new InvalidOperationException("Regression source snapshot changed");
        return Path.Combine(destination, "verification");
    }

    internal Dictionary<string, string> Inputs()
    {
        HashSet<string> paths = [Path.Combine(Root, "global.json"), Path.Combine(Root, ".editorconfig"), Path.Combine(Verification, "lean-toolchain")];
        paths.UnionWith(Directory.EnumerateFiles(Root).Where(path => Path.GetExtension(path).ToLowerInvariant() is ".props" or ".targets" or ".config"));
        string workflows = Path.Combine(Root, ".github/workflows");
        if (Directory.Exists(workflows)) paths.UnionWith(Directory.EnumerateFiles(workflows, "verify-uint256*.yml"));
        foreach (string directory in new[] { Path.Combine(Root, "src"), Verification })
            paths.UnionWith(SourceFiles(directory, [".cs", ".csproj", ".props", ".targets", ".lean", ".in", ".json", ".toml", ".py"]));
        return paths.Order(StringComparer.Ordinal).ToDictionary(path => Relative(Root, path), Hash, StringComparer.Ordinal);
    }

    internal static bool SameInputs(IReadOnlyDictionary<string, string> left, IReadOnlyDictionary<string, string> right) =>
        left.Count == right.Count && left.All(pair => right.TryGetValue(pair.Key, out string? hash) && hash == pair.Value);

    internal static Dictionary<string, string> CheckProofSnapshot(string proof, IEnumerable<string> paths, IReadOnlyDictionary<string, string> inputs)
    {
        Dictionary<string, string> hashes = [];
        foreach (string path in paths)
        {
            string relative = path.Replace('\\', '/');
            string hash = Hash(Path.Combine(proof, path));
            if (!inputs.TryGetValue("verification/" + relative, out string? expected) || hash != expected)
                throw new InvalidOperationException("Proof snapshot does not match captured source inputs");
            hashes.Add(relative, hash);
        }
        return hashes;
    }

    internal string[] CopyProofSources(string proof, IReadOnlyDictionary<string, string> inputs)
    {
        string[] paths = [.. SourceFiles(Verification, [".lean"]).Select(path => Relative(Verification, path)).Order(StringComparer.Ordinal), "lakefile.toml", "lean-toolchain"];
        foreach (string path in paths)
        {
            string target = Path.Combine(proof, path);
            Directory.CreateDirectory(Path.GetDirectoryName(target)!);
            File.Copy(Path.Combine(Verification, path), target, overwrite: true);
        }
        CheckProofSnapshot(proof, paths, inputs);
        return paths;
    }

    internal ArtifactBundle BuildArtifact(string project, string work, string method, string? fixture = null, bool registeredFixture = false, string? fixtureName = null)
    {
        Dictionary<string, string> inputs = Inputs();
        Dictionary<string, double> timings = [];
        string artifacts = Path.Combine(work, "artifacts");
        List<string> build = ["dotnet", "build", project, "-c", "Release", "--no-incremental", $"-p:ArtifactsPath={artifacts}", "-p:EnableZkEvm=false"];
        if (fixture is not null)
        {
            build.AddRange([$"-p:FixtureMethod={method}", "-p:EnforceCodeStyleInBuild=true", "-p:GenerateDocumentationFile=true",
                registeredFixture ? $"-p:FixtureCase={fixtureName}" : $"-p:FixtureSource={fixture}"]);
        }
        Stopwatch timer = Stopwatch.StartNew();
        Run([.. build], Root, fixture is null ? "Production build" : "Fixture maintenance/build");
        timings["assemblyBuildSeconds"] = timer.Elapsed.TotalSeconds;
        string assembly = Path.Combine(artifacts, "bin/Nethermind.Int256/release/Nethermind.Int256.dll");
        if (!File.Exists(assembly)) throw new InvalidOperationException("Fresh build did not produce the selected assembly");
        string tools = Path.Combine(work, "tools");
        timer.Restart();
        Run(["dotnet", "build", Path.Combine(Verification, "Extractor/Extractor.csproj"), "-c", "Release", "--no-incremental",
            $"-p:ArtifactsPath={tools}", "-p:EnforceCodeStyleInBuild=true", "-p:GenerateDocumentationFile=true"], Root);
        timings["extractorBuildSeconds"] = timer.Elapsed.TotalSeconds;
        string extractor = Path.Combine(tools, "bin/Extractor/release/Extractor.dll");
        if (!SameInputs(inputs, Inputs())) throw new InvalidOperationException("Inputs changed during artifact build");
        return new(assembly, extractor, timings, inputs, Hash(assembly), Hash(extractor), Path.GetFullPath(project), fixture is null ? null : fixtureName);
    }

    internal void ValidateBundle(ArtifactBundle bundle, IReadOnlyDictionary<string, string> inputs, bool production = false)
    {
        if (!SameInputs(bundle.SourceInputs, inputs) || !SameInputs(inputs, Inputs()))
            throw new InvalidOperationException("Shared artifact build has stale source inputs");
        if (Hash(bundle.Assembly) != bundle.AssemblySha256 || Hash(bundle.Extractor) != bundle.ExtractorSha256)
            throw new InvalidOperationException("Artifact build identity changed");
        if (production && (bundle.Project != ProductionProject || bundle.Fixture is not null))
            throw new InvalidOperationException("A shared production build cannot verify fixtures");
    }

    internal JsonObject Extract(ArtifactBundle bundle, string generated, string method, string profile)
    {
        ValidateBundle(bundle, bundle.SourceInputs);
        JsonObject manifest = Catalog.Manifest(method);
        JsonObject expectedProfile = Catalog.Profile(profile);
        if (Catalog.Legacy.Contains(method) && !Catalog.Profiles.Contains(profile))
            throw new InvalidOperationException("Additional profiles require an exact API profile-agreement audit gate");
        string[] selection = Catalog.Legacy.Contains(method) ? [method, profile]
            : [Catalog.Text(manifest["entry"]), Catalog.Profiles.Contains(profile) ? profile : "@" + Path.Combine(Verification, $"manifests/profiles/{profile}.json"),
                Path.Combine(Verification, "manifests/api-coverage.json")];
        Run(["dotnet", bundle.Extractor, bundle.Assembly, generated, .. selection], Root, "Extraction");
        JsonObject artifact = JsonNode.Parse(File.ReadAllText(Path.Combine(generated, "artifact.json")))!.AsObject();
        JsonObject entry = artifact["methods"]![artifact["entryIndex"]!.GetValue<int>()]!.AsObject();
        if (Catalog.Text(artifact["sha256"]) != Hash(bundle.Assembly) || Catalog.Text(entry["signature"]) != Catalog.Text(manifest["entry"]))
            throw new InvalidOperationException("Artifact identity mismatch");
        if (!Catalog.Legacy.Contains(method)) Catalog.CheckCallingConvention(entry, manifest["callingConvention"]!.AsObject());
        if (!JsonNode.DeepEquals(artifact["profile"], expectedProfile))
            throw new InvalidOperationException("Extracted feature profile does not match the requested profile");
        ValidateBundle(bundle, bundle.SourceInputs);
        return artifact;
    }

    internal string RunRejected(string[] command, string cwd, string stage) => RunProcess(command, cwd, stage, false);

    private static string RunProcess(string[] command, string cwd, string stage) => RunProcess(command, cwd, stage, true);

    private static string RunProcess(string[] command, string cwd, string stage, bool succeeds)
    {
        ProcessStartInfo start = new(command[0])
        {
            WorkingDirectory = cwd, UseShellExecute = false, CreateNoWindow = true,
            RedirectStandardOutput = true, RedirectStandardError = true,
            StandardOutputEncoding = Encoding.UTF8, StandardErrorEncoding = Encoding.UTF8
        };
        foreach (string argument in command.Skip(1)) start.ArgumentList.Add(argument);
        start.Environment["DOTNET_EnableHWIntrinsic"] = "0";
        start.Environment["DOTNET_CLI_TELEMETRY_OPTOUT"] = "1";
        start.Environment["DOTNET_SKIP_FIRST_TIME_EXPERIENCE"] = "1";
        start.Environment["MSBuildEnableWorkloadResolver"] = "false";
        using Process process = Process.Start(start) ?? throw new InvalidOperationException($"Cannot start {command[0]}");
        Task<string> stdout = process.StandardOutput.ReadToEndAsync(), stderr = process.StandardError.ReadToEndAsync();
        process.WaitForExit();
        string output = stdout.GetAwaiter().GetResult() + stderr.GetAwaiter().GetResult();
        Console.Error.Write(output);
        if ((process.ExitCode == 0) != succeeds) throw new InvalidOperationException($"{stage} failure: Unexpected exit {process.ExitCode}: {string.Join(' ', command)}");
        return output;
    }
}

internal sealed record ArtifactBundle(string Assembly, string Extractor, Dictionary<string, double> Timings,
    Dictionary<string, string> SourceInputs, string AssemblySha256, string ExtractorSha256, string Project, string? Fixture);
