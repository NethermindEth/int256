#!/usr/bin/env dotnet
// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT
#:property PublishAot=false
#:include RegressionBatch.cs

using System.Diagnostics;
using System.Text.Json.Nodes;

if (args.Length > 2) throw new ArgumentException("Usage: ShiftPositiveRegression.cs [verification-directory] [all|scalar|x64-vector256]");
string root = Path.GetFullPath(args.Length > 0 ? args[0] : "verification");
string selection = args.Length > 1 ? args[1] : "all";
string[] profiles = selection switch
{
    "all" => ["scalar", "x64-vector256"],
    "scalar" or "x64-vector256" => [selection],
    _ => throw new ArgumentException("Unknown profile: " + selection),
};
string fixtures = Path.Combine(root, "Tests/Fixtures/Shift");
string work = Path.Combine(root, "artifacts/shift-positive-regressions");
string consumer = Path.Combine(work, "consumer");
string tool = Path.Combine(root, ".lake/packages/leancil/Extractor/bin/Nethermind.LeanCIL.dll");
JsonArray targets = JsonNode.Parse(File.ReadAllText(Path.Combine(root, "manifests/targets.json")))!["methods"]!.AsArray();
const string fixture = "LshHelper";
string[] methods = ["Lsh", "LeftShift", "OperatorLsh"];

async Task<string> Run(string executable, IEnumerable<string> arguments)
{
    ProcessStartInfo start = new(executable) { WorkingDirectory = root, RedirectStandardOutput = true, RedirectStandardError = true, UseShellExecute = false };
    foreach (string argument in arguments) start.ArgumentList.Add(argument);
    using Process process = Process.Start(start) ?? throw new InvalidOperationException("Cannot start " + executable);
    Task<string> stdout = process.StandardOutput.ReadToEndAsync(), stderr = process.StandardError.ReadToEndAsync();
    await process.WaitForExitAsync();
    string output = await stdout + await stderr;
    if (process.ExitCode != 0 || output.Contains("IDE0005", StringComparison.Ordinal)) throw new InvalidOperationException(output);
    return output;
}

void CopySources(string source, string destination)
{
    Directory.CreateDirectory(destination);
    foreach (string file in Directory.EnumerateFiles(source))
        if (Path.GetExtension(file) is ".lean" or ".json" or ".toml" || Path.GetFileName(file) == "lean-toolchain")
            File.Copy(file, Path.Combine(destination, Path.GetFileName(file)), true);
    foreach (string directory in Directory.EnumerateDirectories(source))
    {
        string name = Path.GetFileName(directory);
        if (name is ".lake" or ".git" or "artifacts" or "generated" or "bin" or "obj" or ".work") continue;
        if ((File.GetAttributes(directory) & FileAttributes.ReparsePoint) != 0)
            throw new InvalidOperationException("Source snapshot cannot contain links: " + directory);
        CopySources(directory, Path.Combine(destination, name));
    }
}
// Freeze the complete consumer source snapshot before issuing any certificates.
CopySources(root, consumer);
JsonArray packages = JsonNode.Parse(File.ReadAllText(Path.Combine(root, "lake-manifest.json")))!["packages"]!.AsArray();
foreach (JsonNode? package in packages)
{
    string name = package!["name"]!.GetValue<string>();
    string destination = Path.Combine(consumer, ".lake/packages", name);
    await DropStaleClone(destination, package["rev"]!.GetValue<string>());
    if (!Directory.Exists(destination))
    {
        Directory.CreateDirectory(Path.GetDirectoryName(destination)!);
        await Run("git", ["clone", "--no-hardlinks", Path.Combine(root, ".lake/packages", name), destination]);
    }
    await Run("git", ["-C", destination, "checkout", "--detach", package["rev"]!.GetValue<string>()]);
}

Dictionary<string, string> assemblies = [];
foreach (string variant in new[] { "Baseline", fixture })
{
    string build = Path.Combine(work, "build", variant);
    string intermediate = Path.Combine(build, "obj") + Path.DirectorySeparatorChar;
    await Run("dotnet", ["build", Path.Combine(fixtures, "Nethermind.Int256.csproj"), "-c", "Release", "-p:FixtureCase=" + variant,
        "-p:BaseOutputPath=" + Path.Combine(build, "bin") + Path.DirectorySeparatorChar,
        "-p:BaseIntermediateOutputPath=" + intermediate, "-p:MSBuildProjectExtensionsPath=" + intermediate,
        "-p:EnforceCodeStyleInBuild=true", "-p:GenerateDocumentationFile=true", "-v:q"]);
    assemblies[variant] = Path.Combine(build, "bin/Release/net10.0/Nethermind.Int256.dll");
}

async Task<string> Extract(string variant, string method, string profile)
{
    string extraction = Path.Combine(work, profile, variant, method);
    if (Directory.Exists(extraction)) Directory.Delete(extraction, true);
    string signature = targets.Single(target => target!["id"]!.GetValue<string>() == method)!["signature"]!.GetValue<string>();
    string profileArgument = profile == "scalar" ? profile : "@" + Path.Combine(root, "manifests/profiles", profile + ".json");
    await Run("dotnet", [tool, "extract", assemblies[variant], signature, extraction, profileArgument]);
    return extraction;
}

// The assembly digest always differs between builds; only the extracted program text decides equivalence.
static string ProgramText(string extraction) => string.Join('\n', File.ReadAllLines(Path.Combine(extraction, "Extracted.lean"))
    .Where(line => !line.StartsWith("def assemblySha256", StringComparison.Ordinal)));

List<string> failed = [], incomplete = [];
List<RegressionCheck> checks = [];
foreach (string profile in profiles)
foreach (string method in methods)
{
    string name = $"{method}/{profile}/{fixture}";
    string log = Path.Combine(work, profile, $"{method}-{fixture}.log");
    Directory.CreateDirectory(Path.GetDirectoryName(log)!);
    string proof = Path.Combine(consumer, "Tests/Fixtures/Shift", fixture, $"{method}_{profile.Replace('-', '_')}.lean");
    if (!File.Exists(proof))
    {
        Console.WriteLine($"PENDING {name}: no fixture proof");
        incomplete.Add(name);
        continue;
    }
    try
    {
        string extraction = await Extract(fixture, method, profile);
        if (ProgramText(await Extract("Baseline", method, profile)) == ProgramText(extraction))
            throw new InvalidOperationException("Fixture extraction does not differ from Baseline: " + extraction);
        checks.Add(new(name, extraction, proof, "UInt256Proof.Shift.Fixture.correctness", "full positive certificate"));
    }
    catch (InvalidOperationException exception)
    {
        File.WriteAllText(log, exception.Message);
        failed.Add(name);
        Console.WriteLine($"FAIL {name}: see {log}");
    }
}
failed.AddRange(await RegressionBatch.Verify(root, tool, work, consumer, checks));
if (incomplete.Count != 0) Console.WriteLine("INCOMPLETE: " + string.Join(", ", incomplete));
if (failed.Count != 0) Console.WriteLine("FAILED: " + string.Join(", ", failed));
Environment.ExitCode = incomplete.Count == 0 && failed.Count == 0 ? 0 : 1;

// Re-clone when a reused snapshot predates a pin change; the package source is a partial clone and cannot serve fetches.
static async Task DropStaleClone(string repository, string revision)
{
    if (!Directory.Exists(repository)) return;
    ProcessStartInfo start = new("git") { RedirectStandardOutput = true, RedirectStandardError = true, UseShellExecute = false };
    foreach (string argument in new[] { "-C", repository, "cat-file", "-e", revision + "^{commit}" }) start.ArgumentList.Add(argument);
    using Process probe = Process.Start(start) ?? throw new InvalidOperationException("git");
    await Task.WhenAll(probe.StandardOutput.ReadToEndAsync(), probe.StandardError.ReadToEndAsync(), probe.WaitForExitAsync());
    if (probe.ExitCode == 0) return;
    foreach (string file in Directory.EnumerateFiles(repository, "*", SearchOption.AllDirectories)) File.SetAttributes(file, FileAttributes.Normal);
    Directory.Delete(repository, true);
}
