#!/usr/bin/env dotnet
// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT
#:property PublishAot=false
#:include RegressionBatch.cs
#:include RegressionManifest.cs

using System.Diagnostics;
using System.Text.Json.Nodes;

string root = Path.GetFullPath(args.Length > 0 ? args[0] : "verification");
string profile = args.Length > 1 ? args[1] : "scalar";
string[] profiles = RegressionManifest.RequireProfiles(root, "ShiftRegression.cs", ["scalar", "x64-vector256"]);
if (args.Length > 2 || !profiles.Contains(profile))
    throw new ArgumentException("Usage: ShiftRegression.cs [verification-directory] [scalar|x64-vector256]");
string fixtures = Path.Combine(root, "Tests/Fixtures/Shift");
string work = Path.Combine(root, "artifacts/shift-regressions", profile);
string tool = Path.Combine(root, ".lake/packages/leancil/Extractor/bin/Nethermind.LeanCIL.dll");
string profileArgument = profile == "scalar" ? profile : "@" + Path.Combine(root, "manifests/profiles", profile + ".json");
JsonObject witnesses = JsonNode.Parse(File.ReadAllText(Path.Combine(fixtures, "Witnesses.json")))!["negativeCases"]!.AsObject();
JsonArray targets = JsonNode.Parse(File.ReadAllText(Path.Combine(root, "manifests/targets.json")))!["methods"]!.AsArray();
string[] methods = ["Lsh", "Rsh", "LeftShift", "RightShift", "OperatorLsh", "OperatorRsh"];

async Task<string> Run(string executable, IEnumerable<string> arguments)
{
    ProcessStartInfo start = new(executable) { WorkingDirectory = root, RedirectStandardOutput = true, RedirectStandardError = true, UseShellExecute = false };
    foreach (string argument in arguments) start.ArgumentList.Add(argument);
    using Process process = Process.Start(start) ?? throw new InvalidOperationException("Cannot start " + executable);
    Task<string> stdout = process.StandardOutput.ReadToEndAsync(), stderr = process.StandardError.ReadToEndAsync();
    await process.WaitForExitAsync();
    string output = await stdout + await stderr;
    if (process.ExitCode != 0) throw new InvalidOperationException(output);
    return output;
}

string consumer = Path.Combine(work, "consumer");
Directory.CreateDirectory(consumer);
void CopySources(string source, string destination)
{
    Directory.CreateDirectory(destination);
    foreach (string file in Directory.EnumerateFiles(source))
    {
        string name = Path.GetFileName(file);
        if (name == "lean-toolchain" || Path.GetExtension(file) is ".lean" or ".json" or ".toml")
            File.Copy(file, Path.Combine(destination, name), overwrite: true);
    }
    foreach (string directory in Directory.EnumerateDirectories(source))
    {
        string name = Path.GetFileName(directory);
        if (name is "artifacts" or ".lake" or ".git" or "bin" or "obj") continue;
        CopySources(directory, Path.Combine(destination, name));
    }
}
CopySources(root, consumer);
JsonArray dependencies = JsonNode.Parse(File.ReadAllText(Path.Combine(root, "lake-manifest.json")))!["packages"]!.AsArray();
foreach (JsonNode? package in dependencies)
{
    string name = package!["name"]!.GetValue<string>();
    string dependency = Path.Combine(consumer, ".lake", "packages", name);
    await DropStaleClone(dependency, package["rev"]!.GetValue<string>());
    if (!Directory.Exists(dependency))
        await Run("git", ["clone", "--no-hardlinks", "--no-checkout", Path.Combine(root, ".lake", "packages", name), dependency]);
    await Run("git", ["-C", dependency, "checkout", "--detach", package["rev"]!.GetValue<string>()]);
}
List<(string Method, string Mutation, string Extraction, string Proof)> checks = [];
foreach (var pair in witnesses)
{
    string mutation = pair.Key;
    JsonObject witness = pair.Value!.AsObject();
    string build = Path.Combine(work, "build", mutation);
    string output = await Run("dotnet", ["build", Path.Combine(fixtures, "Nethermind.Int256.csproj"), "-c", "Release",
        "-p:FixtureCase=" + mutation, "-p:BaseOutputPath=" + Path.Combine(build, "bin") + Path.DirectorySeparatorChar,
        "-p:BaseIntermediateOutputPath=" + Path.Combine(build, "obj") + Path.DirectorySeparatorChar,
        "-p:EnforceCodeStyleInBuild=true", "-p:GenerateDocumentationFile=true", "-v:q"]);
    if (output.Contains("IDE0005", StringComparison.Ordinal)) throw new InvalidOperationException(output);
    string assembly = Path.Combine(build, "bin/Release/net10.0/Nethermind.Int256.dll");
    foreach (string method in methods)
    {
        bool returned = method.StartsWith("Operator", StringComparison.Ordinal);
        string direction = method is "Lsh" or "LeftShift" or "OperatorLsh" ? "left" : "right";
        if (witness["direction"]!.GetValue<string>() != direction || returned && witness["operatorActual"] is null) continue;
        string extraction = Path.Combine(work, mutation, method);
        string signature = targets.Single(target => target!["id"]!.GetValue<string>() == method)!["signature"]!.GetValue<string>();
        await Run("dotnet", [tool, "extract", assembly, signature, extraction, profileArgument]);
        string template = File.ReadAllText(Path.Combine(fixtures, returned ? "CheckedOperatorRefutationTemplate.lean.in" : "CheckedRefutationTemplate.lean.in"));
        string initialOffset = witness["initialBytes"]!.AsObject().Single().Key;
        string actual = witness["operatorActual"]?.ToString() ?? "0";
        template = template.Replace("@INITIAL_OFFSET@", initialOffset).Replace("@OUTPUT@", witness["outputBase"]!.ToString())
            .Replace("@COUNT@", witness["count"]!.ToString()).Replace("@ACTUAL@", actual).Replace("@DIRECTION@", direction);
        string proof = Path.Combine(consumer, "proofs", $"Regression{mutation}{method}.lean");
        File.WriteAllText(proof, template);
        checks.Add((method, mutation, extraction, proof));
    }
}
string suffix = profile == "scalar" ? "Scalar" : "Vector";
List<string> failed = await RegressionBatch.Verify(root, tool, work, consumer, [.. checks.Select(check => new RegressionCheck($"{check.Method}/{profile}/{check.Mutation}",
    check.Extraction, check.Proof, "ShiftWitness.refuted", "checked full-contract refutation and public proof rejection",
    Path.Combine(consumer, "proofs", check.Method + suffix + ".lean"), "UInt256Proof." + check.Method + "." + suffix.ToLowerInvariant() + "_correctness"))]);
if (failed.Count != 0) throw new InvalidOperationException("FAILED: " + string.Join(", ", failed));

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
