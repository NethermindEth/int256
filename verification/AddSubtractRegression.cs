#!/usr/bin/env dotnet
// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT
#:property PublishAot=false
#:include RegressionBatch.cs
using System.Diagnostics;
using System.Globalization;
using System.Text.Json.Nodes;

if (args.Length > 1) throw new ArgumentException("Usage: AddSubtractRegression.cs [verification-directory]");
string root = Path.GetFullPath(args.Length == 1 ? args[0] : "verification");
string work = Path.Combine(root, "artifacts/add-subtract-regressions");
string consumer = Path.Combine(work, "consumer");
string tool = Path.Combine(root, ".lake/packages/leancil/Extractor/bin/Nethermind.LeanCIL.dll");
JsonArray targets = JsonNode.Parse(File.ReadAllText(Path.Combine(root, "manifests/targets.json")))!["methods"]!.AsArray();
// The production proofs follow the production call graph; structurally different fixtures need their own proof.
HashSet<string> production = ["Baseline", "Renamed", "ReversedStore", "ExpandedHardware"];
List<string> incomplete = [];
(string Method, string Operation, string[] Positives)[] groups =
[
    ("Add", "(· + ·)", ["Baseline", "Renamed", "ExtractedHelper", "ExpandedHardware", "ReversedStore"]),
    ("Subtract", "(· - ·)", ["Baseline", "Renamed", "ExtractedHelper"]),
];

async Task<string> Run(string executable, IEnumerable<string> arguments)
{
    ProcessStartInfo start = new(executable) { WorkingDirectory = root, RedirectStandardOutput = true, RedirectStandardError = true, UseShellExecute = false };
    foreach (string argument in arguments) start.ArgumentList.Add(argument);
    using Process process = Process.Start(start) ?? throw new InvalidOperationException(executable);
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

List<(string Name, string Extraction, string Proof, string Theorem, string? Production)> jobs = [];
foreach (var (method, operation, positives) in groups)
{
    string fixtures = Path.Combine(root, "Tests/Fixtures", method);
    string signature = targets.Single(target => target!["id"]!.GetValue<string>() == method)!["signature"]!.GetValue<string>();
    string productionProof = Path.Combine(consumer, "proofs", method + "Scalar.lean");
    string productionTheorem = $"UInt256Proof.{method}.scalar_correctness";
    JsonArray witnesses = JsonNode.Parse(File.ReadAllText(Path.Combine(fixtures, "witnesses.json")))!.AsArray();
    foreach (string fixture in positives.Concat(witnesses.Select(witness => witness!["case"]!.GetValue<string>())))
    {
        string name = method + "/" + fixture;
        string fixtureProof = Path.Combine(consumer, "Tests/Fixtures", method, fixture + ".lean");
        bool negative = witnesses.Any(value => value!["case"]!.GetValue<string>() == fixture);
        if (!negative && !production.Contains(fixture) && !File.Exists(fixtureProof))
        {
            Console.WriteLine($"PENDING {name}: no fixture proof yet");
            incomplete.Add(name);
            continue;
        }
        string build = Path.Combine(work, "build", method + fixture);
        string intermediate = Path.Combine(build, "obj") + Path.DirectorySeparatorChar;
        await Run("dotnet", ["build", Path.Combine(fixtures, "Nethermind.Int256.csproj"), "-c", "Release", "-p:FixtureCase=" + fixture,
            "-p:BaseOutputPath=" + Path.Combine(build, "bin") + Path.DirectorySeparatorChar,
            "-p:BaseIntermediateOutputPath=" + intermediate, "-p:MSBuildProjectExtensionsPath=" + intermediate,
            "-p:EnforceCodeStyleInBuild=true", "-p:GenerateDocumentationFile=true", "-v:q"]);
        string extraction = Path.Combine(work, method + fixture);
        await Run("dotnet", [tool, "extract", Path.Combine(build, "bin/Release/net10.0/Nethermind.Int256.dll"), signature, extraction, "scalar"]);
        JsonNode? witness = witnesses.SingleOrDefault(value => value!["case"]!.GetValue<string>() == fixture);
        if (witness is null)
        {
            jobs.Add(production.Contains(fixture) ? (name, extraction, productionProof, productionTheorem, null)
                : (name, extraction, fixtureProof, $"UInt256Proof.{method}.Fixture{fixture}.correctness", null));
            continue;
        }
        int left = witness["leftBase"]!.GetValue<int>(), right = witness["rightBase"]!.GetValue<int>(), outputBase = witness["outputBase"]!.GetValue<int>();
        string initial = string.Concat(witness["initialBytes"]!.AsObject().Select(pair => $"offset = {pair.Key} then {pair.Value!.GetValue<int>()} else if id = 0 ∧ ")) + "False then 0 else 0";
        string refutation = File.ReadAllText(Path.Combine(root, "Tests/Fixtures/Common/CheckedRefutationTemplate.lean.in"))
            .Replace("@INITIAL@", initial).Replace("@INPUTS@", $"[⟨0,{left}⟩,⟨0,{right}⟩]").Replace("@OUTPUTS@", $"[⟨0,{outputBase}⟩]")
            .Replace("@INPUT_CASES@", "rcases member with rfl | rfl <;> exact ⟨_, rfl⟩").Replace("@OUTPUT_CASE@", "subst output; rfl")
            .Replace("@CONTRACT@", "WrappingBinaryContract").Replace("@OPERATION@", operation)
            .Replace("@REFERENCES@", $"⟨0,{left}⟩ ⟨0,{right}⟩ ⟨0,{outputBase}⟩")
            .Replace("@BYTE_INDEX@", (witness["address"]!.GetValue<int>() - outputBase).ToString(CultureInfo.InvariantCulture))
            .Replace("@ACTUAL@", witness["actualByte"]!.GetValue<int>().ToString(CultureInfo.InvariantCulture));
        string proofPath = Path.Combine(consumer, "proofs", method + "Fixture" + fixture + ".lean");
        File.WriteAllText(proofPath, refutation);
        jobs.Add((name, extraction, proofPath, "FixtureWitness.refuted", productionProof));
    }
}
// Freeze the complete consumer source snapshot before issuing any certificates.
List<string> failed = await RegressionBatch.Verify(root, tool, work, consumer, [.. jobs.Select(job => new RegressionCheck(job.Name + "/scalar", job.Extraction, job.Proof, job.Theorem,
    job.Production is null ? "checked wrapping contract" : "checked contract refutation and production proof rejection",
    job.Production, job.Production is null ? null : $"UInt256Proof.{job.Name[..job.Name.IndexOf('/')]}.scalar_correctness"))]);
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
