#!/usr/bin/env dotnet
// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT
#:property PublishAot=false
using System.Diagnostics;
using System.Text.Json.Nodes;

if (args.Length > 1) throw new ArgumentException("Usage: MultiplyRegression.cs [verification-directory]");
string root = Path.GetFullPath(args.Length == 1 ? args[0] : "verification");
string fixtures = Path.Combine(root, "Tests/Fixtures/Multiply");
string work = Path.Combine(root, "artifacts/multiply-regressions");
string consumer = Path.Combine(work, "consumer");
string tool = Path.Combine(root, ".lake/packages/leancil/Extractor/bin/Nethermind.LeanCIL.dll");
JsonArray targets = JsonNode.Parse(File.ReadAllText(Path.Combine(root, "manifests/targets.json")))!["methods"]!.AsArray();
string signature = targets.Single(target => target!["id"]!.GetValue<string>() == "Multiply")!["signature"]!.GetValue<string>();
JsonArray witnesses = JsonNode.Parse(File.ReadAllText(Path.Combine(fixtures, "witnesses.json")))!.AsArray();

async Task<string> Run(string executable, IEnumerable<string> arguments, bool succeeds = true)
{
    ProcessStartInfo start = new(executable) { WorkingDirectory = root, RedirectStandardOutput = true, RedirectStandardError = true, UseShellExecute = false };
    foreach (string argument in arguments) start.ArgumentList.Add(argument);
    using Process process = Process.Start(start) ?? throw new InvalidOperationException(executable);
    Task<string> stdout = process.StandardOutput.ReadToEndAsync(), stderr = process.StandardError.ReadToEndAsync();
    await process.WaitForExitAsync();
    string output = await stdout + await stderr;
    if ((process.ExitCode == 0) != succeeds || output.Contains("IDE0005", StringComparison.Ordinal)) throw new InvalidOperationException(output);
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
List<(string Fixture, string Profile, string Extraction, string Proof, string Theorem, bool Negative)> jobs = [];
foreach (string fixture in new[] { "Baseline", "AlternativeOrder", "ExtractedHelper", "WrongCarry", "WrongCrossProduct", "WrongHighLow", "WrongAliasing", "WrongBmiHigh" })
{
    string profile = fixture == "WrongBmiHigh" ? "x64-bmi2" : "scalar";
    string profileArgument = profile == "scalar" ? profile : "@" + Path.Combine(root, "manifests/profiles", profile + ".json");
    string build = Path.Combine(work, "build", fixture);
    string intermediate = Path.Combine(build, "obj") + Path.DirectorySeparatorChar;
    await Run("dotnet", ["build", Path.Combine(fixtures, "Nethermind.Int256.csproj"), "-c", "Release", "-p:FixtureCase=" + fixture,
        "-p:BaseOutputPath=" + Path.Combine(build, "bin") + Path.DirectorySeparatorChar,
        "-p:BaseIntermediateOutputPath=" + intermediate, "-p:MSBuildProjectExtensionsPath=" + intermediate,
        "-p:EnforceCodeStyleInBuild=true", "-p:GenerateDocumentationFile=true", "-v:q"]);
    string extraction = Path.Combine(work, fixture);
    await Run("dotnet", [tool, "extract", Path.Combine(build, "bin/Release/net10.0/Nethermind.Int256.dll"), signature, extraction, profileArgument]);
    JsonNode? witness = witnesses.SingleOrDefault(value => value!["case"]!.GetValue<string>() == fixture);
    if (witness is null)
    {
        string proof = fixture == "Baseline" ? Path.Combine(consumer, "proofs/MultiplyProfile_scalar.lean") : Path.Combine(consumer, "Tests/Fixtures/Multiply", fixture + ".lean");
        string theorem = fixture == "Baseline" ? "UInt256Proof.Multiply.profile_correctness" : "UInt256Proof.Multiply.Fixture" + (fixture == "ExtractedHelper" ? "Helper" : "Alternative") + ".correctness";
        jobs.Add((fixture, profile, extraction, proof, theorem, false));
        continue;
    }
    int left = witness["leftBase"]!.GetValue<int>(), right = witness["rightBase"]!.GetValue<int>(), outputBase = witness["outputBase"]!.GetValue<int>();
    string initial = string.Concat(witness["initialBytes"]!.AsObject().Select(pair => $"offset = {pair.Key} then {pair.Value!.GetValue<int>()} else if id = 0 ∧ ")) + "False then 0 else 0";
    string refutation = File.ReadAllText(Path.Combine(root, "Tests/Fixtures/Common/CheckedRefutationTemplate.lean.in"))
        .Replace("@INITIAL@", initial).Replace("@INPUTS@", $"[⟨0,{left}⟩,⟨0,{right}⟩]").Replace("@OUTPUTS@", $"[⟨0,{outputBase}⟩]")
        .Replace("@INPUT_CASES@", "rcases member with rfl | rfl <;> exact ⟨_, rfl⟩").Replace("@OUTPUT_CASE@", "subst output; rfl")
        .Replace("@CONTRACT@", "WrappingBinaryContract").Replace("@OPERATION@", "(· * ·)")
        .Replace("@REFERENCES@", $"⟨0,{left}⟩ ⟨0,{right}⟩ ⟨0,{outputBase}⟩")
        .Replace("@BYTE_INDEX@", (witness["address"]!.GetValue<int>() - outputBase).ToString(System.Globalization.CultureInfo.InvariantCulture))
        .Replace("@ACTUAL@", witness["actualByte"]!.GetValue<int>().ToString(System.Globalization.CultureInfo.InvariantCulture));
    string proofPath = Path.Combine(consumer, "proofs", "MultiplyFixture" + fixture + ".lean");
    File.WriteAllText(proofPath, refutation);
    jobs.Add((fixture, profile, extraction, proofPath, "FixtureWitness.refuted", true));
}
// Freeze the complete consumer source snapshot before issuing any certificates.
foreach (var job in jobs)
{
    await Run("dotnet", [tool, "verify", job.Extraction, "--proof", job.Proof, "--theorem", job.Theorem, "--proof-root", consumer]);
    if (!job.Negative)
    {
        Console.WriteLine($"PASS {job.Fixture}/{job.Profile}: checked multiplication contract");
        continue;
    }
    string expectedProof = Path.Combine(consumer, "proofs", "MultiplyProfile_" + job.Profile.Replace('-', '_') + ".lean");
    const string expectedTheorem = "UInt256Proof.Multiply.profile_correctness";
    string rejected = await Run("dotnet", [tool, "verify", job.Extraction, "--proof", expectedProof, "--theorem", expectedTheorem, "--proof-root", consumer], succeeds: false);
    if (!rejected.Contains("proof checking", StringComparison.OrdinalIgnoreCase) || File.Exists(Path.Combine(job.Extraction, "verified.json")))
        throw new InvalidOperationException("Mutation was not rejected during proof checking or retained a stale certificate: " + rejected);
    Console.WriteLine($"PASS {job.Fixture}/{job.Profile}: checked contract refutation and production proof rejection");
}

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
