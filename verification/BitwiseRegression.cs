#!/usr/bin/env dotnet
// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT
#:property PublishAot=false
#:include RegressionBatch.cs
#:include RegressionManifest.cs
using System.Diagnostics;
using System.Security.Cryptography;
using System.Text.Json.Nodes;

string root = Path.GetFullPath(args.Length > 0 ? args[0] : "verification");
string fixtures = Path.Combine(root, "Tests/Fixtures/Bitwise");
string profile = args.Length > 1 ? args[1] : "scalar";
string[] profiles = RegressionManifest.RequireProfiles(root, "BitwiseRegression.cs", ["scalar", "x64-v3"]);
if (args.Length > 2 || !profiles.Contains(profile))
    throw new ArgumentException("Usage: BitwiseRegression.cs [verification-directory] [scalar|x64-v3]");
string work = Path.Combine(root, "artifacts/bitwise-regressions", profile);
string tool = Path.Combine(root, ".lake/packages/leancil/Extractor/bin/Nethermind.LeanCIL.dll");
string profileArgument = File.Exists(Path.Combine(root, "manifests/profiles", profile + ".json")) ? "@" + Path.Combine(root, "manifests/profiles", profile + ".json") : profile;
string consumer = Path.Combine(work, "consumer");
List<(string Extraction, string Proof, string Id, string Mutation)> jobs = [];
JsonArray targets = JsonNode.Parse(File.ReadAllText(Path.Combine(root, "manifests/targets.json")))!["methods"]!.AsArray();
async Task<string> Run(string executable, IEnumerable<string> arguments, bool disableIntrinsics = false)
{
    ProcessStartInfo start = new(executable) { WorkingDirectory = root, RedirectStandardOutput = true, RedirectStandardError = true, UseShellExecute = false };
    foreach (string argument in arguments) start.ArgumentList.Add(argument);
    if (disableIntrinsics) start.Environment["DOTNET_EnableHWIntrinsic"] = "0";
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
foreach (bool early in new[] { false, true })
{
    string mutation = early ? "BitwiseEarlyStore" : "BitwiseWrongOperator";
    string build = Path.Combine(work, "build", mutation);
    await Run("dotnet", ["build", Path.Combine(fixtures, "Nethermind.Int256.csproj"), "-c", "Release",
        "-p:FixtureCase=" + mutation, "-p:BaseOutputPath=" + Path.Combine(build, "bin") + Path.DirectorySeparatorChar,
        "-p:BaseIntermediateOutputPath=" + Path.Combine(build, "obj") + Path.DirectorySeparatorChar,
        "-p:EnforceCodeStyleInBuild=true", "-p:GenerateDocumentationFile=true", "-v:q"]);
    string nativeBuild = Path.Combine(build, "native");
    await Run("dotnet", ["build", Path.Combine(fixtures, "NativeWitness.csproj"), "-c", "Release",
        "-p:FixtureAssembly=" + Path.Combine(build, "bin/Release/net10.0/Nethermind.Int256.dll"),
        "-p:BaseOutputPath=" + Path.Combine(nativeBuild, "bin") + Path.DirectorySeparatorChar,
        "-p:BaseIntermediateOutputPath=" + Path.Combine(nativeBuild, "obj") + Path.DirectorySeparatorChar,
        "-p:EnforceCodeStyleInBuild=true", "-p:GenerateDocumentationFile=true", "-v:q"]);
    byte[] expectedAssembly = SHA256.HashData(File.ReadAllBytes(Path.Combine(build, "bin/Release/net10.0/Nethermind.Int256.dll")));
    byte[] loadedAssembly = SHA256.HashData(File.ReadAllBytes(Path.Combine(nativeBuild, "bin/Release/net10.0/Nethermind.Int256.dll")));
    if (!expectedAssembly.AsSpan().SequenceEqual(loadedAssembly)) throw new InvalidOperationException("Native witness resolved a different fixture assembly");
    Console.Write(await Run("dotnet", [Path.Combine(nativeBuild, "bin/Release/net10.0/NativeWitness.dll"), mutation]));
    Console.Write(await Run("dotnet", [Path.Combine(nativeBuild, "bin/Release/net10.0/NativeWitness.dll"), mutation], disableIntrinsics: true));
    foreach (string operation in new[] { "And", "Or", "Xor", "Not" })
    foreach (bool returned in new[] { false, true })
    {
        if (early && returned) continue;
        bool unary = operation == "Not";
        string id = (returned ? "Operator" : "") + operation;
        string extraction = Path.Combine(work, mutation, id);
        string signature = targets.Single(target => target!["id"]!.GetValue<string>() == id)!["signature"]!.GetValue<string>();
        await Run("dotnet", [tool, "extract", Path.Combine(build, "bin/Release/net10.0/Nethermind.Int256.dll"), signature, extraction, profileArgument]);
        ulong[] initial = early ? [1, 2, 4, 8] : [1, 0, 0, 0];
        ulong[] actual = early ? operation switch
        {
            "And" => [1, 0, 0, 0], "Or" => [1, 3, 7, 15], "Xor" => [0, 2, 6, 14],
            _ => [ulong.MaxValue - 1, 1, ulong.MaxValue - 1, 1]
        } : operation switch { "And" or "Or" => [0, 0, 0, 0], _ => [1, 0, 0, 0] };
        string operationTerm = operation switch { "And" => "(fun a b => a &&& b)", "Or" => "(fun a b => a ||| b)", "Xor" => "(fun a b => a ^^^ b)", _ => "(fun a => ~~~a)" };
        string initialTerm = "";
        for (int i = 0; i < 4; i++)
            initialTerm += $"offset = {16 + i * 8} then {initial[i]} else if id = 0 ∧ offset = {64 + i * 8} then {initial[i]} else if id = 0 ∧ ";
        initialTerm += "False then 0 else 0";
        string value = $"({actual[0]} + {actual[1]} * 2^64 + {actual[2]} * 2^128 + {actual[3]} * 2^192)";
        string refutation = "checked_" + (unary ? "unary" : "binary") + (returned ? "_return" : "") + "_refuted";
        string contract = returned ? "UInt256Model.Safety.AggregateReturn." + (unary ? "UnaryContract" : "BinaryContract") : unary ? "WrappingUnaryContract" : "WrappingBinaryContract";
        string output = early ? "24" : "104";
        string proof = File.ReadAllText(Path.Combine(fixtures, "CheckedRefutationTemplate.lean.in"))
            .Replace("@INITIAL@", initialTerm).Replace("@INPUTS@", unary ? "[⟨0,16⟩]" : "[⟨0,16⟩,⟨0,64⟩]")
            .Replace("@OUTPUTS@", returned ? "[]" : $"[⟨0,{output}⟩]")
            .Replace("@INPUT_CASES@", unary ? "subst input; exact ⟨_, rfl⟩" : "rcases member with rfl | rfl <;> exact ⟨_, rfl⟩")
            .Replace("@OUTPUT_CASE@", returned ? "" : "subst output; rfl")
            .Replace("@CONTRACT@", contract).Replace("@OPERATION@", operationTerm).Replace("@REFUTATION@", refutation)
            .Replace("@REFERENCES@", "⟨0,16⟩" + (unary ? "" : " ⟨0,64⟩") + (returned ? "" : $" ⟨0,{output}⟩"))
            .Replace("@ACTUAL@", returned ? $"(numberBytes {value} 32)" : $"(BitVec.ofNat 256 {value})");
        if (returned) proof = proof.Replace("  · intro output member\n    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at member\n    ", "  · intro output member\n    simp only [List.map_nil, List.not_mem_nil] at member\n");
        string proofPath = Path.Combine(consumer, "proofs", mutation + id + "Refutation.lean");
        File.WriteAllText(proofPath, proof);
        jobs.Add((extraction, proofPath, id, mutation));
    }
}
string suffix = profile == "scalar" ? "Scalar" : "Vector";
List<string> failed = await RegressionBatch.Verify(root, tool, work, consumer, [.. jobs.Select(job => new RegressionCheck($"{job.Id}/{profile}/{job.Mutation}",
    job.Extraction, job.Proof, "BitwiseWitness.refuted", "checked contract refutation", Path.Combine(consumer, "proofs", job.Id + suffix + ".lean"),
    "UInt256Proof." + job.Id + "." + suffix.ToLowerInvariant() + "_correctness"))]);
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
