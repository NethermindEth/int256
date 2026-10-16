#!/usr/bin/env dotnet
// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT
#:property PublishAot=false
using System.Diagnostics;
using System.Text.Json.Nodes;
using System.Xml.Linq;

const string usage = "Usage: SafetyRegression.cs [verification-directory] [--case C]";
string? directory = null, selected = null;
for (int i = 0; i < args.Length; i++)
{
    if (args[i] == "--case" && i + 1 < args.Length) selected = args[++i];
    else if (directory is null && !args[i].StartsWith("--", StringComparison.Ordinal)) directory = args[i];
    else throw new ArgumentException(usage);
}
string root = Path.GetFullPath(directory ?? "verification");
string work = Path.Combine(root, "artifacts/safety-regressions");
string consumer = Path.Combine(work, "consumer");
string tool = Path.Combine(root, ".lake/packages/leancil/Extractor/bin/Nethermind.LeanCIL.dll");
string fixtures = Path.Combine(root, "Tests/Fixtures/Safety");
string signature = JsonNode.Parse(File.ReadAllText(Path.Combine(root, "manifests/targets.json")))!["methods"]!.AsArray()
    .Single(target => target!["id"]!.GetValue<string>() == "Add")!["signature"]!.GetValue<string>();
string productionProof = Path.Combine(consumer, "proofs/AddScalar.lean");
const string productionTheorem = "UInt256Proof.Add.scalar_correctness";
XElement[] registry = XDocument.Load(Path.Combine(fixtures, "Cases.props")).Descendants("SafetyCase").ToArray();
if (selected is not null && registry.All(entry => (string)entry.Attribute("Include")! != selected)) throw new ArgumentException("Unknown safety case: " + selected);
List<string> failed = [];

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
    foreach (string child in Directory.EnumerateDirectories(source))
    {
        string name = Path.GetFileName(child);
        if (name is ".lake" or ".git" or "artifacts" or "generated" or "bin" or "obj" or ".work") continue;
        if ((File.GetAttributes(child) & FileAttributes.ReparsePoint) != 0)
            throw new InvalidOperationException("Source snapshot cannot contain links: " + child);
        CopySources(child, Path.Combine(destination, name));
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

List<(string Name, string Extraction, string Proof, string Theorem, bool Negative)> jobs = [];
foreach (XElement entry in registry)
{
    string name = (string)entry.Attribute("Include")!, suite = (string)entry.Attribute("Suite")!;
    if (selected is not null && selected != name) continue;
    if (suite == "upstream")
    {
        Console.WriteLine($"UPSTREAM {name}: extractor behaviour belongs to LeanCIL; see Tests/Fixtures/Safety/README.md");
        continue;
    }
    string build = Path.Combine(work, "build", name);
    string intermediate = Path.Combine(build, "obj") + Path.DirectorySeparatorChar;
    await Run("dotnet", ["build", Path.Combine(fixtures, "Nethermind.Int256.csproj"), "-c", "Release", "-p:FixtureCase=" + name,
        "-p:BaseOutputPath=" + Path.Combine(build, "bin") + Path.DirectorySeparatorChar,
        "-p:BaseIntermediateOutputPath=" + intermediate, "-p:MSBuildProjectExtensionsPath=" + intermediate,
        "-p:EnforceCodeStyleInBuild=true", "-p:GenerateDocumentationFile=true", "-v:q"]);
    string extraction = Path.Combine(work, name);
    if (Directory.Exists(extraction)) Directory.Delete(extraction, true);
    await Run("dotnet", [tool, "extract", Path.Combine(build, "bin/Release/net10.0/Nethermind.Int256.dll"), signature, extraction, "scalar"]);
    string inputBase = (string?)entry.Attribute("InputBase") ?? "0", input = $"⟨0, {inputBase}⟩", arguments = $"{input} {input} ⟨1, 0⟩";
    bool negative = suite == "negative";
    string theorem;
    // Method indices are assigned per extraction, so methods are named in the registry.
    string Method(string name) => File.ReadLines(Path.Combine(extraction, "Extracted.lean"))
        .Select(line => System.Text.RegularExpressions.Regex.Match(line, $@"^def method(\d+)Signature : String := "".*::{name}\("))
        .Single(match => match.Success).Groups[1].Value;
    if (negative)
    {
        // The fault is pinned to its method, instruction, rule, reference and width.
        string located = $"⟨{Method((string)entry.Attribute("FaultMethod")!)}, {(string)entry.Attribute("FaultInstruction")!}, {(string)entry.Attribute("Fault")!}⟩";
        theorem = $"""
            theorem refuted : ¬ WrappingBinaryContract (· + ·) Extracted.program 0 :=
              UInt256Model.Safety.ContractRefutation.checked_binary_fault_refuted Extracted.program 0 1024 (· + ·) memory
                {arguments} {located} call (by decide) (by rfl)
            #print axioms refuted
            """;
    }
    else
    {
        // The public result ignores the probe, so the probe's own value is pinned separately.
        string probe = Method("Probe");
        theorem = $"""
            theorem accepted : CallingConditions Extracted.program memory [{input}, {input}] [⟨1, 0⟩] ∧
                (invoke Extracted.program 1024 0 (binaryArguments {arguments}) memory).map
                  (fun outcome => (inputValue outcome.1 ⟨1, 0⟩, outcome.2)) =
                  .ok (inputValue memory {input} + inputValue memory {input}, []) ∧
                (invoke Extracted.program 1024 {probe} [.reference (.address {input})] memory).map Prod.snd =
                  .ok [.scalar (.i64 {(string)entry.Attribute("ProbeValue")!})] := ⟨call, by rfl, by rfl⟩
            #print axioms accepted
            """;
    }
    string source = File.ReadAllText(Path.Combine(fixtures, "WitnessTemplate.lean.in"))
        .Replace("@INPUT_SIZE@", (string?)entry.Attribute("InputSize") ?? "32").Replace("@INPUT_BASE@", inputBase).Replace("@THEOREM@", theorem);
    string proof = Path.Combine(consumer, "proofs", "SafetyFixture" + name + ".lean");
    File.WriteAllText(proof, source);
    jobs.Add((name, extraction, proof, negative ? "SafetyWitness.refuted" : "SafetyWitness.accepted", negative));
}
// The consumer snapshot is complete before any certificate is issued.
foreach (var job in jobs)
{
    string log = Path.Combine(work, job.Name + ".log");
    try
    {
        await Run("dotnet", [tool, "verify", job.Extraction, "--proof", job.Proof, "--theorem", job.Theorem, "--proof-root", consumer]);
        if (!job.Negative)
        {
            Console.WriteLine($"PASS Safety/{job.Name}: checked valid call returns the initial-input sum");
            continue;
        }
        string rejected = await Run("dotnet", [tool, "verify", job.Extraction, "--proof", productionProof, "--theorem", productionTheorem, "--proof-root", consumer], succeeds: false);
        if (!rejected.Contains("proof checking", StringComparison.OrdinalIgnoreCase) || File.Exists(Path.Combine(job.Extraction, "verified.json")))
            throw new InvalidOperationException("Probe was not rejected during proof checking or retained a stale certificate: " + rejected);
        Console.WriteLine($"PASS Safety/{job.Name}: checked fault refutation and production proof rejection");
    }
    catch (InvalidOperationException exception)
    {
        File.WriteAllText(log, exception.Message);
        failed.Add(job.Name);
        Console.WriteLine($"FAIL Safety/{job.Name}: see {log}");
    }
}
if (failed.Count != 0) Console.WriteLine("FAILED: " + string.Join(", ", failed));
Environment.ExitCode = failed.Count == 0 ? 0 : 1;

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
