#!/usr/bin/env dotnet
// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT
#:property PublishAot=false
using System.Diagnostics;
using System.Globalization;
using System.Numerics;
using System.Text.Json.Nodes;
using System.Text.RegularExpressions;
using System.Xml.Linq;

string[] profiles = ["scalar", "x64-vector256", "x64-avx2", "x64-avx512"];
string usage = "Usage: CompareRegression.cs [verification-directory] [all|" + string.Join('|', profiles) + "]";
if (args.Length > 2) throw new ArgumentException(usage);
string root = Path.GetFullPath(args.Length > 0 ? args[0] : "verification");
string selected = args.Length > 1 ? args[1] : "all";
if (selected != "all" && !profiles.Contains(selected)) throw new ArgumentException(usage);
string work = Path.Combine(root, "artifacts/compare-regressions", selected);
string consumer = Path.Combine(work, "consumer");
string fixtures = Path.Combine(root, "Tests/Fixtures/Compare");
string tool = Path.Combine(root, ".lake/packages/leancil/Extractor/bin/Nethermind.LeanCIL.dll");
JsonArray targets = JsonNode.Parse(File.ReadAllText(Path.Combine(root, "manifests/targets.json")))!["methods"]!.AsArray();
JsonArray gates = JsonNode.Parse(File.ReadAllText(Path.Combine(root, "manifests/gates.json")))!["gates"]!.AsArray();
JsonObject witnesses = JsonNode.Parse(File.ReadAllText(Path.Combine(fixtures, "witnesses.json")))!.AsObject();
JsonObject positives = witnesses["positiveCases"]!.AsObject(), negatives = witnesses["negativeCases"]!.AsObject();
string[] cases = XDocument.Load(Path.Combine(fixtures, "Cases.props")).Descendants("CompareCase").Select(item => (string)item.Attribute("Include")!).ToArray();
string[] methods = ["LtUInt256UInt256", "CompareToUInt256Ref"];
List<string> incomplete = [], failed = [];

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

// Method bodies only; assembly identity and metadata tokens do not affect the checked program.
static string Bodies(string extraction) => string.Join('\n', Regex.Matches(File.ReadAllText(Path.Combine(extraction, "Extracted.lean")),
    @"^def method\d+ : Method := .*?(?=^def )", RegexOptions.Multiline | RegexOptions.Singleline).Select(match => match.Value));

static string Statement(string proof, string theorem)
{
    Match match = Regex.Match(File.ReadAllText(proof), @"theorem\s+" + Regex.Escape(theorem) + @"\s*:(.*?):=", RegexOptions.Singleline);
    if (!match.Success) throw new InvalidOperationException($"Theorem {theorem} not found in {proof}");
    return Regex.Replace(match.Groups[1].Value.Trim(), @"\s+", " ");
}

// A case reaches a profile only where its witness entry says so; elsewhere the extraction must stay unchanged.
bool Applicable(string fixture, string method, string profile)
{
    if (fixture == "Baseline") return true;
    JsonObject entry = (positives[fixture] ?? negatives[fixture])?.AsObject() ?? throw new InvalidOperationException("Case without witness entry: " + fixture);
    return entry["method"]!.GetValue<string>() == method && entry["profiles"]!.AsArray().Any(item => item!.GetValue<string>() == profile);
}

static BigInteger Number(JsonObject initial, int start) => Enumerable.Range(0, 32)
    .Select(i => (BigInteger)(initial[(start + i).ToString(CultureInfo.InvariantCulture)]?.GetValue<int>() ?? 0) << (8 * i))
    .Aggregate(BigInteger.Zero, (sum, value) => sum + value);

static string Word(int value) => value < 0 ? $"(BitVec.ofInt 32 ({value}))" : value.ToString(CultureInfo.InvariantCulture);

string Refutation(string fixture, string method, string statement)
{
    JsonObject data = negatives[fixture]!.AsObject();
    JsonObject initial = data["initialBytes"]!.AsObject();
    int left = data["leftBase"]!.GetValue<int>(), right = data["rightBase"]!.GetValue<int>(), actual = data["actualResult"]!.GetValue<int>();
    BigInteger leftValue = Number(initial, left), rightValue = Number(initial, right);
    int expected = method == "CompareToUInt256Ref" ? leftValue.CompareTo(rightValue) : leftValue < rightValue ? 1 : 0;
    if (actual == expected) throw new InvalidOperationException($"{fixture} witness does not contradict the contract for {method}");
    if (!statement.StartsWith("UInt256Model.Safety.ReadOnlyContract ", StringComparison.Ordinal))
        throw new InvalidOperationException($"Unexpected production contract for {method}: {statement}");
    string bytes = string.Concat(initial.Select(pair => $"offset = {pair.Key} then {pair.Value!.GetValue<int>()} else if id = 0 ∧ ")) + "False then 0 else 0";
    return File.ReadAllText(Path.Combine(fixtures, "RefutationTemplate.lean.in"))
        .Replace("@INITIAL@", bytes)
        .Replace("@INPUTS@", $"[⟨0,{left}⟩,⟨0,{right}⟩]")
        .Replace("@INPUT_CASES@", "rcases member with rfl | rfl <;> exact ⟨_, rfl⟩")
        .Replace("@STATEMENT@", statement)
        .Replace("@LEMMA@", $"checked_readonly_refuted _ Extracted.program _ 2 1024 memory [⟨0,{left}⟩, ⟨0,{right}⟩] [.scalar (.i32 {Word(actual)})] rfl call");
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

Dictionary<string, string> assemblies = [];
foreach (string fixture in cases)
{
    string build = Path.Combine(work, "build", fixture);
    string intermediate = Path.Combine(build, "obj") + Path.DirectorySeparatorChar;
    await Run("dotnet", ["build", Path.Combine(fixtures, "Nethermind.Int256.csproj"), "-c", "Release", "-p:FixtureCase=" + fixture,
        "-p:BaseOutputPath=" + Path.Combine(build, "bin") + Path.DirectorySeparatorChar,
        "-p:BaseIntermediateOutputPath=" + intermediate, "-p:MSBuildProjectExtensionsPath=" + intermediate,
        "-p:EnforceCodeStyleInBuild=true", "-p:GenerateDocumentationFile=true", "-v:q"]);
    assemblies[fixture] = Path.Combine(build, "bin/Release/net10.0/Nethermind.Int256.dll");
}
await Run("dotnet", ["build", Path.Combine(root, "../src/Nethermind.Int256/Nethermind.Int256.csproj"), "-c", "Release", "-v:q"]);
string production = Path.Combine(root, "../src/artifacts/bin/Nethermind.Int256/release/Nethermind.Int256.dll");

List<(string Name, string Extraction, string Proof, string Theorem, string? Production, string? ProductionTheorem)> jobs = [];
foreach (JsonNode? gate in gates)
{
    string method = gate!["method"]!.GetValue<string>(), profile = gate["profile"]!.GetValue<string>();
    if (!methods.Contains(method) || !profiles.Contains(profile) || selected != "all" && selected != profile) continue;
    string signature = targets.Single(target => target!["id"]!.GetValue<string>() == method)!["signature"]!.GetValue<string>();
    string profileArgument = File.Exists(Path.Combine(root, "manifests/profiles", profile + ".json"))
        ? "@" + Path.Combine(root, "manifests/profiles", profile + ".json") : profile;
    string productionProof = Path.Combine(consumer, gate["proof"]!.GetValue<string>()), productionTheorem = gate["theorem"]!.GetValue<string>();
    string statement = Statement(productionProof, productionTheorem);
    string reference = Path.Combine(work, "production", method, profile);
    await Run("dotnet", [tool, "extract", production, signature, reference, profileArgument, "--assume-initialized", "Nethermind.Int256.UInt256"]);
    foreach (string fixture in cases)
    {
        string name = $"{method}/{profile}/{fixture}";
        string extraction = Path.Combine(work, method, profile, fixture);
        await Run("dotnet", [tool, "extract", assemblies[fixture], signature, extraction, profileArgument]);
        bool unchanged = Bodies(extraction) == Bodies(reference), applicable = Applicable(fixture, method, profile);
        if (!applicable)
        {
            if (!unchanged)
            {
                Console.WriteLine($"FAIL {name}: mutation reaches a profile its witness entry does not cover");
                failed.Add(name);
            }
            continue;
        }
        if (unchanged != (fixture == "Baseline"))
        {
            Console.WriteLine($"FAIL {name}: " + (unchanged ? "fixture did not change the extracted program" : "baseline differs from the production program"));
            failed.Add(name);
            continue;
        }
        if (fixture == "Baseline")
        {
            jobs.Add((name, extraction, productionProof, productionTheorem, null, null));
            continue;
        }
        if (positives.ContainsKey(fixture))
        {
            string fixtureProof = Path.Combine(consumer, "Tests/Fixtures/Compare", fixture, $"{method}_{profile.Replace('-', '_')}.lean");
            if (!File.Exists(fixtureProof))
            {
                Console.WriteLine($"PENDING {name}: no fixture proof yet");
                incomplete.Add(name);
                continue;
            }
            if (Statement(fixtureProof, "CompareFixture.correct") != statement)
                throw new InvalidOperationException($"Fixture proof {fixtureProof} does not state the production contract");
            jobs.Add((name, extraction, fixtureProof, "CompareFixture.correct", null, null));
            continue;
        }
        string proofPath = Path.Combine(consumer, "proofs", $"CompareFixture{fixture}{method}{profile.Replace("-", "")}.lean");
        File.WriteAllText(proofPath, Refutation(fixture, method, statement));
        jobs.Add((name, extraction, proofPath, "CompareWitness.refuted", productionProof, productionTheorem));
    }
}
// Freeze the complete consumer source snapshot before issuing any certificates.
// Each verify builds in its own fresh session, so independent jobs may run concurrently.
await Parallel.ForEachAsync(jobs, new ParallelOptions { MaxDegreeOfParallelism = Math.Max(1, Environment.ProcessorCount / 4) }, async (job, _) =>
{
    string log = Path.Combine(work, job.Name.Replace('/', '-') + ".log");
    try
    {
        await Run("dotnet", [tool, "verify", job.Extraction, "--proof", job.Proof, "--theorem", job.Theorem, "--proof-root", consumer]);
        if (job.Production is null)
        {
            Console.WriteLine($"PASS {job.Name}: checked production contract");
            return;
        }
        string rejected = await Run("dotnet", [tool, "verify", job.Extraction, "--proof", job.Production, "--theorem", job.ProductionTheorem!, "--proof-root", consumer], succeeds: false);
        if (!rejected.Contains("proof checking", StringComparison.OrdinalIgnoreCase) || File.Exists(Path.Combine(job.Extraction, "verified.json")))
            throw new InvalidOperationException("Mutation was not rejected during proof checking or retained a stale certificate: " + rejected);
        Console.WriteLine($"PASS {job.Name}: checked contract refutation and production proof rejection");
    }
    catch (InvalidOperationException exception)
    {
        File.WriteAllText(log, exception.Message);
        lock (failed) failed.Add(job.Name);
        Console.WriteLine($"FAIL {job.Name}: see {log}");
    }
});
Console.WriteLine($"SUMMARY: {jobs.Count - failed.Count(jobs.Select(job => job.Name).Contains)} passed, {failed.Count} failed, {incomplete.Count} pending");
if (incomplete.Count != 0) Console.WriteLine("INCOMPLETE: " + string.Join(", ", incomplete));
if (failed.Count != 0) Console.WriteLine("FAILED: " + string.Join(", ", failed.Order(StringComparer.Ordinal)));
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
