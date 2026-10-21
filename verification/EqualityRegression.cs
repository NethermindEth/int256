#!/usr/bin/env dotnet
// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT
#:property PublishAot=false
#:include RegressionBatch.cs
using System.Diagnostics;
using System.Globalization;
using System.Numerics;
using System.Text.Json.Nodes;
using System.Text.RegularExpressions;
using System.Xml.Linq;

const string Usage = "Usage: EqualityRegression.cs [verification-directory] [all|scalar|x64-vector256|x64-sse41] [all|<case>]";
if (args.Length > 3) throw new ArgumentException(Usage);
string root = Path.GetFullPath(args.Length > 0 ? args[0] : "verification");
string selected = args.Length > 1 ? args[1] : "all", selectedCase = args.Length > 2 ? args[2] : "all";
if (selected is not ("all" or "scalar" or "x64-vector256" or "x64-sse41")) throw new ArgumentException(Usage);
string work = Path.Combine(root, "artifacts/equality-regressions", selectedCase == "all" ? selected : selected + "-" + selectedCase);
string consumer = Path.Combine(work, "consumer");
string fixtures = Path.Combine(root, "Tests/Fixtures/Equality");
string tool = Path.Combine(root, ".lake/packages/leancil/Extractor/bin/Nethermind.LeanCIL.dll");
JsonArray targets = JsonNode.Parse(File.ReadAllText(Path.Combine(root, "manifests/targets.json")))!["methods"]!.AsArray();
JsonArray gates = JsonNode.Parse(File.ReadAllText(Path.Combine(root, "manifests/gates.json")))!["gates"]!.AsArray();
JsonObject negatives = JsonNode.Parse(File.ReadAllText(Path.Combine(fixtures, "witnesses.json")))!["negativeCases"]!.AsObject();
string[] cases = XDocument.Load(Path.Combine(fixtures, "Cases.props")).Descendants("EqualityCase").Select(item => (string)item.Attribute("Include")!).ToArray();
if (selectedCase != "all" && !cases.Contains(selectedCase)) throw new ArgumentException(Usage);
if (selectedCase != "all") cases = [selectedCase];
string[] references = ["EqUInt256UInt256", "NeUInt256UInt256", "EqualsUInt256Ref", "EqualsUInt256Value"];
List<string> incomplete = [], failed = [];

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

// Method bodies only; assembly identity and metadata tokens do not affect the checked program.
static string Bodies(string extraction) => string.Join('\n', Regex.Matches(File.ReadAllText(Path.Combine(extraction, "Extracted.lean")),
    @"^def method\d+ : Method := .*?(?=^def )", RegexOptions.Multiline | RegexOptions.Singleline).Select(match => match.Value));

static string Statement(string proof, string theorem)
{
    Match match = Regex.Match(File.ReadAllText(proof), @"theorem\s+" + Regex.Escape(theorem) + @"\s*:(.*?):=", RegexOptions.Singleline);
    if (!match.Success) throw new InvalidOperationException($"Theorem {theorem} not found in {proof}");
    return Regex.Replace(match.Groups[1].Value.Trim(), @"\s+", " ");
}

(string Kind, bool Negate, bool ScalarFirst, int Width, bool Signed) Shape(string signature)
{
    Match match = Regex.Match(signature, @"::(\w+)\((.*)\)$");
    string name = match.Groups[1].Value;
    string[] parameters = match.Groups[2].Value.Split(',');
    bool negate = name == "op_Inequality";
    if (parameters.All(parameter => parameter == "Nethermind.Int256.UInt256&")) return ("reference", negate, false, 0, false);
    if (parameters is ["Nethermind.Int256.UInt256"]) return ("snapshot", negate, false, 0, false);
    string scalar = parameters.Single(parameter => parameter.StartsWith("System.", StringComparison.Ordinal));
    (int width, bool signed) = scalar switch
    {
        "System.Int32" => (32, true), "System.UInt32" => (32, false),
        "System.Int64" => (64, true), "System.UInt64" => (64, false),
        _ => throw new InvalidOperationException("Unsupported equality signature: " + signature)
    };
    return ("scalar", negate, name.StartsWith("op_", StringComparison.Ordinal) && parameters[0] == scalar, width, signed);
}

bool Applicable(string fixture, string method, string profile, string signature)
{
    var shape = Shape(signature);
    return fixture switch
    {
        "Baseline" or "Renamed" => true,
        "EquivalentReduction" => profile != "scalar",
        _ => negatives[fixture]!["group"]!.GetValue<string>() switch
        {
            "reference" => references.Contains(method),
            "snapshot" => shape.Kind == "snapshot",
            "signed" => shape.Signed,
            "inequality" => shape.Negate,
            var group => throw new InvalidOperationException("Unknown witness group: " + group)
        }
    };
}

static BigInteger Number(JsonObject initial, int start) => Enumerable.Range(0, 32)
    .Select(i => (BigInteger)(initial[(start + i).ToString(CultureInfo.InvariantCulture)]?.GetValue<int>() ?? 0) << (8 * i))
    .Aggregate(BigInteger.Zero, (sum, value) => sum + value);

string Refutation(string fixture, string signature, string statement)
{
    var shape = Shape(signature);
    JsonObject data = negatives[fixture]!.DeepClone().AsObject();
    if (data["widths"] is JsonObject widths)
        foreach (var pair in widths[shape.Width.ToString(CultureInfo.InvariantCulture)]!.AsObject()) data[pair.Key] = pair.Value?.DeepClone();
    JsonObject initial = data["initialBytes"]!.AsObject();
    int left = data["leftBase"]!.GetValue<int>(), right = data["rightBase"]!.GetValue<int>();
    BigInteger leftValue = Number(initial, left), rightValue = Number(initial, right);
    BigInteger snapshot = data["snapshot"] is JsonNode value ? BigInteger.Parse(value.ToString(), CultureInfo.InvariantCulture) : rightValue;
    BigInteger bits = data["scalarBits"] is JsonNode scalarBits ? BigInteger.Parse(scalarBits.ToString(), CultureInfo.InvariantCulture) : 0;
    BigInteger scalar = shape.Signed && bits >= BigInteger.One << (shape.Width - 1) ? bits - (BigInteger.One << shape.Width) : bits;
    bool equal = shape.Kind switch { "scalar" => leftValue == scalar, "snapshot" => leftValue == snapshot, _ => leftValue == rightValue };
    bool expected = equal != shape.Negate;
    bool actual = data["actualResult"]?.GetValue<bool>() ?? data["actualEquality"]!.GetValue<bool>() != shape.Negate;
    if (actual == expected) throw new InvalidOperationException($"{fixture} witness does not contradict the contract for {signature}");
    string observed = $"[.scalar (.i32 {(actual ? 1 : 0)})]";
    (string head, string lemma) = shape.Kind switch
    {
        "reference" => ("UInt256Model.Safety.ReadOnlyContract",
            $"checked_readonly_refuted _ Extracted.program _ 2 1024 memory [⟨0,{left}⟩, ⟨0,{right}⟩] {observed} rfl call"),
        "snapshot" => ("UInt256Model.Safety.ReadOnlyScalarContract",
            $"checked_readonly_scalar_refuted _ _ Extracted.program _ 1024 memory ⟨0,{left}⟩ (BitVec.ofNat 256 {snapshot}) {observed} call"),
        _ => ("UInt256Model.Safety.ScalarOperatorContract",
            $"checked_scalar_operator_refuted _ _ _ _ Extracted.program _ 1024 memory ⟨0,{left}⟩ (BitVec.ofNat {shape.Width} {bits}) {observed} call")
    };
    if (!statement.StartsWith(head + " ", StringComparison.Ordinal)) throw new InvalidOperationException($"Unexpected production contract for {signature}: {statement}");
    string bytes = string.Concat(initial.Select(pair => $"offset = {pair.Key} then {pair.Value!.GetValue<int>()} else if id = 0 ∧ ")) + "False then 0 else 0";
    return File.ReadAllText(Path.Combine(fixtures, "RefutationTemplate.lean.in"))
        .Replace("@INITIAL@", bytes)
        .Replace("@INPUTS@", shape.Kind == "reference" ? $"[⟨0,{left}⟩,⟨0,{right}⟩]" : $"[⟨0,{left}⟩]")
        .Replace("@INPUT_CASES@", shape.Kind == "reference" ? "rcases member with rfl | rfl <;> exact ⟨_, rfl⟩" : "subst input; exact ⟨_, rfl⟩")
        .Replace("@STATEMENT@", statement).Replace("@LEMMA@", lemma);
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
    if (!Regex.IsMatch(method, "^(Eq|Ne)") || selected != "all" && selected != profile) continue;
    string signature = targets.Single(target => target!["id"]!.GetValue<string>() == method)!["signature"]!.GetValue<string>();
    string profileArgument = File.Exists(Path.Combine(root, "manifests/profiles", profile + ".json"))
        ? "@" + Path.Combine(root, "manifests/profiles", profile + ".json") : profile;
    string productionProof = Path.Combine(consumer, gate["proof"]!.GetValue<string>()), productionTheorem = gate["theorem"]!.GetValue<string>();
    string statement = Statement(productionProof, productionTheorem);
    string reference = Path.Combine(work, "production", method, profile);
    await Run("dotnet", [tool, "extract", production, signature, reference, profileArgument, "--assume-initialized", "Nethermind.Int256.UInt256"]);
    foreach (string fixture in cases.Where(fixture => Applicable(fixture, method, profile, signature)))
    {
        string name = $"{method}/{profile}/{fixture}";
        string extraction = Path.Combine(work, method, profile, fixture);
        await Run("dotnet", [tool, "extract", assemblies[fixture], signature, extraction, profileArgument]);
        bool unchanged = Bodies(extraction) == Bodies(reference);
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
        if (!negatives.ContainsKey(fixture))
        {
            string fixtureProof = Path.Combine(consumer, "Tests/Fixtures/Equality", fixture, $"{method}_{profile.Replace('-', '_')}.lean");
            if (!File.Exists(fixtureProof))
            {
                Console.WriteLine($"PENDING {name}: no fixture proof yet");
                incomplete.Add(name);
                continue;
            }
            if (Statement(fixtureProof, "EqualityFixture.correct") != statement)
                throw new InvalidOperationException($"Fixture proof {fixtureProof} does not state the production contract");
            jobs.Add((name, extraction, fixtureProof, "EqualityFixture.correct", null, null));
            continue;
        }
        string proofPath = Path.Combine(consumer, "proofs", $"EqualityFixture{fixture}{method}{profile.Replace("-", "")}.lean");
        File.WriteAllText(proofPath, Refutation(fixture, signature, statement));
        jobs.Add((name, extraction, proofPath, "EqualityWitness.refuted", productionProof, productionTheorem));
    }
}
// Freeze the complete consumer source snapshot before issuing any certificates.
failed.AddRange(await RegressionBatch.Verify(root, tool, work, consumer, [.. jobs.Select(job => new RegressionCheck(job.Name, job.Extraction, job.Proof, job.Theorem,
    job.Production is null ? "checked production contract" : "checked contract refutation and production proof rejection", job.Production, job.ProductionTheorem))]));
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
