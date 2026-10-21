#!/usr/bin/env dotnet
// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT
#:property PublishAot=false
#:include RegressionBatch.cs
using System.Diagnostics;
using System.Globalization;
using System.Numerics;
using System.Text.Json.Nodes;
using System.Xml.Linq;

const string usage = "Usage: SimdRegression.cs [verification-directory] [--group SIMD|Reporting] [--method M] [--profile P] [--case C]";
string? directory = null;
Dictionary<string, string> filters = [];
for (int i = 0; i < args.Length; i++)
{
    if (args[i] is "--group" or "--method" or "--profile" or "--case" && i + 1 < args.Length) filters[args[i][2..]] = args[++i];
    else if (directory is null && !args[i].StartsWith("--", StringComparison.Ordinal)) directory = args[i];
    else throw new ArgumentException(usage);
}
string root = Path.GetFullPath(directory ?? "verification");
string work = Path.Combine(root, "artifacts/simd-regressions");
string consumer = Path.Combine(work, "consumer");
string tool = Path.Combine(root, ".lake/packages/leancil/Extractor/bin/Nethermind.LeanCIL.dll");
JsonArray targets = JsonNode.Parse(File.ReadAllText(Path.Combine(root, "manifests/targets.json")))!["methods"]!.AsArray();
JsonArray gates = JsonNode.Parse(File.ReadAllText(Path.Combine(root, "manifests/gates.json")))!["gates"]!.AsArray();
JsonArray witnesses = JsonNode.Parse(File.ReadAllText(Path.Combine(root, "Tests/Fixtures/SIMD/witnesses.json")))!.AsArray();
string[] simdProfiles = ["arm64-advsimd", "x64-sse42", "x64-avx2", "x64-avx2-bmi1", "x64-avx512", "x64-avx512-bmi1"];
// Only these positives keep every production method body; other refactors need their own fixture proof.
HashSet<string> productionShaped = ["Baseline", "Renamed"];
(string Group, string Item, (string Method, string Legacy, string Operation, string Flag)[] Methods, string[] Profiles)[] groups =
[
    ("SIMD", "SimdCase", [("Add", "Add", "(· + ·)", ""), ("Subtract", "Subtract", "(· - ·)", "")], simdProfiles),
    ("Reporting", "ReportingCase",
    [
        ("AddOverflow", "Add", "(fun left right => left + right)", "(fun left right => decide (2^256 ≤ left.toNat + right.toNat))"),
        ("SubtractUnderflow", "Subtract", "(fun left right => left - right)", "(fun left right => decide (left.toNat < right.toNat))"),
    ], ["scalar", .. simdProfiles]),
];
List<string> incomplete = [], failed = [];

// Applicability is the original suite's: features each mutation can reach on a profile.
static bool Positive(string name, string profile) => name switch
{
    "Baseline" or "Renamed" => true,
    "EquivalentMask" => profile is "x64-avx2" or "x64-avx2-bmi1",
    _ => false
};
static bool Negative(string name, string method, string profile) => name switch
{
    "WrongAlignment" => profile is "arm64-advsimd" or "x64-sse42",
    "WrongTop" => profile == "arm64-advsimd" || method == "Subtract" && profile == "x64-sse42",
    "WrongBlend" => profile is "x64-avx2" or "x64-avx2-bmi1",
    "WrongAvxAlignment" or "WrongTernary" => profile is "x64-avx512" or "x64-avx512-bmi1",
    _ => profile is "x64-avx2" or "x64-avx2-bmi1" or "x64-avx512" or "x64-avx512-bmi1"
};
bool Selected(string key, string value) => !filters.TryGetValue(key, out string? wanted) || wanted == value;

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

Dictionary<string, string> builds = [];
async Task<string> Build(string group, string fixture)
{
    string key = group + "/" + fixture;
    if (builds.TryGetValue(key, out string? built)) return built;
    string build = Path.Combine(work, "build", group + fixture);
    string intermediate = Path.Combine(build, "obj") + Path.DirectorySeparatorChar;
    await Run("dotnet", ["build", Path.Combine(root, "Tests/Fixtures", group, "Nethermind.Int256.csproj"), "-c", "Release", "-p:FixtureCase=" + fixture,
        "-p:BaseOutputPath=" + Path.Combine(build, "bin") + Path.DirectorySeparatorChar,
        "-p:BaseIntermediateOutputPath=" + intermediate, "-p:MSBuildProjectExtensionsPath=" + intermediate,
        "-p:EnforceCodeStyleInBuild=true", "-p:GenerateDocumentationFile=true", "-v:q"]);
    return builds[key] = Path.Combine(build, "bin/Release/net10.0/Nethermind.Int256.dll");
}
async Task<string> Extract(string group, string fixture, string method, string profile)
{
    string signature = targets.Single(target => target!["id"]!.GetValue<string>() == method)!["signature"]!.GetValue<string>();
    string extraction = Path.Combine(work, group, method, profile, fixture);
    if (Directory.Exists(extraction)) Directory.Delete(extraction, true);
    await Run("dotnet", [tool, "extract", await Build(group, fixture), signature, extraction, profile]);
    return extraction;
}
// The `methodN : Method` bodies are what gate proofs bind; signatures carry the method names.
static (string Code, string Names) ProgramText(string extraction)
{
    List<string> code = [], names = [];
    bool body = false;
    foreach (string line in File.ReadAllLines(Path.Combine(extraction, "Extracted.lean")))
    {
        if (line.StartsWith("def ", StringComparison.Ordinal) || line.StartsWith("theorem ", StringComparison.Ordinal) || line.StartsWith("@[", StringComparison.Ordinal))
            body = System.Text.RegularExpressions.Regex.IsMatch(line, @"^def method\d+ : Method :=");
        if (body) code.Add(line);
        else if (line.Contains("Signature : String", StringComparison.Ordinal)) names.Add(line);
    }
    return (string.Join('\n', code), string.Join('\n', names));
}

static string Bytes(ulong[] left, ulong[] right)
{
    IEnumerable<(int Offset, int Value)> Cells(ulong[] words, int origin) =>
        words.SelectMany((word, limb) => Enumerable.Range(0, 8).Select(i => (origin + 8 * limb + i, (int)((word >> (8 * i)) & 255))));
    return string.Concat(Cells(left, 0).Concat(Cells(right, 64)).Where(cell => cell.Value != 0)
        .Select(cell => $"offset = {cell.Offset} then {cell.Value} else if id = 0 ∧ ")) + "False then 0 else 0";
}
static BigInteger Number(ulong[] words) => words.Select((word, i) => (BigInteger)word << (64 * i)).Aggregate(BigInteger.Zero, (a, b) => a + b);
static ulong[] Words(JsonNode node) => node.AsArray().Select(word => ulong.Parse(word!.GetValue<string>(), CultureInfo.InvariantCulture)).ToArray();

string Refutation(string group, string method, string legacy, string operation, string flag, JsonNode witness)
{
    ulong[] left = Words(witness["left"]!), right = Words(witness["right"]!);
    int output = witness["outputBase"]!.GetValue<int>();
    string inputs = "[⟨0,0⟩,⟨0,64⟩]", outputs = $"[⟨0,{output}⟩]", references = $"⟨0,0⟩ ⟨0,64⟩ ⟨0,{output}⟩";
    string source = File.ReadAllText(Path.Combine(root, "Tests/Fixtures/SIMD/CheckedRefutationTemplate.lean.in"))
        .Replace("@INITIAL@", Bytes(left, right)).Replace("@INPUTS@", inputs).Replace("@OUTPUTS@", outputs)
        .Replace("@INPUT_CASES@", "rcases member with rfl | rfl <;> exact ⟨_, rfl⟩").Replace("@OUTPUT_CASE@", "subst output; rfl")
        .Replace("@REFERENCES@", references)
        .Replace("@CONTRACT@", group == "SIMD" ? "WrappingBinaryContract" : "ReportingBinaryContract")
        .Replace("@ARGUMENTS@", group == "SIMD" ? operation : operation + " " + flag);
    if (witness["flag"] is JsonNode returned)
    {
        BigInteger a = Number(left), b = Number(right);
        int expected = (legacy == "Add" ? a + b >= BigInteger.One << 256 : a < b) ? 1 : 0;
        if (group != "Reporting" || expected == returned.GetValue<int>()) throw new InvalidOperationException("Flag witness fails to distinguish full contract");
        return source.Replace("@LEMMA@", "checked_reporting_flag_refuted").Replace("@WITNESS@", $"[.scalar (.i32 {returned.GetValue<int>()})]");
    }
    BigInteger modulus = BigInteger.One << 256;
    BigInteger value = ((legacy == "Add" ? Number(left) + Number(right) : Number(left) - Number(right)) % modulus + modulus) % modulus;
    int index = witness["address"]!.GetValue<int>() - output, actual = witness["actualByte"]!.GetValue<int>();
    if ((int)((value >> (8 * index)) & 255) == actual) throw new InvalidOperationException("Byte witness fails to distinguish full contract");
    return source.Replace("@LEMMA@", group == "SIMD" ? "checked_binary_byte_refuted" : "checked_reporting_byte_refuted")
        .Replace("@WITNESS@", $"{index} {actual}");
}

List<(string Name, string Extraction, string Proof, string Theorem, Gate? Production)> jobs = [];
foreach (var (group, item, methods, profiles) in groups)
{
    if (!Selected("group", group)) continue;
    XElement[] registry = XDocument.Load(Path.Combine(root, "Tests/Fixtures", group, "Cases.props")).Descendants(item).ToArray();
    foreach (var (method, legacy, operation, flag) in methods)
    foreach (string profile in profiles)
    {
        if (!Selected("method", method) || !Selected("profile", profile)) continue;
        List<(string Case, bool Negative)> cases = [];
        foreach (XElement entry in registry)
        {
            string name = (string)entry.Attribute("Include")!;
            bool negative = (string?)entry.Attribute("Suite") == "negative";
            bool applies = group == "SIMD"
                ? negative ? Negative(name, legacy, profile) : Positive(name, profile)
                : negative ? name == "WrongFlag" || Negative(name, legacy, profile) : Positive(name, profile);
            if (applies && Selected("case", name)) cases.Add((name, negative));
        }
        if (cases.Count == 0) continue;
        string prefix = $"{group}/{method}/{profile}";
        Gate? gate = gates.Where(node => node!["method"]!.GetValue<string>() == method && node["profile"]!.GetValue<string>() == profile)
            .Select(node => new Gate(Path.Combine(consumer, node!["proof"]!.GetValue<string>()), node["theorem"]!.GetValue<string>())).SingleOrDefault();
        if (gate is null)
        {
            foreach (var (name, _) in cases) incomplete.Add($"{prefix}/{name}");
            Console.WriteLine($"PENDING {prefix}: no production gate yet ({string.Join(", ", cases.Select(entry => entry.Case))})");
            continue;
        }
        var baseline = ProgramText(await Extract(group, "Baseline", method, profile));
        foreach (var (name, negative) in cases)
        {
            string label = $"{prefix}/{name}";
            string fixtureProof = Path.Combine(consumer, "Tests/Fixtures", group, $"{method}_{profile.Replace('-', '_')}_{name}.lean");
            JsonNode? witness = witnesses.SingleOrDefault(value => value!["case"]!.GetValue<string>() == name && value["method"]!.GetValue<string>() == legacy);
            if (negative ? witness is null : !productionShaped.Contains(name) && !File.Exists(fixtureProof))
            {
                Console.WriteLine($"PENDING {label}: " + (negative ? "no checked witness yet" : "structurally different; no fixture proof yet"));
                incomplete.Add(label);
                continue;
            }
            string extraction = name == "Baseline" ? Path.Combine(work, group, method, profile, "Baseline") : await Extract(group, name, method, profile);
            var program = ProgramText(extraction);
            // A fixture that leaves the extracted program unchanged would certify nothing new.
            bool changed = name == "Renamed" ? program.Names != baseline.Names && program.Code == baseline.Code : program.Code != baseline.Code;
            if (name != "Baseline" && !changed)
            {
                Console.WriteLine($"FAIL {label}: the fixture did not make its targeted change to the extracted program");
                failed.Add(label);
                continue;
            }
            if (!negative)
            {
                jobs.Add(productionShaped.Contains(name) ? (label, extraction, gate.Proof, gate.Theorem, null)
                    : (label, extraction, fixtureProof, $"UInt256Proof.Fixture.{group}.{method}_{profile.Replace('-', '_')}_{name}.correctness", null));
                continue;
            }
            string proofPath = Path.Combine(consumer, "proofs", $"{group}Fixture_{method}_{profile.Replace('-', '_')}_{name}.lean");
            File.WriteAllText(proofPath, Refutation(group, method, legacy, operation, flag, witness!));
            jobs.Add((label, extraction, proofPath, "FixtureWitness.refuted", gate));
        }
    }
}
// The consumer snapshot is complete before any certificate is issued.
failed.AddRange(await RegressionBatch.Verify(root, tool, work, consumer, [.. jobs.Select(job => new RegressionCheck(job.Name, job.Extraction, job.Proof, job.Theorem,
    job.Production is null ? "checked production contract" : "checked contract refutation and production proof rejection", job.Production?.Proof, job.Production?.Theorem))]));
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

internal sealed record Gate(string Proof, string Theorem);
