#!/usr/bin/env dotnet
// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT
#:property PublishAot=false
#:include RegressionBatch.cs
#:include VerificationSupport.cs
#:include ProofBindings.cs
#:include RegressionManifest.cs
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
JsonArray witnesses = JsonNode.Parse(File.ReadAllText(Path.Combine(root, "Tests/Fixtures/SIMD/witnesses.json")))!.AsArray();
string[] simdProfiles = ["arm64-advsimd", "x64-sse42", "x64-v3", "x64-v4"];
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
string[] supported = RegressionManifest.RequireProfiles(root, "SimdRegression.cs", groups.SelectMany(group => group.Profiles));
if (filters.TryGetValue("profile", out string? filtered) && !supported.Contains(filtered))
    throw new ArgumentException($"Unknown profile {filtered}; expected one of {string.Join(", ", supported)}");

// Applicability is the original suite's: features each mutation can reach on a profile.
static bool Positive(string name, string profile) => name switch
{
    "Baseline" or "Renamed" => true,
    "EquivalentMask" => profile == "x64-v3",
    _ => false
};
static bool Negative(string name, string method, string profile) => name switch
{
    "WrongArgumentOrder" => method == "Subtract",
    "WrongAlignment" => profile is "arm64-advsimd" or "x64-sse42",
    "WrongTop" => profile == "arm64-advsimd" || method == "Subtract" && profile == "x64-sse42",
    "WrongBlend" => profile == "x64-v3",
    "WrongAvxAlignment" or "WrongTernary" => profile == "x64-v4",
    _ => profile is "x64-v3" or "x64-v4"
};
bool Selected(string key, string value) => !filters.TryGetValue(key, out string? wanted) || wanted == value;

RegressionBatch batch = await RegressionBatch.Start(root, "simd-regressions");
Gate[] gates = VerificationSupport.Gates(root);
Dictionary<string, string> builds = [];
async Task<string> Extract(string group, string fixture, string method, string profile)
{
    if (!builds.TryGetValue(group + "/" + fixture, out string? assembly))
        builds[group + "/" + fixture] = assembly = await batch.Build(group, fixture, group + fixture);
    return await batch.Extract(assembly, method, profile, Path.Combine(group, method, profile, fixture), fresh: true);
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
    return RegressionBatch.InitialBytes(Cells(left, 0).Concat(Cells(right, 64)).Where(cell => cell.Value != 0));
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
        Gate? gate = gates.SingleOrDefault(gate => gate.Method == method && gate.Profile == profile);
        if (gate is null)
        {
            foreach (var (name, _) in cases) batch.Incomplete.Add($"{prefix}/{name}");
            Console.WriteLine($"PENDING {prefix}: no production gate yet ({string.Join(", ", cases.Select(entry => entry.Case))})");
            continue;
        }
        string production = Path.Combine(batch.Consumer, gate.Proof), profileName = profile.Replace('-', '_');
        var baseline = ProgramText(await Extract(group, "Baseline", method, profile));
        foreach (var (name, negative) in cases)
        {
            string label = $"{prefix}/{name}";
            string fixtureProof = Path.Combine(batch.Consumer, "Tests/Fixtures", group,
                $"{method}_{profileName}_{name}.lean");
            JsonNode? witness = witnesses.SingleOrDefault(value => value!["case"]!.GetValue<string>() == name && value["method"]!.GetValue<string>() == legacy);
            if (negative ? witness is null : !productionShaped.Contains(name) && !File.Exists(fixtureProof))
            {
                batch.Pending(label,
                    negative ? "no checked witness yet" : "structurally different; no fixture proof yet");
                continue;
            }
            string extraction = name == "Baseline" ? Path.Combine(batch.Work, group, method, profile, "Baseline")
                : await Extract(group, name, method, profile);
            var program = ProgramText(extraction);
            // A fixture that leaves the extracted program unchanged would certify nothing new.
            bool changed = name == "Renamed" ? program.Names != baseline.Names && program.Code == baseline.Code : program.Code != baseline.Code;
            if (name != "Baseline" && !changed)
            {
                batch.Fail(label, "the fixture did not make its targeted change to the extracted program");
                continue;
            }
            if (negative)
                batch.Checks.Add(new(label, extraction, batch.Proof($"{group}Fixture_{method}_{profileName}_{name}",
                    Refutation(group, method, legacy, operation, flag, witness!)), "FixtureWitness.refuted",
                    "checked contract refutation and production proof rejection", production, gate.Theorem));
            else if (productionShaped.Contains(name))
                batch.Checks.Add(new(label, extraction, production, gate.Theorem, "checked production contract"));
            else
                batch.Checks.Add(new(label, extraction, fixtureProof,
                    $"UInt256Proof.Fixture.{group}.{method}_{profileName}_{name}.correctness",
                    "checked production contract"));
        }
    }
}
// A mistyped CI shard filter must not pass by checking nothing.
if (batch.Checks.Count == 0) throw new ArgumentException("No regression check matches the filters. " + usage);
await batch.Finish();
