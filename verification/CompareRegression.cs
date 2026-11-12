#!/usr/bin/env dotnet
// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT
#:property PublishAot=false
#:include RegressionBatch.cs
#:include VerificationSupport.cs
#:include ProofBindings.cs
using System.Globalization;
using System.Numerics;
using System.Text.Json.Nodes;
using System.Xml.Linq;

string[] profiles = ["scalar", "x64-v3", "x64-v4"];
string usage = "Usage: CompareRegression.cs [verification-directory] [all|" + string.Join('|', profiles) + "]";
if (args.Length > 2) throw new ArgumentException(usage);
string root = Path.GetFullPath(args.Length > 0 ? args[0] : "verification");
string selected = args.Length > 1 ? args[1] : "all";
if (selected != "all" && !profiles.Contains(selected)) throw new ArgumentException(usage);
string fixtures = Path.Combine(root, "Tests/Fixtures/Compare");
JsonObject witnesses = JsonNode.Parse(File.ReadAllText(Path.Combine(fixtures, "witnesses.json")))!.AsObject();
JsonObject positives = witnesses["positiveCases"]!.AsObject(), negatives = witnesses["negativeCases"]!.AsObject();
string[] cases = XDocument.Load(Path.Combine(fixtures, "Cases.props")).Descendants("CompareCase").Select(item => (string)item.Attribute("Include")!).ToArray();
string[] methods = ["LtUInt256UInt256", "CompareToUInt256Ref"];
// A case reaches a profile only where its witness entry says so; elsewhere the extraction must stay unchanged.
bool Applicable(string fixture, string method, string profile)
{
    if (fixture == "Baseline") return true;
    JsonObject entry = (positives[fixture] ?? negatives[fixture])?.AsObject() ?? throw new InvalidOperationException("Case without witness entry: " + fixture);
    return entry["method"]!.GetValue<string>() == method && entry["profiles"]!.AsArray().Any(item => item!.GetValue<string>() == profile);
}

static string Word(int value) => value < 0 ? $"(BitVec.ofInt 32 ({value}))" : value.ToString(CultureInfo.InvariantCulture);

string Refutation(string fixture, string method, string statement)
{
    JsonObject data = negatives[fixture]!.AsObject();
    JsonObject initial = data["initialBytes"]!.AsObject();
    int left = data["leftBase"]!.GetValue<int>(), right = data["rightBase"]!.GetValue<int>(), actual = data["actualResult"]!.GetValue<int>();
    BigInteger leftValue = RegressionBatch.Number(initial, left), rightValue = RegressionBatch.Number(initial, right);
    int expected = method == "CompareToUInt256Ref" ? leftValue.CompareTo(rightValue) : leftValue < rightValue ? 1 : 0;
    if (actual == expected) throw new InvalidOperationException($"{fixture} witness does not contradict the contract for {method}");
    if (!statement.StartsWith("UInt256Model.Safety.ReadOnlyContract ", StringComparison.Ordinal))
        throw new InvalidOperationException($"Unexpected production contract for {method}: {statement}");
    return File.ReadAllText(Path.Combine(fixtures, "RefutationTemplate.lean.in"))
        .Replace("@INITIAL@", RegressionBatch.InitialBytes(initial))
        .Replace("@INPUTS@", $"[⟨0,{left}⟩,⟨0,{right}⟩]")
        .Replace("@INPUT_CASES@", "rcases member with rfl | rfl <;> exact ⟨_, rfl⟩")
        .Replace("@STATEMENT@", statement)
        .Replace("@LEMMA@", $"checked_readonly_refuted _ Extracted.program _ 2 1024 memory [⟨0,{left}⟩, ⟨0,{right}⟩] [.scalar (.i32 {Word(actual)})] rfl call");
}

RegressionBatch batch = await RegressionBatch.Start(root, "compare-regressions/" + selected);
Dictionary<string, string> assemblies = [];
foreach (string fixture in cases) assemblies[fixture] = await batch.Build("Compare", fixture);
foreach (Gate gate in VerificationSupport.Gates(root))
{
    string method = gate.Method, profile = gate.Profile;
    if (!methods.Contains(method) || !profiles.Contains(profile) || selected != "all" && selected != profile) continue;
    Gate production = gate with { Proof = Path.Combine(batch.Consumer, gate.Proof) };
    string statement = RegressionBatch.Statement(production.Proof, production.Theorem);
    string reference = await batch.ExtractProduction(method, profile);
    foreach (string fixture in cases)
    {
        string extraction = await batch.Extract(assemblies[fixture], method, profile,
            Path.Combine(method, profile, fixture));
        bool unchanged = RegressionBatch.Bodies(extraction) == RegressionBatch.Bodies(reference);
        if (!Applicable(fixture, method, profile))
        {
            const string reached = "mutation reaches a profile its witness entry does not cover";
            if (!unchanged) batch.Fail($"{method}/{profile}/{fixture}", reached);
            continue;
        }
        string fixtureProof = Path.Combine(batch.Consumer, "Tests/Fixtures/Compare", fixture,
            fixture == "ComparisonAlternative" ? method + ".lean" : $"{method}_{profile.Replace('-', '_')}.lean");
        batch.GateFixture("Compare", production, statement, fixture, extraction, unchanged,
            positives.ContainsKey(fixture) ? fixtureProof : null, () => Refutation(fixture, method, statement));
    }
}
await batch.Finish(summary: true);
