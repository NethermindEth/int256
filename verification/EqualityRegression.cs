#!/usr/bin/env dotnet
// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT
#:property PublishAot=false
#:include RegressionBatch.cs
#:include VerificationSupport.cs
#:include ProofBindings.cs
#:include RegressionManifest.cs
#:include EqualityCoverage.cs
using System.Globalization;
using System.Numerics;
using System.Text.Json.Nodes;
using System.Text.RegularExpressions;
using System.Xml.Linq;

const string Usage = "Usage: EqualityRegression.cs [verification-directory] [all|<profile>] [all|<case>] [method]";
if (args.Length > 4) throw new ArgumentException(Usage);
string root = Path.GetFullPath(args.Length > 0 ? args[0] : "verification");
string selected = args.Length > 1 ? args[1] : "all", selectedCase = args.Length > 2 ? args[2] : "all";
var selectedMethod = args.Length > 3 ? args[3] : null;
if (selectedMethod is not null && !EqualityCoverage.Helpers.ContainsKey(selectedMethod))
    throw new ArgumentException("Unknown equality method: " + selectedMethod);
string fixtures = Path.Combine(root, "Tests/Fixtures/Equality");
Gate[] gates = VerificationSupport.Gates(root);
// Every equality gate profile has fixtures, so the manifest must list exactly those profiles.
string[] profiles = RegressionManifest.RequireProfiles(root, "EqualityRegression.cs",
    gates.Where(gate => Regex.IsMatch(gate.Method, "^(Eq|Ne)")).Select(gate => gate.Profile));
if (selected != "all" && !profiles.Contains(selected)) throw new ArgumentException(Usage + " with a profile from " + string.Join(", ", profiles));
JsonObject negatives = JsonNode.Parse(File.ReadAllText(Path.Combine(fixtures, "witnesses.json")))!["negativeCases"]!.AsObject();
string[] cases = XDocument.Load(Path.Combine(fixtures, "Cases.props")).Descendants("EqualityCase").Select(item => (string)item.Attribute("Include")!).ToArray();
if (selectedCase != "all" && !cases.Contains(selectedCase)) throw new ArgumentException(Usage);
if (selectedCase != "all") cases = [selectedCase];
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

string Refutation(string fixture, string signature, string statement)
{
    var shape = Shape(signature);
    JsonObject data = negatives[fixture]!.DeepClone().AsObject();
    if (data["widths"] is JsonObject widths)
        foreach (var pair in widths[shape.Width.ToString(CultureInfo.InvariantCulture)]!.AsObject()) data[pair.Key] = pair.Value?.DeepClone();
    JsonObject initial = data["initialBytes"]!.AsObject();
    int left = data["leftBase"]!.GetValue<int>(), right = data["rightBase"]!.GetValue<int>();
    BigInteger leftValue = RegressionBatch.Number(initial, left), rightValue = RegressionBatch.Number(initial, right);
    BigInteger snapshot = data["snapshot"] is JsonNode value ? BigInteger.Parse(value.ToString(), CultureInfo.InvariantCulture) : rightValue;
    BigInteger bits = data["scalarBits"] is JsonNode scalarBits ? BigInteger.Parse(scalarBits.ToString(), CultureInfo.InvariantCulture) : 0;
    BigInteger scalar = shape.Signed && bits >= BigInteger.One << (shape.Width - 1) ? bits - (BigInteger.One << shape.Width) : bits;
    bool equal = shape.Kind switch { "scalar" => leftValue == scalar, "snapshot" => leftValue == snapshot, _ => leftValue == rightValue };
    bool expected = equal != shape.Negate;
    bool actual = data["actualResult"]?.GetValue<bool>() ?? data["actualEquality"]!.GetValue<bool>() != shape.Negate;
    if (actual == expected) throw new InvalidOperationException($"{fixture} witness does not contradict the contract for {signature}");
    string observed = $"[.scalar (.i32 {(actual ? 1 : 0)})]";
    var fuel = fixture == "WrongPolarity" ? "fuel" : "1024";
    var observation = "";
    var observedProof = "rfl";
    if (fixture == "WrongPolarity")
    {
        var reference = $"(.reference (.address ⟨0,{left}⟩))";
        var other = shape.Kind == "reference" ? $"(.reference (.address ⟨0,{right}⟩))"
            : $"(.scalar (.i{shape.Width} (BitVec.ofNat {shape.Width} {bits})))";
        var first = shape.ScalarFirst ? other : reference;
        var second = shape.ScalarFirst ? reference : other;
        // The mutated wrapper forwards without negation. Its complete body must still match.
        observation = $"""
              obtain ⟨fuel, final, observed⟩ := UInt256Proof.Equality.WrapperObservation.forward
                Extracted.profile {shape.ScalarFirst.ToString().ToLowerInvariant()} false {actual.ToString().ToLowerInvariant()}
                Extracted.program 0 1 1024 (by rfl) memory {first} {second}
                (by rfl) (by rfl) (by rfl) (by rfl) ⟨_, by rfl⟩
            """;
        observedProof = "simpa [Extracted.entryIndex, Except.map, scalarOperatorArguments, " +
            "scalarArguments, readOnlyArguments] " +
            "using congrArg (fun result => result.map Prod.snd) observed";
    }
    (string head, string lemma) = shape.Kind switch
    {
        "reference" => ("UInt256Model.Safety.ReadOnlyContract",
            $"checked_readonly_refuted _ Extracted.program _ 2 {fuel} memory [⟨0,{left}⟩, ⟨0,{right}⟩] {observed} rfl call"),
        "snapshot" => ("UInt256Model.Safety.ReadOnlyScalarContract",
            $"checked_readonly_scalar_refuted _ _ Extracted.program _ {fuel} memory ⟨0,{left}⟩ (BitVec.ofNat 256 {snapshot}) {observed} call"),
        _ => ("UInt256Model.Safety.ScalarOperatorContract",
            $"checked_scalar_operator_refuted _ _ _ _ Extracted.program _ {fuel} memory ⟨0,{left}⟩ (BitVec.ofNat {shape.Width} {bits}) {observed} call")
    };
    if (!statement.StartsWith(head + " ", StringComparison.Ordinal)) throw new InvalidOperationException($"Unexpected production contract for {signature}: {statement}");
    return File.ReadAllText(Path.Combine(fixtures, "RefutationTemplate.lean.in"))
        .Replace("@IMPORTS@", fixture == "WrongPolarity"
            ? "import UInt256.Methods.Equality.WrapperObservation"
            : shape.Kind == "snapshot" ? "import UInt256.Methods.Equality.ValueScalar" : "")
        .Replace("@INITIAL@", RegressionBatch.InitialBytes(initial))
        .Replace("@INPUTS@", shape.Kind == "reference" ? $"[⟨0,{left}⟩,⟨0,{right}⟩]" : $"[⟨0,{left}⟩]")
        .Replace("@INPUT_CASES@", shape.Kind == "reference" ? "rcases member with rfl | rfl <;> exact ⟨_, rfl⟩" : "subst input; exact ⟨_, rfl⟩")
        .Replace("@STATEMENT@", statement).Replace("@LEMMA@", lemma)
        .Replace("@OBSERVATION@", observation).Replace("@OBSERVED_PROOF@", observedProof);
}

RegressionBatch batch = await RegressionBatch.Start(root,
    "equality-regressions/" + (selectedCase == "all" ? selected : selected + "-" + selectedCase));
Dictionary<string, string> assemblies = [];
foreach (string fixture in cases) assemblies[fixture] = await batch.Build("Equality", fixture);
foreach (Gate gate in gates)
{
    string method = gate.Method, profile = gate.Profile;
    if (!Regex.IsMatch(method, "^(Eq|Ne)") || selected != "all" && selected != profile) continue;
    if (!EqualityCoverage.Helpers.ContainsKey(method))
        throw new InvalidOperationException("Equality overload needs a coverage mapping: " + method);
    if (selectedMethod is not null && method != selectedMethod) continue;
    var selectedFixtures = cases.Where(fixture => EqualityCoverage.Applicable(fixture, method, profile) &&
        EqualityCoverage.Representative(fixture, method) == method).ToArray();
    if (selectedFixtures.Length == 0) continue;
    Gate production = gate with { Proof = Path.Combine(batch.Consumer, gate.Proof) };
    string statement = RegressionBatch.Statement(production.Proof, production.Theorem);
    string reference = await batch.ExtractProduction(method, profile);
    foreach (string fixture in selectedFixtures)
    {
        string extraction = await batch.Extract(assemblies[fixture], method, profile,
            Path.Combine(method, profile, fixture));
        string? fixtureProof = negatives.ContainsKey(fixture) ? null : Path.Combine(batch.Consumer,
            "Tests/Fixtures/Equality", fixture, $"{method}_{profile.Replace('-', '_')}.lean");
        batch.GateFixture("Equality", production, statement, fixture, extraction,
            RegressionBatch.Bodies(extraction) == RegressionBatch.Bodies(reference), fixtureProof,
            () => Refutation(fixture, VerificationSupport.Signature(root, method), statement));
    }
}
if (batch.Checks.Count == 0) throw new InvalidOperationException("No representative equality checks selected");
await batch.Finish(summary: true);
