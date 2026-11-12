#!/usr/bin/env dotnet
// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT
#:property PublishAot=false
#:include RegressionBatch.cs
#:include VerificationSupport.cs
#:include ProofBindings.cs
using System.Text.Json.Nodes;

if (args.Length > 1) throw new ArgumentException("Usage: MultiplyRegression.cs [verification-directory]");
string root = Path.GetFullPath(args.Length == 1 ? args[0] : "verification");
string witnessFile = Path.Combine(root, "Tests/Fixtures/Multiply/witnesses.json");
JsonArray witnesses = JsonNode.Parse(File.ReadAllText(witnessFile))!.AsArray();
RegressionBatch batch = await RegressionBatch.Start(root, "multiply-regressions");
string production = Path.Combine(batch.Consumer, "proofs/MultiplyProfile.lean");
const string productionTheorem = "UInt256Proof.Multiply.profile_correctness";
foreach (string fixture in new[] { "Baseline", "AlternativeOrder", "WrongCarry", "WrongCrossProduct", "WrongHighLow", "WrongAliasing", "WrongBmiHigh" })
{
    string profile = fixture == "WrongBmiHigh" ? "x64-v3" : "scalar", name = fixture + "/" + profile;
    string extraction = await batch.Extract(await batch.Build("Multiply", fixture), "Multiply", profile, fixture);
    JsonNode? witness = witnesses.SingleOrDefault(value => value!["case"]!.GetValue<string>() == fixture);
    if (witness is not null)
        batch.Checks.Add(new(name, extraction,
            batch.Proof("MultiplyFixture" + fixture, batch.ByteRefutation(witness, "(· * ·)")),
            "FixtureWitness.refuted", "checked contract refutation and production proof rejection",
            production, productionTheorem));
    else if (fixture == "Baseline")
        batch.Checks.Add(new(name, extraction, production, productionTheorem, "checked multiplication contract"));
    else
        batch.Checks.Add(new(name, extraction,
            Path.Combine(batch.Consumer, "Tests/Fixtures/Multiply", fixture + ".lean"),
            "UInt256Proof.Multiply.FixtureAlternative.correctness", "checked multiplication contract"));
}
await batch.FinishOrThrow();
