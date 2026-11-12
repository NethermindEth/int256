#!/usr/bin/env dotnet
// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT
#:property PublishAot=false
#:include RegressionBatch.cs
#:include VerificationSupport.cs
#:include ProofBindings.cs
using System.Text.Json.Nodes;

if (args.Length > 1) throw new ArgumentException("Usage: AddSubtractRegression.cs [verification-directory]");
string root = Path.GetFullPath(args.Length == 1 ? args[0] : "verification");
// The production proofs follow the production call graph; structurally different fixtures need their own proof.
HashSet<string> production = ["Baseline", "Renamed", "ReversedStore", "ExpandedHardware"];
(string Method, string Operation, string[] Positives)[] groups =
[
    ("Add", "(· + ·)", ["Baseline", "Renamed", "ExtractedHelper", "ExpandedHardware", "ReversedStore"]),
    ("Subtract", "(· - ·)", ["Baseline", "Renamed", "ExtractedHelper"]),
];
RegressionBatch batch = await RegressionBatch.Start(root, "add-subtract-regressions");
foreach (var (method, operation, positives) in groups)
{
    string productionProof = Path.Combine(batch.Consumer, "proofs", method + "Scalar.lean");
    string productionTheorem = $"UInt256Proof.{method}.scalar_correctness";
    string witnessFile = Path.Combine(root, "Tests/Fixtures", method, "witnesses.json");
    JsonArray witnesses = JsonNode.Parse(File.ReadAllText(witnessFile))!.AsArray();
    foreach (string fixture in positives.Concat(witnesses.Select(witness => witness!["case"]!.GetValue<string>())))
    {
        string name = method + "/" + fixture + "/scalar";
        string fixtureProof = Path.Combine(batch.Consumer, "Tests/Fixtures", method, fixture + ".lean");
        JsonNode? witness = witnesses.SingleOrDefault(value => value!["case"]!.GetValue<string>() == fixture);
        if (witness is null && !production.Contains(fixture) && !File.Exists(fixtureProof))
        {
            batch.Pending(method + "/" + fixture, "no fixture proof yet");
            continue;
        }
        string extraction = await batch.Extract(await batch.Build(method, fixture, method + fixture), method, "scalar",
            method + fixture);
        if (witness is not null)
            batch.Checks.Add(new(name, extraction,
                batch.Proof(method + "Fixture" + fixture, batch.ByteRefutation(witness, operation)),
                "FixtureWitness.refuted", "checked contract refutation and production proof rejection",
                productionProof, productionTheorem));
        else if (production.Contains(fixture))
            batch.Checks.Add(new(name, extraction, productionProof, productionTheorem, "checked wrapping contract"));
        else
            batch.Checks.Add(new(name, extraction, fixtureProof, $"UInt256Proof.{method}.Fixture{fixture}.correctness",
                "checked wrapping contract"));
    }
}
await batch.Finish();
