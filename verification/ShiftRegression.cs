#!/usr/bin/env dotnet
// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT
#:property PublishAot=false
#:include RegressionBatch.cs
#:include VerificationSupport.cs
#:include ProofBindings.cs
#:include RegressionManifest.cs

using System.Text.Json.Nodes;

string root = Path.GetFullPath(args.Length > 0 ? args[0] : "verification");
string profile = args.Length > 1 ? args[1] : "scalar";
string[] profiles = RegressionManifest.RequireProfiles(root, "ShiftRegression.cs", ["scalar", "x64-v3"]);
if (args.Length > 2 || !profiles.Contains(profile))
    throw new ArgumentException("Usage: ShiftRegression.cs [verification-directory] [scalar|x64-v3]");
string fixtures = Path.Combine(root, "Tests/Fixtures/Shift");
JsonObject witnesses = JsonNode.Parse(File.ReadAllText(Path.Combine(fixtures, "Witnesses.json")))!["negativeCases"]!.AsObject();
string[] methods = ["Lsh", "Rsh", "LeftShift", "RightShift", "OperatorLsh", "OperatorRsh"];
string suffix = profile == "scalar" ? "Scalar" : "Vector";
RegressionBatch batch = await RegressionBatch.Start(root, "shift-regressions/" + profile);
foreach (var pair in witnesses)
{
    string mutation = pair.Key;
    JsonObject witness = pair.Value!.AsObject();
    string assembly = await batch.Build("Shift", mutation);
    foreach (string method in methods)
    {
        bool returned = method.StartsWith("Operator", StringComparison.Ordinal);
        string direction = method is "Lsh" or "LeftShift" or "OperatorLsh" ? "left" : "right";
        if (witness["direction"]!.GetValue<string>() != direction || returned && witness["operatorActual"] is null) continue;
        string extraction = await batch.Extract(assembly, method, profile, Path.Combine(mutation, method));
        string template = File.ReadAllText(Path.Combine(fixtures, returned ? "CheckedOperatorRefutationTemplate.lean.in" : "CheckedRefutationTemplate.lean.in"));
        string initialOffset = witness["initialBytes"]!.AsObject().Single().Key;
        string actual = witness["operatorActual"]?.ToString() ?? "0";
        template = template.Replace("@INITIAL_OFFSET@", initialOffset).Replace("@OUTPUT@", witness["outputBase"]!.ToString())
            .Replace("@COUNT@", witness["count"]!.ToString()).Replace("@ACTUAL@", actual).Replace("@DIRECTION@", direction);
        batch.Checks.Add(new($"{method}/{profile}/{mutation}", extraction,
            batch.Proof($"Regression{mutation}{method}", template), "ShiftWitness.refuted",
            "checked full-contract refutation and public proof rejection",
            Path.Combine(batch.Consumer, "proofs", method + suffix + ".lean"),
            "UInt256Proof." + method + "." + suffix.ToLowerInvariant() + "_correctness"));
    }
}
await batch.FinishOrThrow();
