#!/usr/bin/env dotnet
// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT
#:property PublishAot=false
#:include RegressionBatch.cs
#:include VerificationSupport.cs
#:include RegressionManifest.cs

using System.Text.Json.Nodes;

string root = Path.GetFullPath(args.Length > 0 ? args[0] : "verification");
string profile = args.Length > 1 ? args[1] : "scalar";
string[] profiles = RegressionManifest.RequireProfiles(root, "ShiftRegression.cs", ["scalar", "x64-v3"]);
if (args.Length > 2 || !profiles.Contains(profile))
    throw new ArgumentException("Usage: ShiftRegression.cs [verification-directory] [scalar|x64-v3]");
string fixtures = Path.Combine(root, "Tests/Fixtures/Shift");
string work = Path.Combine(root, "artifacts/shift-regressions", profile);
string tool = Path.Combine(root, ".lake/packages/leancil/Extractor/bin/Nethermind.LeanCIL.dll");
string profileArgument = File.Exists(Path.Combine(root, "manifests/profiles", profile + ".json")) ? "@" + Path.Combine(root, "manifests/profiles", profile + ".json") : profile;
JsonObject witnesses = JsonNode.Parse(File.ReadAllText(Path.Combine(fixtures, "Witnesses.json")))!["negativeCases"]!.AsObject();
JsonArray targets = JsonNode.Parse(File.ReadAllText(Path.Combine(root, "manifests/targets.json")))!["methods"]!.AsArray();
string[] methods = ["Lsh", "Rsh", "LeftShift", "RightShift", "OperatorLsh", "OperatorRsh"];

Task<string> Run(string executable, IEnumerable<string> arguments, bool disableIntrinsics = false) =>
    VerificationSupport.RunChecked(root, executable, arguments, disableIntrinsics);

string consumer = Path.Combine(work, "consumer");
Directory.CreateDirectory(consumer);
await VerificationSupport.PrepareConsumer(root, consumer);
List<(string Method, string Mutation, string Extraction, string Proof)> checks = [];
foreach (var pair in witnesses)
{
    string mutation = pair.Key;
    JsonObject witness = pair.Value!.AsObject();
    string build = Path.Combine(work, "build", mutation);
    string output = await Run("dotnet", ["build", Path.Combine(fixtures, "Nethermind.Int256.csproj"), "-c", "Release",
        "-p:FixtureCase=" + mutation, "-p:BaseOutputPath=" + Path.Combine(build, "bin") + Path.DirectorySeparatorChar,
        "-p:BaseIntermediateOutputPath=" + Path.Combine(build, "obj") + Path.DirectorySeparatorChar,
        "-p:EnforceCodeStyleInBuild=true", "-p:GenerateDocumentationFile=true", "-v:q"]);
    if (output.Contains("IDE0005", StringComparison.Ordinal)) throw new InvalidOperationException(output);
    string assembly = Path.Combine(build, "bin/Release/net10.0/Nethermind.Int256.dll");
    foreach (string method in methods)
    {
        bool returned = method.StartsWith("Operator", StringComparison.Ordinal);
        string direction = method is "Lsh" or "LeftShift" or "OperatorLsh" ? "left" : "right";
        if (witness["direction"]!.GetValue<string>() != direction || returned && witness["operatorActual"] is null) continue;
        string extraction = Path.Combine(work, mutation, method);
        string signature = targets.Single(target => target!["id"]!.GetValue<string>() == method)!["signature"]!.GetValue<string>();
        await Run("dotnet", [tool, "extract", assembly, signature, extraction, profileArgument]);
        string template = File.ReadAllText(Path.Combine(fixtures, returned ? "CheckedOperatorRefutationTemplate.lean.in" : "CheckedRefutationTemplate.lean.in"));
        string initialOffset = witness["initialBytes"]!.AsObject().Single().Key;
        string actual = witness["operatorActual"]?.ToString() ?? "0";
        template = template.Replace("@INITIAL_OFFSET@", initialOffset).Replace("@OUTPUT@", witness["outputBase"]!.ToString())
            .Replace("@COUNT@", witness["count"]!.ToString()).Replace("@ACTUAL@", actual).Replace("@DIRECTION@", direction);
        string proof = Path.Combine(consumer, "proofs", $"Regression{mutation}{method}.lean");
        File.WriteAllText(proof, template);
        checks.Add((method, mutation, extraction, proof));
    }
}
string suffix = profile == "scalar" ? "Scalar" : "Vector";
List<string> failed = await RegressionBatch.Verify(root, tool, work, consumer, [.. checks.Select(check => new RegressionCheck($"{check.Method}/{profile}/{check.Mutation}",
    check.Extraction, check.Proof, "ShiftWitness.refuted", "checked full-contract refutation and public proof rejection",
    Path.Combine(consumer, "proofs", check.Method + suffix + ".lean"), "UInt256Proof." + check.Method + "." + suffix.ToLowerInvariant() + "_correctness"))]);
if (failed.Count != 0) throw new InvalidOperationException("FAILED: " + string.Join(", ", failed));
