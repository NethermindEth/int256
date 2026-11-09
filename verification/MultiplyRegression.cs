#!/usr/bin/env dotnet
// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT
#:property PublishAot=false
#:include RegressionBatch.cs
#:include VerificationSupport.cs
using System.Text.Json.Nodes;

if (args.Length > 1) throw new ArgumentException("Usage: MultiplyRegression.cs [verification-directory]");
string root = Path.GetFullPath(args.Length == 1 ? args[0] : "verification");
string fixtures = Path.Combine(root, "Tests/Fixtures/Multiply");
string work = Path.Combine(root, "artifacts/multiply-regressions");
string consumer = Path.Combine(work, "consumer");
string tool = Path.Combine(root, ".lake/packages/leancil/Extractor/bin/Nethermind.LeanCIL.dll");
JsonArray targets = JsonNode.Parse(File.ReadAllText(Path.Combine(root, "manifests/targets.json")))!["methods"]!.AsArray();
string signature = targets.Single(target => target!["id"]!.GetValue<string>() == "Multiply")!["signature"]!.GetValue<string>();
JsonArray witnesses = JsonNode.Parse(File.ReadAllText(Path.Combine(fixtures, "witnesses.json")))!.AsArray();

Task<string> Run(string executable, IEnumerable<string> arguments, bool disableIntrinsics = false) =>
    VerificationSupport.RunChecked(root, executable, arguments, disableIntrinsics);

await VerificationSupport.PrepareConsumer(root, consumer);
List<(string Fixture, string Profile, string Extraction, string Proof, string Theorem, bool Negative)> jobs = [];
foreach (string fixture in new[] { "Baseline", "AlternativeOrder", "WrongCarry", "WrongCrossProduct", "WrongHighLow", "WrongAliasing", "WrongBmiHigh" })
{
    string profile = fixture == "WrongBmiHigh" ? "x64-v3" : "scalar";
    string profileArgument = File.Exists(Path.Combine(root, "manifests/profiles", profile + ".json"))
        ? "@" + Path.Combine(root, "manifests/profiles", profile + ".json") : profile;
    string build = Path.Combine(work, "build", fixture);
    string intermediate = Path.Combine(build, "obj") + Path.DirectorySeparatorChar;
    await Run("dotnet", ["build", Path.Combine(fixtures, "Nethermind.Int256.csproj"), "-c", "Release", "-p:FixtureCase=" + fixture,
        "-p:BaseOutputPath=" + Path.Combine(build, "bin") + Path.DirectorySeparatorChar,
        "-p:BaseIntermediateOutputPath=" + intermediate, "-p:MSBuildProjectExtensionsPath=" + intermediate,
        "-p:EnforceCodeStyleInBuild=true", "-p:GenerateDocumentationFile=true", "-v:q"]);
    string extraction = Path.Combine(work, fixture);
    await Run("dotnet", [tool, "extract", Path.Combine(build, "bin/Release/net10.0/Nethermind.Int256.dll"), signature, extraction, profileArgument]);
    JsonNode? witness = witnesses.SingleOrDefault(value => value!["case"]!.GetValue<string>() == fixture);
    if (witness is null)
    {
        string proof = fixture == "Baseline" ? Path.Combine(consumer, "proofs/MultiplyProfile.lean") : Path.Combine(consumer, "Tests/Fixtures/Multiply", fixture + ".lean");
        string theorem = fixture == "Baseline" ? "UInt256Proof.Multiply.profile_correctness" : "UInt256Proof.Multiply.FixtureAlternative.correctness";
        jobs.Add((fixture, profile, extraction, proof, theorem, false));
        continue;
    }
    int left = witness["leftBase"]!.GetValue<int>(), right = witness["rightBase"]!.GetValue<int>(), outputBase = witness["outputBase"]!.GetValue<int>();
    string initial = string.Concat(witness["initialBytes"]!.AsObject().Select(pair => $"offset = {pair.Key} then {pair.Value!.GetValue<int>()} else if id = 0 ∧ ")) + "False then 0 else 0";
    string refutation = File.ReadAllText(Path.Combine(root, "Tests/Fixtures/Common/CheckedRefutationTemplate.lean.in"))
        .Replace("@INITIAL@", initial).Replace("@INPUTS@", $"[⟨0,{left}⟩,⟨0,{right}⟩]").Replace("@OUTPUTS@", $"[⟨0,{outputBase}⟩]")
        .Replace("@INPUT_CASES@", "rcases member with rfl | rfl <;> exact ⟨_, rfl⟩").Replace("@OUTPUT_CASE@", "subst output; rfl")
        .Replace("@CONTRACT@", "WrappingBinaryContract").Replace("@OPERATION@", "(· * ·)")
        .Replace("@REFERENCES@", $"⟨0,{left}⟩ ⟨0,{right}⟩ ⟨0,{outputBase}⟩")
        .Replace("@BYTE_INDEX@", (witness["address"]!.GetValue<int>() - outputBase).ToString(System.Globalization.CultureInfo.InvariantCulture))
        .Replace("@ACTUAL@", witness["actualByte"]!.GetValue<int>().ToString(System.Globalization.CultureInfo.InvariantCulture));
    string proofPath = Path.Combine(consumer, "proofs", "MultiplyFixture" + fixture + ".lean");
    File.WriteAllText(proofPath, refutation);
    jobs.Add((fixture, profile, extraction, proofPath, "FixtureWitness.refuted", true));
}
// Freeze the complete consumer source snapshot before issuing any certificates.
List<string> failed = await RegressionBatch.Verify(root, tool, work, consumer, [.. jobs.Select(job => new RegressionCheck(job.Fixture + "/" + job.Profile, job.Extraction, job.Proof, job.Theorem,
    job.Negative ? "checked contract refutation and production proof rejection" : "checked multiplication contract",
    job.Negative ? Path.Combine(consumer, "proofs/MultiplyProfile.lean") : null,
    job.Negative ? "UInt256Proof.Multiply.profile_correctness" : null))]);
if (failed.Count != 0) throw new InvalidOperationException("FAILED: " + string.Join(", ", failed));
