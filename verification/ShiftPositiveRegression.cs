#!/usr/bin/env dotnet
// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT
#:property PublishAot=false
#:include RegressionBatch.cs
#:include VerificationSupport.cs
#:include ProofBindings.cs

using System.Text.Json.Nodes;

if (args.Length > 2) throw new ArgumentException("Usage: ShiftPositiveRegression.cs [verification-directory] [all|scalar|x64-v3]");
string root = Path.GetFullPath(args.Length > 0 ? args[0] : "verification");
string selection = args.Length > 1 ? args[1] : "all";
string[] profiles = selection switch
{
    "all" => ["scalar", "x64-v3"],
    "scalar" or "x64-v3" => [selection],
    _ => throw new ArgumentException("Unknown profile: " + selection),
};
string fixtures = Path.Combine(root, "Tests/Fixtures/Shift");
string work = Path.Combine(root, "artifacts/shift-positive-regressions");
string consumer = Path.Combine(work, "consumer");
string tool = Path.Combine(root, ".lake/packages/leancil/Extractor/bin/Nethermind.LeanCIL.dll");
JsonArray targets = JsonNode.Parse(File.ReadAllText(Path.Combine(root, "manifests/targets.json")))!["methods"]!.AsArray();
const string fixture = "LshHelper";
string[] methods = ["Lsh", "LeftShift", "OperatorLsh"];

Task<string> Run(string executable, IEnumerable<string> arguments, bool disableIntrinsics = false) =>
    VerificationSupport.RunChecked(root, executable, arguments, disableIntrinsics);

// Freeze the complete consumer source snapshot before issuing any certificates.
await VerificationSupport.PrepareConsumer(root, consumer);

Dictionary<string, string> assemblies = [];
foreach (string variant in new[] { "Baseline", fixture })
{
    string build = Path.Combine(work, "build", variant);
    string intermediate = Path.Combine(build, "obj") + Path.DirectorySeparatorChar;
    await Run("dotnet", ["build", Path.Combine(fixtures, "Nethermind.Int256.csproj"), "-c", "Release", "-p:FixtureCase=" + variant,
        "-p:BaseOutputPath=" + Path.Combine(build, "bin") + Path.DirectorySeparatorChar,
        "-p:BaseIntermediateOutputPath=" + intermediate, "-p:MSBuildProjectExtensionsPath=" + intermediate,
        "-p:EnforceCodeStyleInBuild=true", "-p:GenerateDocumentationFile=true", "-v:q"]);
    assemblies[variant] = Path.Combine(build, "bin/Release/net10.0/Nethermind.Int256.dll");
}

async Task<string> Extract(string variant, string method, string profile)
{
    string extraction = Path.Combine(work, profile, variant, method);
    if (Directory.Exists(extraction)) Directory.Delete(extraction, true);
    string signature = targets.Single(target => target!["id"]!.GetValue<string>() == method)!["signature"]!.GetValue<string>();
    string profileArgument = File.Exists(Path.Combine(root, "manifests/profiles", profile + ".json")) ? "@" + Path.Combine(root, "manifests/profiles", profile + ".json") : profile;
    await Run("dotnet", [tool, "extract", assemblies[variant], signature, extraction, profileArgument]);
    return extraction;
}

// The assembly digest always differs between builds; only the extracted program text decides equivalence.
static string ProgramText(string extraction) => string.Join('\n', File.ReadAllLines(Path.Combine(extraction, "Extracted.lean"))
    .Where(line => !line.StartsWith("def assemblySha256", StringComparison.Ordinal)));

List<string> failed = [], incomplete = [];
List<RegressionCheck> checks = [];
foreach (string profile in profiles)
foreach (string method in methods)
{
    string name = $"{method}/{profile}/{fixture}";
    string log = Path.Combine(work, profile, $"{method}-{fixture}.log");
    Directory.CreateDirectory(Path.GetDirectoryName(log)!);
    string proof = Path.Combine(consumer, "Tests/Fixtures/Shift", fixture, $"{method}_{profile.Replace('-', '_')}.lean");
    if (!File.Exists(proof))
    {
        Console.WriteLine($"PENDING {name}: no fixture proof");
        incomplete.Add(name);
        continue;
    }
    try
    {
        string extraction = await Extract(fixture, method, profile);
        if (ProgramText(await Extract("Baseline", method, profile)) == ProgramText(extraction))
            throw new InvalidOperationException("Fixture extraction does not differ from Baseline: " + extraction);
        checks.Add(new(name, extraction, proof, "UInt256Proof.Shift.Fixture.correctness", "full positive certificate"));
    }
    catch (InvalidOperationException exception)
    {
        File.WriteAllText(log, exception.Message);
        failed.Add(name);
        Console.WriteLine($"FAIL {name}: see {log}");
    }
}
failed.AddRange(await RegressionBatch.Verify(root, tool, work, consumer, checks));
if (incomplete.Count != 0) Console.WriteLine("INCOMPLETE: " + string.Join(", ", incomplete));
if (failed.Count != 0) Console.WriteLine("FAILED: " + string.Join(", ", failed));
Environment.ExitCode = incomplete.Count == 0 && failed.Count == 0 ? 0 : 1;
