#!/usr/bin/env dotnet
// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT
#:property PublishAot=false

using System.Diagnostics;
using System.Text.Json.Nodes;

string root = Path.GetFullPath(args.Length > 0 ? args[0] : "verification");
string profile = args.Length > 1 ? args[1] : "scalar";
if (args.Length > 2 || profile is not ("scalar" or "x64-vector256"))
    throw new ArgumentException("Usage: ShiftRegression.cs [verification-directory] [scalar|x64-vector256]");
string fixtures = Path.Combine(root, "Tests/Fixtures/Shift");
string work = Path.Combine(root, "artifacts/shift-regressions", profile);
string tool = Path.Combine(root, ".lake/packages/leancil/Extractor/bin/Nethermind.LeanCIL.dll");
string profileArgument = profile == "scalar" ? profile : "@" + Path.Combine(root, "manifests/profiles", profile + ".json");
JsonObject witnesses = JsonNode.Parse(File.ReadAllText(Path.Combine(fixtures, "Witnesses.json")))!["negativeCases"]!.AsObject();
JsonArray targets = JsonNode.Parse(File.ReadAllText(Path.Combine(root, "manifests/targets.json")))!["methods"]!.AsArray();
string[] methods = ["Lsh", "Rsh", "LeftShift", "RightShift", "OperatorLsh", "OperatorRsh"];

async Task<string> Run(string executable, IEnumerable<string> arguments, bool succeeds = true)
{
    ProcessStartInfo start = new(executable) { WorkingDirectory = root, RedirectStandardOutput = true, RedirectStandardError = true, UseShellExecute = false };
    foreach (string argument in arguments) start.ArgumentList.Add(argument);
    using Process process = Process.Start(start) ?? throw new InvalidOperationException("Cannot start " + executable);
    Task<string> stdout = process.StandardOutput.ReadToEndAsync(), stderr = process.StandardError.ReadToEndAsync();
    await process.WaitForExitAsync();
    string output = await stdout + await stderr;
    if ((process.ExitCode == 0) != succeeds) throw new InvalidOperationException(output);
    return output;
}

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
        string proof = Path.Combine(extraction, "Refutation.lean");
        File.WriteAllText(proof, template);
        await Run("dotnet", [tool, "verify", extraction, "--proof", proof, "--theorem", "ShiftWitness.refuted", "--proof-root", root]);
        string suffix = profile == "scalar" ? "Scalar" : "Vector";
        string theorem = "UInt256Proof." + method + "." + suffix.ToLowerInvariant() + "_correctness";
        string rejected = await Run("dotnet", [tool, "verify", extraction, "--proof", Path.Combine(root, "proofs", method + suffix + ".lean"),
            "--theorem", theorem, "--proof-root", root], succeeds: false);
        if (!rejected.Contains("proof checking", StringComparison.OrdinalIgnoreCase) || File.Exists(Path.Combine(extraction, "verified.json")))
            throw new InvalidOperationException("Mutation was not rejected during proof checking or retained a stale certificate: " + rejected);
        Console.WriteLine($"PASS {method}/{profile}/{mutation}: checked full-contract refutation and public proof rejection");
    }
}
