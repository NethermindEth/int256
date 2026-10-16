#!/usr/bin/env dotnet
// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT
#:property PublishAot=false
using System.Diagnostics;
using System.Text.Json.Nodes;

string root = Path.GetFullPath(args.Length > 0 ? args[0] : "verification");
string fixtures = Path.Combine(root, "Tests/Fixtures/Bitwise");
string profile = args.Length > 1 ? args[1] : "scalar";
if (args.Length > 2 || profile is not ("scalar" or "x64-vector256"))
    throw new ArgumentException("Usage: BitwiseRegression.cs [verification-directory] [scalar|x64-vector256]");
string work = Path.Combine(root, "artifacts/bitwise-regressions", profile);
string tool = Path.Combine(root, ".lake/packages/leancil/Extractor/bin/Nethermind.LeanCIL.dll");
string profileArgument = profile == "scalar" ? profile : "@" + Path.Combine(root, "manifests/profiles", profile + ".json");
JsonArray targets = JsonNode.Parse(File.ReadAllText(Path.Combine(root, "manifests/targets.json")))!["methods"]!.AsArray();
async Task<string> Run(string executable, IEnumerable<string> arguments, bool succeeds = true)
{
    ProcessStartInfo start = new(executable) { WorkingDirectory = root, RedirectStandardOutput = true, RedirectStandardError = true, UseShellExecute = false };
    foreach (string argument in arguments) start.ArgumentList.Add(argument);
    using Process process = Process.Start(start) ?? throw new InvalidOperationException(executable);
    Task<string> stdout = process.StandardOutput.ReadToEndAsync(), stderr = process.StandardError.ReadToEndAsync();
    await process.WaitForExitAsync();
    string output = await stdout + await stderr;
    if ((process.ExitCode == 0) != succeeds || output.Contains("IDE0005", StringComparison.Ordinal)) throw new InvalidOperationException(output);
    return output;
}
foreach (bool early in new[] { false, true })
{
    string mutation = early ? "BitwiseEarlyStore" : "BitwiseWrongOperator";
    string build = Path.Combine(work, "build", mutation);
    await Run("dotnet", ["build", Path.Combine(fixtures, "Nethermind.Int256.csproj"), "-c", "Release",
        "-p:FixtureCase=" + mutation, "-p:BaseOutputPath=" + Path.Combine(build, "bin") + Path.DirectorySeparatorChar,
        "-p:BaseIntermediateOutputPath=" + Path.Combine(build, "obj") + Path.DirectorySeparatorChar,
        "-p:EnforceCodeStyleInBuild=true", "-p:GenerateDocumentationFile=true", "-v:q"]);
    foreach (string operation in new[] { "And", "Or", "Xor", "Not" })
    foreach (bool returned in new[] { false, true })
    {
        if (early && returned) continue;
        bool unary = operation == "Not";
        string id = (returned ? "Operator" : "") + operation;
        string extraction = Path.Combine(work, mutation, id);
        string signature = targets.Single(target => target!["id"]!.GetValue<string>() == id)!["signature"]!.GetValue<string>();
        await Run("dotnet", [tool, "extract", Path.Combine(build, "bin/Release/net10.0/Nethermind.Int256.dll"), signature, extraction, profileArgument]);
        ulong[] initial = early ? [1, 2, 4, 8] : [1, 0, 0, 0];
        ulong[] actual = early ? operation switch
        {
            "And" => [1, 0, 0, 0], "Or" => [1, 3, 7, 15], "Xor" => [0, 2, 6, 14],
            _ => [ulong.MaxValue - 1, 1, ulong.MaxValue - 1, 1]
        } : operation switch { "And" or "Or" => [0, 0, 0, 0], _ => [1, 0, 0, 0] };
        string operationTerm = operation switch { "And" => "(fun a b => a &&& b)", "Or" => "(fun a b => a ||| b)", "Xor" => "(fun a b => a ^^^ b)", _ => "(fun a => ~~~a)" };
        string initialTerm = "";
        for (int i = 0; i < 4; i++)
            initialTerm += $"offset = {16 + i * 8} then {initial[i]} else if id = 0 ∧ offset = {64 + i * 8} then {initial[i]} else if id = 0 ∧ ";
        initialTerm += "False then 0 else 0";
        string value = $"({actual[0]} + {actual[1]} * 2^64 + {actual[2]} * 2^128 + {actual[3]} * 2^192)";
        string refutation = "checked_" + (unary ? "unary" : "binary") + (returned ? "_return" : "") + "_refuted";
        string contract = returned ? "UInt256Proof.Bitwise.ReturnSafety." + (unary ? "UnaryContract" : "BinaryContract") : unary ? "WrappingUnaryContract" : "WrappingBinaryContract";
        string output = early ? "24" : "104";
        string proof = File.ReadAllText(Path.Combine(fixtures, "CheckedRefutationTemplate.lean.in"))
            .Replace("@INITIAL@", initialTerm).Replace("@INPUTS@", unary ? "[⟨0,16⟩]" : "[⟨0,16⟩,⟨0,64⟩]")
            .Replace("@OUTPUTS@", returned ? "[]" : $"[⟨0,{output}⟩]")
            .Replace("@INPUT_CASES@", unary ? "subst input; exact ⟨_, rfl⟩" : "rcases member with rfl | rfl <;> exact ⟨_, rfl⟩")
            .Replace("@OUTPUT_CASE@", returned ? "" : "subst output; rfl")
            .Replace("@CONTRACT@", contract).Replace("@OPERATION@", operationTerm).Replace("@REFUTATION@", refutation)
            .Replace("@REFERENCES@", "⟨0,16⟩" + (unary ? "" : " ⟨0,64⟩") + (returned ? "" : $" ⟨0,{output}⟩"))
            .Replace("@ACTUAL@", returned ? $"(numberBytes {value} 32)" : $"(BitVec.ofNat 256 {value})");
        if (returned) proof = proof.Replace("  · intro output member\n    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at member\n    ", "  · intro output member\n    simp only [List.map_nil, List.not_mem_nil] at member\n");
        string proofPath = Path.Combine(extraction, "Proof.lean");
        File.WriteAllText(proofPath, proof);
        await Run("dotnet", [tool, "verify", extraction, "--proof", proofPath, "--theorem", "BitwiseWitness.refuted", "--proof-root", root]);
        string suffix = profile == "scalar" ? "Scalar" : "Vector";
        string rejected = await Run("dotnet", [tool, "verify", extraction, "--proof", Path.Combine(root, "proofs", id + suffix + ".lean"),
            "--theorem", "UInt256Proof." + id + "." + suffix.ToLowerInvariant() + "_correctness", "--proof-root", root], succeeds: false);
        if (!rejected.Contains("proof checking", StringComparison.OrdinalIgnoreCase) || File.Exists(Path.Combine(extraction, "verified.json")))
            throw new InvalidOperationException("Mutation was not rejected during proof checking or retained a stale certificate: " + rejected);
        Console.WriteLine($"PASS {id}/{profile}/{mutation}: checked contract refutation");
    }
}
