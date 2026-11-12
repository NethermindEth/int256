#!/usr/bin/env dotnet
// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT
#:property PublishAot=false
#:include RegressionBatch.cs
#:include VerificationSupport.cs
#:include ProofBindings.cs
#:include RegressionManifest.cs
using System.Security.Cryptography;

string root = Path.GetFullPath(args.Length > 0 ? args[0] : "verification");
string fixtures = Path.Combine(root, "Tests/Fixtures/Bitwise");
string profile = args.Length > 1 ? args[1] : "scalar";
string[] profiles = RegressionManifest.RequireProfiles(root, "BitwiseRegression.cs", ["scalar", "x64-v3"]);
if (args.Length > 2 || !profiles.Contains(profile))
    throw new ArgumentException("Usage: BitwiseRegression.cs [verification-directory] [scalar|x64-v3]");
string suffix = profile == "scalar" ? "Scalar" : "Vector";
RegressionBatch batch = await RegressionBatch.Start(root, "bitwise-regressions/" + profile);
foreach (bool early in new[] { false, true })
{
    string mutation = early ? "BitwiseEarlyStore" : "BitwiseWrongOperator";
    string assembly = await batch.Build("Bitwise", mutation);
    string nativeBuild = Path.Combine(batch.Work, "build", mutation, "native");
    await batch.Run("dotnet", ["build", Path.Combine(fixtures, "NativeWitness.csproj"), "-c", "Release",
        "-p:FixtureAssembly=" + assembly,
        "-p:BaseOutputPath=" + Path.Combine(nativeBuild, "bin") + Path.DirectorySeparatorChar,
        "-p:BaseIntermediateOutputPath=" + Path.Combine(nativeBuild, "obj") + Path.DirectorySeparatorChar,
        "-p:EnforceCodeStyleInBuild=true", "-p:GenerateDocumentationFile=true", "-v:q"]);
    byte[] expectedAssembly = SHA256.HashData(File.ReadAllBytes(assembly));
    byte[] loadedAssembly = SHA256.HashData(File.ReadAllBytes(Path.Combine(nativeBuild, "bin/Release/net10.0/Nethermind.Int256.dll")));
    if (!expectedAssembly.AsSpan().SequenceEqual(loadedAssembly)) throw new InvalidOperationException("Native witness resolved a different fixture assembly");
    string[] nativeWitness = [Path.Combine(nativeBuild, "bin/Release/net10.0/NativeWitness.dll"), mutation];
    Console.Write(await batch.Run("dotnet", nativeWitness));
    Console.Write(await batch.Run("dotnet", nativeWitness, disableIntrinsics: true));
    foreach (string operation in new[] { "And", "Or", "Xor", "Not" })
    foreach (bool returned in new[] { false, true })
    {
        if (early && returned) continue;
        bool unary = operation == "Not";
        string id = (returned ? "Operator" : "") + operation;
        string extraction = await batch.Extract(assembly, id, profile, Path.Combine(mutation, id));
        ulong[] initial = early ? [1, 2, 4, 8] : [1, 0, 0, 0];
        ulong[] actual = early ? operation switch
        {
            "And" => [1, 0, 0, 0], "Or" => [1, 3, 7, 15], "Xor" => [0, 2, 6, 14],
            _ => [ulong.MaxValue - 1, 1, ulong.MaxValue - 1, 1]
        } : operation switch { "And" or "Or" => [0, 0, 0, 0], _ => [1, 0, 0, 0] };
        string operationTerm = operation switch { "And" => "(fun a b => a &&& b)", "Or" => "(fun a b => a ||| b)", "Xor" => "(fun a b => a ^^^ b)", _ => "(fun a => ~~~a)" };
        string initialTerm = RegressionBatch.InitialBytes(Enumerable.Range(0, 4)
            .SelectMany(i => new[] { (16 + i * 8, initial[i]), (64 + i * 8, initial[i]) }));
        string value = $"({actual[0]} + {actual[1]} * 2^64 + {actual[2]} * 2^128 + {actual[3]} * 2^192)";
        string refutation = "checked_" + (unary ? "unary" : "binary") + (returned ? "_return" : "") + "_refuted";
        string contract = returned ? "UInt256Model.Safety.AggregateReturn." + (unary ? "UnaryContract" : "BinaryContract") : unary ? "WrappingUnaryContract" : "WrappingBinaryContract";
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
        batch.Checks.Add(new($"{id}/{profile}/{mutation}", extraction, batch.Proof(mutation + id + "Refutation", proof),
            "BitwiseWitness.refuted", "checked contract refutation",
            Path.Combine(batch.Consumer, "proofs", id + suffix + ".lean"),
            "UInt256Proof." + id + "." + suffix.ToLowerInvariant() + "_correctness"));
    }
}
await batch.FinishOrThrow();
