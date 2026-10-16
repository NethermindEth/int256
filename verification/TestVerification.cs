#!/usr/bin/env dotnet
// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT
#:property PublishAot=false
#:include VerificationSupport.cs
#:include VerificationSelection.cs
#:include VerificationRunner.cs
#:include ConsumerSupportSelection.cs

using System.Text.Json;

string root = VerificationSupport.Root;
string[] allMethods = VerificationSupport.Gates(root).Select(gate => gate.Method).ToArray();
void Require(bool condition, string message)
{
    if (!condition) throw new InvalidOperationException(message);
}
void SelectionCheck(string[] paths, string[] expected, bool contracts, bool all = false)
{
    Selection selected = VerificationSelection.Select(root, paths, all);
    Require(selected.Contracts == contracts, "Incorrect contract selection");
    Require(selected.Include.Select(gate => gate.Method).Order().SequenceEqual(expected.Order()), "Incorrect gate selection");
    Require(selected.Batches.SelectMany(batch => batch.Methods).Order().SequenceEqual(expected.Order()), "Batches lost or duplicated gates");
    Require(selected.Batches.GroupBy(batch => batch.Profile).All(group => group.Count() <= 8), "Each profile should use at most eight batches");
    foreach (Batch batch in selected.Batches)
        Require(batch.Methods.All(method => selected.Include.Any(gate => gate.Method == method && gate.Profile == batch.Profile)), "Incorrect batch profile");
}
SelectionCheck(["README.md", "verification/README.md", "LICENSE"], [], false);
SelectionCheck(["verification/proofs/AddScalar.lean"], ["Add"], true);
SelectionCheck(["verification/UInt256/Methods/Equality/ScalarSafetyContract.lean"], ["EqUInt256UInt256", "EqualsUInt256Ref", "NeUInt256UInt256"], true);
SelectionCheck(["verification/UnusedProof.lean"], [], true);
SelectionCheck(["src/Nethermind.Int256.Tests/UInt256Tests.cs"], [], false);
SelectionCheck(["src/Nethermind.Int256.Benchmark/AddBenchmarks.cs"], [], false);
SelectionCheck(["src/Nethermind.Int256/UInt256.cs"], allMethods, true);
SelectionCheck(["verification/manifests/gates.json"], allMethods, true);
SelectionCheck(["verification/VerificationRunner.cs"], allMethods, true);
SelectionCheck([], allMethods, true, all: true);
Console.WriteLine("Verification gate selection checks passed.");

using (JsonDocument runs = JsonDocument.Parse("""
    {"workflow_runs":[
      {"id":1,"event":"pull_request","head_branch":"main","conclusion":"success","head_repository":{"full_name":"owner/repo"}},
      {"id":2,"event":"push","head_branch":"main","conclusion":"success","head_repository":{"full_name":"fork/repo"}},
      {"id":3,"event":"push","head_branch":"main","conclusion":"failure","head_repository":{"full_name":"owner/repo"}},
      {"id":4,"event":"push","head_branch":"feature","conclusion":"success","head_repository":{"full_name":"owner/repo"}},
      {"id":5,"event":"push","head_branch":"main","conclusion":"success","head_repository":{"full_name":"owner/repo"}}]}
    """))
    Require(ConsumerSupportSelection.TrustedRun(runs.RootElement, "owner/repo") == 5, "Only successful main pushes in this repository may certify support");
string digest = new('a', 64);
using (JsonDocument artifacts = JsonDocument.Parse($$"""
    {"artifacts":[
      {"id":1,"name":"consumer-support-scalar-0-1-{{digest}}","expired":true},
      {"id":2,"name":"consumer-support-scalar-0-1-untrusted","expired":false},
      {"id":3,"name":"consumer-support-scalar-0-1-{{digest}}","expired":false}]}
    """))
    Require(ConsumerSupportSelection.Select(5, artifacts.RootElement) == new ConsumerSupport(5, 3, digest), "Support requires a live artifact and a digest from trusted metadata");
Console.WriteLine("Consumer support provenance checks passed.");

string version = (await VerificationSupport.Run(root, "dotnet", ["--version"], true)).Trim();
TextWriter previousOutput = Console.Out;
using (StringWriter forwarded = new())
{
    try
    {
        Console.SetOut(forwarded);
        await VerificationSupport.Run(root, "dotnet", ["--version"]);
    }
    finally { Console.SetOut(previousOutput); }
    Require(forwarded.ToString().Trim() == version && version.Length > 0, "Child command output was lost");
}
Console.WriteLine("Verification command output checks passed.");

string temporary = Path.GetFullPath(Path.Combine(Path.GetTempPath(), "uint256-batch-" + Guid.NewGuid().ToString("N")));
try
{
    Directory.CreateDirectory(Path.Combine(temporary, "manifests"));
    File.WriteAllText(Path.Combine(temporary, "manifests/targets.json"), """
        {"methods":[{"id":"First","signature":"first"},{"id":"Second","signature":"second"}]}
        """);
    File.WriteAllText(Path.Combine(temporary, "manifests/gates.json"), """
        {"gates":[{"method":"First","profile":"scalar","proof":"First.lean","theorem":"first"},
                  {"method":"Second","profile":"scalar","proof":"Second.lean","theorem":"second"}]}
        """);
    File.WriteAllText(Path.Combine(temporary, "First.lean"), "");
    File.WriteAllText(Path.Combine(temporary, "Second.lean"), "");
    foreach (string? failure in new string?[] { null, "extract", "verify" })
    {
        List<string[]> calls = [];
        string stale = Path.Combine(temporary, "artifacts/First/scalar/verified.json");
        Directory.CreateDirectory(Path.GetDirectoryName(stale)!);
        File.WriteAllText(stale, "old certificate");
        Task Command(string command, string[] arguments)
        {
            if (command == "dotnet") calls.Add(arguments);
            if ((failure == "verify" && arguments.Contains("verify") && arguments.Contains("artifacts/First/scalar")) ||
                (failure == "extract" && arguments.Contains("extract") && arguments.Contains("first")))
                throw new InvalidOperationException("Expected test failure");
            return Task.CompletedTask;
        }
        bool failed = false;
        try { await VerificationRunner.Run(temporary, new("verify", ["First", "Second"], "scalar"), Command); }
        catch (InvalidOperationException) { failed = true; }
        Require(failed == (failure is not null), "Batch did not propagate failure");
        Require(!File.Exists(stale), "A stale certificate survived fresh extraction");
        Require(calls.Count(call => call[0] == "build") == 2, "Builds must run once per batch");
        string[][] verifies = calls.Where(call => call.Contains("verify")).ToArray();
        Require(verifies.Length == (failure == "extract" ? 1 : 2), "Incorrect number of verification attempts");
        Require(verifies[^1][4] == "Second.lean" && verifies[^1][6] == "second", "Proof selection leaked between methods");
        if (failure != "extract") Require(verifies[0][4] == "First.lean", "First method used the wrong proof");
    }
    Console.WriteLine("Verification batch checks passed.");
}
finally
{
    string parent = Path.GetFullPath(Path.GetTempPath()).TrimEnd(Path.DirectorySeparatorChar) + Path.DirectorySeparatorChar;
    if (!temporary.StartsWith(parent, StringComparison.OrdinalIgnoreCase)) throw new InvalidOperationException("Unexpected temporary directory");
    Directory.Delete(temporary, recursive: true);
}
