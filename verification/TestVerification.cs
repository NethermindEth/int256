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
    string[] Pairs(IEnumerable<(string Method, string Profile)> gates) => [.. gates.Select(gate => gate.Method + "/" + gate.Profile).Order(StringComparer.Ordinal)];
    Require(Pairs(selected.Batches.SelectMany(batch => batch.Groups.SelectMany(group => group.Methods.Select(method => (method, group.Profile)))))
        .SequenceEqual(Pairs(selected.Include.Select(gate => (gate.Method, gate.Profile)))), "Batches lost, duplicated or moved gates between profiles");
    Require(selected.Batches.Length <= VerificationSelection.Jobs, "Each job pays the support build, so the job count must stay bounded");
    Require(selected.Batches.All(batch => batch.Groups.Length > 0 && batch.Groups.All(group => group.Methods.Length > 0)), "Empty jobs waste a runner");
    Require(selected.Batches.All(batch => batch.Groups.Select(group => group.Profile).Distinct().Count() == batch.Groups.Length),
        "A profile repeated within a job would split one batch session");
    Require(selected.Batches.Count(batch => batch.Export) == (selected.Include.Length > 0 ? 1 : 0) &&
        (selected.Batches.Length == 0 || (selected.Batches[0].Export && selected.Batches[0].Id == "job-0")),
        "Exactly one job exports support, and provenance selection expects it to be job-0");
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
{
    Selection full = VerificationSelection.Select(root, [], all: true);
    Require(full.Batches.Length == VerificationSelection.Jobs, "A full run should use every parallel job");
    // One session per profile and job: only profiles larger than a job may be split.
    foreach (IGrouping<string, Gate> profile in full.Include.GroupBy(gate => gate.Profile).Where(group => group.Count() <= VerificationSelection.Jobs))
        Require(full.Batches.Count(batch => batch.Groups.Any(group => group.Profile == profile.Key)) == 1, "Small profile split across jobs: " + profile.Key);
    BatchGroup exportedGroup = full.Batches[0].Groups[^1];
    Gate exported = full.Include.Single(gate => gate.Method == exportedGroup.Methods[^1] && gate.Profile == exportedGroup.Profile);
    var costs = VerificationSelection.Costs(root, full.Include);
    Require(costs[exported].Support == costs.Values.Max(cost => cost.Support),
        "Support export covers only the exporting request's closure, so the widest gate must export");
    Gate add = full.Include.Single(gate => gate.Method == "Add" && gate.Profile == "scalar");
    Gate and = full.Include.Single(gate => gate.Method == "And" && gate.Profile == "scalar");
    Require(costs[add].Weight > costs[and].Weight, "Modules importing Extracted are rebuilt per extraction and must weigh in");
}
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
      {"id":1,"name":"consumer-support-job-0-1-{{digest}}","expired":true},
      {"id":2,"name":"consumer-support-job-0-1-untrusted","expired":false},
      {"id":4,"name":"consumer-support-job-1-1-{{digest}}","expired":false},
      {"id":3,"name":"consumer-support-job-0-1-{{digest}}","expired":false}]}
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
    const string export = "LEANCIL_EXPORT_CONSUMER_SUPPORT";
    string? previousExport = Environment.GetEnvironmentVariable(export);
    foreach (string? failure in new string?[] { null, "extract", "verify", "crash", "export" })
    {
        List<string[]> calls = [];
        List<string[]> batches = [];
        string stale = Path.Combine(temporary, "artifacts/First/scalar/verified.json");
        Directory.CreateDirectory(Path.GetDirectoryName(stale)!);
        File.WriteAllText(stale, "old certificate");
        Task Command(string command, string[] arguments)
        {
            if (command == "dotnet") calls.Add(arguments);
            if (failure == "extract" && arguments.Contains("extract") && arguments.Contains("first"))
                throw new InvalidOperationException("Expected test failure");
            if (arguments.Contains("verify-batch"))
            {
                Require(Environment.GetEnvironmentVariable(export) is null, "Support export leaked into a batch");
                using JsonDocument manifest = JsonDocument.Parse(File.ReadAllText(arguments[2]));
                string[][] requests = [.. manifest.RootElement.GetProperty("requests").EnumerateArray()
                    .Select(request => new[] { request.GetProperty("output").GetString()!, Path.GetFileName(request.GetProperty("proof").GetString()!), request.GetProperty("theorem").GetString()! })];
                batches.AddRange(requests);
                if (failure == "crash") throw new InvalidOperationException("Expected test failure");
                File.WriteAllText(arguments[4], JsonSerializer.Serialize(requests.Select(request => new
                {
                    status = failure == "verify" && request[2] == "first" ? "failed" : "verified",
                    stage = "proof checking",
                    error = "Expected test failure",
                })));
                if (failure == "verify") throw new InvalidOperationException("Expected test failure");
            }
            return Task.CompletedTask;
        }
        Environment.SetEnvironmentVariable(export, failure == "export" ? temporary : null);
        string? message = null;
        try { await VerificationRunner.Run(temporary, new("verify", ["First", "Second"], "scalar"), Command); }
        catch (InvalidOperationException exception) { message = exception.Message; }
        Require((message is null) == failure is null or "export", "Batch did not propagate failure");
        Require(failure is not ("extract" or "verify") || (message!.Contains("First/scalar") && !message.Contains("Second/scalar")),
            "A failure was attributed to the wrong method");
        Require(failure != "crash" || (message!.Contains("First/scalar") && message.Contains("Second/scalar")),
            "Requests without results must fail");
        Require(!File.Exists(stale), "A stale certificate survived fresh extraction");
        Require(calls.Count(call => call[0] == "build") == 2, "Builds must run once per batch");
        Require(calls.Count(call => call.Contains("verify-batch")) == 1, "Verification must share one batch session");
        string[][] expected = failure switch
        {
            "extract" => [["second", "Second.lean"]],
            "export" => [["first", "First.lean"]],
            _ => [["first", "First.lean"], ["second", "Second.lean"]],
        };
        Require(batches.Select(request => request[2] + "/" + request[1]).SequenceEqual(expected.Select(pair => pair[0] + "/" + pair[1])),
            "Proof selection leaked between methods");
        Require(batches.All(request => Path.IsPathRooted(request[0])), "Batch outputs must not depend on the tool directory");
        string[][] singles = [.. calls.Where(call => call.Contains("verify"))];
        Require(singles.Length == (failure == "export" ? 1 : 0), "Only the exported method may use a single-request verify");
        if (failure == "export") Require(singles[0][4] == "Second.lean" && singles[0][6] == "second", "Export used the wrong proof");
        Require(Environment.GetEnvironmentVariable(export) == (failure == "export" ? temporary : null), "Support export setting was not restored");
    }
    // A job spans several profiles: one build, one session per profile, and one export from the last group.
    File.WriteAllText(Path.Combine(temporary, "manifests/targets.json"), """
        {"methods":[{"id":"First","signature":"first"},{"id":"Second","signature":"second"},{"id":"Third","signature":"third"}]}
        """);
    File.WriteAllText(Path.Combine(temporary, "manifests/gates.json"), """
        {"gates":[{"method":"First","profile":"scalar","proof":"First.lean","theorem":"first"},
                  {"method":"Second","profile":"scalar","proof":"Second.lean","theorem":"second"},
                  {"method":"Third","profile":"x64-avx2","proof":"Third.lean","theorem":"third"}]}
        """);
    File.WriteAllText(Path.Combine(temporary, "Third.lean"), "");
    foreach (bool exporting in new[] { false, true })
    {
        List<string[]> calls = [];
        List<string> sessions = [];
        Task Command(string command, string[] arguments)
        {
            if (command == "dotnet") calls.Add(arguments);
            if (arguments.Contains("verify-batch"))
            {
                Require(Environment.GetEnvironmentVariable(export) is null, "Support export leaked into a batch");
                using JsonDocument manifest = JsonDocument.Parse(File.ReadAllText(arguments[2]));
                JsonElement[] requests = [.. manifest.RootElement.GetProperty("requests").EnumerateArray()];
                sessions.Add(string.Join(",", requests.Select(request => request.GetProperty("theorem").GetString())));
                File.WriteAllText(arguments[4], JsonSerializer.Serialize(requests.Select(_ => new { status = "verified", stage = "", error = "" })));
            }
            return Task.CompletedTask;
        }
        Environment.SetEnvironmentVariable(export, exporting ? temporary : null);
        await VerificationRunner.Run(temporary, new("verify", [], "scalar",
            Groups: [new("scalar", ["First", "Second"]), new("x64-avx2", ["Third"])]), Command);
        Require(calls.Count(call => call[0] == "build") == 2, "A multi-profile job must build the tools once");
        Require(sessions.SequenceEqual(exporting ? ["first,second"] : ["first,second", "third"]), "Each profile needs its own batch session");
        string[][] singles = [.. calls.Where(call => call.Contains("verify"))];
        Require(singles.Length == (exporting ? 1 : 0) && (!exporting || (singles[0][2] == "artifacts/Third/x64-avx2" && singles[0][6] == "third")),
            "Only the last group's last method may export support");
        Require(calls.Where(call => call.Contains("extract")).Select(call => call[4]).SequenceEqual(
            ["artifacts/First/scalar", "artifacts/Second/scalar", "artifacts/Third/x64-avx2"]), "Methods were extracted under the wrong profile");
    }
    bool rejected = false;
    try { await VerificationRunner.Run(temporary, new("verify", [], "scalar", Groups: [new("scalar", ["First"]), new("scalar", ["Second"])]), (_, _) => Task.CompletedTask); }
    catch (ArgumentException) { rejected = true; }
    Require(rejected, "A repeated profile would overwrite its batch manifest");
    Environment.SetEnvironmentVariable(export, previousExport);
    Console.WriteLine("Verification batch checks passed.");
}
finally
{
    string parent = Path.GetFullPath(Path.GetTempPath()).TrimEnd(Path.DirectorySeparatorChar) + Path.DirectorySeparatorChar;
    if (!temporary.StartsWith(parent, StringComparison.OrdinalIgnoreCase)) throw new InvalidOperationException("Unexpected temporary directory");
    Directory.Delete(temporary, recursive: true);
}
