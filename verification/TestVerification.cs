#!/usr/bin/env dotnet
// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT
#:property PublishAot=false
#:include VerificationSupport.cs
#:include VerificationSelection.cs
#:include VerificationRunner.cs
#:include ConsumerSupportSelection.cs
#:include RegressionManifest.cs

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
    Require(selected.Batches.Select((batch, index) => batch.Id == $"job-{index}").All(match => match),
        "Provenance selection reads job artifacts by their job-<n> names");
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
    // A runner missing from CI would let a pin or template change stop refuting its mutants unnoticed.
    string[] files = [.. Directory.EnumerateFiles(root, "*Regression.cs").Select(path => Path.GetFileName(path)!).Order(StringComparer.Ordinal)];
    RegressionRunner[] runners = RegressionManifest.Runners(root);
    Require(runners.Select(runner => runner.File).Order(StringComparer.Ordinal).SequenceEqual(files),
        "manifests/regressions.json must list every *Regression.cs runner exactly once");
    Require(runners.All(runner => runner.ProfileOption is null || runner.Profiles is { Length: > 0 }), "A profile option needs profiles");
    string[] Runs(IEnumerable<string[]> runs) => [.. runs.Select(run => string.Join(' ', run)).Order(StringComparer.Ordinal)];
    string[] expectedRuns = Runs(runners.SelectMany(runner => runner.Profiles is null ? [new[] { runner.File }]
        : runner.Profiles.Select(profile => runner.ProfileOption is null ? new[] { runner.File, profile } : [runner.File, runner.ProfileOption, profile])));
    RegressionShard[] shards = RegressionManifest.Shards(root);
    Require(Runs(shards.SelectMany(shard => shard.Runs)).SequenceEqual(expectedRuns), "Regression shards lost or duplicated a runner profile");
    Require(shards.Select(shard => shard.Id).Distinct().Count() == shards.Length, "Regression shard ids must be unique");
    Require(File.ReadAllText(Path.Combine(root, "../.github/workflows/verification.yml")).Contains("fromJSON(needs.select.outputs.regressions)"),
        "The regression matrix must come from the manifest");
}
{
    Selection full = VerificationSelection.Select(root, [], all: true);
    Require(full.Batches.Length == VerificationSelection.Jobs, "A full run should use every parallel job");
    var costs = VerificationSelection.Costs(root, full.Include);
    // Each split repeats the support build, so only a profile heavier than one job's share may be split.
    double share = full.Include.Sum(gate => costs[gate].Weight) / VerificationSelection.Jobs;
    foreach (IGrouping<string, Gate> profile in full.Include.GroupBy(gate => gate.Profile).Where(group => group.Sum(gate => costs[gate].Weight) <= share))
        Require(full.Batches.Count(batch => batch.Groups.Any(group => group.Profile == profile.Key)) == 1, "Light profile split across jobs: " + profile.Key);
    int Shareable(BatchGroup group) => group.Methods.Sum(method => costs[full.Include.Single(gate => gate.Method == method && gate.Profile == group.Profile)].Support);
    Require(full.Batches.All(batch => batch.Groups.All(group => Shareable(group) <= Shareable(batch.Groups[^1]))),
        "Only a job's last group exports support, so it must be the group with the most shareable modules");
    Gate add = full.Include.Single(gate => gate.Method == "Add" && gate.Profile == "scalar");
    Gate and = full.Include.Single(gate => gate.Method == "And" && gate.Profile == "scalar");
    Require(costs[add].Weight > costs[and].Weight, "Shards balance on measured seconds, so the slower Add gate must outweigh And");
    // A gate with no sample must not count as free, or one job would collect all of them.
    Gate unsampled = full.Include.Single(gate => gate.Method == "Multiply" && gate.Profile == "scalar") with { Profile = "unsampled-profile" };
    double[] multiply = [.. full.Include.Where(gate => gate.Method == "Multiply").Select(gate => costs[gate].Weight).Order()];
    Require(VerificationSelection.Costs(root, [unsampled])[unsampled].Weight == multiply[multiply.Length / 2],
        "An unsampled gate must take its method's measured median");
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
string digest = new('a', 64), other = new('b', 64);
using (JsonDocument artifacts = JsonDocument.Parse($$"""
    {"artifacts":[
      {"id":1,"name":"consumer-support-job-0-1-{{digest}}","expired":true},
      {"id":2,"name":"consumer-support-job-0-1-untrusted","expired":false},
      {"id":3,"name":"consumer-support-job-0-1-{{digest}}","expired":false},
      {"id":4,"name":"consumer-support-job-1-1-{{other}}","expired":false},
      {"id":5,"name":"consumer-support-job-1-2-{{other}}","expired":false},
      {"id":6,"name":"consumer-support-scalar-0-1-{{other}}","expired":false}]}
    """))
    Require(ConsumerSupportSelection.Select(5, artifacts.RootElement).SequenceEqual([new ConsumerSupport(5, 3, digest), new ConsumerSupport(5, 4, other)]),
        "Every job's live artifact counts once, with its digest from trusted metadata");
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
// The forwarded diagnosis must reach the failure summary; an empty reason hid an extractor rejection.
using (StringWriter forwarded = new())
{
    TextWriter previousError = Console.Error;
    string? reason = null;
    try
    {
        // One wrapper, one lock: separate SetOut/SetError wrappers let stdout and stderr corrupt the shared builder.
        TextWriter shared = TextWriter.Synchronized(forwarded);
        Console.SetOut(shared);
        Console.SetError(shared);
        await VerificationSupport.Run(root, "dotnet", ["uint256-missing-tool.dll"]);
    }
    catch (InvalidOperationException exception) { reason = exception.Message; }
    finally
    {
        Console.SetOut(previousOutput);
        Console.SetError(previousError);
    }
    Require(reason is not null && reason.Contains("uint256-missing-tool.dll", StringComparison.Ordinal),
        "A failed child command must report its last output lines");
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
                Require(Environment.GetEnvironmentVariable(export) == (failure == "export" ? temporary : null),
                    "The only group's batch must see the support export");
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
            _ => [["first", "First.lean"], ["second", "Second.lean"]],
        };
        Require(batches.Select(request => request[2] + "/" + request[1]).SequenceEqual(expected.Select(pair => pair[0] + "/" + pair[1])),
            "Proof selection leaked between methods");
        Require(batches.All(request => Path.IsPathRooted(request[0])), "Batch outputs must not depend on the tool directory");
        string[][] singles = [.. calls.Where(call => call.Contains("verify"))];
        Require(singles.Length == 0, "Batch sessions export support themselves; no request is split out");
        Require(Environment.GetEnvironmentVariable(export) == (failure == "export" ? temporary : null), "Support export setting was not restored");
    }
    // A job spans several profiles: one build, one session per profile, and only the last group exports.
    File.WriteAllText(Path.Combine(temporary, "manifests/targets.json"), """
        {"methods":[{"id":"First","signature":"first"},{"id":"Second","signature":"second"},{"id":"Third","signature":"third"}]}
        """);
    File.WriteAllText(Path.Combine(temporary, "manifests/gates.json"), """
        {"gates":[{"method":"First","profile":"scalar","proof":"First.lean","theorem":"first"},
                  {"method":"Second","profile":"scalar","proof":"Second.lean","theorem":"second"},
                  {"method":"Third","profile":"x64-v3","proof":"Third.lean","theorem":"third"}]}
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
                bool last = arguments[2].EndsWith("verify-batch-x64-v3.json", StringComparison.Ordinal);
                Require(Environment.GetEnvironmentVariable(export) == (exporting && last ? temporary : null),
                    "Only the last group's session may export, since one artifact name carries one digest");
                using JsonDocument manifest = JsonDocument.Parse(File.ReadAllText(arguments[2]));
                JsonElement[] requests = [.. manifest.RootElement.GetProperty("requests").EnumerateArray()];
                sessions.Add(string.Join(",", requests.Select(request => request.GetProperty("theorem").GetString())));
                File.WriteAllText(arguments[4], JsonSerializer.Serialize(requests.Select(_ => new { status = "verified", stage = "", error = "" })));
            }
            return Task.CompletedTask;
        }
        Environment.SetEnvironmentVariable(export, exporting ? temporary : null);
        await VerificationRunner.Run(temporary, new("verify", [], "scalar",
            Groups: [new("scalar", ["First", "Second"]), new("x64-v3", ["Third"])]), Command);
        Require(calls.Count(call => call[0] == "build") == 2, "A multi-profile job must build the tools once");
        Require(sessions.SequenceEqual(["first,second", "third"]), "Each profile needs its own batch session");
        Require(!calls.Any(call => call.Contains("verify")), "Batch sessions export support themselves; no request is split out");
        Require(calls.Where(call => call.Contains("extract")).Select(call => call[4]).SequenceEqual(
            ["artifacts/First/scalar", "artifacts/Second/scalar", "artifacts/Third/x64-v3"]), "Methods were extracted under the wrong profile");
    }
    // Later profiles overlap but start only after the first, which builds the support they restore;
    // failures still read in group order.
    File.WriteAllText(Path.Combine(temporary, "manifests/gates.json"), """
        {"gates":[{"method":"First","profile":"scalar","proof":"First.lean","theorem":"first"},
                  {"method":"Second","profile":"x64-sse42","proof":"Second.lean","theorem":"second"},
                  {"method":"Third","profile":"x64-v3","proof":"Third.lean","theorem":"third"}]}
        """);
    Environment.SetEnvironmentVariable(export, null);
    foreach (int? groupParallel in new int?[] { 1, 2 })
    {
        object gate = new();
        int running = 0, peak = 0;
        bool early = false;
        List<string> started = [], finished = [];
        async Task Command(string command, string[] arguments)
        {
            if (!arguments.Contains("verify-batch")) return;
            using JsonDocument manifest = JsonDocument.Parse(File.ReadAllText(arguments[2]));
            string theorem = manifest.RootElement.GetProperty("requests")[0].GetProperty("theorem").GetString()!;
            lock (gate) { early |= theorem != "first" && !finished.Contains("first"); started.Add(theorem); peak = Math.Max(peak, ++running); }
            // Both later sessions overlap, and the third finishes before the second.
            for (int wait = 0; groupParallel == 2 && theorem != "first" && wait < 500; wait++)
            {
                lock (gate) if (started.Count == 3 && (theorem == "third" || finished.Contains("third"))) break;
                await Task.Delay(10);
            }
            File.WriteAllText(arguments[4], JsonSerializer.Serialize(new[] { new { status = "failed", stage = "proof checking", error = theorem } }));
            lock (gate) { finished.Add(theorem); running--; }
        }
        string? message = null;
        try
        {
            await VerificationRunner.Run(temporary, new("verify", [], "scalar", GroupParallel: groupParallel,
                Groups: [new("scalar", ["First"]), new("x64-sse42", ["Second"]), new("x64-v3", ["Third"])]), Command);
        }
        catch (InvalidOperationException exception) { message = exception.Message; }
        Require(!early && started.Count == 3,
            "Later profiles must start after the first builds the shared support");
        Require(peak == groupParallel, "Group concurrency must follow GroupParallel");
        Require(message is not null && message.IndexOf("First/scalar", StringComparison.Ordinal) < message.IndexOf("Second/x64-sse42", StringComparison.Ordinal)
            && message.IndexOf("Second/x64-sse42", StringComparison.Ordinal) < message.IndexOf("Third/x64-v3", StringComparison.Ordinal),
            "Failures must be reported in group order regardless of completion order");
    }
    // An exporting job stays sequential: hiding the export is process-wide.
    Environment.SetEnvironmentVariable(export, temporary);
    {
        int running = 0, peak = 0;
        async Task Command(string command, string[] arguments)
        {
            if (!arguments.Contains("verify-batch")) return;
            peak = Math.Max(peak, Interlocked.Increment(ref running));
            await Task.Delay(20);
            using JsonDocument manifest = JsonDocument.Parse(File.ReadAllText(arguments[2]));
            File.WriteAllText(arguments[4], JsonSerializer.Serialize(manifest.RootElement.GetProperty("requests").EnumerateArray()
                .Select(_ => new { status = "verified", stage = "", error = "" })));
            Interlocked.Decrement(ref running);
        }
        await VerificationRunner.Run(temporary, new("verify", [], "scalar", GroupParallel: 3,
            Groups: [new("scalar", ["First"]), new("x64-sse42", ["Second"]), new("x64-v3", ["Third"])]), Command);
        Require(peak == 1, "An exporting job must not overlap sessions");
    }
    Environment.SetEnvironmentVariable(export, null);
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
