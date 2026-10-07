// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System.Collections.Concurrent;
using System.Text.Json.Nodes;
using UInt256Verification;

namespace UInt256VerificationTests;

internal static class RegressionRunnerTests
{
    private sealed class Harness
    {
        internal string Root { get; }
        internal string Output { get; }
        internal Workspace Workspace => new(Root);
        internal Harness(string manifests)
        {
            Root = Path.Combine(Path.GetDirectoryName(manifests)!, "source");
            Output = Path.Combine(Path.GetDirectoryName(manifests)!, "receipts");
            Directory.CreateDirectory(Root);
            Directory.CreateDirectory(Output);
            File.WriteAllText(Path.Combine(Root, "source.txt"), "immutable");
        }
        internal static Dictionary<string, string> Inputs(string root) => new() { ["source.txt"] = Workspace.Hash(Path.Combine(root, "source.txt")) };
        internal static void Copy(string source, string target) { Directory.CreateDirectory(target); File.Copy(Path.Combine(source, "source.txt"), Path.Combine(target, "source.txt")); }
        internal static int Success(string[] command, string directory, string log) { File.WriteAllText(log, "passed\n"); return 0; }
        internal RegressionRunner Runner(Func<string[], string, string, int>? execute = null, Action<string, string>? copy = null) => new(Workspace, Inputs, copy ?? Copy, execute ?? Success);
        internal string Full => Path.Combine(Output, "report.json");
        internal JsonObject Receipt(string id) => JsonNode.Parse(File.ReadAllText(Directory.GetFiles(Output, "receipt.json", SearchOption.AllDirectories).Single(path => Path.GetFileName(Path.GetDirectoryName(path)) == id)))!.AsObject();
    }
    private static RegressionPlan.Job Job(string id, params string[] projects) => new(id, (projects.Length == 0 ? ["runner.csproj"] : projects).Select(project => new[] { project }).ToArray());

    internal static void Register(Action<string, Action<Catalog, string>> check)
    {
        check("regression CLI prints exact plans, appends CI output and attempts every batch job", (_, manifests) =>
        {
            foreach (string[] args in new string[][] { ["--jobs", "0"], ["--jobs", "9"], ["--jobs", "x"], ["--job"], ["--unknown"],
                ["--print-plan", "--print-plan"], ["--github-output", "file"], ["--batch", "[]"], ["--batch", "[null]"],
                ["--batch", "[\"a\",\"a\"]"], ["--batch", "[\"a\"]", "--job", "a"] }) Program.Reject(() => RegressionOptions.Parse(args));
            var job = Job("legacy-Add"); Program.Reject(() => RegressionCli.Select([job], "legacy"));
            Program.Require(RegressionCli.Select([job], job.Id).Single() == job, "Exact CLI job selection changed");
            Workspace workspace = new(Directory.GetCurrentDirectory()); var before = workspace.Inputs();
            string github = Path.Combine(Path.GetDirectoryName(manifests)!, "github-output"); File.WriteAllText(github, "prior=value\n");
            using StringWriter output = new(); TextWriter saved = Console.Out;
            try
            {
                Console.SetOut(output);
                RegressionCli.Run(workspace, ["--print-plan", "--job", "legacy-Add"]);
                var printed = JsonNode.Parse(output.ToString())!;
                Program.Require(Catalog.Text(printed["scope"]) == "partial" && printed["jobs"]!.AsArray().Count == 1 && Catalog.Text(printed["jobs"]![0]!["id"]) == "legacy-Add", "Printed plan not exact partial selection");
                output.GetStringBuilder().Clear();
                RegressionCli.Run(workspace, ["--print-plan", "--github-output", github]);
                printed = JsonNode.Parse(output.ToString())!;
                string[] lines = File.ReadAllLines(github);
                Program.Require(lines.Length == 2 && lines[0] == "prior=value" && lines[1].StartsWith("matrix=", StringComparison.Ordinal)
                    && JsonNode.DeepEquals(JsonNode.Parse(lines[1][7..]), printed["matrix"]) && printed["jobs"]!.AsArray().Count == printed["requiredJobs"]!.GetValue<int>(), "GitHub matrix output changed or replaced prior output");
            }
            finally { Console.SetOut(saved); }
            Program.Require(Workspace.SameInputs(before, workspace.Inputs()), "Printing changed source inputs");
            List<string> attempted = []; using StringWriter errors = new(); TextWriter savedError = Console.Error;
            try
            {
                Console.SetError(errors);
                Program.Reject(() => RegressionCli.RunBatch([[Job("one")], [Job("two")]], jobs => { attempted.Add(jobs[0].Id); if (jobs[0].Id == "one") throw new InvalidOperationException("failed first"); }));
            }
            finally { Console.SetError(savedError); }
            Program.Require(attempted.SequenceEqual(new[] { "one", "two" }), "Batch abandoned jobs after failure");
        });
        check("regression failed baseline skips negatives and invalidates the full report", (_, manifests) =>
        {
            Harness h = new(manifests); File.WriteAllText(h.Full, "old certificate");
            List<string[]> commands = [];
            var runner = h.Runner((command, _, log) => { commands.Add(command); File.WriteAllText(log, "failure"); return 7; });
            var job = Job("legacy-Add", "baseline.csproj", "negative.csproj");
            Program.Reject(() => runner.Run([job], [job], 1, h.Output));
            Program.Require(commands.Count == 1 && commands[0][3].EndsWith("baseline.csproj", StringComparison.Ordinal) && !File.Exists(h.Full), "Failed baseline proceeded or retained full success");
            var receipt = h.Receipt(job.Id); var commandReceipt = receipt["commands"]!.AsArray().Single()!;
            string logPath = Directory.GetFiles(h.Output, "1.log", SearchOption.AllDirectories).Single();
            Program.Require(Catalog.Text(receipt["status"]) == "failed" && commandReceipt["exitCode"]!.GetValue<int>() == 7 && Catalog.Text(commandReceipt["logSha256"]) == Workspace.Hash(logPath), "Failed receipt lost command/log identity");
            Program.Require(!File.Exists(Path.Combine(h.Output, "full.lock")), "Failed suite retained lock");
        });
        check("regression command dispatch and partial receipts preserve full evidence", (_, manifests) =>
        {
            Harness h = new(manifests); File.WriteAllText(h.Full, "prior full certificate");
            List<string[]> commands = [];
            var runner = h.Runner((command, directory, log) => { commands.Add(command); return Harness.Success(command, directory, log); });
            var plan = new[] { Job("one"), Job("two") };
            string target = runner.Run(plan, [plan[0]], 1, h.Output);
            Program.Require(commands.Count == 1 && commands[0][..3].SequenceEqual(new[] { "dotnet", "run", "--project" }) && commands[0][4..].SequenceEqual(new[] { "-c", "Release", "--" }), "C# command dispatch changed");
            var report = JsonNode.Parse(File.ReadAllText(target))!;
            Program.Require(File.ReadAllText(h.Full) == "prior full certificate" && target != h.Full && Catalog.Text(report["scope"]) == "partial" && !report["fullSuite"]!.GetValue<bool>() && report["selectedJobs"]!.AsArray().Select(Catalog.Text).SequenceEqual(new[] { "one" }), "Partial run overwrote or claimed full success");
            var receipt = report["receipts"]!.AsArray().Single()!;
            Program.Require(Catalog.Text(receipt["sha256"]) == Workspace.Hash(Path.Combine(h.Output, Catalog.Text(receipt["path"]))), "Aggregate receipt hash changed");
        });
        check("regression immutable seed and command-plan mismatch prevent execution", (_, manifests) =>
        {
            Harness h = new(manifests); var job = Job("one"); int copies = 0, commands = 0;
            var runner = h.Runner((command, directory, log) => { commands++; return Harness.Success(command, directory, log); },
                (source, target) => { copies++; Harness.Copy(source, target); File.WriteAllText(Path.Combine(target, "source.txt"), "changed"); });
            Program.Reject(() => runner.Run([job], [job], 1, h.Output, new() { ["source.txt"] = "stale" }));
            Program.Require(copies == 0 && commands == 0, "Stale plan started copying/execution");
            Program.Reject(() => runner.Run([job], [job], 1, h.Output));
            Program.Require(copies == 1 && commands == 0 && !File.Exists(h.Full), "Changed seed started commands/published success");
        });
        check("regression source drift in worker, seed or original prevents success", (_, manifests) =>
        {
            Harness h = new(manifests); var job = Job("one");
            foreach (string location in new[] { "worker", "seed", "original" })
            {
                File.WriteAllText(Path.Combine(h.Root, "source.txt"), "immutable"); string? seed = null;
                var runner = h.Runner((command, directory, log) =>
                {
                    Harness.Success(command, directory, log);
                    File.WriteAllText(Path.Combine(location == "original" ? h.Root : location == "seed" ? seed! : directory, "source.txt"), "drift"); return 0;
                }, (source, target) => { Harness.Copy(source, target); if (source == h.Root) seed = target; });
                Program.Reject(() => runner.Run([job], [job], 1, h.Output));
                Program.Require(!File.Exists(h.Full), "Source drift published success");
            }
        });
        check("regression workers overlap within bounds and use independent complete snapshots", (_, manifests) =>
        {
            Harness h = new(manifests); using Barrier rendezvous = new(2);
            int active = 0, maximum = 0; object guard = new(); ConcurrentBag<string> roots = [];
            var runner = h.Runner((command, directory, log) =>
            {
                Program.Require(Workspace.SameInputs(Harness.Inputs(directory), Harness.Inputs(h.Root)), "Incomplete worker snapshot");
                lock (guard) { active++; maximum = Math.Max(maximum, active); roots.Add(directory); }
                if (!rendezvous.SignalAndWait(TimeSpan.FromSeconds(10))) throw new InvalidOperationException("Workers did not overlap");
                Harness.Success(command, directory, log); lock (guard) active--; return 0;
            });
            var plan = Enumerable.Range(0, 4).Select(i => Job(i.ToString())).ToArray();
            string target = runner.Run(plan, plan, 2, h.Output); var report = JsonNode.Parse(File.ReadAllText(target))!;
            Program.Require(maximum == 2 && roots.Distinct().Count() == 4 && report["fullSuite"]!.GetValue<bool>() && report["receipts"]!.AsArray().Count == 4, "Worker isolation, concurrency or completeness changed");
            Program.Require(roots.All(root => !Directory.Exists(root)), "Worker snapshots not cleaned up");
        });
        check("regression failure waits for running work and stops queued work", (_, manifests) =>
        {
            Harness h = new(manifests); using Barrier rendezvous = new(2); using ManualResetEventSlim failed = new(); bool finished = false;
            var runner = h.Runner((command, directory, log) =>
            {
                if (!rendezvous.SignalAndWait(TimeSpan.FromSeconds(10))) throw new InvalidOperationException("Missing concurrent worker");
                File.WriteAllText(log, "outcome");
                if (command[3].EndsWith("failure.csproj", StringComparison.Ordinal)) { failed.Set(); return 1; }
                Program.Require(failed.Wait(TimeSpan.FromSeconds(10)), "Failed worker did not run"); finished = true; return 0;
            });
            var plan = new[] { Job("failure", "failure.csproj"), Job("running", "running.csproj") };
            Program.Reject(() => runner.Run(plan, plan, 2, h.Output));
            Program.Require(finished && !File.Exists(h.Full) && Directory.GetFiles(h.Output, "receipt.json", SearchOption.AllDirectories).Length == 2, "Failure abandoned running work or published success");
            int executed = 0;
            runner = h.Runner((_, _, log) => { executed++; File.WriteAllText(log, "failure"); return 1; });
            Program.Reject(() => runner.Run(plan, plan, 1, h.Output));
            Program.Require(executed == 1, "Queued work started after failure");
        });
        check("regression rejects invalid selections and concurrent full publication", (_, manifests) =>
        {
            Harness h = new(manifests); var job = Job("one"); var runner = h.Runner();
            foreach (int jobs in new[] { 0, 9 }) Program.Reject(() => runner.Run([job], [job], jobs, h.Output));
            foreach (var selection in new[] { Array.Empty<RegressionPlan.Job>(), new[] { job, job }, new[] { Job("unknown") }, new[] { Job("one", "changed.csproj") } })
                Program.Reject(() => runner.Run([job], selection, 1, h.Output));
            var traversal = Job("../escape"); Program.Reject(() => runner.Run([traversal], [traversal], 1, h.Output));
            string lockPath = Path.Combine(h.Output, "full.lock"); File.WriteAllText(lockPath, "held"); File.WriteAllText(h.Full, "existing");
            bool rejected = false; try { runner.Run([job], [job], 1, h.Output); } catch (IOException) { rejected = true; }
            Program.Require(rejected && File.ReadAllText(lockPath) == "held" && File.ReadAllText(h.Full) == "existing", "Contended lock changed existing evidence");
        });
        check("regression source selector failure preserves subprocess diagnostics", (_, manifests) =>
        {
            Harness h = new(manifests); int commands = 0;
            var runner = new RegressionRunner(h.Workspace, copy: Harness.Copy, execute: (command, directory, log) => { commands++; return Harness.Success(command, directory, log); });
            var job = Job("selector"); Program.Reject(() => runner.RunJob(job, h.Root, Harness.Inputs(h.Root), h.Output));
            var receipt = h.Receipt(job.Id); string error = Catalog.Text(receipt["error"]);
            Program.Require(error.StartsWith("Source input subprocess failed: ", StringComparison.Ordinal), "Missing selector failure diagnostics");
            var details = JsonNode.Parse(error["Source input subprocess failed: ".Length..])!;
            Program.Require(commands == 0 && receipt["commands"]!.AsArray().Count == 0 && Catalog.Text(receipt["status"]) == "failed"
                && Catalog.Text(details["cwd"]) == Catalog.Text(receipt["workspace"]) && details["exitCode"]!.GetValue<int>() != 0
                && details["command"]!.AsArray().Count > 0 && Catalog.Text(details["stdout"]).Contains("MSB1009", StringComparison.Ordinal)
                && details["stderr"] is JsonValue, "Selector receipt lost process details");
        });
    }
}
