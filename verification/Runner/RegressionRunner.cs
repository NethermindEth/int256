// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System.Collections.Concurrent;
using System.Diagnostics;
using System.Text;
using System.Text.Json;
using System.Text.Json.Nodes;

namespace UInt256Verification;

internal sealed class RegressionRunner(Workspace workspace,
    Func<string, Dictionary<string, string>>? inputs = null,
    Action<string, string>? copy = null,
    Func<string[], string, string, int>? execute = null)
{
    private static void Write(string path, object value) => File.WriteAllText(path,
        JsonSerializer.Serialize(value, new JsonSerializerOptions { WriteIndented = true }) + "\n", new UTF8Encoding(false));

    private Dictionary<string, string> Inputs(string directory)
    {
        if (inputs is not null) return inputs(directory);
        if (directory == workspace.Root) return workspace.Inputs();
        // Compile and execute the copied source selector, including its newly added inputs.
        string project = Path.Combine(directory, RegressionPlan.Runner);
        Capture(["dotnet", "build", project, "-c", "Release", "--nologo"], directory, requireSuccess: true);
        var result = Capture(["dotnet", Path.Combine(Path.GetDirectoryName(project)!, "bin/Release/net10.0/Verification.dll"), "inputs"], directory, requireSuccess: true);
        return JsonSerializer.Deserialize<Dictionary<string, string>>(result.Stdout)
            ?? throw new InvalidOperationException("Source selector returned no inputs");
    }

    private void RequireInputs(string directory, Dictionary<string, string> expected)
    {
        if (!Workspace.SameInputs(Inputs(directory), expected)) throw new InvalidOperationException($"Immutable source inputs changed: {directory}");
    }

    private void Copy(string source, string destination)
    {
        if (copy is not null) { copy(source, destination); return; }
        workspace.Run(["git", "clone", "--shared", "--no-checkout", "--quiet", source, destination], source, "Regression clone");
        new Workspace(source).CopyRegressionSource(destination);
    }

    private sealed record ProcessResult(int ExitCode, string Stdout, string Stderr);

    private static ProcessResult Capture(string[] command, string directory, bool requireSuccess, string? log = null)
    {
        ProcessStartInfo start = new(command[0])
        {
            WorkingDirectory = directory, UseShellExecute = false, CreateNoWindow = true,
            RedirectStandardOutput = true, RedirectStandardError = true,
            StandardOutputEncoding = Encoding.UTF8, StandardErrorEncoding = Encoding.UTF8
        };
        foreach (string argument in command.Skip(1)) start.ArgumentList.Add(argument);
        start.Environment["DOTNET_EnableHWIntrinsic"] = "0";
        start.Environment["DOTNET_CLI_TELEMETRY_OPTOUT"] = "1";
        start.Environment["DOTNET_SKIP_FIRST_TIME_EXPERIENCE"] = "1";
        start.Environment["MSBuildEnableWorkloadResolver"] = "false";
        using Process process = Process.Start(start) ?? throw new InvalidOperationException($"Cannot start {command[0]}");
        if (log is not null)
        {
            using TextWriter output = TextWriter.Synchronized(new StreamWriter(log, append: false, new UTF8Encoding(false)) { AutoFlush = true });
            async Task Drain(StreamReader reader)
            {
                char[] buffer = new char[4096];
                int count;
                while ((count = await reader.ReadAsync(buffer)) != 0) output.Write(buffer, 0, count);
            }
            Task[] drains = [Drain(process.StandardOutput), Drain(process.StandardError)];
            process.WaitForExit();
            Task.WaitAll(drains);
            return new(process.ExitCode, "", "");
        }
        Task<string> stdout = process.StandardOutput.ReadToEndAsync(), stderr = process.StandardError.ReadToEndAsync();
        process.WaitForExit();
        ProcessResult result = new(process.ExitCode, stdout.GetAwaiter().GetResult(), stderr.GetAwaiter().GetResult());
        if (requireSuccess && result.ExitCode != 0)
            throw new InvalidOperationException("Source input subprocess failed: " + JsonSerializer.Serialize(new
            { command, cwd = directory, exitCode = result.ExitCode, stdout = result.Stdout, stderr = result.Stderr }));
        return result;
    }

    internal void RunJob(RegressionPlan.Job job, string seed, Dictionary<string, string> expected, string output)
    {
        string directory = Path.Combine(output, job.Id);
        Directory.CreateDirectory(directory);
        JsonArray commands = [];
        JsonObject receipt = new() { ["job"] = job.Id, ["status"] = "failed", ["commands"] = commands };
        Stopwatch timer = Stopwatch.StartNew();
        string temporary = Directory.CreateTempSubdirectory("int256-check-").FullName;
        try
        {
            string root = Path.Combine(temporary, "source");
            receipt["workspace"] = root;
            Copy(seed, root);
            RequireInputs(root, expected);
            for (int index = 0; index < job.Commands.Length; index++)
            {
                string[] tokens = job.Commands[index];
                if (!tokens[0].EndsWith(".csproj", StringComparison.Ordinal)) throw new InvalidOperationException("Regression commands must select a C# project");
                string[] command = ["dotnet", "run", "--project", Path.Combine(root, tokens[0]), "-c", "Release", "--", .. tokens.Skip(1)];
                string log = Path.Combine(directory, $"{index + 1}.log");
                Stopwatch commandTimer = Stopwatch.StartNew();
                int code = execute is null ? Capture(command, root, false, log).ExitCode : execute(command, root, log);
                commands.Add(JsonSerializer.SerializeToNode(new { command, exitCode = code, elapsedSeconds = commandTimer.Elapsed.TotalSeconds,
                    log = Path.GetFileName(log), logSha256 = Workspace.Hash(log) }));
                RequireInputs(root, expected);
                if (code != 0) throw new InvalidOperationException($"Regression command failed: {job.Id} (exit {code})");
            }
            receipt["status"] = "passed";
        }
        catch (Exception error) { receipt["error"] = error.Message; throw; }
        finally
        {
            receipt["elapsedSeconds"] = timer.Elapsed.TotalSeconds;
            Write(Path.Combine(directory, "receipt.json"), receipt);
            Directory.Delete(temporary, recursive: true);
        }
    }

    internal string Run(RegressionPlan.Job[] plan, RegressionPlan.Job[] selected, int jobs, string output,
        Dictionary<string, string>? captured = null)
    {
        if (jobs is < 1 or > 8) throw new ArgumentException("Jobs must be between 1 and 8");
        bool Same(RegressionPlan.Job left, RegressionPlan.Job right) => left.Id == right.Id
            && left.Commands.Length == right.Commands.Length && left.Commands.Zip(right.Commands).All(pair => pair.First.SequenceEqual(pair.Second));
        if (selected.Length == 0 || selected.Select(job => job.Id).Distinct().Count() != selected.Length
            || selected.Any(job => !plan.Any(candidate => Same(job, candidate)) || job.Id.Length == 0
                || job.Id.Any(c => !char.IsAsciiLetterOrDigit(c) && c is not '-' and not '_')
                || job.Commands.Length == 0 || job.Commands.Any(command => command.Length == 0)))
            throw new InvalidOperationException("Invalid or incomplete job selection");
        bool full = selected.Length == plan.Length && selected.Zip(plan).All(pair => Same(pair.First, pair.Second));
        Directory.CreateDirectory(output);
        string lockPath = Path.Combine(output, "full.lock"), fullReport = Path.Combine(output, "report.json");
        if (full) { using FileStream acquired = new(lockPath, FileMode.CreateNew, FileAccess.Write, FileShare.None); }
        try
        {
            if (full) File.Delete(fullReport);
            string records = Path.Combine(output, "run-" + Guid.NewGuid().ToString("N"));
            Directory.CreateDirectory(records);
            var expected = captured ?? Inputs(workspace.Root);
            if (!Workspace.SameInputs(Inputs(workspace.Root), expected)) throw new InvalidOperationException("Source inputs changed after command-plan selection");
            Write(Path.Combine(records, "source-inputs.json"), expected);
            string temporary = Directory.CreateTempSubdirectory("int256-check-seed-").FullName;
            try
            {
                string seed = Path.Combine(temporary, "source");
                Copy(workspace.Root, seed);
                RequireInputs(seed, expected);
                if (!Workspace.SameInputs(Inputs(workspace.Root), expected)) throw new InvalidOperationException("Source inputs changed during seed capture");
                ConcurrentQueue<RegressionPlan.Job> queued = new(selected);
                ConcurrentBag<string> completed = [];
                ConcurrentQueue<Exception> errors = new();
                Task.WaitAll(Enumerable.Range(0, Math.Min(jobs, selected.Length)).Select(_ => Task.Run(() =>
                {
                    while (errors.IsEmpty && queued.TryDequeue(out var job))
                    {
                        try { RunJob(job, seed, expected, records); completed.Add(job.Id); Console.WriteLine($"PASS: {job.Id}"); }
                        catch (Exception error) { errors.Enqueue(error); Console.WriteLine($"FAIL: {job.Id}; receipts: {records}"); }
                    }
                })).ToArray());
                if (errors.TryPeek(out Exception? failure)) throw new InvalidOperationException($"Regression suite failed; receipts: {records}", failure);
                if (!completed.ToHashSet(StringComparer.Ordinal).SetEquals(selected.Select(job => job.Id))) throw new InvalidOperationException("Incomplete regression results");
                RequireInputs(seed, expected);
            }
            finally { Directory.Delete(temporary, recursive: true); }
            if (!Workspace.SameInputs(Inputs(workspace.Root), expected)) throw new InvalidOperationException("Source inputs changed during regression checking");
            var report = new { status = "passed", scope = full ? "full" : "partial", fullSuite = full, requiredJobs = plan.Length,
                selectedJobs = selected.Select(job => job.Id), sourceInputs = expected,
                receipts = selected.Select(job => new { job = job.Id, path = Workspace.Relative(output, Path.Combine(records, job.Id, "receipt.json")),
                    sha256 = Workspace.Hash(Path.Combine(records, job.Id, "receipt.json")) }).ToArray() };
            string target = full ? fullReport : Path.Combine(records, "subset.json"), staged = Path.ChangeExtension(target, ".tmp");
            Write(staged, report);
            File.Move(staged, target, overwrite: true);
            return target;
        }
        finally { if (full) File.Delete(lockPath); }
    }
}
