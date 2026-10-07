// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System.Text;
using System.Text.Json;
using System.Text.Json.Nodes;

namespace UInt256Verification;

internal sealed record RegressionOptions(int Jobs = 1, string? Job = null, bool PrintPlan = false, string? GithubOutput = null, string[]? Batch = null)
{
    internal static RegressionOptions Parse(string[] args)
    {
        RegressionOptions result = new(); HashSet<string> seen = [];
        for (int index = 0; index < args.Length; index++)
        {
            string name = args[index];
            if (!seen.Add(name)) throw new ArgumentException($"Duplicate option: {name}");
            string Value() => ++index < args.Length ? args[index] : throw new ArgumentException($"{name} requires a value");
            result = name switch
            {
                "--jobs" => int.TryParse(Value(), out int jobs) ? result with { Jobs = jobs } : throw new ArgumentException("--jobs requires an integer"),
                "--job" => result with { Job = Value() },
                "--print-plan" => result with { PrintPlan = true },
                "--github-output" => result with { GithubOutput = Value() },
                "--batch" => result with { Batch = JsonSerializer.Deserialize<string[]>(Value()) ?? throw new ArgumentException("Expected a job array") },
                _ => throw new ArgumentException($"Unknown regression option: {name}")
            };
        }
        if (result.Jobs is < 1 or > 8) throw new ArgumentException("--jobs must be between 1 and 8");
        if (result.Batch is not null && (result.Job is not null || result.PrintPlan || result.Batch.Length == 0 || result.Batch.Any(string.IsNullOrEmpty) || result.Batch.Distinct().Count() != result.Batch.Length))
            throw new ArgumentException("Batch requires distinct jobs and cannot select --job or --print-plan");
        if (result.GithubOutput is not null && (!result.PrintPlan || result.Job is not null)) throw new ArgumentException("GitHub output requires the full printed plan");
        return result;
    }
}

internal static class RegressionCli
{
    internal static void RunBatch(RegressionPlan.Job[][] batch, Action<RegressionPlan.Job[]> run)
    {
        List<string> failures = [];
        foreach (var jobs in batch)
        {
            try { run(jobs); }
            catch (Exception error) { failures.Add(jobs[0].Id); Console.Error.WriteLine(error); }
        }
        if (failures.Count > 0) throw new InvalidOperationException("Failed regression groups: " + string.Join(", ", failures));
    }

    internal static RegressionPlan.Job[] Select(RegressionPlan.Job[] plan, string? id)
    {
        var selected = id is null ? plan : plan.Where(job => job.Id == id).ToArray();
        if (selected.Length == 0) throw new ArgumentException("Unknown exact job ID");
        return selected;
    }

    internal static void Run(Workspace workspace, string[] args)
    {
        RegressionOptions options = RegressionOptions.Parse(args);
        var captured = workspace.Inputs();
        var plan = RegressionPlan.Create(workspace.Catalog);
        if (!Workspace.SameInputs(captured, workspace.Inputs())) throw new InvalidOperationException("Source inputs changed during command-plan selection");
        var selected = Select(plan, options.Job);
        if (options.PrintPlan)
        {
            JsonObject matrix = RegressionPlan.Matrix(selected.Select(job => job.Id).ToArray());
            if (options.GithubOutput is not null)
            {
                var batches = matrix["include"]!.AsArray();
                if (batches.Count > 256 || !batches.SelectMany(batch => batch!["jobs"]!.AsArray().Select(Catalog.Text)).SequenceEqual(plan.Select(job => job.Id)))
                    throw new InvalidOperationException("Incomplete or oversized regression matrix");
                File.AppendAllText(options.GithubOutput, "matrix=" + matrix.ToJsonString() + "\n", new UTF8Encoding(false));
            }
            Console.WriteLine(JsonSerializer.Serialize(new { scope = options.Job is null ? "full" : "partial", requiredJobs = plan.Length, jobs = selected, matrix }, new JsonSerializerOptions { WriteIndented = true }));
            return;
        }
        RegressionRunner runner = new(workspace);
        string output = Path.Combine(workspace.Verification, "generated/all-checks");
        if (options.Batch is not null)
        {
            // Validate the entire batch before starting, then retain evidence for every attempted job.
            var batch = options.Batch.Select(id => Select(plan, id)).ToArray();
            RunBatch(batch, jobs => Console.WriteLine("Partial regression job passed: " + runner.Run(plan, jobs, options.Jobs, output, captured)));
            return;
        }
        string target = runner.Run(plan, selected, options.Jobs, output, captured);
        Console.WriteLine($"{(options.Job is null ? "Full regression suite" : "Partial regression job")} passed: {target}");
    }
}
