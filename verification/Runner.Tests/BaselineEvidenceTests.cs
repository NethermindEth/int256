// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System.Text.Json;
using System.Text.Json.Nodes;
using UInt256Verification;

namespace UInt256VerificationTests;

internal static class BaselineEvidenceTests
{
    private const string Repository = "NethermindEth/int256";
    private static readonly string Baseline = new('a', 40);
    private static JsonObject Run() => new()
    {
        ["id"] = 12, ["run_attempt"] = 2, ["head_sha"] = Baseline, ["head_branch"] = "main", ["event"] = "push",
        ["status"] = "completed", ["conclusion"] = "success", ["path"] = ".github/workflows/verify-uint256.yml", ["repository"] = new JsonObject { ["full_name"] = Repository }
    };
    private static JsonObject Job() => new()
    {
        ["name"] = "Production proof (Subtract, scalar)", ["head_sha"] = Baseline, ["status"] = "completed", ["conclusion"] = "success",
        ["steps"] = new JsonArray(new JsonObject { ["name"] = "Verify UInt256 arithmetic and memory safety", ["status"] = "completed", ["conclusion"] = "success" })
    };
    private static bool Check(JsonObject run, JsonObject job) => BaselineEvidence.Check(Baseline, "Subtract", "scalar", Repository, path =>
        path.StartsWith("actions/workflows/", StringComparison.Ordinal) ? new JsonObject { ["workflow_runs"] = new JsonArray(run.DeepClone()) }
            : new JsonObject { ["jobs"] = new JsonArray(job.DeepClone()), ["total_count"] = 1 });

    internal static void Register(Action<string, Action<Catalog, string>> check)
    {
        check("baseline evidence requires the exact combined proof and successful attempt", (_, _) =>
        {
            Program.Require(Check(Run(), Job()), "Exact successful proof rejected");
            foreach (string stepName in new[] { "Verify freshly built UInt256", "Other step" })
            {
                var job = Job(); job["steps"]![0]!["name"] = stepName;
                Program.Require(!Check(Run(), job), "Wrong proof step accepted");
            }
        });
        check("baseline run identity, status and repository cannot be substituted", (_, _) =>
        {
            foreach (var (key, value) in new[] { ("head_sha", new string('b', 40)), ("head_branch", "feature"), ("event", "pull_request"),
                ("status", "in_progress"), ("conclusion", "failure"), ("path", ".github/workflows/other.yml") })
            {
                var run = Run(); run[key] = value;
                Program.Require(!Check(run, Job()), $"Wrong run {key} accepted");
            }
            var wrongRepository = Run(); wrongRepository["repository"]!["full_name"] = "attacker/int256";
            Program.Require(!Check(wrongRepository, Job()), "Wrong repository accepted");
        });
        check("baseline job identity and status must match method and profile", (_, _) =>
        {
            foreach (var (key, value) in new[] { ("name", "Production proof (Add, scalar)"), ("name", "Production proof (Subtract, x64-avx2)"),
                ("head_sha", new string('b', 40)), ("status", "queued"), ("conclusion", "cancelled") })
            {
                var job = Job(); job[key] = value;
                Program.Require(!Check(Run(), job), $"Wrong job {key} accepted");
            }
        });
        check("green jobs with skipped, failed or missing proof steps cannot skip verification", (_, _) =>
        {
            foreach (string conclusion in new[] { "skipped", "failure", "cancelled" })
            {
                var job = Job(); job["steps"]![0]!["conclusion"] = conclusion;
                Program.Require(!Check(Run(), job), "Non-successful proof step accepted");
            }
            var missing = Job(); missing.Remove("steps"); Program.Require(!Check(Run(), missing), "Missing proof accepted");
            missing["steps"] = new JsonArray(); Program.Require(!Check(Run(), missing), "Empty steps accepted");
            var pending = Job(); pending["steps"]![0]!["status"] = "in_progress"; Program.Require(!Check(Run(), pending), "Pending proof accepted");
        });
        check("unavailable and malformed baseline evidence always forces a proof", (_, _) =>
        {
            foreach (Exception error in new Exception[] { new IOException(), new HttpRequestException(), new TaskCanceledException(), new JsonException(), new InvalidOperationException(), new FormatException() })
                Program.Require(!BaselineEvidence.Check(Baseline, "Subtract", "scalar", Repository, _ => throw error), "Unavailable evidence accepted");
            foreach (JsonNode bad in new JsonNode[] { new JsonObject(), new JsonArray(), JsonValue.Create(3)! })
                Program.Require(!BaselineEvidence.Check(Baseline, "Subtract", "scalar", Repository, _ => bad), "Malformed evidence accepted");
            foreach (string key in new[] { "id", "run_attempt" })
            {
                var run = Run(); run.Remove(key); Program.Require(!Check(run, Job()), "Incomplete attempt identity accepted");
            }
        });
        check("baseline jobs are paginated within the successful attempt with a bounded search", (_, _) =>
        {
            List<string> paths = [];
            JsonNode Request(string path)
            {
                paths.Add(path);
                return path.StartsWith("actions/workflows/", StringComparison.Ordinal) ? new JsonObject { ["workflow_runs"] = new JsonArray(Run()) }
                    : new JsonObject { ["jobs"] = path.EndsWith("page=2", StringComparison.Ordinal) ? new JsonArray(Job()) : new JsonArray(), ["total_count"] = 101 };
            }
            Program.Require(BaselineEvidence.Check(Baseline, "Subtract", "scalar", Repository, Request), "Second-page proof missed");
            Program.Require(paths[^1] == "actions/runs/12/attempts/2/jobs?per_page=100&page=2", "Wrong attempt pagination");
            int calls = 0;
            Program.Require(!BaselineEvidence.Check(Baseline, "Subtract", "scalar", Repository, path =>
            {
                calls++;
                return path.StartsWith("actions/workflows/", StringComparison.Ordinal) ? new JsonObject { ["workflow_runs"] = new JsonArray(Run()) }
                    : new JsonObject { ["jobs"] = new JsonArray(), ["total_count"] = 2000 };
            }) && calls == 11, "Unbounded or insufficient history search");
        });
        check("invalid baseline identities cannot form API requests", (_, _) =>
        {
            foreach (var (baseline, repository) in new[] { (Baseline, "invalid/path/extra"), ("not-a-sha", Repository), (Baseline + "\n", Repository), (Baseline, Repository + "\n") })
            {
                bool called = false;
                Program.Require(!BaselineEvidence.Check(baseline, "Subtract", "scalar", repository, _ => { called = true; return new JsonObject(); }) && !called, "Invalid identity requested evidence");
            }
        });
    }
}
