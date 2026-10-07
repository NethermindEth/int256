// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System.Globalization;
using System.Net.Http.Headers;
using System.Text.Json;
using System.Text.Json.Nodes;
using System.Text.RegularExpressions;

namespace UInt256Verification;

internal static class BaselineEvidence
{
    internal static bool Check(string baseline, string method, string profile, string repository, Func<string, JsonNode>? request = null)
    {
        if (!Regex.IsMatch(repository, @"\A[\w.-]+/[\w.-]+\z") || !Regex.IsMatch(baseline, @"\A[0-9a-f]{40}\z")) return false;
        try
        {
            JsonNode Get(string path) => request is null ? GitHub(repository, path) : request(path);
            bool Is(JsonNode? node, string key, string expected) => node?[key]?.GetValue<string>() == expected;
            JsonArray Array(JsonNode node, string key) => node[key]?.AsArray() ?? throw new InvalidOperationException("Missing evidence array");
            long Number(JsonNode node, string key) => long.Parse(node[key]?.ToString() ?? "", CultureInfo.InvariantCulture);
            JsonNode runs = Get($"actions/workflows/verify-uint256.yml/runs?head_sha={baseline}&branch=main&event=push&status=success&per_page=100");
            foreach (JsonNode? run in Array(runs, "workflow_runs"))
            {
                if (!Is(run, "head_sha", baseline) || !Is(run, "head_branch", "main") || !Is(run, "event", "push")
                    || !Is(run, "status", "completed") || !Is(run, "conclusion", "success")
                    || !Is(run, "path", ".github/workflows/verify-uint256.yml") || !Is(run?["repository"], "full_name", repository)) continue;
                long id = Number(run!, "id"), attempt = Number(run!, "run_attempt");
                for (int page = 1; page <= 10; page++)
                {
                    JsonNode jobs = Get($"actions/runs/{id}/attempts/{attempt}/jobs?per_page=100&page={page}");
                    foreach (JsonNode? job in Array(jobs, "jobs"))
                    {
                        if (Is(job, "name", $"Production proof ({method}, {profile})") && Is(job, "head_sha", baseline)
                            && Is(job, "status", "completed") && Is(job, "conclusion", "success")
                            && (job?["steps"]?.AsArray() ?? []).Any(step => Is(step, "name", "Verify UInt256 arithmetic and memory safety")
                                && Is(step, "status", "completed") && Is(step, "conclusion", "success"))) return true;
                    }
                    if (page * 100 >= Number(jobs, "total_count")) break;
                }
            }
        }
        catch (Exception exception) when (exception is HttpRequestException or IOException or OperationCanceledException
            or JsonException or InvalidOperationException or FormatException or OverflowException or ArgumentException)
        {
            // Missing or malformed history disables only the skip optimization.
            return false;
        }
        return false;
    }

    private static JsonNode GitHub(string repository, string path)
    {
        using HttpClient client = new() { Timeout = TimeSpan.FromSeconds(15) };
        using HttpRequestMessage request = new(HttpMethod.Get, $"https://api.github.com/repos/{repository}/{path}");
        request.Headers.Accept.Add(new MediaTypeWithQualityHeaderValue("application/vnd.github+json"));
        request.Headers.Add("X-GitHub-Api-Version", "2022-11-28");
        request.Headers.UserAgent.ParseAdd("int256-verification");
        string? token = Environment.GetEnvironmentVariable("GH_TOKEN");
        if (!string.IsNullOrEmpty(token)) request.Headers.Authorization = new AuthenticationHeaderValue("Bearer", token);
        using HttpResponseMessage response = client.SendAsync(request).GetAwaiter().GetResult();
        response.EnsureSuccessStatusCode();
        return JsonNode.Parse(response.Content.ReadAsStringAsync().GetAwaiter().GetResult()) ?? throw new JsonException("Empty GitHub evidence");
    }
}
