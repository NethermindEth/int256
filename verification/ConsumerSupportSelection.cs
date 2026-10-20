// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT

using System.Text.Json;
using System.Text.RegularExpressions;

internal sealed record ConsumerSupport(long Run, long Artifact, string Digest);

internal static class ConsumerSupportSelection
{
    internal static long? TrustedRun(JsonElement runs, string repository) => runs.GetProperty("workflow_runs").EnumerateArray()
        .Where(run => run.GetProperty("event").GetString() == "push" &&
            run.GetProperty("head_branch").GetString() == "main" &&
            run.GetProperty("conclusion").GetString() == "success" &&
            run.GetProperty("head_repository").GetProperty("full_name").GetString() == repository)
        .Select(run => (long?)run.GetProperty("id").GetInt64()).FirstOrDefault();

    internal static ConsumerSupport? Select(long run, JsonElement artifacts)
    {
        foreach (JsonElement artifact in artifacts.GetProperty("artifacts").EnumerateArray())
        {
            if (artifact.GetProperty("expired").GetBoolean()) continue;
            Match name = Regex.Match(artifact.GetProperty("name").GetString()!,
                @"\Aconsumer-support-job-0-\d+-([a-f0-9]{64})\z");
            if (name.Success) return new(run, artifact.GetProperty("id").GetInt64(), name.Groups[1].Value);
        }
        return null;
    }
}
