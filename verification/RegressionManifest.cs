// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT

using System.Text.Json;

internal sealed record RegressionRunner(string File, string[]? Profiles = null, string? ProfileOption = null, string? Job = null);
internal sealed record RegressionShard(string Id, string[][] Runs);

// CI runs exactly the runs this manifest lists, so a runner and its CI shards share one profile list.
internal static class RegressionManifest
{
    static readonly JsonSerializerOptions Json = new() { PropertyNamingPolicy = JsonNamingPolicy.CamelCase };

    internal static RegressionRunner[] Runners(string root) =>
        JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(root, "manifests/regressions.json")))
            .GetProperty("runners").Deserialize<RegressionRunner[]>(Json)!;

    // Each run is a runner file followed by its arguments after the verification directory.
    internal static RegressionShard[] Shards(string root)
    {
        List<(string Id, string[] Run)> runs = [];
        foreach (RegressionRunner runner in Runners(root))
        {
            string stem = runner.File.Replace("Regression.cs", "").ToLowerInvariant();
            if (runner.Profiles is null) runs.Add((runner.Job ?? stem, [runner.File]));
            else foreach (string profile in runner.Profiles)
                runs.Add((runner.Job ?? stem + "-" + profile,
                    runner.ProfileOption is null ? [runner.File, profile] : [runner.File, runner.ProfileOption, profile]));
        }
        return [.. runs.GroupBy(run => run.Id).Select(job => new RegressionShard(job.Key, [.. job.Select(run => run.Run)]))];
    }

    // A profile the runner supports but CI omits would never be refuted; one CI lists but the runner lacks would fail late.
    internal static string[] RequireProfiles(string root, string file, IEnumerable<string> supported)
    {
        RegressionRunner runner = Runners(root).SingleOrDefault(runner => runner.File == file)
            ?? throw new InvalidOperationException($"{file} is missing from manifests/regressions.json");
        string[] listed = runner.Profiles ?? [], actual = [.. supported.Distinct()];
        if (!listed.Order(StringComparer.Ordinal).SequenceEqual(actual.Order(StringComparer.Ordinal), StringComparer.Ordinal))
            throw new InvalidOperationException($"manifests/regressions.json lists {file} profiles [{string.Join(", ", listed)}], " +
                $"but the runner supports [{string.Join(", ", actual)}]");
        return listed;
    }
}
