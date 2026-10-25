// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT

using System.Text.Json;
using System.Text.RegularExpressions;

internal static class VerificationSelection
{
    internal static Selection Select(string root, IEnumerable<string> paths, bool all = false)
    {
        string[] changed = paths.Select(path => path.Replace('\\', '/')).Where(path =>
            path.Length > 0 && !Regex.IsMatch(path, @"\.(md|txt)$|(^|/)(LICENSE|NOTICE|THIRD-PARTY-NOTICES)$", RegexOptions.IgnoreCase)).ToArray();
        bool full = all || changed.Any(path =>
            !Regex.IsMatch(path, @"^src/Nethermind\.Int256\.(Tests|Benchmark)/") &&
            (path.StartsWith("src/", StringComparison.Ordinal) ||
             Regex.IsMatch(path, @"(^|/)(global\.json|NuGet\.Config|Directory\.(Build|Packages)\..*|\.editorconfig)$") ||
             path == ".github/workflows/verification.yml" ||
             (path.StartsWith("verification/", StringComparison.Ordinal) && !path.EndsWith(".lean", StringComparison.Ordinal))));
        // Gates share most modules, so each source is read and parsed once per selection.
        Dictionary<string, string[]> imports = new(StringComparer.Ordinal);
        Gate[] selected = VerificationSupport.Gates(root).Where(gate =>
        {
            HashSet<string> sources = ProofSources(root, gate.Proof, imports);
            return full || changed.Any(sources.Contains);
        }).ToArray();
        return new(full || changed.Any(path => path.StartsWith("verification/", StringComparison.Ordinal) && path.EndsWith(".lean", StringComparison.Ordinal)),
            selected, Partition(root, selected, imports));
    }

    internal const int Jobs = 8;

    // Every job builds the shared support once, so fewer, balanced jobs beat one job per gate.
    // Each profile in a job is its own batch session, so only profiles heavier than a job are split.
    internal static Batch[] Partition(string root, Gate[] selected, Dictionary<string, string[]>? imports = null)
    {
        if (selected.Length == 0) return [];
        Dictionary<Gate, (double Weight, int Support)> cost = Costs(root, selected, imports);
        double Weight(IEnumerable<Gate> gates) => gates.Sum(gate => cost[gate].Weight);
        double target = (double)Weight(selected) / Math.Min(Jobs, selected.Length);
        List<List<Gate>> chunks = [];
        foreach (IGrouping<string, Gate> profile in selected.GroupBy(gate => gate.Profile).OrderBy(group => group.Key, StringComparer.Ordinal))
            chunks.AddRange(Balance(profile, gate => cost[gate].Weight, (int)Math.Ceiling(Weight(profile) / target))
                .Where(chunk => chunk.Count > 0));
        List<List<Gate>>[] jobs = Balance(chunks, Weight, Math.Min(Jobs, chunks.Count));
        // Only a job's last group exports support, so it is the group with the most shareable modules.
        return [.. jobs.Select((job, index) => new Batch($"job-{index}",
            [.. job.SelectMany(chunk => chunk).GroupBy(gate => gate.Profile)
                .OrderBy(group => group.Sum(gate => cost[gate].Support))
                .ThenBy(group => group.Key, StringComparer.Ordinal)
                .Select(group => new BatchGroup(group.Key, [.. group.Select(gate => gate.Method)]))]))];
    }

    // Weight: measured CI seconds; module counts did not predict them. Support: modules shareable across extractions.
    internal static Dictionary<Gate, (double Weight, int Support)> Costs(string root, Gate[] gates, Dictionary<string, string[]>? imports = null)
    {
        imports ??= new(StringComparer.Ordinal);
        Dictionary<string, bool> dependent = new(StringComparer.Ordinal);
        Func<Gate, double> seconds = MeasuredSeconds(root);
        return gates.ToDictionary(gate => gate, gate =>
        {
            HashSet<string> sources = ProofSources(root, gate.Proof, imports);
            return (seconds(gate), sources.Count(source => !DependsOnExtraction(root, source, dependent, imports)));
        });
    }

    // A gate without a sample takes its method's median, then the overall median.
    static Func<Gate, double> MeasuredSeconds(string root)
    {
        Dictionary<string, double> samples = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(root, "manifests/gate-seconds.json")))
            .GetProperty("seconds").EnumerateObject().ToDictionary(pair => pair.Name, pair => pair.Value.GetDouble(), StringComparer.Ordinal);
        double Median(IEnumerable<double> values) => values.Order().ElementAtOrDefault(values.Count() / 2);
        double overall = Median(samples.Values);
        return gate => samples.TryGetValue($"{gate.Method}/{gate.Profile}", out double value) ? value
            : samples.Where(pair => pair.Key.StartsWith(gate.Method + "/", StringComparison.Ordinal)).Select(pair => pair.Value) is var method && method.Any()
                ? Median(method) : overall;
    }

    // Heaviest first into the lightest bin; ties keep input order.
    static List<T>[] Balance<T>(IEnumerable<T> items, Func<T, double> weight, int bins)
    {
        List<T>[] result = [.. Enumerable.Range(0, Math.Max(1, bins)).Select(_ => new List<T>())];
        double[] loads = new double[result.Length];
        foreach (T item in items.OrderByDescending(weight))
        {
            int bin = Array.IndexOf(loads, loads.Min());
            result[bin].Add(item);
            loads[bin] += weight(item);
        }
        return result;
    }

    // Modules importing Extracted are rebuilt for every extraction.
    static bool DependsOnExtraction(string root, string source, Dictionary<string, bool> memo, Dictionary<string, string[]> imports)
    {
        if (memo.TryGetValue(source, out bool known)) return known;
        memo[source] = false;
        bool result = false;
        foreach (string module in Imports(Path.GetFullPath(source["verification/".Length..], root), imports))
        {
            string dependency = module.Replace('.', '/') + ".lean";
            result |= module == "Extracted" ||
                (File.Exists(Path.Combine(root, dependency)) && DependsOnExtraction(root, "verification/" + dependency, memo, imports));
        }
        return memo[source] = result;
    }

    static string[] Imports(string path, Dictionary<string, string[]> cache) =>
        cache.TryGetValue(path, out string[]? known) ? known : cache[path] = [.. Regex.Matches(File.ReadAllText(path), @"(?m)^\s*(?:public\s+)?import\s+([^\r\n]+)").SelectMany(import =>
            import.Groups[1].Value.Split("--")[0].Split((char[]?)null, StringSplitOptions.RemoveEmptyEntries))];

    private static HashSet<string> ProofSources(string root, string proof, Dictionary<string, string[]> imports)
    {
        HashSet<string> seen = new(StringComparer.Ordinal);
        Stack<string> pending = new([proof]);
        while (pending.TryPop(out string? relative))
        {
            if (!seen.Add("verification/" + relative)) continue;
            string path = Path.GetFullPath(relative, root);
            string back = Path.GetRelativePath(root, path);
            if (back == ".." || back.StartsWith(".." + Path.DirectorySeparatorChar, StringComparison.Ordinal) || Path.IsPathRooted(back))
                throw new InvalidOperationException($"Proof dependency escapes verification/: {relative}");
            foreach (string module in Imports(path, imports))
            {
                string dependency = module.Replace('.', '/') + ".lean";
                if (File.Exists(Path.Combine(root, dependency))) pending.Push(dependency);
                else if (module != "Extracted" && !Regex.IsMatch(module, @"^(CIL|Lean|Std|Init)(\.|$)"))
                    throw new InvalidOperationException($"Unresolved consumer import: {module}");
            }
        }
        return seen;
    }
}
