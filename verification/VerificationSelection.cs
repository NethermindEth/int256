// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT

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
        Gate[] selected = VerificationSupport.Gates(root).Where(gate =>
        {
            HashSet<string> sources = ProofSources(root, gate.Proof);
            return full || changed.Any(sources.Contains);
        }).ToArray();
        return new(full || changed.Any(path => path.StartsWith("verification/", StringComparison.Ordinal) && path.EndsWith(".lean", StringComparison.Ordinal)),
            selected, Partition(root, selected));
    }

    internal const int Jobs = 8;

    // Every job builds the shared support once, so fewer, balanced jobs beat one job per gate.
    // Each profile in a job is its own batch session, so only profiles heavier than a job are split.
    internal static Batch[] Partition(string root, Gate[] selected)
    {
        if (selected.Length == 0) return [];
        Dictionary<Gate, (int Weight, int Support)> cost = Costs(root, selected);
        int Weight(IEnumerable<Gate> gates) => gates.Sum(gate => cost[gate].Weight);
        // The exported manifest covers only its request's closure; export the widest one.
        Gate exported = selected.OrderByDescending(gate => cost[gate].Support)
            .ThenBy(gate => gate.Profile, StringComparer.Ordinal).ThenBy(gate => gate.Method, StringComparer.Ordinal).First();
        double target = (double)Weight(selected) / Math.Min(Jobs, selected.Length);
        List<List<Gate>> chunks = [];
        foreach (IGrouping<string, Gate> profile in selected.GroupBy(gate => gate.Profile).OrderBy(group => group.Key, StringComparer.Ordinal))
            chunks.AddRange(Balance(profile, gate => cost[gate].Weight, (int)Math.Ceiling(Weight(profile) / target), null)
                .Where(chunk => chunk.Count > 0));
        List<List<Gate>>[] jobs = Balance(chunks, Weight, Math.Min(Jobs, chunks.Count), chunks.Single(chunk => chunk.Contains(exported)));
        return [.. jobs.Select((job, index) => new Batch($"job-{index}", index == 0,
            [.. job.SelectMany(chunk => chunk).GroupBy(gate => gate.Profile)
                .OrderBy(group => group.Key == exported.Profile && index == 0)
                .ThenBy(group => group.Key, StringComparer.Ordinal)
                .Select(group => new BatchGroup(group.Key, [.. group.OrderBy(gate => gate == exported).Select(gate => gate.Method)]))]))];
    }

    // Weight: per-extraction cost plus the modules rebuilt per extraction. Support: modules shareable across extractions.
    internal static Dictionary<Gate, (int Weight, int Support)> Costs(string root, Gate[] gates)
    {
        Dictionary<string, bool> dependent = new(StringComparer.Ordinal);
        return gates.ToDictionary(gate => gate, gate =>
        {
            HashSet<string> sources = ProofSources(root, gate.Proof);
            int rebuilt = sources.Count(source => DependsOnExtraction(root, source, dependent));
            return (PerExtraction + rebuilt, sources.Count - rebuilt);
        });
    }

    // Heaviest first into the lightest bin; the pinned item opens bin 0, and ties keep input order.
    static List<T>[] Balance<T>(IEnumerable<T> items, Func<T, int> weight, int bins, T? pinned) where T : class
    {
        List<T>[] result = [.. Enumerable.Range(0, Math.Max(1, bins)).Select(_ => new List<T>())];
        int[] loads = new int[result.Length];
        IEnumerable<T> ordered = items.OrderByDescending(weight);
        if (pinned is not null) ordered = ordered.Where(item => !ReferenceEquals(item, pinned)).Prepend(pinned);
        foreach (T item in ordered)
        {
            int bin = Array.IndexOf(loads, loads.Min());
            result[bin].Add(item);
            loads[bin] += weight(item);
        }
        return result;
    }

    // Fixed cost of one extraction (integrity check, certificate and theorem audits), in module builds.
    const int PerExtraction = 6;

    // Modules importing Extracted are rebuilt for every extraction.
    static bool DependsOnExtraction(string root, string source, Dictionary<string, bool> memo)
    {
        if (memo.TryGetValue(source, out bool known)) return known;
        memo[source] = false;
        bool result = false;
        foreach (string module in Imports(Path.GetFullPath(source["verification/".Length..], root)))
        {
            string dependency = module.Replace('.', '/') + ".lean";
            result |= module == "Extracted" ||
                (File.Exists(Path.Combine(root, dependency)) && DependsOnExtraction(root, "verification/" + dependency, memo));
        }
        return memo[source] = result;
    }

    static IEnumerable<string> Imports(string path) =>
        Regex.Matches(File.ReadAllText(path), @"(?m)^\s*(?:public\s+)?import\s+([^\r\n]+)").SelectMany(import =>
            import.Groups[1].Value.Split("--")[0].Split((char[]?)null, StringSplitOptions.RemoveEmptyEntries));

    private static HashSet<string> ProofSources(string root, string proof)
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
            foreach (string module in Imports(path))
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
