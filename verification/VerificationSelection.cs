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
        List<Batch> batches = [];
        foreach (IGrouping<string, Gate> group in selected.GroupBy(gate => gate.Profile))
        {
            Gate[] gates = group.ToArray();
            int count = Math.Min(8, gates.Length);
            for (int index = 0; index < count; index++)
                batches.Add(new($"{group.Key}-{index}", group.Key,
                    gates.Where((_, offset) => offset % count == index).Select(gate => gate.Method).ToArray()));
        }
        return new(full || changed.Any(path => path.StartsWith("verification/", StringComparison.Ordinal) && path.EndsWith(".lean", StringComparison.Ordinal)),
            selected, batches.ToArray());
    }

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
            foreach (Match import in Regex.Matches(File.ReadAllText(path), @"(?m)^\s*(?:public\s+)?import\s+([^\r\n]+)"))
                foreach (string module in import.Groups[1].Value.Split("--")[0].Split((char[]?)null, StringSplitOptions.RemoveEmptyEntries))
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
