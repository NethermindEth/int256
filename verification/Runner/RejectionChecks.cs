// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System.Text.RegularExpressions;

namespace UInt256Verification;

// These diagnostics classify failures only after an independent kernel-checked
// full-contract refutation. They are not themselves evidence of a counterexample.
internal static class RejectionChecks
{
    internal static void Resources(string output)
    {
        string[] markers = ["maximum number of heartbeats", "maximum recursion depth", "maximum number of steps exceeded",
            "deep recursion", "stack overflow", "out of memory", "allocation failed", "killed", "timed out"];
        if (markers.Any(marker => output.Contains(marker, StringComparison.OrdinalIgnoreCase)))
            throw new InvalidOperationException("Mutation rejection was inconclusive due to exhausted proof resources");
    }

    internal static void Diagnostic(string output, string module, string diagnostic)
    {
        string normalized = output.Replace('\\', '/');
        Resources(normalized);
        string expected = $@"\Aerror: {Regex.Escape(module)}:\d+:\d+: (?:{diagnostic})\z";
        string[] errors = normalized.Replace("\r\n", "\n").Split('\n').Where(line => line.StartsWith("error: ", StringComparison.Ordinal)).ToArray();
        if (!errors.Any(line => Regex.IsMatch(line, expected))) throw new InvalidOperationException("Missing expected execution proof rejection");
        if (errors.Any(line => line != "error: build failed" && !Regex.IsMatch(line, expected)))
            throw new InvalidOperationException("Rejection included an unrelated proof failure");
        if (!output.Contains("Proof checking failure:", StringComparison.Ordinal))
            throw new InvalidOperationException("The complete public verifier did not reach its proof gate");
    }

    internal static void Semantic(string output, string module)
    {
        string normalized = output.Replace('\\', '/').Replace("\r\n", "\n");
        Resources(normalized);
        string[] errors = Regex.Split(normalized, @"(?=^error: )", RegexOptions.Multiline)
            .Where(block => block.StartsWith("error: ", StringComparison.Ordinal)).ToArray();
        string prefix = $"error: {module}:";
        const string noProgress = @":\d+:\d+: `simp` made no progress(?:\n|$)";
        if (!errors.Any(block => block.StartsWith(prefix, StringComparison.Ordinal) && (block.Contains('⊢') || Regex.IsMatch(block, noProgress))))
            throw new InvalidOperationException("Mutation failed outside the expected semantic proof obligation");
        foreach (string block in errors)
        {
            string headline = block.Split('\n')[0];
            if (headline == "error: build failed") continue;
            if (!block.StartsWith(prefix, StringComparison.Ordinal) || !(headline.Contains("unsolved goals", StringComparison.Ordinal)
                || headline.Contains("Tactic `introN` failed:", StringComparison.Ordinal)
                || headline.Contains("Extracted storage operands differ from the required result:", StringComparison.Ordinal)
                || Regex.IsMatch(headline + "\n", noProgress)))
                throw new InvalidOperationException("Mutation included an unrelated or maintenance proof failure");
        }
    }
}
