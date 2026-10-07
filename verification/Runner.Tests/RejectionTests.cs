// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using UInt256Verification;

namespace UInt256VerificationTests;

internal static class RejectionTests
{
    internal static void Register(Action<string, Action<Catalog, string>> check)
    {
        const string module = "UInt256/Methods/Add/Entry.lean";
        const string goal = $"error: {module}:1:1: unsolved goals\n⊢ False\n";
        const string diagnostic = "omega could not prove the goal:";
        const string family = $"error: {module}:1:1: {diagnostic}\nProof checking failure: failed\n";
        check("family rejection requires exact diagnostic, module and public proof gate", (_, _) =>
        {
            RejectionChecks.Diagnostic(family, module, diagnostic);
            foreach (string text in new[] { family.Replace(module, "Other.lean"), family.Replace("Proof checking failure:", "Extraction failure:"),
                family + "error: Other.lean:1:1: unknown identifier\n", family.Replace(diagnostic, "unknown identifier") })
                Program.Reject(() => RejectionChecks.Diagnostic(text, module, diagnostic));
        });
        check("semantic rejection accepts supported final goal diagnostics", (_, _) =>
        {
            RejectionChecks.Semantic(goal + "error: build failed\n", module);
            RejectionChecks.Semantic($"error: {module}:1:1: `simp` made no progress\n", module);
            foreach (string headline in new[] { "Tactic `introN` failed: no binders", "Extracted storage operands differ from the required result:" })
                RejectionChecks.Semantic($"error: {module}:1:1: {headline}\n⊢ False\n", module);
            RejectionChecks.Semantic(goal.Replace('/', '\\').Replace("\n", "\r\n"), module);
        });
        check("semantic rejection excludes maintenance and wrong-module failures", (_, _) =>
        {
            foreach (string text in new[] { goal.Replace(module, "Other.lean"), goal + "error: Other.lean:1:1: unexpected token\n",
                goal + "error: Other.lean:1:1: unknown module prefix\n", $"error: {module}:1:1: unexpected token\n⊢ False\n",
                $"error: {module}:1:1: Extracted storage operands differ from the required result:\n", "" })
                Program.Reject(() => RejectionChecks.Semantic(text, module));
        });
        check("rejection excludes resource exhaustion including optional summaries", (_, _) =>
        {
            foreach (string marker in new[] { "maximum number of heartbeats", "maximum recursion depth", "maximum number of steps exceeded",
                "deep recursion", "stack overflow", "out of memory", "allocation failed", "killed", "timed out" })
            {
                Program.Reject(() => RejectionChecks.Semantic(goal + marker.ToUpperInvariant(), module));
                Program.Reject(() => RejectionChecks.Diagnostic(family + marker.ToUpperInvariant(), module, diagnostic));
                Program.Reject(() => RejectionChecks.Semantic("info: optional summary " + marker + "\n" + goal, module));
            }
        });
    }
}
