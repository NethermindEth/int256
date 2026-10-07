// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System.Text.Json.Nodes;
using System.Text.RegularExpressions;

namespace UInt256Verification;

internal static class ProofAudits
{
    internal static string[] Names(Catalog catalog, string method)
    {
        if (!Catalog.Legacy.Contains(method))
        {
            JsonObject gate = catalog.Manifest(method)["verification"]!.AsObject();
            return [.. gate["auditedTheorems"]!.AsArray().Select(Catalog.Text),
                .. gate.ContainsKey("template") ? [] : AuditGates.BoundAuditNames(catalog.Entries()[method])];
        }
        (string theorem, string certificate) = method == "Add" ? ("checked_contract", "checked_add_family_certificate")
            : ("checked_subtract_contract", "checked_subtract_family_certificate");
        return [$"UInt256Proof.{theorem}", $"UInt256Proof.{theorem}_family", $"UInt256Proof.{certificate}", "UInt256Proof.checked_profile_representative"];
    }

    internal static Dictionary<string, string[]> Check(string output, IEnumerable<string> names, IEnumerable<string> approved)
    {
        HashSet<string> allowed = approved.ToHashSet(StringComparer.Ordinal);
        Dictionary<string, string[]> audits = [];
        foreach (string name in names)
        {
            MatchCollection matches = Regex.Matches(output, $"'{Regex.Escape(name)}' (?:depends on axioms: \\[([\\w.,\\s]*)\\]|does not depend on any axioms)");
            if (matches.Count != 1) throw new InvalidOperationException($"Missing or ambiguous theorem axiom audit: {name}");
            string[] axioms = matches[0].Groups[1].Value.Split(',', StringSplitOptions.TrimEntries | StringSplitOptions.RemoveEmptyEntries);
            if (axioms.Distinct(StringComparer.Ordinal).Count() != axioms.Length || axioms.Any(axiom => !allowed.Contains(axiom)))
                throw new InvalidOperationException($"Unapproved or duplicate axioms for {name}: {string.Join(", ", axioms)}");
            audits[name] = axioms;
        }
        return audits;
    }
}
