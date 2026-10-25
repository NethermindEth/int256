// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: MIT

// Production certificates cover every overload; fixture checks cover distinct helpers and wrapper faults.
internal static class EqualityCoverage
{
    internal static readonly IReadOnlyDictionary<string, string> Helpers = new Dictionary<string, string>
    {
        ["EqualsInt32"] = "EqualsInt32",
        ["EqUInt256Int32"] = "EqualsInt32", ["EqInt32UInt256"] = "EqualsInt32",
        ["NeUInt256Int32"] = "EqualsInt32", ["NeInt32UInt256"] = "EqualsInt32",
        ["EqualsInt64"] = "EqualsInt64",
        ["EqUInt256Int64"] = "EqualsInt64", ["EqInt64UInt256"] = "EqualsInt64",
        ["NeUInt256Int64"] = "EqualsInt64", ["NeInt64UInt256"] = "EqualsInt64",
        ["EqualsUInt32"] = "EqualsUInt32",
        ["EqUInt256UInt32"] = "EqualsUInt32", ["EqUInt32UInt256"] = "EqualsUInt32",
        ["NeUInt256UInt32"] = "EqualsUInt32", ["NeUInt32UInt256"] = "EqualsUInt32",
        ["EqualsUInt64"] = "EqualsUInt64",
        ["EqUInt256UInt64"] = "EqualsUInt64", ["EqUInt64UInt256"] = "EqualsUInt64",
        ["NeUInt256UInt64"] = "EqualsUInt64", ["NeUInt64UInt256"] = "EqualsUInt64",
        ["EqualsUInt256Ref"] = "EqualsUInt256Ref",
        ["EqUInt256UInt256"] = "EqualsUInt256Ref", ["NeUInt256UInt256"] = "EqualsUInt256Ref",
        ["EqualsUInt256Value"] = "EqualsUInt256Value"
    };

    internal static bool Applicable(string fixture, string method, string profile)
    {
        if (!Helpers.TryGetValue(method, out var helper))
            throw new InvalidOperationException("Equality overload needs a coverage mapping: " + method);
        return fixture switch
        {
            "Baseline" or "Renamed" => true,
            "EquivalentReduction" => profile != "scalar",
            "WrongLane" or "WrongReduction" or "WrongReceiver" =>
                helper == "EqualsUInt256Ref" || method == "EqualsUInt256Value",
            "WrongSignedEmbedding" => helper is "EqualsInt32" or "EqualsInt64",
            "WrongPolarity" => method.StartsWith("Ne", StringComparison.Ordinal),
            "WrongSnapshot" => method == "EqualsUInt256Value",
            _ => throw new InvalidOperationException("Equality fixture needs a coverage mapping: " + fixture)
        };
    }

    internal static string Representative(string fixture, string method)
    {
        if (!Helpers.TryGetValue(method, out var helper))
            throw new InvalidOperationException("Equality overload needs a coverage mapping: " + method);
        return fixture switch
        {
            // Retain reversed signed, primitive negation, and nested reference wrappers end to end.
            "Baseline" or "Renamed" or "EquivalentReduction" =>
                method is "EqInt32UInt256" or "NeUInt256UInt64" or "NeUInt256UInt256" ? method : helper,
            "WrongLane" or "WrongReduction" or "WrongReceiver" => "EqualsUInt256Ref",
            "WrongSignedEmbedding" => helper,
            // These faults are in the wrappers themselves, not in a shared helper.
            "WrongPolarity" or "WrongSnapshot" => method,
            _ => throw new InvalidOperationException("Equality fixture needs a coverage mapping: " + fixture)
        };
    }
}
