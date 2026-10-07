// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System.Text.Json.Nodes;

namespace UInt256Verification;

internal static class FixtureChecks
{
    internal static void ChangedMethod(JsonObject artifact, JsonObject baseline, string signature)
    {
        JsonArray Instructions(JsonObject source)
        {
            JsonObject body = source["methods"]!.AsArray().Select(node => node!.AsObject())
                .FirstOrDefault(body => Catalog.Text(body["signature"]) == signature)
                ?? throw new InvalidOperationException($"Fixture omitted the intended compiled operation: {signature}");
            return new JsonArray(body["instructions"]!.AsArray().Select(item => (JsonNode)new JsonArray(
                item!["opcode"]?.DeepClone(), item["scope"]?.DeepClone(), item["operand"]?.DeepClone())).ToArray());
        }
        if (JsonNode.DeepEquals(Instructions(artifact), Instructions(baseline)))
            throw new InvalidOperationException("Fixture did not change the intended compiled operation");
    }

    internal static void SafetyReport(JsonObject report, string method, string profile)
    {
        if (report["evidenceKind"]?.GetValue<string>() != "arithmetic-and-memory-safety" || !JsonNode.DeepEquals(report["safety"], SafetyCatalog.Gate(method, profile)))
            throw new InvalidOperationException("Fixture prerequisite lacks the selected combined safety evidence");
    }

    internal static void Production(JsonObject production, JsonObject inputs)
    {
        if (Catalog.Text(production["source"]?["kind"]) != "production" || !JsonNode.DeepEquals(production["sourceInputs"], inputs))
            throw new InvalidOperationException("Fresh production prerequisite was not established");
    }

    internal static void Baseline(JsonObject production, JsonObject baseline, JsonObject inputs)
    {
        Production(production, inputs);
        if (!JsonNode.DeepEquals(baseline["leanSourceSha256"], production["leanSourceSha256"]))
            throw new InvalidOperationException("Fixture baseline changed handwritten proofs");
    }

    internal static void Alternative(JsonObject baseline, JsonObject alternative)
    {
        if (!JsonNode.DeepEquals(alternative["leanSourceSha256"], baseline["leanSourceSha256"]))
            throw new InvalidOperationException("Equivalent fixture changed handwritten proofs");
        if (JsonNode.DeepEquals(alternative["generatedProgramSha256"], baseline["generatedProgramSha256"]))
            throw new InvalidOperationException("Equivalent fixture did not change its actual extracted program");
    }
}
