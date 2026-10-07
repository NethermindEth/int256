// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System.Text.Json;
using System.Text.Json.Nodes;

namespace UInt256Verification;

internal static class Program
{
    private static int Main(string[] args)
    {
        try
        {
            string root = Directory.GetCurrentDirectory();
            List<string> arguments = [.. args];
            int rootIndex = arguments.IndexOf("--root");
            if (rootIndex >= 0)
            {
                if (rootIndex + 1 == arguments.Count)
                    throw new ArgumentException("--root requires a repository directory");
                root = Path.GetFullPath(arguments[rootIndex + 1]);
                arguments.RemoveRange(rootIndex, 2);
            }

            Catalog catalog = new(Path.Combine(root, "verification"));
            if (arguments is ["gate" or "bound-audits", "--entry-json"])
            {
                JsonObject entry = JsonNode.Parse(Console.In.ReadToEnd()) as JsonObject
                    ?? throw new ArgumentException("Expected an entry JSON object");
                Console.Write(arguments[0] == "gate" ? AuditGates.Module(entry)
                    : JsonSerializer.Serialize(AuditGates.BoundAuditNames(entry)));
                return 0;
            }
            if (arguments is ["gate", string selector])
            {
                _ = catalog.Manifest(selector);
                if (!catalog.Entries().TryGetValue(selector, out JsonObject? entry))
                    throw new ArgumentException("Legacy Add/Subtract use their existing static audit modules");
                Console.Write(AuditGates.Module(entry).ReplaceLineEndings("\n"));
                return 0;
            }
            JsonNode output = arguments.ToArray() switch
            {
                ["catalog"] => catalog.Snapshot(),
                ["manifest", string method] => catalog.Manifest(method),
                ["plan", "--expanded"] => catalog.Plan(catalog.MethodNames),
                ["plan", "--method", string method] => catalog.Plan([method]),
                ["plan"] => catalog.Plan(Catalog.Legacy),
                _ => throw new ArgumentException(
                    "Usage: Verification [--root <repository>] catalog | manifest <method> | gate <method> | plan [--expanded | --method <method>]")
            };
            Console.WriteLine(output.ToJsonString(new JsonSerializerOptions { WriteIndented = true }));
            return 0;
        }
        catch (Exception error) when (error is ArgumentException or InvalidOperationException or IOException or JsonException)
        {
            Console.Error.WriteLine($"Verification failed: {error.Message}");
            return 1;
        }
    }
}
