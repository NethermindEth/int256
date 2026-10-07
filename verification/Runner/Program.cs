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
            if (arguments is ["safety-registry"])
            {
                Console.Write(JsonSerializer.Serialize(SafetyCatalog.Registry()));
                return 0;
            }
            if (arguments is ["safety" or "safety-representative" or "safety-module", string safetyMethod, string profile])
            {
                Console.Write(arguments[0] switch
                {
                    "safety" => SafetyCatalog.Gate(safetyMethod, profile).ToJsonString(),
                    "safety-representative" => SafetyCatalog.Representative(safetyMethod, profile).ToJsonString(),
                    _ => SafetyGates.Module(catalog, safetyMethod, profile)
                });
                return 0;
            }
            if (arguments is [string command, "--json"])
            {
                JsonNode input = JsonNode.Parse(Console.In.ReadToEnd())
                    ?? throw new ArgumentException("Expected JSON input");
                object result;
                switch (command)
                {
                    case "entries": result = Catalog.Entries(input.AsObject()); break;
                    case "manifest": result = catalog.Manifest(input.AsObject()); break;
                    case "native-limitations": result = catalog.NativeLimitations(input.AsArray().Select(Catalog.Text)); break;
                    case "calling-convention":
                        Catalog.CheckCallingConvention(input["actual"]!.AsObject(), input["expected"]!.AsObject());
                        result = true;
                        break;
                    case "fixture-groups":
                        JsonObject[] entries = input["entries"]!.AsArray().Select(node => node!.AsObject()).ToArray();
                        Catalog.ResolveFixtureGroups(entries, input["groups"]!.AsObject());
                        result = entries;
                        break;
                    default: throw new ArgumentException("Unknown JSON command");
                }
                Console.Write(JsonSerializer.Serialize(result));
                return 0;
            }
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
            bool safetyPlan = arguments.Count > 0 && arguments[0] == "plan" && arguments.Remove("--safety");
            JsonNode output = arguments.ToArray() switch
            {
                ["catalog"] => catalog.Snapshot(),
                ["manifest", string method] => catalog.Manifest(method),
                ["plan", "--expanded"] => catalog.Plan(catalog.MethodNames, safetyPlan),
                ["plan", "--method", string method] => catalog.Plan([method], safetyPlan),
                ["plan"] => catalog.Plan(Catalog.Legacy, safetyPlan),
                _ => throw new ArgumentException(
                    "Usage: Verification [--root <repository>] catalog | manifest <method> | gate <method> | safety[-module] <method> <profile> | plan [--expanded | --method <method>] [--safety]")
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
