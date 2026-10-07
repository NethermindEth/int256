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
            JsonNode output = arguments.ToArray() switch
            {
                ["catalog"] => catalog.Snapshot(),
                ["manifest", string method] => catalog.Manifest(method),
                ["plan", "--expanded"] => catalog.Plan(catalog.MethodNames),
                ["plan", "--method", string method] => catalog.Plan([method]),
                ["plan"] => catalog.Plan(Catalog.Legacy),
                _ => throw new ArgumentException(
                    "Usage: Verification [--root <repository>] catalog | manifest <method> | plan [--expanded | --method <method>]")
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
