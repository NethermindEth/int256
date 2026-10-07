// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System.Text.Json.Nodes;
using UInt256Verification;

namespace UInt256VerificationTests;

internal static class Program
{
    private static int Main()
    {
        string manifests = Path.Combine(Directory.GetCurrentDirectory(), "verification", "manifests");
        if (!Directory.Exists(manifests))
            throw new InvalidOperationException("Run the tests from the repository root");
        int passed = 0;
        void Check(string name, Action<Catalog, string> test)
        {
            string temporary = Path.Combine(Path.GetTempPath(), "int256-csharp-tests-" + Guid.NewGuid().ToString("N"));
            Directory.CreateDirectory(temporary);
            try
            {
                string destination = Path.Combine(temporary, "manifests");
                foreach (string path in Directory.EnumerateFiles(manifests, "*", SearchOption.AllDirectories))
                {
                    string target = Path.Combine(destination, Path.GetRelativePath(manifests, path));
                    Directory.CreateDirectory(Path.GetDirectoryName(target)!);
                    File.Copy(path, target);
                }
                test(new Catalog(temporary), destination);
                passed++;
                Console.WriteLine($"PASS {name}");
            }
            finally
            {
                Directory.Delete(temporary, recursive: true);
            }
        }

        Check("expanded production inventory", (catalog, _) =>
        {
            Require(catalog.MethodNames.Length == 87, "Selected API count changed");
            Require(catalog.Snapshot()["profiles"]!.AsObject().Count == 21, "Profile count changed");
            Require(catalog.Plan(catalog.MethodNames)["include"]!.AsArray().Count == 256, "Coverage plan changed");
        });
        Check("legacy default plan", (catalog, _) =>
            Require(catalog.Plan(Catalog.Legacy)["include"]!.AsArray().Count == 14, "Legacy coverage changed"));
        Check("empty and repeated selectors", (catalog, _) =>
        {
            Reject(() => catalog.Plan([]));
            Reject(() => catalog.Plan(["Add", "Add"]));
            Reject(() => catalog.Manifest("missing"));
            Reject(() => catalog.Profile("missing"));
        });

        (string Name, Action<JsonObject> Mutate)[] invalid =
        [
            ("schema", document => document["schemaVersion"] = 2),
            ("duplicate selector", document => document["entries"]!.AsArray().Add(Selected(document).DeepClone())),
            ("non-ASCII selector", document => Selected(document)["id"] = "Méthode"),
            ("reserved selector", document => Selected(document)["id"] = "Add"),
            ("missing audit", document => Gate(document).Remove("auditedTheorems")),
            ("empty audits", document => Gate(document)["auditedTheorems"] = new JsonArray()),
            ("duplicate audit", document =>
                Gate(document)["auditedTheorems"]!.AsArray().Add(Gate(document)["auditedTheorems"]![0]!.DeepClone())),
            ("Boolean audit flag", document => Gate(document)["allProfiles"] = "true"),
            ("null audit flag", document => Gate(document)["allProfiles"] = null),
            ("unbound all-profile coverage", document => Gate(document)["profileCoverage"] = "all-valid-profiles"),
            ("unknown coverage", document => Gate(document)["profileCoverage"] = "unchecked"),
            ("unaudited family theorem", document => Family(document)["theorem"] = "Unchecked.result"),
            ("missing family representative", document => Family(document)["representatives"]!.AsArray().RemoveAt(0)),
            ("extra family key", document => Family(document)["unchecked"] = true),
            ("fixture path escape", document => FirstGroup(document)["source"] = "../escape.cs"),
            ("duplicate fixture", document =>
                FirstGroup(document)["cases"]!.AsArray().Add(FirstGroup(document)["cases"]![0]!.DeepClone())),
            ("unknown fixture field", document => FirstGroup(document)["unchecked"] = true),
            ("null fixture groups", document => document["fixtureGroups"] = null)
        ];
        foreach ((string name, Action<JsonObject> mutate) in invalid)
        {
            Check(name, (catalog, directory) =>
            {
                Edit(Path.Combine(directory, "api-coverage.json"), mutate);
                Reject(() => catalog.Snapshot());
            });
        }
        Check("profile field set", (catalog, directory) =>
        {
            Edit(Path.Combine(directory, "profiles/x64-vector256.json"), profile => profile.Remove("avx2"));
            Reject(() => catalog.Profile("x64-vector256"));
        });
        Check("profile name binding", (catalog, directory) =>
        {
            Edit(Path.Combine(directory, "profiles/x64-vector256.json"), profile => profile["name"] = "scalar");
            Reject(() => catalog.Profile("x64-vector256"));
        });
        Check("family premises checked before planning", (catalog, directory) =>
        {
            Edit(Path.Combine(directory, "profiles/x64-vector256.json"), profile => profile["vector256Accelerated"] = false);
            Reject(() => catalog.Plan(catalog.MethodNames));
        });
        Check("null capability cannot satisfy a false premise", (catalog, directory) =>
        {
            Edit(Path.Combine(directory, "profiles/x64-bmi2.json"), profile => profile["vector256Accelerated"] = null);
            Reject(() => catalog.Plan(catalog.MethodNames));
        });
        GateTests.Register(Check);
        Console.WriteLine($"Passed {passed} C# verification tests.");
        return 0;
    }

    private static JsonObject Selected(JsonObject document) => document["entries"]!.AsArray()
        .Select(item => item!.AsObject()).First(entry => Catalog.Text(entry["selection"]) == "selected");

    private static JsonObject Gate(JsonObject document) => Selected(document)["verification"]!.AsObject();

    private static JsonObject Family(JsonObject document) => document["entries"]!.AsArray()
        .Select(item => item!["verification"]?["familyCoverage"]).First(item => item is not null)!.AsObject();

    private static JsonObject FirstGroup(JsonObject document) => document["fixtureGroups"]!.AsObject().First().Value!.AsObject();

    private static void Edit(string path, Action<JsonObject> edit)
    {
        JsonObject document = JsonNode.Parse(File.ReadAllText(path))!.AsObject();
        edit(document);
        File.WriteAllText(path, document.ToJsonString());
    }

    internal static void Require(bool condition, string message)
    {
        if (!condition) throw new InvalidOperationException(message);
    }

    internal static void Reject(Action action)
    {
        try { action(); }
        catch (Exception error) when (error is InvalidOperationException or ArgumentException) { return; }
        throw new InvalidOperationException("Malformed input was accepted");
    }
}
