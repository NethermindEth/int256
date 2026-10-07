// SPDX-FileCopyrightText: 2026 Demerzel Solutions Limited
// SPDX-License-Identifier: LGPL-3.0-only

using System.Text.Json.Nodes;

namespace UInt256Verification;

internal sealed class Catalog(string verificationDirectory)
{
    internal static readonly string[] Legacy = ["Add", "Subtract"];
    internal static readonly string[] Profiles =
    [
        "scalar", "arm64-advsimd", "x64-sse42", "x64-avx2", "x64-avx2-bmi1",
        "x64-avx512", "x64-avx512-bmi1"
    ];
    internal static readonly string[] MultiplyProfiles =
    [
        "scalar", "x64-vector256", "x64-avx2", "x64-avx2-vector256",
        "x64-avx512dqvl", "x64-avx512dqvl-vector256", "x64-bmi2", "x64-bmi2-vector256",
        "x64-avx2-bmi2", "x64-avx2-bmi2-vector256", "x64-avx512dqvl-bmi2",
        "x64-avx512dqvl-bmi2-vector256", "arm64-armbase", "arm64-armbase-vector256"
    ];

    private readonly string _manifests = Path.Combine(verificationDirectory, "manifests");

    private JsonObject Read(string name) => JsonNode.Parse(File.ReadAllText(Path.Combine(_manifests, name)))?.AsObject()
        ?? throw new InvalidOperationException($"Missing manifest: {name}");

    internal static string Text(JsonNode? node) => node is JsonValue value && value.TryGetValue(out string? text)
        ? text : throw new InvalidOperationException("Expected a string");

    private static bool Flag(JsonNode? node, bool fallback = false) => node is null ? fallback
        : node is JsonValue value && value.TryGetValue(out bool flag) ? flag
        : throw new InvalidOperationException("Expected a Boolean");

    private static bool Identifier(string value) => value.Length > 0 && value.All(char.IsAsciiLetterOrDigit);
    private static string[] Strings(JsonNode? node) => node is JsonArray array ? array.Select(Text).ToArray()
        : throw new InvalidOperationException("Expected a string array");
    private static JsonArray Array(IEnumerable<string> values) => new(values.Select(x => (JsonNode?)JsonValue.Create(x)).ToArray());

    internal Dictionary<string, JsonObject> Entries() => Entries(Read("api-coverage.json"));

    internal static Dictionary<string, JsonObject> Entries(JsonObject document)
    {
        if (document["schemaVersion"]?.GetValue<int>() != 1)
            throw new InvalidOperationException("Unsupported API coverage manifest schema");
        Dictionary<string, JsonObject> entries = [];
        HashSet<string> signatures = [];
        foreach (JsonNode? node in document["entries"]!.AsArray())
        {
            JsonObject entry = node!.AsObject();
            if (Text(entry["selection"]) != "selected") continue;
            string name = Text(entry["id"]);
            if (!Identifier(name) || Legacy.Contains(name))
                throw new InvalidOperationException("Invalid selected API selector");
            if (!entries.TryAdd(name, entry) || !signatures.Add(Text(entry["signature"])))
                throw new InvalidOperationException("Ambiguous selected API identity");
        }

        JsonObject groups = document.ContainsKey("fixtureGroups")
            ? document["fixtureGroups"]?.AsObject() ?? throw new InvalidOperationException("Invalid shared fixture groups")
            : [];
        ResolveFixtureGroups(entries.Values, groups);
        return entries;
    }

    internal static void ResolveFixtureGroups(IEnumerable<JsonObject> entries, JsonObject groups)
    {
        foreach ((string group, JsonNode? value) in groups)
        {
            JsonObject data = value?.AsObject() ?? throw new InvalidOperationException("Invalid shared fixture groups");
            string[] cases = Strings(data["cases"]);
            string source = Text(data["source"]);
            if (!Identifier(group) || data.Count != 2 || !data.ContainsKey("cases") || !data.ContainsKey("source")
                || cases.Length == 0 || cases.Any(x => !Identifier(x)) || cases.Distinct().Count() != cases.Length
                || Path.GetFileName(source) != source || !source.EndsWith(".cs", StringComparison.Ordinal))
                throw new InvalidOperationException($"Invalid shared fixture group: {group}");
        }
        foreach (JsonObject entry in entries)
        {
            if (entry["verification"] is not JsonObject gate || gate["fixtureGroup"] is not JsonValue groupValue
                || !groupValue.TryGetValue(out string? group) || !groups.TryGetPropertyValue(group, out JsonNode? data)) continue;
            if (gate.ContainsKey("fixtureCases") || gate.ContainsKey("fixtureSources"))
                throw new InvalidOperationException($"Shared fixture group has per-API overrides: {entry["id"]}");
            gate["fixtureCases"] = data!["cases"]!.DeepClone();
            JsonObject sources = [];
            foreach (string item in Strings(data["cases"])) sources[item] = Text(data["source"]);
            gate["fixtureSources"] = sources;
        }
    }

    internal string[] MethodNames => [.. Legacy, .. Entries().Keys];
    internal string[] ProfileNames => [.. Profiles, .. Directory.EnumerateFiles(Path.Combine(_manifests, "profiles"), "*.json")
        .Select(path => Path.GetFileNameWithoutExtension(path)).Order(StringComparer.Ordinal)];

    internal JsonObject Profile(string name)
    {
        if (ProfileNames.Contains(name) && !Profiles.Contains(name))
        {
            JsonObject profile = Read($"profiles/{name}.json");
            HashSet<string> expected = Profile("scalar").Select(x => char.ToLowerInvariant(x.Key[0]) + x.Key[1..]).ToHashSet();
            if (!expected.SetEquals(profile.Select(x => x.Key)) || Text(profile["name"]) != name)
                throw new InvalidOperationException("Named profile has incomplete or inconsistent capability fields");
            JsonObject result = [];
            foreach ((string key, JsonNode? value) in profile)
                result[char.ToUpperInvariant(key[0]) + key[1..]] = value?.DeepClone();
            return result;
        }
        if (!Profiles.Contains(name)) throw new InvalidOperationException($"Unclassified representative: {name}");
        bool x64 = name.StartsWith("x64-", StringComparison.Ordinal);
        bool avx = name.StartsWith("x64-avx", StringComparison.Ordinal);
        bool vl = name.StartsWith("x64-avx512", StringComparison.Ordinal);
        return new JsonObject
        {
            ["Name"] = name, ["Architecture"] = x64 ? "x64" : name == "arm64-advsimd" ? "arm64" : "scalar",
            ["NativeWidth"] = 64, ["LittleEndian"] = true, ["AdvSimd"] = name == "arm64-advsimd",
            ["Sse2"] = x64, ["Ssse3"] = x64, ["Sse42"] = x64, ["Avx"] = avx, ["Avx2"] = avx,
            ["Avx512F"] = vl, ["Avx512FVL"] = vl, ["Bmi1"] = name.EndsWith("-bmi1", StringComparison.Ordinal),
            ["Sse41"] = x64, ["Avx512DQ"] = false, ["Avx512DQVL"] = false, ["Bmi2"] = false,
            ["ArmBase64"] = name == "arm64-advsimd", ["Vector256Accelerated"] = false
        };
    }

    internal JsonObject Manifest(string name)
    {
        if (Legacy.Contains(name)) return Read($"{name.ToLowerInvariant()}.json");
        if (!Entries().TryGetValue(name, out JsonObject? entry))
            throw new ArgumentException($"Unknown verification method: {name}");
        return Manifest(entry);
    }

    internal JsonObject Manifest(JsonObject entry)
    {
        string name = Text(entry["id"]);
        JsonObject gate = entry["verification"]?.AsObject()
            ?? throw new InvalidOperationException($"Selected API proof is not implemented yet: {name}");
        string coverage = Text(gate["profileCoverage"]);
        string[] audited = Strings(gate["auditedTheorems"]);
        if (string.IsNullOrEmpty(Text(gate["auditTarget"])) || string.IsNullOrEmpty(Text(gate["contract"]))
            || audited.Length == 0 || coverage is not ("program-agreement" or "all-valid-profiles"))
            throw new InvalidOperationException($"Incomplete verification gate: {name}");
        if (audited.Any(string.IsNullOrEmpty) || audited.Distinct().Count() != audited.Length)
            throw new InvalidOperationException($"Invalid verification audit requirements: {name}");
        if (gate.ContainsKey("allProfiles") && gate["allProfiles"] is null)
            throw new InvalidOperationException($"Invalid verification audit requirements: {name}");
        bool all = Flag(gate["allProfiles"]);
        if (all != (coverage == "all-valid-profiles"))
            throw new InvalidOperationException($"Unbound all-profile contract gate: {name}");
        if (all && !audited.Skip(1).Contains(Text(gate["allProfilesTheorem"])))
            throw new InvalidOperationException($"Missing audited all-profile contract gate: {name}");
        if (gate["familyCoverage"] is JsonNode familyNode)
        {
            JsonObject family = familyNode.AsObject();
            if (family["kind"] is not JsonValue familyKind || !familyKind.TryGetValue(out string? kind))
                throw new InvalidOperationException($"Unbound feature-family contract gate: {name}");
            string[] expected = kind switch
            {
                "vector256-storage" => ["scalar", "x64-vector256"],
                "vector-reduction" => ["scalar", "x64-sse41", "x64-vector256"],
                "relational-dispatch" => ["scalar", "x64-vector256", "x64-avx2", "x64-avx512"],
                "multiply-dispatch-storage" => MultiplyProfiles,
                "feature-class" => Profiles,
                _ => throw new InvalidOperationException($"Unbound feature-family contract gate: {name}")
            };
            if (family.Count != 3 || !family.ContainsKey("theorem") || !family.ContainsKey("representatives")
                || !Strings(family["representatives"]).SequenceEqual(expected)
                || !audited.Skip(1).Contains(Text(family["theorem"])) || all)
                throw new InvalidOperationException($"Unbound feature-family contract gate: {name}");
        }
        if (gate.ContainsKey("template"))
        {
            List<string> names = ["UInt256Proof.Selected.checked_contract", "UInt256Proof.Selected.checked_profile_contract"];
            if (all)
            {
                names.Add("UInt256Proof.Selected.checked_all_profiles_contract");
                if (Text(gate["allProfilesTheorem"]) != names[^1])
                    throw new InvalidOperationException($"Typed all-profile audit identity differs: {name}");
            }
            else if (gate["familyCoverage"] is JsonObject family)
            {
                names.Add("UInt256Proof.Selected.checked_family_contract");
                if (Text(family["kind"]) != "vector256-storage" || Text(family["theorem"]) != names[^1])
                    throw new InvalidOperationException($"Typed family audit identity differs: {name}");
            }
            if (Text(gate["auditTarget"]) != "+UInt256.Methods.SelectedGate:olean" || !audited.SequenceEqual(names))
                throw new InvalidOperationException($"Typed template audit identities differ: {name}");
        }
        JsonObject manifest = Read("add.json");
        manifest["entry"] = entry["signature"]!.DeepClone();
        manifest["callingConvention"] = entry["callingConvention"]!.DeepClone();
        manifest["verification"] = gate.DeepClone();
        manifest["excluded"] = Array(["zkEVM build", "JIT and native machine code"]);
        manifest["callingAssumptions"]![0] = "Live readable UInt256 reference inputs; live writable output references where declared; "
            + "by-value operands are initial snapshots with their declared widths";
        return manifest;
    }

    internal JsonObject Snapshot()
    {
        JsonObject methods = [], profiles = [];
        foreach (string method in MethodNames) methods[method] = Manifest(method);
        foreach (string profile in ProfileNames) profiles[profile] = Profile(profile);
        return new JsonObject { ["methods"] = methods, ["profiles"] = profiles };
    }

    internal JsonArray NativeLimitations(IEnumerable<string> methods)
    {
        if (!methods.Any(method => !Legacy.Contains(method)
            && Manifest(method)["verification"]?["familyCoverage"]?["kind"]?.GetValue<string>() == "multiply-dispatch-storage"))
            return [];
        return JsonNode.Parse("""
            [{"kind":"runtime-jit-struct-copy","status":"observed-failure",
              "runtime":".NET 10.0.12","architecture":"Windows x64",
              "currentMain":{"commit":"d90dbf43be153cc7ba7f49bb271e0b7e56a81891",
                "standaloneCopy":"fails","multiplicationDefaultTiered":"fails","multiplicationFullyOptimized":"passes"},
              "condition":"Hardware intrinsics disabled; partially overlapping input/output",
              "witness":"verification/Tests/NativeMultiplyWitness/Program.cs",
              "minimalWitness":"verification/Tests/NativeStructCopyWitness/Program.cs",
              "scope":"The CIL proof does not establish native partial-overlap correctness",
              "notes":"verification/UInt256/Methods/Multiply/README.md"}]
            """)!.AsArray();
    }

    internal static void CheckCallingConvention(JsonObject actual, JsonObject expected)
    {
        static bool RequiredFlag(JsonNode? node) => node is JsonValue value && value.TryGetValue(out bool flag)
            ? flag : throw new InvalidOperationException("Expected a Boolean calling convention field");
        bool isStatic = RequiredFlag(expected["static"]);
        if (RequiredFlag(actual["isStatic"]) != isStatic || Text(actual["returnType"]) != Text(expected["returns"]))
            throw new InvalidOperationException("Extracted entry static/return convention differs from its selected contract");
        JsonArray parameters = actual["parameters"]?.AsArray() ?? [];
        JsonArray selected = expected["parameters"]!.AsArray();
        if (parameters.Count != selected.Count)
            throw new InvalidOperationException("Extracted entry parameter count changed");
        for (int i = 0; i < parameters.Count; i++)
            if (Text(parameters[i]!["type"]) != Text(selected[i]!["type"])
                || RequiredFlag(parameters[i]!["IsIn"]) != RequiredFlag(selected[i]!["isIn"])
                || RequiredFlag(parameters[i]!["IsOut"]) != RequiredFlag(selected[i]!["isOut"]))
                throw new InvalidOperationException("Extracted entry parameter type/direction changed");
        if (RequiredFlag(actual["hasThis"]) != !isStatic)
            throw new InvalidOperationException("Extracted implicit receiver convention changed");
    }

    internal JsonObject Plan(IReadOnlyList<string> methods, bool safety = false)
    {
        if (methods.Count == 0 || methods.Distinct().Count() != methods.Count)
            throw new InvalidOperationException("Coverage requires distinct selected methods");
        JsonArray include = [];
        foreach (string method in methods)
        {
            JsonObject manifest = Manifest(method);
            if (!Legacy.Contains(method) && manifest["verification"]!["familyCoverage"] is JsonObject selectedFamily)
                ValidateRepresentatives(selectedFamily);
            string[] profiles = Legacy.Contains(method) ? Profiles
                : Flag(manifest["verification"]!["allProfiles"]) ? ["scalar"]
                : manifest["verification"]!["familyCoverage"] is JsonObject family
                    ? Strings(family["representatives"])
                    : throw new InvalidOperationException($"Total feature coverage is not implemented yet: {method}");
            foreach (string profile in profiles)
            {
                if (safety && SafetyCatalog.Gate(method, profile)["coverage"]?["kind"]?.GetValue<string>() is not ("feature-family" or "all-profiles"))
                    throw new InvalidOperationException($"Total safety feature coverage is not implemented yet: {method}/{profile}");
                include.Add(new JsonObject { ["method"] = method, ["profile"] = profile });
            }
        }
        return new JsonObject { ["include"] = include };
    }

    private void ValidateRepresentatives(JsonObject family)
    {
        string kind = Text(family["kind"]);
        if (kind == "feature-class") return;
        List<Dictionary<string, bool>> required = kind switch
        {
            "vector256-storage" => [new() { ["Vector256Accelerated"] = false }, new() { ["Vector256Accelerated"] = true }],
            "vector-reduction" =>
            [
                new() { ["Vector256Accelerated"] = false, ["Sse41"] = false },
                new() { ["Vector256Accelerated"] = false, ["Sse41"] = true },
                new() { ["Vector256Accelerated"] = true }
            ],
            "relational-dispatch" =>
            [
                new() { ["Avx512FVL"] = false, ["Avx2"] = false, ["Vector256Accelerated"] = false },
                new() { ["Avx512FVL"] = false, ["Avx2"] = false, ["Vector256Accelerated"] = true },
                new() { ["Avx512FVL"] = false, ["Avx2"] = true }, new() { ["Avx512FVL"] = true }
            ],
            "multiply-dispatch-storage" => [],
            _ => throw new InvalidOperationException($"Unknown total feature family: {kind}")
        };
        if (kind == "multiply-dispatch-storage")
        {
            (bool Bmi2, bool Arm, bool Avx512, bool Avx2)[] arithmetic =
            [
                (false, false, false, false), (false, false, false, true), (false, false, true, true),
                (true, false, false, false), (true, false, false, true), (true, false, true, true),
                (false, true, false, false)
            ];
            foreach (var flags in arithmetic)
                foreach (bool storage in new[] { false, true })
                    required.Add(new() { ["Bmi2"] = flags.Bmi2, ["ArmBase64"] = flags.Arm,
                        ["Avx512DQVL"] = flags.Avx512, ["Avx2"] = flags.Avx2, ["Vector256Accelerated"] = storage });
        }
        string[] representatives = Strings(family["representatives"]);
        if (representatives.Length != required.Count)
            throw new InvalidOperationException("Incomplete feature-family representative premises");
        for (int i = 0; i < required.Count; i++)
        {
            JsonObject profile = Profile(representatives[i]);
            foreach ((string key, bool value) in required[i])
                if (profile[key] is null || Flag(profile[key]) != value)
                    throw new InvalidOperationException($"Feature-family representative premises differ: {representatives[i]}");
        }
    }
}
