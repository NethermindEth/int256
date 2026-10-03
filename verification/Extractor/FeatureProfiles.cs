using Mono.Cecil;
using System.Text.Json;
using System.Text.Json.Serialization;

internal enum Feature
{
    AdvSimd, Sse2, Ssse3, Sse42, Avx, Avx2, Avx512F, Avx512FVL, Bmi1,
    Sse41, Avx512DQ, Avx512DQVL, Bmi2, ArmBase64, Vector256Accelerated
}

// A profile describes runtime-visible capabilities, including runtime disabling.
// BMI1 is deliberately independent of AVX2. The x86 prerequisites follow .NET's
// documented inheritance, not merely combinations found on common processors.
internal sealed record FeatureProfile(string Name, string Architecture, int NativeWidth,
    bool LittleEndian, bool AdvSimd = false, bool Sse2 = false, bool Ssse3 = false,
    bool Sse42 = false, bool Avx = false, bool Avx2 = false,
    bool Avx512F = false, bool Avx512FVL = false, bool Bmi1 = false,
    bool Sse41 = false, bool Avx512DQ = false, bool Avx512DQVL = false,
    bool Bmi2 = false, bool ArmBase64 = false, bool Vector256Accelerated = false)
{
    internal static FeatureProfile Scalar { get; } = new("scalar", "scalar", 64, true);

    internal bool Get(Feature feature) => feature switch
    {
        Feature.AdvSimd => AdvSimd, Feature.Sse2 => Sse2, Feature.Ssse3 => Ssse3,
        Feature.Sse42 => Sse42, Feature.Avx => Avx, Feature.Avx2 => Avx2,
        Feature.Avx512F => Avx512F, Feature.Avx512FVL => Avx512FVL,
        Feature.Bmi1 => Bmi1, Feature.Sse41 => Sse41, Feature.Avx512DQ => Avx512DQ,
        Feature.Avx512DQVL => Avx512DQVL, Feature.Bmi2 => Bmi2, Feature.ArmBase64 => ArmBase64,
        Feature.Vector256Accelerated => Vector256Accelerated,
        _ => throw new InvalidDataException($"Unknown feature: {feature}")
    };

    internal void Validate()
    {
        if (string.IsNullOrWhiteSpace(Name) || NativeWidth != 64 || !LittleEndian || Architecture is not ("scalar" or "arm64" or "x64") ||
            ((AdvSimd || ArmBase64) && Architecture != "arm64") ||
            ((Sse2 || Ssse3 || Sse42 || Avx || Avx2 || Avx512F || Avx512FVL || Bmi1 || Sse41 || Avx512DQ || Avx512DQVL || Bmi2) && Architecture != "x64") ||
            (Ssse3 && !Sse2) || (Sse42 && (!Sse2 || !Ssse3)) ||
            (Avx2 && !Avx) || (Avx512FVL && !Avx512F) ||
            (Avx && !Sse42) || (Avx512F && !Avx2) ||
            (Sse41 && !Ssse3) || (Sse42 && !Sse41) ||
            (Avx512DQ && !Avx512F) || (Avx512DQVL && (!Avx512DQ || !Avx512FVL)) ||
            (AdvSimd && !ArmBase64))
            throw new InvalidDataException($"Invalid execution profile: {Name}");
    }

    internal static FeatureProfile Select(string name)
    {
        if (name.StartsWith('@'))
        {
            JsonSerializerOptions options = new()
            {
                PropertyNamingPolicy = JsonNamingPolicy.CamelCase,
                UnmappedMemberHandling = JsonUnmappedMemberHandling.Disallow
            };
            using JsonDocument document = JsonDocument.Parse(File.ReadAllText(name[1..]));
            string[] expected = JsonSerializer.SerializeToElement(Scalar, options).EnumerateObject()
                .Select(p => p.Name).Order().ToArray();
            string[] actual = document.RootElement.EnumerateObject().Select(p => p.Name).Order().ToArray();
            if (!actual.SequenceEqual(expected))
                throw new InvalidDataException("Execution profile requires every exact capability field");
            FeatureProfile selected = document.RootElement.Deserialize<FeatureProfile>(options)
                ?? throw new InvalidDataException("Missing execution profile");
            selected.Validate();
            return selected;
        }
        FeatureProfile profile = name switch
        {
            "scalar" => Scalar,
            "arm64-advsimd" => new(name, "arm64", 64, true, AdvSimd: true, ArmBase64: true),
            "arm64-armbase" => new(name, "arm64", 64, true, ArmBase64: true),
            "x64-sse41" => new(name, "x64", 64, true, Sse2: true, Ssse3: true, Sse41: true),
            "x64-vector256" => new(name, "x64", 64, true, Vector256Accelerated: true),
            "x64-bmi2" => new(name, "x64", 64, true, Bmi2: true),
            "x64-sse42" => new(name, "x64", 64, true, Sse2: true, Ssse3: true, Sse41: true, Sse42: true),
            "x64-avx2" or "x64-avx2-bmi1" => new(name, "x64", 64, true,
                Sse2: true, Ssse3: true, Sse41: true, Sse42: true, Avx: true, Avx2: true, Bmi1: name.EndsWith("-bmi1", StringComparison.Ordinal)),
            "x64-avx512" or "x64-avx512-bmi1" => new(name, "x64", 64, true,
                Sse2: true, Ssse3: true, Sse41: true, Sse42: true, Avx: true, Avx2: true,
                Avx512F: true, Avx512FVL: true, Bmi1: name.EndsWith("-bmi1", StringComparison.Ordinal)),
            _ => throw new ArgumentException($"Unknown execution profile: {name}")
        };
        profile.Validate();
        return profile;
    }

    internal string Lean => $"{{ architecture := .{Architecture}, nativeWidth := {NativeWidth}, littleEndian := {Bool(LittleEndian)}, " +
        $"advSimd := {Bool(AdvSimd)}, sse2 := {Bool(Sse2)}, ssse3 := {Bool(Ssse3)}, sse42 := {Bool(Sse42)}, " +
        $"avx := {Bool(Avx)}, avx2 := {Bool(Avx2)}, avx512F := {Bool(Avx512F)}, avx512FVL := {Bool(Avx512FVL)}, bmi1 := {Bool(Bmi1)}, " +
        $"sse41 := {Bool(Sse41)}, avx512DQ := {Bool(Avx512DQ)}, avx512DQVL := {Bool(Avx512DQVL)}, " +
        $"bmi2 := {Bool(Bmi2)}, armBase64 := {Bool(ArmBase64)}, vector256Accelerated := {Bool(Vector256Accelerated)} }}";

    internal Feature[] ClassifiedQueries => Avx2
        ? Avx512FVL
            ? [Feature.Avx2, Feature.Avx512FVL, Feature.Bmi1, Feature.Avx, Feature.Sse42, Feature.Ssse3, Feature.Sse2, Feature.Avx512F]
            : [Feature.Avx2, Feature.Avx512FVL, Feature.Bmi1, Feature.Avx, Feature.Sse42, Feature.Ssse3, Feature.Sse2]
        : AdvSimd ? [Feature.Avx2, Feature.AdvSimd, Feature.Avx512F, Feature.Avx512FVL]
        : Sse42 ? [Feature.Avx2, Feature.AdvSimd, Feature.Sse42, Feature.Sse2, Feature.Ssse3, Feature.Avx512F, Feature.Avx512FVL]
        : [Feature.Avx2, Feature.AdvSimd, Feature.Sse42, Feature.Avx512F, Feature.Avx512FVL];

    internal static string LeanFeature(Feature feature) =>
        "." + char.ToLowerInvariant(feature.ToString()[0]) + feature.ToString()[1..];

    private static string Bool(bool value) => value ? "true" : "false";

    internal static Feature? Getter(MethodReference reference)
    {
        if (reference.Name is not ("get_IsSupported" or "get_IsHardwareAccelerated") ||
            !reference.DeclaringType.FullName.StartsWith("System.Runtime.Intrinsics.", StringComparison.Ordinal)) return null;
        // Never reinterpret an unrecognised getter as a disabled capability.
        if (!RuntimeModels.ExactScope(reference.DeclaringType.Scope, "System.Runtime.Intrinsics") ||
            reference.HasThis || reference.ExplicitThis || reference.CallingConvention != MethodCallingConvention.Default ||
            reference.HasGenericParameters || reference.Parameters.Count != 0 ||
            reference.ReturnType.FullName != "System.Boolean" ||
            reference.FullName != $"System.Boolean {reference.DeclaringType.FullName}::{reference.Name}()")
            throw new InvalidDataException($"Unsupported feature getter: {reference.FullName} [{reference.DeclaringType.Scope.Name}]");
        RuntimeModels.ValidateSignature(reference);
        return reference.DeclaringType.FullName switch
        {
            "System.Runtime.Intrinsics.Vector256" when reference.Name == "get_IsHardwareAccelerated" => Feature.Vector256Accelerated,
            _ when reference.Name != "get_IsSupported" => throw new InvalidDataException($"Unclassified feature getter: {reference.FullName}"),
            "System.Runtime.Intrinsics.Arm.AdvSimd" => Feature.AdvSimd,
            "System.Runtime.Intrinsics.Arm.ArmBase/Arm64" => Feature.ArmBase64,
            "System.Runtime.Intrinsics.X86.Sse2" => Feature.Sse2,
            "System.Runtime.Intrinsics.X86.Ssse3" => Feature.Ssse3,
            "System.Runtime.Intrinsics.X86.Sse42" => Feature.Sse42,
            "System.Runtime.Intrinsics.X86.Sse41" => Feature.Sse41,
            "System.Runtime.Intrinsics.X86.Avx" => Feature.Avx,
            "System.Runtime.Intrinsics.X86.Avx2" => Feature.Avx2,
            "System.Runtime.Intrinsics.X86.Avx512F" => Feature.Avx512F,
            "System.Runtime.Intrinsics.X86.Avx512F/VL" => Feature.Avx512FVL,
            "System.Runtime.Intrinsics.X86.Bmi1" => Feature.Bmi1,
            "System.Runtime.Intrinsics.X86.Bmi2/X64" => Feature.Bmi2,
            "System.Runtime.Intrinsics.X86.Avx512DQ" => Feature.Avx512DQ,
            "System.Runtime.Intrinsics.X86.Avx512DQ/VL" => Feature.Avx512DQVL,
            _ => throw new InvalidDataException($"Unclassified feature getter: {reference.FullName}")
        };
    }
}
