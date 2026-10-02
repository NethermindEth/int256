using Mono.Cecil;

internal enum Feature
{
    AdvSimd, Sse2, Ssse3, Sse42, Avx, Avx2, Avx512F, Avx512FVL, Bmi1
}

// A profile describes runtime-visible capabilities, including runtime disabling.
// BMI1 is deliberately independent of AVX2. Prerequisites here are those required
// by reachable operations, rather than assumptions about usual CPU combinations.
internal sealed record FeatureProfile(string Name, string Architecture, int NativeWidth,
    bool LittleEndian, bool AdvSimd = false, bool Sse2 = false, bool Ssse3 = false,
    bool Sse42 = false, bool Avx = false, bool Avx2 = false,
    bool Avx512F = false, bool Avx512FVL = false, bool Bmi1 = false)
{
    internal static FeatureProfile Scalar { get; } = new("scalar", "scalar", 64, true);

    internal bool Get(Feature feature) => feature switch
    {
        Feature.AdvSimd => AdvSimd, Feature.Sse2 => Sse2, Feature.Ssse3 => Ssse3,
        Feature.Sse42 => Sse42, Feature.Avx => Avx, Feature.Avx2 => Avx2,
        Feature.Avx512F => Avx512F, Feature.Avx512FVL => Avx512FVL,
        Feature.Bmi1 => Bmi1,
        _ => throw new InvalidDataException($"Unknown feature: {feature}")
    };

    internal void Validate()
    {
        if (NativeWidth != 64 || !LittleEndian || Architecture is not ("scalar" or "arm64" or "x64") ||
            (AdvSimd && Architecture != "arm64") ||
            ((Sse2 || Ssse3 || Sse42 || Avx || Avx2 || Avx512F || Avx512FVL || Bmi1) && Architecture != "x64") ||
            (Ssse3 && !Sse2) || (Sse42 && (!Sse2 || !Ssse3)) ||
            (Avx2 && !Avx) || (Avx512FVL && !Avx512F))
            throw new InvalidDataException($"Invalid execution profile: {Name}");
    }

    internal static FeatureProfile Select(string name)
    {
        FeatureProfile profile = name switch
        {
            "scalar" => Scalar,
            "arm64-advsimd" => new(name, "arm64", 64, true, AdvSimd: true),
            "x64-sse42" => new(name, "x64", 64, true, Sse2: true, Ssse3: true, Sse42: true),
            "x64-avx2" or "x64-avx2-bmi1" => new(name, "x64", 64, true,
                Sse2: true, Ssse3: true, Sse42: true, Avx: true, Avx2: true, Bmi1: name.EndsWith("-bmi1", StringComparison.Ordinal)),
            "x64-avx512" or "x64-avx512-bmi1" => new(name, "x64", 64, true,
                Sse2: true, Ssse3: true, Sse42: true, Avx: true, Avx2: true,
                Avx512F: true, Avx512FVL: true, Bmi1: name.EndsWith("-bmi1", StringComparison.Ordinal)),
            _ => throw new ArgumentException($"Unknown execution profile: {name}")
        };
        profile.Validate();
        return profile;
    }

    internal string Lean => $"{{ architecture := .{Architecture}, nativeWidth := {NativeWidth}, littleEndian := {Bool(LittleEndian)}, " +
        $"advSimd := {Bool(AdvSimd)}, sse2 := {Bool(Sse2)}, ssse3 := {Bool(Ssse3)}, sse42 := {Bool(Sse42)}, " +
        $"avx := {Bool(Avx)}, avx2 := {Bool(Avx2)}, avx512F := {Bool(Avx512F)}, avx512FVL := {Bool(Avx512FVL)}, bmi1 := {Bool(Bmi1)} }}";

    internal Feature[] ClassifiedQueries => Avx2
        ? [Feature.Avx2, Feature.Avx512FVL, Feature.Bmi1]
        : AdvSimd ? [Feature.Avx2, Feature.AdvSimd] : [Feature.Avx2, Feature.AdvSimd, Feature.Sse42];

    internal static string LeanFeature(Feature feature) =>
        "." + char.ToLowerInvariant(feature.ToString()[0]) + feature.ToString()[1..];

    private static string Bool(bool value) => value ? "true" : "false";

    internal static Feature? Getter(MethodReference reference)
    {
        if (reference.Name != "get_IsSupported" ||
            !reference.DeclaringType.FullName.StartsWith("System.Runtime.Intrinsics.", StringComparison.Ordinal)) return null;
        // Never reinterpret an unrecognised getter as a disabled capability.
        if (!RuntimeModels.ExactScope(reference.DeclaringType.Scope, "System.Runtime.Intrinsics") ||
            reference.HasThis || reference.ExplicitThis || reference.CallingConvention != MethodCallingConvention.Default ||
            reference.HasGenericParameters || reference.Parameters.Count != 0 ||
            reference.ReturnType.FullName != "System.Boolean" ||
            reference.FullName != $"System.Boolean {reference.DeclaringType.FullName}::get_IsSupported()")
            throw new InvalidDataException($"Unsupported feature getter: {reference.FullName} [{reference.DeclaringType.Scope.Name}]");
        RuntimeModels.ValidateSignature(reference);
        return reference.DeclaringType.FullName switch
        {
            "System.Runtime.Intrinsics.Arm.AdvSimd" => Feature.AdvSimd,
            "System.Runtime.Intrinsics.X86.Sse2" => Feature.Sse2,
            "System.Runtime.Intrinsics.X86.Ssse3" => Feature.Ssse3,
            "System.Runtime.Intrinsics.X86.Sse42" => Feature.Sse42,
            "System.Runtime.Intrinsics.X86.Avx" => Feature.Avx,
            "System.Runtime.Intrinsics.X86.Avx2" => Feature.Avx2,
            "System.Runtime.Intrinsics.X86.Avx512F" => Feature.Avx512F,
            "System.Runtime.Intrinsics.X86.Avx512F/VL" => Feature.Avx512FVL,
            "System.Runtime.Intrinsics.X86.Bmi1" => Feature.Bmi1,
            _ => throw new InvalidDataException($"Unclassified feature getter: {reference.FullName}")
        };
    }
}
