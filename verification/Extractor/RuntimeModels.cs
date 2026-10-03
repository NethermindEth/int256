using Mono.Cecil;

internal static class RuntimeModels
{
    private const string UInt256 = "Nethermind.Int256.UInt256";
    private static string Vector(int width, string element) => $"System.Runtime.Intrinsics.Vector{width}`1<{element}>";

    internal static bool ExactScope(IMetadataScope scope, string name) => scope is AssemblyNameReference assembly &&
        assembly.Name == name && assembly.Version == new Version(10, 0, 0, 0) &&
        string.IsNullOrEmpty(assembly.Culture) && Convert.ToHexString(assembly.PublicKeyToken).ToLowerInvariant() ==
            (name == "System.Runtime.Intrinsics" ? "cc7b13ffcd2ddd51" : "b03f5f7f11d50a3a");

    internal static bool SupportedType(TypeReference type)
    {
        string name = type.FullName;
        return name is "System.UInt32" or "System.Byte" or "System.UIntPtr" or "System.IntPtr" or
            "System.ReadOnlySpan`1<System.Byte>" ||
            (type is ByReferenceType byRef && SupportedType(byRef.ElementType)) ||
            new[] { 128, 256 }.Any(width => new[] { "System.UInt64", "System.Int64", "System.UInt32", "System.Int32", "System.Byte", "System.Double", "System.Single" }
                .Any(element => name == Vector(width, element)));
    }

    internal static bool HasRuntimeValueTypeBase(TypeDefinition type) =>
        type.BaseType is { FullName: "System.ValueType" } parent && ExactScope(parent.Scope, "System.Runtime");

    internal static void ValidateTypeIdentity(TypeReference type, ModuleDefinition module)
    {
        if (type is GenericParameter) return;
        if (type is GenericInstanceType generic)
        {
            if (generic.IsValueType != generic.ElementType.IsValueType)
                throw new InvalidDataException($"Unsupported type identity: {generic.FullName} (generic value-type encoding)");
            ValidateTypeIdentity(generic.ElementType, module);
            foreach (TypeReference argument in generic.GenericArguments) ValidateTypeIdentity(argument, module);
            return;
        }
        if (type is TypeSpecification specification)
        {
            ValidateTypeIdentity(specification.ElementType, module);
            return;
        }
        bool expectedValueType = type.FullName is UInt256 or "System.UInt64" or "System.Int64" or
            "System.UInt32" or "System.Int32" or "System.Byte" or "System.Boolean" or "System.Double" or "System.Single" or
            "System.IntPtr" or "System.UIntPtr" or "System.ReadOnlySpan`1" or
            "System.Runtime.Intrinsics.Vector128`1" or "System.Runtime.Intrinsics.Vector256`1";
        bool valid = type.IsValueType == expectedValueType && (type.FullName == UInt256
            ? type.Scope == module && type.Resolve() == module.GetType(UInt256)
            : ExactScope(type.Scope, type.FullName.StartsWith("System.Runtime.Intrinsics.", StringComparison.Ordinal)
                ? "System.Runtime.Intrinsics" : "System.Runtime")) &&
            (type.FullName != "System.Void" || type.MetadataType == MetadataType.Void);
        if (!valid) throw new InvalidDataException($"Unsupported type identity: {type.FullName} [{type.Scope}]");
    }

    internal static void ValidateSignature(MethodReference reference)
    {
        ValidateTypeIdentity(reference.DeclaringType, reference.Module);
        ValidateTypeIdentity(reference.ReturnType, reference.Module);
        foreach (ParameterDefinition parameter in reference.Parameters)
            ValidateTypeIdentity(parameter.ParameterType, reference.Module);
        if (reference is GenericInstanceMethod generic)
            foreach (TypeReference argument in generic.GenericArguments) ValidateTypeIdentity(argument, reference.Module);
    }

    internal static string? Translate(MethodReference reference, FeatureProfile profile)
    {
        if (reference.ExplicitThis || reference.CallingConvention == MethodCallingConvention.VarArg ||
            (reference.HasThis && reference.Name != ".ctor") ||
            (reference.Name == ".ctor" && !reference.HasThis)) return null;
        string scope = reference.DeclaringType.Scope.Name;
        if (scope is "System.Runtime" or "System.Runtime.Intrinsics" && !ExactScope(reference.DeclaringType.Scope, scope))
            throw new InvalidDataException($"Unsupported runtime assembly scope: {reference.FullName} [{reference.DeclaringType.Scope}]");
        string? op = scope switch
        {
            "System.Runtime" => Runtime(reference.FullName),
            "System.Runtime.Intrinsics" => Intrinsic(reference.FullName, profile),
            _ => null
        };
        if (op is not null) ValidateSignature(reference);
        return op;
    }

    private static string? Runtime(string signature) => signature switch
    {
        "System.Void System.Runtime.CompilerServices.Unsafe::SkipInit<Nethermind.Int256.UInt256>(!!0&)" => ".skipInit",
        "!!0& System.Runtime.CompilerServices.Unsafe::AsRef<System.UInt64>(!!0&)" => ".asRef",
        "!!0& System.Runtime.CompilerServices.Unsafe::AsRef<Nethermind.Int256.UInt256>(!!0&)" => ".memory .asRef",
        "!!1& System.Runtime.CompilerServices.Unsafe::As<Nethermind.Int256.UInt256,System.Runtime.Intrinsics.Vector128`1<System.UInt64>>(!!0&)" => ".memory .asRef",
        "!!1& System.Runtime.CompilerServices.Unsafe::As<Nethermind.Int256.UInt256,System.Runtime.Intrinsics.Vector256`1<System.UInt64>>(!!0&)" => ".memory .asRef",
        "!!1& System.Runtime.CompilerServices.Unsafe::As<Nethermind.Int256.UInt256,System.UInt64>(!!0&)" => ".memory .asRef",
        "!!0& System.Runtime.CompilerServices.Unsafe::Add<System.UInt64>(!!0&,System.Int32)" => ".memory (.add 8 true)",
        "!!1& System.Runtime.CompilerServices.Unsafe::As<System.Byte,System.Runtime.Intrinsics.Vector256`1<System.UInt64>>(!!0&)" => ".memory .asRef",
        "!!0& System.Runtime.CompilerServices.Unsafe::Add<System.Runtime.Intrinsics.Vector128`1<System.UInt64>>(!!0&,System.Int32)" => ".memory (.add 16 true)",
        "!!0& System.Runtime.CompilerServices.Unsafe::Add<System.Runtime.Intrinsics.Vector256`1<System.UInt64>>(!!0&,System.UIntPtr)" => ".memory (.add 32 false)",
        "!!1 System.Runtime.CompilerServices.Unsafe::BitCast<Nethermind.Int256.UInt256,System.Runtime.Intrinsics.Vector256`1<System.UInt64>>(!!0)" => ".memory .bitcast256",
        "!!1 System.Runtime.CompilerServices.Unsafe::BitCast<Nethermind.Int256.UInt256,System.Runtime.Intrinsics.Vector256`1<System.UInt32>>(!!0)" => ".memory .bitcast256",
        "!!1 System.Runtime.CompilerServices.Unsafe::BitCast<System.Runtime.Intrinsics.Vector256`1<System.UInt64>,Nethermind.Int256.UInt256>(!!0)" => ".memory .bitcast256",
        "!!1 System.Runtime.CompilerServices.Unsafe::BitCast<System.Byte,System.Boolean>(!!0)" => ".memory .bitcastByteBool",
        "!!0& System.Runtime.InteropServices.MemoryMarshal::GetReference<System.Byte>(System.ReadOnlySpan`1<!!0>)" => ".memory .spanReference",
        "System.Void System.ReadOnlySpan`1<System.Byte>::.ctor(System.Void*,System.Int32)" => ".memory .spanCreate",
        _ => null
    };

    private static string? Intrinsic(string signature, FeatureProfile profile)
    {
        string? Finish(string intrinsic, int argc, Feature? required = null)
        {
            if (required is Feature feature && !profile.Get(feature))
                throw new InvalidDataException($"Reachable intrinsic lacks {feature}: {signature}");
            return $".intrinsic ({intrinsic}) {argc}";
        }
        foreach (int width in new[] { 128, 256 })
        {
            string ulongVector = Vector(width, "System.UInt64");
            string genericVector = Vector(width, "!!0");
            string memberVector = Vector(width, "!0");
            string owner = $"System.Runtime.Intrinsics.Vector{width}";
            string genericOwner = Vector(width, "System.UInt64");
            foreach ((string name, string op) in new[] { ("op_Addition", "add64"), ("op_Subtraction", "sub64"),
                ("op_BitwiseAnd", "band"), ("op_BitwiseOr", "bor"), ("op_ExclusiveOr", "bxor") })
                if (signature == $"{memberVector} {genericOwner}::{name}({memberVector},{memberVector})")
                    return Finish($".vector (.{op} {width})", 2);
            foreach (string element in new[] { "System.UInt64", "System.UInt32", "System.Int32" })
            {
                string vectorOwner = Vector(width, element);
                foreach ((string name, string op) in new[] { ("op_BitwiseAnd", "band"), ("op_BitwiseOr", "bor"), ("op_ExclusiveOr", "bxor") })
                    if (signature == $"{memberVector} {vectorOwner}::{name}({memberVector},{memberVector})")
                        return Finish($".vector (.{op} {width})", 2);
                if (signature == $"System.Boolean {vectorOwner}::op_Equality({memberVector},{memberVector})")
                    return Finish($".vector (.equalsAll {width})", 2);
                if (signature == $"{memberVector} {vectorOwner}::op_OnesComplement({memberVector})")
                    return Finish($".vector (.bnot {width})", 1);
            }
            foreach ((string name, string op) in new[] { ("LessThan", "ltu64"), ("Equals", "eq64") })
                if (signature == $"{genericVector} {owner}::{name}<System.UInt64>({genericVector},{genericVector})")
                    return Finish($".vector (.{op} {width})", 2);
            if (signature == $"System.Boolean {owner}::EqualsAll<System.UInt64>({genericVector},{genericVector})")
                return Finish($".vector (.equalsAll {width})", 2);
            if (signature == $"!!0 {owner}::GetElement<System.UInt64>({genericVector},System.Int32)")
                return Finish($".vector (.extract64 {width})", 2);
            foreach (string element in new[] { "System.UInt64", "System.UInt32" })
                if (signature == $"{memberVector} {Vector(width, element)}::get_Zero()")
                    return Finish($".vector (.zero {width})", 0);
            if (signature == $"{memberVector} {genericOwner}::get_AllBitsSet()")
                return Finish($".vector (.ones {width})", 0);
            foreach ((string method, string target) in new[] { ("AsByte", "System.Byte"), ("AsUInt32", "System.UInt32"),
                ("AsInt64", "System.Int64"), ("AsDouble", "System.Double"), ("AsUInt64", "System.UInt64"),
                ("AsInt32", "System.Int32"), ("AsSingle", "System.Single") })
                foreach (string source in new[] { "System.UInt64", "System.Byte", "System.UInt32", "System.Int64", "System.Int32", "System.Single" })
                    if (signature == $"{Vector(width, target)} {owner}::{method}<{source}>({genericVector})")
                        return Finish($".vector (.reinterpret {width})", 1);
            if (signature == $"{Vector(width, "System.Int64")} {owner}::ShiftRightArithmetic({Vector(width, "System.Int64")},System.Int32)")
                return Finish($".vector (.ashr64 {width})", 2);
            if (signature == $"{ulongVector} {owner}::Create({string.Join(",", Enumerable.Repeat("System.UInt64", width / 64))})")
                return Finish($".vector (.create64 {width})", width / 64);
            if (signature == $"{ulongVector} {owner}::Create(System.UInt64)")
                return Finish($".vector (.create64 {width})", 1);
            if (signature == $"{ulongVector} {owner}::CreateScalar(System.UInt64)")
                return Finish($".vector (.createScalar64 {width})", 1);
            if (signature == $"{Vector(width, "System.UInt32")} {owner}::CreateScalar(System.UInt32)")
                return Finish($".vector (.createScalar32 {width})", 1);
            if (signature == $"System.UInt32 {owner}::ExtractMostSignificantBits<System.UInt64>({genericVector})")
                return Finish($".vector (.extractMSB64 {width})", 1);
            if (signature == $"!!0 {owner}::Sum<System.UInt64>({genericVector})")
                return Finish($".vector (.sum64 {width})", 1);
        }
        return signature switch
        {
            "System.Runtime.Intrinsics.Vector128`1<System.UInt64> System.Runtime.Intrinsics.Arm.AdvSimd::ExtractVector128(System.Runtime.Intrinsics.Vector128`1<System.UInt64>,System.Runtime.Intrinsics.Vector128`1<System.UInt64>,System.Byte)" => Finish(".advSimd .extract64", 3, Feature.AdvSimd),
            "System.Runtime.Intrinsics.Vector128`1<System.UInt64> System.Runtime.Intrinsics.X86.Sse2::ShiftLeftLogical128BitLane(System.Runtime.Intrinsics.Vector128`1<System.UInt64>,System.Byte)" => Finish(".sse .shiftLeftBytes", 2, Feature.Sse2),
            "System.Runtime.Intrinsics.Vector128`1<System.Byte> System.Runtime.Intrinsics.X86.Ssse3::AlignRight(System.Runtime.Intrinsics.Vector128`1<System.Byte>,System.Runtime.Intrinsics.Vector128`1<System.Byte>,System.Byte)" => Finish(".sse .alignBytes", 3, Feature.Ssse3),
            "System.Runtime.Intrinsics.Vector256`1<System.UInt64> System.Runtime.Intrinsics.X86.Avx2::Permute4x64(System.Runtime.Intrinsics.Vector256`1<System.UInt64>,System.Byte)" => Finish(".avx2 .permute4x64", 2, Feature.Avx2),
            "System.Runtime.Intrinsics.Vector256`1<System.UInt32> System.Runtime.Intrinsics.X86.Avx2::Blend(System.Runtime.Intrinsics.Vector256`1<System.UInt32>,System.Runtime.Intrinsics.Vector256`1<System.UInt32>,System.Byte)" => Finish(".avx2 .blend32", 3, Feature.Avx2),
            "System.Runtime.Intrinsics.Vector256`1<System.Int32> System.Runtime.Intrinsics.X86.Avx2::Blend(System.Runtime.Intrinsics.Vector256`1<System.Int32>,System.Runtime.Intrinsics.Vector256`1<System.Int32>,System.Byte)" => Finish(".avx2 .blend32", 3, Feature.Avx2),
            "System.Runtime.Intrinsics.Vector256`1<System.UInt64> System.Runtime.Intrinsics.X86.Avx2::Add(System.Runtime.Intrinsics.Vector256`1<System.UInt64>,System.Runtime.Intrinsics.Vector256`1<System.UInt64>)" => Finish(".avx2 .add64", 2, Feature.Avx2),
            "System.Runtime.Intrinsics.Vector256`1<System.UInt64> System.Runtime.Intrinsics.X86.Avx2::CompareEqual(System.Runtime.Intrinsics.Vector256`1<System.UInt64>,System.Runtime.Intrinsics.Vector256`1<System.UInt64>)" => Finish(".avx2 .eq64", 2, Feature.Avx2),
            "System.Runtime.Intrinsics.Vector256`1<System.UInt64> System.Runtime.Intrinsics.X86.Avx2::ShiftLeftLogical(System.Runtime.Intrinsics.Vector256`1<System.UInt64>,System.Byte)" => Finish(".avx2 .shl64", 2, Feature.Avx2),
            "System.Runtime.Intrinsics.Vector256`1<System.Int64> System.Runtime.Intrinsics.X86.Avx2::CompareGreaterThan(System.Runtime.Intrinsics.Vector256`1<System.Int64>,System.Runtime.Intrinsics.Vector256`1<System.Int64>)" => Finish(".avx2 .signedgt64", 2, Feature.Avx2),
            "System.Runtime.Intrinsics.Vector256`1<System.UInt64> System.Runtime.Intrinsics.X86.Avx2::Multiply(System.Runtime.Intrinsics.Vector256`1<System.UInt32>,System.Runtime.Intrinsics.Vector256`1<System.UInt32>)" => Finish(".avx2 .multiplyEven32", 2, Feature.Avx2),
            "System.Runtime.Intrinsics.Vector256`1<System.UInt64> System.Runtime.Intrinsics.X86.Avx2::ShiftRightLogical(System.Runtime.Intrinsics.Vector256`1<System.UInt64>,System.Byte)" => Finish(".avx2 .shr64", 2, Feature.Avx2),
            "System.Runtime.Intrinsics.Vector256`1<System.UInt64> System.Runtime.Intrinsics.X86.Avx512F/VL::AlignRight64(System.Runtime.Intrinsics.Vector256`1<System.UInt64>,System.Runtime.Intrinsics.Vector256`1<System.UInt64>,System.Byte)" => Finish(".avx512 .alignRight64", 3, Feature.Avx512FVL),
            "System.Runtime.Intrinsics.Vector256`1<System.UInt64> System.Runtime.Intrinsics.X86.Avx512F/VL::TernaryLogic(System.Runtime.Intrinsics.Vector256`1<System.UInt64>,System.Runtime.Intrinsics.Vector256`1<System.UInt64>,System.Runtime.Intrinsics.Vector256`1<System.UInt64>,System.Byte)" => Finish(".avx512 .ternaryLogic", 4, Feature.Avx512FVL),
            "System.Runtime.Intrinsics.Vector256`1<System.UInt64> System.Runtime.Intrinsics.X86.Avx512F/VL::CompareLessThan(System.Runtime.Intrinsics.Vector256`1<System.UInt64>,System.Runtime.Intrinsics.Vector256`1<System.UInt64>)" => Finish(".avx512 .ltu64", 2, Feature.Avx512FVL),
            "System.Runtime.Intrinsics.Vector256`1<System.UInt64> System.Runtime.Intrinsics.X86.Avx512F/VL::CompareGreaterThan(System.Runtime.Intrinsics.Vector256`1<System.UInt64>,System.Runtime.Intrinsics.Vector256`1<System.UInt64>)" => Finish(".avx512 .gtu64", 2, Feature.Avx512FVL),
            "System.Runtime.Intrinsics.Vector256`1<System.UInt64> System.Runtime.Intrinsics.X86.Avx512F/VL::CompareGreaterThanOrEqual(System.Runtime.Intrinsics.Vector256`1<System.UInt64>,System.Runtime.Intrinsics.Vector256`1<System.UInt64>)" => Finish(".avx512 .geu64", 2, Feature.Avx512FVL),
            "System.Int32 System.Runtime.Intrinsics.X86.Avx512DQ::MoveMask(System.Runtime.Intrinsics.Vector256`1<System.UInt64>)" => Finish(".avx512DQ .moveMask64", 1, Feature.Avx512DQ),
            "System.Runtime.Intrinsics.Vector256`1<System.UInt64> System.Runtime.Intrinsics.X86.Avx512DQ/VL::MultiplyLow(System.Runtime.Intrinsics.Vector256`1<System.UInt64>,System.Runtime.Intrinsics.Vector256`1<System.UInt64>)" => Finish(".avx512DQ .mul64", 2, Feature.Avx512DQVL),
            "System.Int32 System.Runtime.Intrinsics.X86.Avx::MoveMask(System.Runtime.Intrinsics.Vector256`1<System.Double>)" => Finish(".avx .moveMask64", 1, Feature.Avx),
            "System.Int32 System.Runtime.Intrinsics.X86.Avx::MoveMask(System.Runtime.Intrinsics.Vector256`1<System.Single>)" => Finish(".avx .moveMask32", 1, Feature.Avx),
            "System.Runtime.Intrinsics.Vector256`1<System.Single> System.Runtime.Intrinsics.X86.Avx::Blend(System.Runtime.Intrinsics.Vector256`1<System.Single>,System.Runtime.Intrinsics.Vector256`1<System.Single>,System.Byte)" => Finish(".avx .blend32", 3, Feature.Avx),
            "System.Boolean System.Runtime.Intrinsics.X86.Avx::TestZ(System.Runtime.Intrinsics.Vector256`1<System.UInt64>,System.Runtime.Intrinsics.Vector256`1<System.UInt64>)" => Finish(".avx .testZ64", 2, Feature.Avx),
            "System.UInt32 System.Runtime.Intrinsics.X86.Bmi1::BitFieldExtract(System.UInt32,System.Byte,System.Byte)" => Finish(".bmi1 .bextr32", 3, Feature.Bmi1),
            "System.UInt64 System.Runtime.Intrinsics.X86.Bmi2/X64::MultiplyNoFlags(System.UInt64,System.UInt64)" => Finish(".bmi2 .multiplyHigh64", 2, Feature.Bmi2),
            "System.UInt64 System.Runtime.Intrinsics.Arm.ArmBase/Arm64::MultiplyHigh(System.UInt64,System.UInt64)" => Finish(".armBase64 .multiplyHigh64", 2, Feature.ArmBase64),
            _ => null
        };
    }
}
