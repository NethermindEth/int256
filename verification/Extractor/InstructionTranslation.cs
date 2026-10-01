using Mono.Cecil;
using Mono.Cecil.Cil;

internal static class InstructionTranslation
{
    internal static bool Feature(MethodReference r) =>
        r.FullName is "System.Boolean System.Runtime.Intrinsics.X86.Avx2::get_IsSupported()" or
            "System.Boolean System.Runtime.Intrinsics.Arm.AdvSimd::get_IsSupported()" or
            "System.Boolean System.Runtime.Intrinsics.X86.Sse42::get_IsSupported()" &&
        r.DeclaringType.Scope.Name == "System.Runtime.Intrinsics";
    internal static string? RuntimeModel(MethodReference reference)
    {
        if (Feature(reference)) return ".featureDisabled";
        if (reference.DeclaringType.FullName != "System.Runtime.CompilerServices.Unsafe" ||
            reference.DeclaringType.Scope.Name != "System.Runtime") return null;
        return reference.FullName switch
        {
            "System.Void System.Runtime.CompilerServices.Unsafe::SkipInit<Nethermind.Int256.UInt256>(!!0&)" => ".skipInit",
            "!!0& System.Runtime.CompilerServices.Unsafe::AsRef<System.UInt64>(!!0&)" => ".asRef",
            _ => null
        };
    }
    internal static string Translate(Instruction i, MethodDefinition m, MethodDefinition[] methods, int methodIndex)
    {
        int Target() => m.Body.Instructions.IndexOf((Instruction)i.Operand);
        int Local() => ((VariableDefinition)i.Operand).Index;
        string Field(string op)
        {
            var f = (FieldReference)i.Operand;
            FieldDefinition resolved = f.Resolve() ?? throw new InvalidDataException("Unresolved field");
            if (resolved.DeclaringType.Module != m.Module || resolved.DeclaringType.FullName != "Nethermind.Int256.UInt256" || resolved.FieldType.FullName != "System.UInt64" ||
                resolved.Name.Length != 2 || resolved.Name[0] != 'u' || resolved.Name[1] < '0' || resolved.Name[1] > '3')
                throw new InvalidDataException($"Unsupported field {f.FullName}");
            return $".{op} ⟨{resolved.Name[1] - '0'}, by decide⟩";
        }
        if (i.OpCode.Code == Code.Call)
        {
            var r = (MethodReference)i.Operand;
            if (RuntimeModel(r) is string modeled) return modeled;
            MethodDefinition resolved = r.Resolve() ?? throw new InvalidDataException($"Unresolved method: {r.FullName}");
            int index = Array.IndexOf(methods, resolved);
            if (index > methodIndex) return $".call {index} {resolved.Parameters.Count}";
            throw new InvalidDataException($"Unsupported or unresolved call: {r.FullName} [{r.DeclaringType.Scope.Name}]");
        }
        return i.OpCode.Code switch
        {
            Code.Ldarg_0 => ".arg 0", Code.Ldarg_1 => ".arg 1", Code.Ldarg_2 => ".arg 2", Code.Ldarg_3 => ".arg 3",
            Code.Ldarg or Code.Ldarg_S => $".arg {((ParameterDefinition)i.Operand).Index}",
            Code.Ldloc_0 => ".local 0", Code.Ldloc_1 => ".local 1", Code.Ldloc_2 => ".local 2", Code.Ldloc_3 => ".local 3",
            Code.Ldloc or Code.Ldloc_S => $".local {Local()}",
            Code.Ldloca or Code.Ldloca_S => $".localAddr {Local()}",
            Code.Stloc_0 => ".setLocal 0", Code.Stloc_1 => ".setLocal 1", Code.Stloc_2 => ".setLocal 2", Code.Stloc_3 => ".setLocal 3",
            Code.Stloc or Code.Stloc_S => $".setLocal {Local()}",
            Code.Ldfld => Field("field"), Code.Ldflda => Field("fieldAddr"),
            Code.Ldc_I4_M1 => ".const32 (BitVec.ofInt 32 (-1))",
            Code.Ldc_I4_0 => ".const32 0", Code.Ldc_I4_1 => ".const32 1",
            Code.Ldc_I4 or Code.Ldc_I4_S => $".const32 (BitVec.ofInt 32 ({i.Operand}))",
            Code.Conv_I8 => ".convI8", Code.Add => ".add", Code.Or => ".bor",
            Code.Clt_Un => ".ltu", Code.Cgt_Un => ".gtu", Code.Ceq => ".eq",
            Code.Ldind_I8 => ".load64", Code.Stind_I8 => ".store64", Code.Dup => ".dup", Code.Pop => ".pop",
            Code.Br or Code.Br_S => $".branch {Target()}",
            Code.Brfalse or Code.Brfalse_S => $".brzero {Target()}",
            Code.Brtrue or Code.Brtrue_S => $".brnonzero {Target()}",
            Code.Blt_Un or Code.Blt_Un_S => $".bltu {Target()}",
            Code.Bge_Un or Code.Bge_Un_S => $".bgeu {Target()}",
            Code.Ret => ".ret",
            _ => throw new InvalidDataException($"Unsupported instruction: {i}")
        };
    }
}
