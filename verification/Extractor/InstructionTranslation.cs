using Mono.Cecil;
using Mono.Cecil.Cil;

internal static class InstructionTranslation
{
    internal static string? RuntimeModel(MethodReference reference, FeatureProfile? profile = null)
    {
        if (FeatureProfile.Getter(reference) is Feature feature)
            return ".feature " + FeatureProfile.LeanFeature(feature);
        return RuntimeModels.Translate(reference, profile ?? FeatureProfile.Scalar);
    }
    internal static string Translate(Instruction i, MethodDefinition m, MethodDefinition[] methods, int methodIndex, FeatureProfile? profile = null)
    {
        int Target() => m.Body.Instructions.IndexOf((Instruction)i.Operand);
        int Local() => ((VariableDefinition)i.Operand).Index;
        string Field(string op)
        {
            var f = (FieldReference)i.Operand;
            FieldDefinition resolved = f.Resolve() ?? throw new InvalidDataException("Unresolved field");
            RuntimeModels.ValidateTypeIdentity(f.DeclaringType, m.Module);
            RuntimeModels.ValidateTypeIdentity(f.FieldType, m.Module);
            if (resolved.DeclaringType.Module != m.Module || resolved.DeclaringType.FullName != "Nethermind.Int256.UInt256" || resolved.FieldType.FullName != "System.UInt64" ||
                resolved.Name.Length != 2 || resolved.Name[0] != 'u' || resolved.Name[1] < '0' || resolved.Name[1] > '3')
                throw new InvalidDataException($"Unsupported field {f.FullName}");
            return $".{op} ⟨{resolved.Name[1] - '0'}, by decide⟩";
        }
        if (i.OpCode.Code is Code.Ldobj or Code.Stobj && i.Operand is TypeReference operandType)
            RuntimeModels.ValidateTypeIdentity(operandType, m.Module);
        if (i.OpCode.Code is Code.Call or Code.Newobj)
        {
            var r = (MethodReference)i.Operand;
            if (RuntimeModel(r, profile) is string modeled) return modeled;
            MethodDefinition resolved = r.Resolve() ?? throw new InvalidDataException($"Unresolved method: {r.FullName}");
            int index = Array.IndexOf(methods, resolved);
            if (index > methodIndex) return $".call {index} {resolved.Parameters.Count}";
            throw new InvalidDataException($"Unsupported or unresolved call: {r.FullName} [{r.DeclaringType.Scope.Name}]");
        }
        return i.OpCode.Code switch
        {
            Code.Ldsflda => $".memory (.staticAddress {StaticData.LeanBytes(StaticData.Validate((FieldReference)i.Operand, m.Module))})",
            Code.Ldobj when ((TypeReference)i.Operand).FullName == "Nethermind.Int256.UInt256" => ".memory .load256",
            Code.Ldobj when ((TypeReference)i.Operand).FullName == "System.Runtime.Intrinsics.Vector128`1<System.UInt64>" => ".memory .load128",
            Code.Ldobj when ((TypeReference)i.Operand).FullName == "System.Runtime.Intrinsics.Vector256`1<System.UInt64>" => ".memory .load256",
            Code.Stobj when ((TypeReference)i.Operand).FullName == "System.Runtime.Intrinsics.Vector128`1<System.UInt64>" => ".memory .store128",
            Code.Stobj when ((TypeReference)i.Operand).FullName == "System.Runtime.Intrinsics.Vector256`1<System.UInt64>" => ".memory .store256",
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
            Code.Ldc_I4_2 => ".const32 2", Code.Ldc_I4_3 => ".const32 3", Code.Ldc_I4_4 => ".const32 4",
            Code.Ldc_I4_5 => ".const32 5", Code.Ldc_I4_6 => ".const32 6", Code.Ldc_I4_7 => ".const32 7", Code.Ldc_I4_8 => ".const32 8",
            Code.Ldc_I4 or Code.Ldc_I4_S => $".const32 (BitVec.ofInt 32 ({i.Operand}))",
            Code.Conv_I8 => ".convI8", Code.Conv_U => ".convU", Code.Conv_U1 => ".convU1", Code.Add => ".add",
            Code.Sub => ".sub",
            Code.And => ".band", Code.Or => ".bor", Code.Xor => ".bxor", Code.Mul when profile is not null && profile.Name != "scalar" => ".mul",
            Code.Shl => ".shl", Code.Shr => ".shr", Code.Shr_Un => ".shrUn", Code.Conv_I4 => ".convI4",
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
