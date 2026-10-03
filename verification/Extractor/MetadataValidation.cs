using Mono.Cecil;
using Mono.Cecil.Cil;

internal static class MetadataValidation
{
    internal const string UInt256Reference = "Nethermind.Int256.UInt256&";
    internal const string EntrySignature = "System.Void Nethermind.Int256.UInt256::Add(Nethermind.Int256.UInt256&,Nethermind.Int256.UInt256&,Nethermind.Int256.UInt256&)";

    internal static (TypeDefinition Type, MethodDefinition[] Methods) Validate(ModuleDefinition module, string entrySignature = EntrySignature, FeatureProfile? selectedProfile = null, EntrySelection? selectedEntry = null)
    {
        FeatureProfile profile = selectedProfile ?? FeatureProfile.Scalar;
        profile.Validate();
        string? AttributeValue(string name) => module.Assembly.CustomAttributes
            .SingleOrDefault(a => a.AttributeType.FullName == name)?.ConstructorArguments.Single().Value as string;
        if (module.Assembly.Name.Name != "Nethermind.Int256" ||
            AttributeValue("System.Runtime.Versioning.TargetFrameworkAttribute") != ".NETCoreApp,Version=v10.0" ||
            AttributeValue("System.Reflection.AssemblyConfigurationAttribute") != "Release")
            throw new InvalidDataException("Unsupported assembly identity, target framework or build configuration");
        TypeDefinition type = module.GetType("Nethermind.Int256.UInt256") ?? throw new InvalidDataException("UInt256 missing");
        if (!type.IsValueType || !RuntimeModels.HasRuntimeValueTypeBase(type) || !type.IsExplicitLayout || type.ClassSize is not (-1 or 0 or 32) ||
            type.Fields.Count(f => !f.IsStatic) != 4)
            throw new InvalidDataException("Unsupported UInt256 layout");
        for (int i = 0; i < 4; i++)
        {
            FieldDefinition f = type.Fields.Single(f => f.Name == $"u{i}");
            if (f.IsStatic || f.FieldType.FullName != "System.UInt64" || f.Offset != i * 8)
                throw new InvalidDataException($"Unsupported field: {f.FullName}");
            RuntimeModels.ValidateTypeIdentity(f.FieldType, module);
        }
        MethodDefinition entry = type.Methods.SingleOrDefault(m => m.FullName == entrySignature)
            ?? throw new InvalidDataException("Entry calling signature changed");
        (selectedEntry ?? EntrySelection.Select(entrySignature == EntrySignature ? "Add" :
            entrySignature == SelectedEntry("Subtract") ? "Subtract" :
            entrySignature == SelectedEntry("AddOverflow") ? "AddOverflow" : "SubtractUnderflow", null)).Validate(entry);

        // Discover the managed dependency DAG in the selected runtime environment.
        // No private name, number of methods or decomposition is prescribed.
        Dictionary<MethodDefinition, int> state = [];
        List<MethodDefinition> reverseOrder = [];
        void Visit(MethodDefinition method)
        {
            if (state.TryGetValue(method, out int visited))
            {
                if (visited == 1) throw new InvalidDataException("Recursive managed dependency");
                return;
            }
            // Only UInt256 initialisation is covered by the calling precondition.
            // Both explicit and beforefieldinit constructors on other types can
            // execute code that the method-body interpreter does not model.
            if (method.DeclaringType != type && method.DeclaringType.Methods.Any(m => m.IsConstructor && m.IsStatic))
                throw new InvalidDataException($"Unmodelled static initialisation: {method.DeclaringType.FullName}");
            if ((!method.IsStatic && method.DeclaringType != type) || method.ExplicitThis ||
                method.CallingConvention == MethodCallingConvention.VarArg ||
                !method.HasBody || method.HasGenericParameters || method.DeclaringType.HasGenericParameters ||
                method.Body.Instructions.Count == 0 || method.Body.ExceptionHandlers.Count != 0 ||
                !SupportedType(method.ReturnType, returns: true) || method.Parameters.Any(p => !SupportedType(p.ParameterType)))
                throw new InvalidDataException($"Unsupported method metadata: {method.FullName}");
            RuntimeModels.ValidateTypeIdentity(method.ReturnType, module);
            foreach (ParameterDefinition parameter in method.Parameters)
                RuntimeModels.ValidateTypeIdentity(parameter.ParameterType, module);
            foreach (VariableDefinition local in method.Body.Variables)
                RuntimeModels.ValidateTypeIdentity(local.VariableType, module);
            state[method] = 1;
            foreach (Instruction instruction in Reachability.Analyze(method, profile))
            {
                if (instruction.OpCode.Code is not (Code.Call or Code.Newobj) || instruction.Operand is not MethodReference reference ||
                    InstructionTranslation.RuntimeModel(reference, profile) is not null) continue;
                RuntimeModels.ValidateTypeIdentity(reference.ReturnType, module);
                foreach (ParameterDefinition parameter in reference.Parameters)
                    RuntimeModels.ValidateTypeIdentity(parameter.ParameterType, module);
                MethodDefinition callee = reference.Resolve()
                    ?? throw new InvalidDataException($"Unresolved method: {reference.FullName}");
                if (callee.Module != module)
                    throw new InvalidDataException($"Unsupported external dependency: {reference.FullName}");
                Visit(callee);
            }
            state[method] = 2;
            reverseOrder.Add(method);
        }
        Visit(entry);
        reverseOrder.Reverse();
        return (type, reverseOrder.ToArray());
    }

    private static bool SupportedType(TypeReference type, bool returns = false) => RuntimeModels.SupportedType(type) || type.FullName is
        "System.UInt64" or "System.Int64" or "System.Boolean" or "System.Int32" or "Nethermind.Int256.UInt256" ||
        (returns ? type.FullName == "System.Void" : type.FullName is UInt256Reference or "System.UInt64&");

    // Optional acceleration roles are signature candidates, not assumptions of
    // behavior. Each summary is separately proved against its generated body.
    internal static string SelectedEntry(string name) => name switch
    {
        "Add" => EntrySignature,
        "Subtract" => EntrySignature.Replace("::Add(", "::Subtract(", StringComparison.Ordinal),
        "AddOverflow" => EntrySignature.Replace("System.Void", "System.Boolean", StringComparison.Ordinal).Replace("::Add(", "::AddOverflow(", StringComparison.Ordinal),
        "SubtractUnderflow" => EntrySignature.Replace("System.Void", "System.Boolean", StringComparison.Ordinal).Replace("::Add(", "::SubtractUnderflow(", StringComparison.Ordinal),
        _ => throw new ArgumentException($"Unsupported verification method: {name}")
    };

    internal static string? Role(MethodDefinition method, string entrySignature = EntrySignature)
    {
        string parameters = string.Join(",", method.Parameters.Select(p => p.ParameterType.FullName));
        bool subtract = entrySignature == SelectedEntry("Subtract") || entrySignature == SelectedEntry("SubtractUnderflow");
        bool add = entrySignature == EntrySignature || entrySignature == SelectedEntry("AddOverflow");
        if (!add && !subtract && method.IsStatic && method.DeclaringType.FullName == "Nethermind.Int256.UInt256" &&
            method.ReturnType.FullName == "System.UInt64" && parameters == "System.UInt64,System.UInt64,System.UInt64&")
            return method.Parameters[2].IsOut && !method.Parameters[2].IsIn ? "wideMultiply" :
                !method.Parameters[2].IsOut && !method.Parameters[2].IsIn ? "carryCount" : null;
        if (!add && !subtract)
            return method.ReturnType.FullName == "System.Void" && parameters == UInt256Reference + ",System.UInt64,System.UInt64,System.UInt64,System.UInt64"
                ? "storeLimbs" : null;
        return (method.ReturnType.FullName, parameters) switch
        {
            ("System.Boolean", UInt256Reference + "," + UInt256Reference + "," + UInt256Reference + ",System.Boolean") when !subtract &&
                method.Body.Variables.Any(v => v.VariableType.FullName == "System.Runtime.Intrinsics.Vector128`1<System.UInt64>") => "addVector128",
            ("System.Boolean", UInt256Reference + "," + UInt256Reference + "," + UInt256Reference) when subtract &&
                method.Body.Variables.Any(v => v.VariableType.FullName == "System.Runtime.Intrinsics.Vector128`1<System.UInt64>") => "subtractVector128",
            ("System.Boolean", UInt256Reference + "," + UInt256Reference + "," + UInt256Reference) when subtract &&
                method.Body.Variables.Any(v => v.VariableType.FullName == "System.Runtime.Intrinsics.Vector256`1<System.UInt64>") => "subtractVector256",
            ("System.Void", UInt256Reference + "," + UInt256Reference + "," + UInt256Reference + "," +
                "System.Runtime.Intrinsics.Vector256`1<System.UInt64>&,System.Runtime.Intrinsics.Vector256`1<System.UInt64>&," +
                "System.Runtime.Intrinsics.Vector256`1<System.UInt64>&,System.Runtime.Intrinsics.Vector256`1<System.UInt64>&") when !subtract => "prepareAdd",
            ("System.Boolean", "System.Runtime.Intrinsics.Vector256`1<System.UInt64>,System.Runtime.Intrinsics.Vector256`1<System.UInt64>," +
                "System.Runtime.Intrinsics.Vector256`1<System.UInt64>," + UInt256Reference) when !subtract => "finishAdd",
            ("System.ReadOnlySpan`1<System.Byte>", "") => "broadcastLookup",
            ("System.Boolean", UInt256Reference + "," + UInt256Reference + "," + UInt256Reference + ",System.Boolean") when !subtract => "addScalar",
            ("System.Boolean", UInt256Reference + ",System.UInt64," + UInt256Reference) => subtract ? "subtractScalarUInt64" : "addScalarUInt64",
            ("System.Void", "System.UInt64,System.UInt64,System.UInt64&,System.UInt64&") => subtract ? "subtractWithBorrow" : "addWithCarry",
            ("System.Void", UInt256Reference + ",System.UInt64,System.UInt64,System.UInt64,System.UInt64") => "storeLimbs",
            _ => null
        };
    }
}
