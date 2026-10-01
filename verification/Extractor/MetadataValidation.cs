using Mono.Cecil;
using Mono.Cecil.Cil;

internal static class MetadataValidation
{
    internal const string UInt256Reference = "Nethermind.Int256.UInt256&";
    internal const string EntrySignature = "System.Void Nethermind.Int256.UInt256::Add(Nethermind.Int256.UInt256&,Nethermind.Int256.UInt256&,Nethermind.Int256.UInt256&)";

    internal static (TypeDefinition Type, MethodDefinition[] Methods) Validate(ModuleDefinition module)
    {
        string? AttributeValue(string name) => module.Assembly.CustomAttributes
            .SingleOrDefault(a => a.AttributeType.FullName == name)?.ConstructorArguments.Single().Value as string;
        if (module.Assembly.Name.Name != "Nethermind.Int256" ||
            AttributeValue("System.Runtime.Versioning.TargetFrameworkAttribute") != ".NETCoreApp,Version=v10.0" ||
            AttributeValue("System.Reflection.AssemblyConfigurationAttribute") != "Release")
            throw new InvalidDataException("Unsupported assembly identity, target framework or build configuration");
        TypeDefinition type = module.GetType("Nethermind.Int256.UInt256") ?? throw new InvalidDataException("UInt256 missing");
        if (!type.IsExplicitLayout || type.Fields.Count(f => !f.IsStatic) != 4)
            throw new InvalidDataException("Unsupported UInt256 layout");
        for (int i = 0; i < 4; i++)
        {
            FieldDefinition f = type.Fields.Single(f => f.Name == $"u{i}");
            if (f.IsStatic || f.FieldType.FullName != "System.UInt64" || f.Offset != i * 8)
                throw new InvalidDataException($"Unsupported field: {f.FullName}");
        }
        MethodDefinition entry = type.Methods.SingleOrDefault(m => m.FullName == EntrySignature)
            ?? throw new InvalidDataException("Entry calling signature changed");
        if (!entry.IsPublic || !entry.IsStatic || !entry.Parameters[0].IsIn || !entry.Parameters[1].IsIn ||
            !entry.Parameters[2].IsOut) throw new InvalidDataException("Entry calling signature changed");

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
            if (!method.IsStatic || !method.HasBody || method.HasGenericParameters ||
                method.Body.Instructions.Count == 0 || method.Body.ExceptionHandlers.Count != 0 ||
                (!method.Body.InitLocals && method.Body.Variables.Count != 0) ||
                !SupportedType(method.ReturnType, returns: true) || method.Parameters.Any(p => !SupportedType(p.ParameterType)))
                throw new InvalidDataException($"Unsupported method metadata: {method.FullName}");
            state[method] = 1;
            foreach (Instruction instruction in Reachability.Analyze(method))
            {
                if (instruction.OpCode.Code != Code.Call || instruction.Operand is not MethodReference reference ||
                    InstructionTranslation.RuntimeModel(reference) is not null) continue;
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

    private static bool SupportedType(TypeReference type, bool returns = false) => type.FullName is
        "System.UInt64" or "System.Boolean" or "System.Int32" ||
        (returns ? type.FullName == "System.Void" : type.FullName is UInt256Reference or "System.UInt64&");

    // Optional acceleration roles are signature candidates, not assumptions of
    // behavior. Each summary is separately proved against its generated body.
    internal static string? Role(MethodDefinition method)
    {
        string parameters = string.Join(",", method.Parameters.Select(p => p.ParameterType.FullName));
        return (method.ReturnType.FullName, parameters) switch
        {
            ("System.Boolean", UInt256Reference + "," + UInt256Reference + "," + UInt256Reference + ",System.Boolean") => "addScalar",
            ("System.Boolean", UInt256Reference + ",System.UInt64," + UInt256Reference) => "addScalarUInt64",
            ("System.Void", "System.UInt64,System.UInt64,System.UInt64&,System.UInt64&") => "addWithCarry",
            ("System.Void", UInt256Reference + ",System.UInt64,System.UInt64,System.UInt64,System.UInt64") => "storeLimbs",
            _ => null
        };
    }
}
