using Mono.Cecil;

internal static class MetadataValidation
{
    internal static (TypeDefinition Type, MethodDefinition[] Methods) Validate(ModuleDefinition module)
    {
        string? AttributeValue(string name) => module.Assembly.CustomAttributes
            .SingleOrDefault(a => a.AttributeType.FullName == name)?.ConstructorArguments.Single().Value as string;
        if (module.Assembly.Name.Name != "Nethermind.Int256" ||
            AttributeValue("System.Runtime.Versioning.TargetFrameworkAttribute") != ".NETCoreApp,Version=v10.0" ||
            AttributeValue("System.Reflection.AssemblyConfigurationAttribute") != "Release")
            throw new InvalidDataException("Unsupported assembly identity, target framework or build configuration");
        TypeDefinition type = module.GetType("Nethermind.Int256.UInt256") ?? throw new InvalidDataException("UInt256 missing");
        string[] names = ["Add", "AddScalar", "AddScalarUInt64", "AddWithCarry", "StoreLimbs"];
        MethodDefinition[] methods = names.Select(n => type.Methods.Single(m => m.Name == n && m.IsStatic)).ToArray();
        if (!type.IsExplicitLayout || type.Fields.Where(f => !f.IsStatic).Count() != 4)
            throw new InvalidDataException("Unsupported UInt256 layout");
        for (int i = 0; i < 4; i++)
        {
            FieldDefinition f = type.Fields.Single(f => f.Name == $"u{i}");
            if (f.IsStatic || f.FieldType.FullName != "System.UInt64" || f.Offset != i * 8)
                throw new InvalidDataException($"Unsupported field: {f.FullName}");
        }
        string u = "Nethermind.Int256.UInt256&";
        string[][] parameters = [[u, u, u], [u, u, u, "System.Boolean"],
            [u, "System.UInt64", u], ["System.UInt64", "System.UInt64", "System.UInt64&", "System.UInt64&"],
            [u, "System.UInt64", "System.UInt64", "System.UInt64", "System.UInt64"]];
        for (int i = 0; i < methods.Length; i++)
        {
            MethodDefinition m = methods[i];
            if (!m.HasBody || m.HasGenericParameters || m.Body.Instructions.Count == 0 || m.Body.ExceptionHandlers.Count != 0 ||
                (!m.Body.InitLocals && m.Body.Variables.Count != 0) ||
                !m.Parameters.Select(p => p.ParameterType.FullName).SequenceEqual(parameters[i]) ||
                m.ReturnType.FullName != (i is 1 or 2 ? "System.Boolean" : "System.Void"))
                throw new InvalidDataException($"Unsupported method metadata: {m.FullName}");
        }
        if (!methods[0].IsPublic || !methods[0].Parameters[0].IsIn || !methods[0].Parameters[1].IsIn ||
            !methods[0].Parameters[2].IsOut) throw new InvalidDataException("Entry calling signature changed");
        return (type, methods);
    }
}
