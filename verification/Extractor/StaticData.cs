using Mono.Cecil;

internal static class StaticData
{
    internal static FieldDefinition Validate(FieldReference reference, ModuleDefinition module)
    {
        FieldDefinition field = reference.Resolve() ?? throw new InvalidDataException($"Unresolved static data: {reference.FullName}");
        TypeDefinition layout = field.FieldType.Resolve() ?? throw new InvalidDataException("Unresolved static-data layout");
        if (reference.DeclaringType.Scope != module || reference.DeclaringType is TypeSpecification ||
            reference.DeclaringType.IsValueType != field.DeclaringType.IsValueType ||
            reference.DeclaringType.Resolve() != field.DeclaringType ||
            reference.FieldType.Scope != module || reference.FieldType is TypeSpecification ||
            reference.FieldType.IsValueType != layout.IsValueType || reference.FieldType.Resolve() != layout ||
            field.Module != module || layout.Module != module || !field.IsStatic || !field.IsInitOnly ||
            (field.Attributes & FieldAttributes.HasFieldRVA) == 0 || field.InitialValue.Length == 0 ||
            field.RVA == 0 || !layout.IsValueType || !RuntimeModels.HasRuntimeValueTypeBase(layout) || layout.HasGenericParameters ||
            !layout.IsExplicitLayout || layout.PackingSize != 1 || layout.ClassSize != field.InitialValue.Length ||
            layout.Fields.Any(f => !f.IsStatic) ||
            field.DeclaringType.Methods.Any(m => m.IsConstructor && m.IsStatic) ||
            layout.Methods.Any(m => m.IsConstructor && m.IsStatic))
            throw new InvalidDataException($"Unsupported static data or initialisation: {reference.FullName}");
        return field;
    }

    internal static string LeanBytes(FieldDefinition field) =>
        "[" + string.Join(", ", field.InitialValue.Select(b => $"(BitVec.ofNat 8 {b})")) + "]";
}
