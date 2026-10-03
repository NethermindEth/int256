using System.Text.Json;
using Mono.Cecil;

// Selection is an exact public calling convention, independent of helper roles.
internal sealed record EntrySelection(string Signature, bool IsStatic, string Returns,
    EntrySelection.Parameter[] Parameters)
{
    internal sealed record Parameter(string Type, bool IsIn, bool IsOut);

    internal static EntrySelection Select(string selector, string? manifestPath)
    {
        string signature = selector.Contains("::", StringComparison.Ordinal)
            ? selector : MetadataValidation.SelectedEntry(selector);
        if (manifestPath is null)
        {
            if (selector.Contains("::", StringComparison.Ordinal))
                throw new InvalidDataException("Exact entry selection requires a coverage manifest");
            return new(signature, true, selector is "AddOverflow" or "SubtractUnderflow" ? "System.Boolean" : "System.Void",
                [new(MetadataValidation.UInt256Reference, true, false),
                 new(MetadataValidation.UInt256Reference, true, false),
                 new(MetadataValidation.UInt256Reference, false, true)]);
        }
        using JsonDocument manifest = JsonDocument.Parse(File.ReadAllText(manifestPath));
        if (manifest.RootElement.GetProperty("schemaVersion").GetInt32() != 1)
            throw new InvalidDataException("Unsupported coverage manifest schema");
        JsonElement[] entries = manifest.RootElement.GetProperty("entries").EnumerateArray()
            .Where(e => e.GetProperty("signature").GetString() == signature).ToArray();
        if (entries.Length != 1 || entries[0].GetProperty("selection").GetString() != "selected")
            throw new InvalidDataException("Entry is not uniquely selected in the coverage manifest");
        JsonElement convention = entries[0].GetProperty("callingConvention");
        return new(signature, convention.GetProperty("static").GetBoolean(),
            convention.GetProperty("returns").GetString() ?? throw new InvalidDataException("Missing entry return type"),
            convention.GetProperty("parameters").EnumerateArray().Select(p => new Parameter(
                p.GetProperty("type").GetString() ?? throw new InvalidDataException("Missing entry parameter type"),
                p.GetProperty("isIn").GetBoolean(), p.GetProperty("isOut").GetBoolean())).ToArray());
    }

    internal void Validate(MethodDefinition method)
    {
        if (!method.IsPublic || method.FullName != Signature || method.IsStatic != IsStatic ||
            method.HasThis == IsStatic || method.ExplicitThis || method.ReturnType.FullName != Returns ||
            method.Parameters.Count != Parameters.Length ||
            method.Parameters.Zip(Parameters).Any(pair => pair.First.ParameterType.FullName != pair.Second.Type ||
                pair.First.IsIn != pair.Second.IsIn || pair.First.IsOut != pair.Second.IsOut))
            throw new InvalidDataException("Entry calling signature changed");
    }
}
