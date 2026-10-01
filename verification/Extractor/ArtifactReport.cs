using System.Security.Cryptography;
using System.Text.Json;
using Mono.Cecil;
using Mono.Cecil.Cil;

internal static class ArtifactReport
{
    internal static string Write(ModuleDefinition module, TypeDefinition type, MethodDefinition[] methods,
        List<object> coverage, string assemblyPath, string outputDirectory)
    {
        var artifact = new
        {
            assembly = module.Assembly.Name.FullName,
            sha256 = Convert.ToHexString(SHA256.HashData(File.ReadAllBytes(assemblyPath))).ToLowerInvariant(),
            extractorVersion = "3",
            entryIndex = Array.FindIndex(methods, m => m.FullName == MetadataValidation.EntrySignature),
            buildConfiguration = new { configuration = "Release", targetFramework = "net10.0" },
            layout = new { type.IsExplicitLayout, type.IsBeforeFieldInit, type.PackingSize, type.ClassSize },
            coverage,
            fields = type.Fields.Where(f => !f.IsStatic).Select(f => new { f.Name, type = f.FieldType.FullName, f.Offset }),
            methods = methods.Select(m => new
            {
                signature = m.FullName,
                token = m.MetadataToken.ToInt32(),
                parameters = m.Parameters.Select(p => new { p.Name, type = p.ParameterType.FullName, p.IsIn, p.IsOut }),
                m.Body.InitLocals,
                m.Body.MaxStackSize,
                locals = m.Body.Variables.Select(v => v.VariableType.FullName),
                exceptions = m.Body.ExceptionHandlers.Select(e => e.HandlerType.ToString()),
                instructions = m.Body.Instructions.Select(i => new
                {
                    i.Offset,
                    opcode = i.OpCode.Name,
                    scope = i.Operand is MemberReference member ? member.DeclaringType.Scope.ToString() : null,
                    operand = i.Operand switch
                    {
                        null => null,
                        Instruction target => target.Offset.ToString(),
                        VariableDefinition v => v.Index.ToString(),
                        ParameterDefinition p => p.Index.ToString(),
                        _ => i.Operand.ToString()
                    }
                })
            })
        };
        File.WriteAllText(Path.Combine(outputDirectory, "artifact.json"), JsonSerializer.Serialize(artifact, new JsonSerializerOptions { WriteIndented = true }) + "\n");
        return artifact.sha256;
    }
}
