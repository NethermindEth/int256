using System.Security.Cryptography;
using System.Text.Json;
using Mono.Cecil;
using Mono.Cecil.Cil;

internal static class ArtifactReport
{
    internal static string Write(ModuleDefinition module, TypeDefinition type, MethodDefinition[] methods,
        List<object> coverage, string assemblyPath, string outputDirectory, string entrySignature = MetadataValidation.EntrySignature, FeatureProfile? selectedProfile = null)
    {
        FeatureProfile profile = selectedProfile ?? FeatureProfile.Scalar;
        var artifact = new
        {
            assembly = module.Assembly.Name.FullName,
            sha256 = Convert.ToHexString(SHA256.HashData(File.ReadAllBytes(assemblyPath))).ToLowerInvariant(),
            extractorVersion = "5",
            profile,
            queriedFeatures = methods.SelectMany(m => Reachability.Analyze(m, profile))
                .Where(i => i.OpCode.Code == Code.Call && i.Operand is MethodReference r && FeatureProfile.Getter(r) is not null)
                .Select(i => FeatureProfile.Getter((MethodReference)i.Operand).ToString()).Distinct().Order().ToArray(),
            staticData = methods.SelectMany(m => Reachability.Analyze(m, profile))
                .Where(i => i.OpCode.Code == Code.Ldsflda)
                .Select(i => StaticData.Validate((FieldReference)i.Operand, module)).Distinct()
                .Select(f => new { signature = f.FullName, scope = f.DeclaringType.Scope.Name,
                    attributes = f.Attributes.ToString(), size = f.FieldType.Resolve().ClassSize,
                    packing = f.FieldType.Resolve().PackingSize, bytes = Convert.ToHexString(f.InitialValue).ToLowerInvariant() }),
            entryIndex = Array.FindIndex(methods, m => m.FullName == entrySignature),
            buildConfiguration = new { configuration = "Release", targetFramework = "net10.0" },
            layout = new { type.IsExplicitLayout, type.IsBeforeFieldInit, type.PackingSize, type.ClassSize },
            coverage,
            fields = type.Fields.Where(f => !f.IsStatic).Select(f => new { f.Name, type = f.FieldType.FullName, f.Offset }),
            methods = methods.Select(m => new
            {
                signature = m.FullName,
                isStatic = m.IsStatic,
                returnType = m.ReturnType.FullName,
                hasThis = m.HasThis,
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
                    scope = i.Operand switch
                    {
                        TypeReference operandType => operandType.Scope.ToString(),
                        MemberReference member => member.DeclaringType.Scope.ToString(),
                        _ => null
                    },
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
