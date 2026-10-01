using Mono.Cecil;
using Mono.Cecil.Cil;

if (args.Length != 3) throw new ArgumentException("Usage: RegressionFixture mode input.dll output.dll");
using ModuleDefinition module = ModuleDefinition.ReadModule(args[1]);
TypeDefinition type = module.GetType("Nethermind.Int256.UInt256") ?? throw new InvalidDataException("UInt256 missing");
switch (args[0])
{
    case "unresolved":
        MethodDefinition scalar = type.Methods.Single(m => m.Name == "AddScalar");
        Instruction call = scalar.Body.Instructions.First(i => i.OpCode == OpCodes.Call &&
            i.Operand is MethodReference method && method.Name == "AddWithCarry");
        MethodReference original = (MethodReference)call.Operand;
        MethodReference missing = new("MissingAddHelper", original.ReturnType, original.DeclaringType)
        {
            HasThis = original.HasThis
        };
        foreach (ParameterDefinition parameter in original.Parameters)
            missing.Parameters.Add(new ParameterDefinition(parameter.ParameterType));
        call.Operand = missing;
        break;
    case "layout":
        type.Fields.Single(f => f.Name == "u0").Offset = 1;
        break;
    case "cycle":
        MethodDefinition entry = type.Methods.Single(m => m.Name == "Add" && m.IsStatic);
        Instruction branch = entry.Body.Instructions.First(i => i.OpCode == OpCodes.Brfalse || i.OpCode == OpCodes.Brfalse_S);
        branch.Operand = branch;
        break;
    case "framework":
        CustomAttribute framework = module.Assembly.CustomAttributes.Single(a =>
            a.AttributeType.FullName == "System.Runtime.Versioning.TargetFrameworkAttribute");
        framework.ConstructorArguments[0] = new CustomAttributeArgument(module.TypeSystem.String, ".NETCoreApp,Version=v9.0");
        break;
    case "configuration":
        CustomAttribute configuration = module.Assembly.CustomAttributes.Single(a =>
            a.AttributeType.FullName == "System.Reflection.AssemblyConfigurationAttribute");
        configuration.ConstructorArguments[0] = new CustomAttributeArgument(module.TypeSystem.String, "Debug");
        break;
    default:
        throw new ArgumentException("Unknown fixture mode");
}
module.Write(args[2]);
