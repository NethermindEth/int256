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
    case "recursion":
        MethodDefinition recursive = type.Methods.Single(m => m.Name == "AddWithCarry");
        ILProcessor recursiveIl = recursive.Body.GetILProcessor();
        Instruction first = recursive.Body.Instructions[0];
        // Keep the injected call stack-valid so this tests dependency recursion,
        // rather than being rejected earlier for missing call arguments.
        foreach (ParameterDefinition parameter in recursive.Parameters)
            recursiveIl.InsertBefore(first, Instruction.Create(OpCodes.Ldarg, parameter));
        recursiveIl.InsertBefore(first, Instruction.Create(OpCodes.Call, recursive));
        break;
    case "layout":
        type.Fields.Single(f => f.Name == "u0").Offset = 1;
        break;
    case "cycle":
        MethodDefinition dispatcher = type.Methods.Single(m => m.Name == "AddScalar");
        Instruction branch = dispatcher.Body.Instructions.First(i => i.OpCode.FlowControl == FlowControl.Cond_Branch);
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
