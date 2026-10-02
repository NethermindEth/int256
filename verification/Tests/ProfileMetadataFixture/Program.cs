using Mono.Cecil;
using Mono.Cecil.Cil;

if (args.Length != 3) throw new ArgumentException("Usage: ProfileMetadataFixture mode fixture.dll output.dll");
using ModuleDefinition module = ModuleDefinition.ReadModule(args[1]);
TypeDefinition type = module.GetType("Nethermind.Int256.UInt256") ?? throw new InvalidDataException("Fixture UInt256 missing");
MethodDefinition probe = type.Methods.Single(m => m.Name == "Probe");
TypeReference Spoof(TypeReference original)
{
    AssemblyNameReference scope = new("Spoof.Runtime", new Version(10, 0, 0, 0));
    module.AssemblyReferences.Add(scope);
    TypeReference changed = new(original.Namespace, original.Name, module, scope, original.IsValueType);
    if (original.DeclaringType is not null) changed.DeclaringType = Spoof(original.DeclaringType);
    return changed;
}
switch (args[0])
{
    case "uint256-base-scope":
        type.BaseType = Spoof(type.BaseType);
        Console.WriteLine("Changed UInt256 ValueType base scope");
        break;
    case "uint256-size":
        if (!type.IsValueType || !type.IsExplicitLayout || type.ClassSize > 32)
            throw new InvalidDataException("UInt256 size fixture structure changed");
        type.ClassSize = 64;
        Console.WriteLine("Changed UInt256 declared size to 64 bytes");
        break;
    case "generic-argument-scope":
    case "vector-class-encoding":
        GenericInstanceMethod unsafeAs = (GenericInstanceMethod)probe.Body.Instructions.Single(i =>
            i.OpCode == OpCodes.Call && i.Operand is GenericInstanceMethod r && r.Name == "As").Operand;
        GenericInstanceType vector = (GenericInstanceType)unsafeAs.GenericArguments[1];
        TypeReference vectorElement = args[0] == "vector-class-encoding"
            ? new TypeReference(vector.ElementType.Namespace, vector.ElementType.Name, module, vector.ElementType.Scope, false)
            : vector.ElementType;
        GenericInstanceType changedVector = new(vectorElement);
        changedVector.GenericArguments.Add(args[0] == "generic-argument-scope"
            ? Spoof(vector.GenericArguments.Single()) : vector.GenericArguments.Single());
        unsafeAs.GenericArguments[1] = changedVector;
        Console.WriteLine($"Changed nested generic type scope: {unsafeAs.FullName}");
        break;
    case "operand-type-scope":
        Instruction load = probe.Body.Instructions.Single(i => i.OpCode == OpCodes.Ldobj &&
            i.Operand is GenericInstanceType r && r.ElementType.FullName == "System.Runtime.Intrinsics.Vector256`1");
        GenericInstanceType operand = (GenericInstanceType)load.Operand;
        GenericInstanceType changedOperand = new(Spoof(operand.ElementType));
        foreach (TypeReference argument in operand.GenericArguments) changedOperand.GenericArguments.Add(argument);
        load.Operand = changedOperand;
        Console.WriteLine($"Changed typed load scope: {changedOperand.FullName}");
        break;
    case "field-type-scope":
        FieldDefinition limb = type.Fields.Single(f => f.Name == "u0");
        limb.FieldType = Spoof(limb.FieldType);
        Console.WriteLine($"Changed scalar field type scope: {limb.FullName}");
        break;
    case "getter-return-scope":
        MethodReference getterQuery = (MethodReference)probe.Body.Instructions.Single(i =>
            i.OpCode == OpCodes.Call && i.Operand is MethodReference r && r.Name == "get_IsSupported").Operand;
        getterQuery.ReturnType = Spoof(getterQuery.ReturnType);
        Console.WriteLine($"Changed feature return type scope: {getterQuery.FullName}");
        break;
    case "feature-scope":
        MethodReference query = (MethodReference)probe.Body.Instructions.Single(i => i.OpCode == OpCodes.Call &&
            i.Operand is MethodReference r && r.FullName == "System.Boolean System.Runtime.Intrinsics.X86.Avx2::get_IsSupported()").Operand;
        ((AssemblyNameReference)query.DeclaringType.Scope).Version = new Version(9, 0, 0, 0);
        Console.WriteLine($"Changed exact feature scope: {query.FullName}");
        break;
    case "generic-feature":
        Instruction featureCall = probe.Body.Instructions.Single(i => i.OpCode == OpCodes.Call &&
            i.Operand is MethodReference r && r.FullName == "System.Boolean System.Runtime.Intrinsics.X86.Avx2::get_IsSupported()");
        GenericInstanceMethod generic = new((MethodReference)featureCall.Operand);
        generic.GenericArguments.Add(module.TypeSystem.Int32);
        featureCall.Operand = generic;
        Console.WriteLine($"Changed exact feature signature: {generic.FullName}");
        break;
    case "intrinsic-scope":
        AssemblyNameReference scope = module.AssemblyReferences.Single(a => a.Name == "System.Runtime.Intrinsics");
        scope.PublicKeyToken = new byte[8];
        Console.WriteLine("Changed intrinsic assembly public key token");
        break;
    case "static-mutable":
    case "static-memberref-scope":
    case "static-base-scope":
    case "static-initializer":
    case "static-byte":
        MethodDefinition getter = type.Methods.Single(m => m.Name == "get_Bytes");
        FieldDefinition field = ((FieldReference)getter.Body.Instructions.Single(i => i.OpCode == OpCodes.Ldsflda).Operand).Resolve();
        if (!field.IsStatic || !field.IsInitOnly || field.InitialValue.Length != 32 ||
            field.FieldType.Resolve().ClassSize != 32)
            throw new InvalidDataException("Static-data fixture structure changed");
        if (args[0] == "static-memberref-scope")
        {
            Instruction address = getter.Body.Instructions.Single(i => i.OpCode == OpCodes.Ldsflda);
            FieldReference original = (FieldReference)address.Operand;
            FieldReference changed = new(original.Name, Spoof(original.FieldType), original.DeclaringType);
            if (changed.FullName != original.FullName || changed.Resolve() != field)
                throw new InvalidDataException("Scoped MemberRef fixture did not preserve Cecil resolution");
            address.Operand = changed;
        }
        else if (args[0] == "static-base-scope")
        {
            TypeDefinition layout = field.FieldType.Resolve();
            layout.BaseType = Spoof(layout.BaseType);
        }
        else if (args[0] == "static-mutable") field.IsInitOnly = false;
        else if (args[0] == "static-initializer")
        {
            MethodDefinition initializer = new(".cctor", MethodAttributes.Private | MethodAttributes.Static |
                MethodAttributes.SpecialName | MethodAttributes.RTSpecialName, module.TypeSystem.Void);
            initializer.Body.Instructions.Add(Instruction.Create(OpCodes.Ret));
            field.DeclaringType.Methods.Add(initializer);
        }
        else
        {
            byte[] bytes = (byte[])field.InitialValue.Clone();
            bytes[0] ^= 1;
            field.InitialValue = bytes;
        }
        Console.WriteLine($"Changed {args[0]}: {field.FullName}");
        break;
    default:
        throw new ArgumentException($"Unknown profile metadata fixture: {args[0]}");
}
module.Write(args[2]);
if (args[0] == "vector-class-encoding")
{
    using ModuleDefinition written = ModuleDefinition.ReadModule(args[2]);
    GenericInstanceMethod writtenCall = (GenericInstanceMethod)written.GetType("Nethermind.Int256.UInt256").Methods
        .Single(m => m.Name == "Probe").Body.Instructions.Single(i => i.OpCode == OpCodes.Call &&
            i.Operand is GenericInstanceMethod r && r.Name == "As").Operand;
    if (writtenCall.GenericArguments[1].IsValueType)
        throw new InvalidDataException("Class-encoding fixture did not preserve the metadata change");
}
