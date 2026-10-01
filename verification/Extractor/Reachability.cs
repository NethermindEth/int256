using Mono.Cecil;
using Mono.Cecil.Cil;

internal static class Reachability
{
    internal static HashSet<Instruction> Analyze(MethodDefinition method)
    {
        var instructions = method.Body.Instructions;
        foreach (Instruction instruction in instructions)
        {
            if (instruction.Operand is Instruction target &&
                (!instructions.Contains(target) || target.Offset <= instruction.Offset))
                throw new InvalidDataException("Malformed or cyclic control flow");
        }
        HashSet<Instruction> reachable = [];
        Queue<Instruction> pending = new();
        pending.Enqueue(instructions[0]);
        while (pending.TryDequeue(out Instruction? i))
        {
            if (!reachable.Add(i)) continue;
            if (i.OpCode.Code == Code.Call && i.Operand is MethodReference r && InstructionTranslation.Feature(r))
            {
                Instruction branch = i.Next ?? throw new InvalidDataException("Missing feature branch");
                if (branch.OpCode.Code is not (Code.Brfalse or Code.Brfalse_S))
                    throw new InvalidDataException("Feature must be consumed by immediate brfalse");
                reachable.Add(branch);
                pending.Enqueue((Instruction)branch.Operand);
                continue;
            }
            if (i.Operand is Instruction target)
            {
                if (!instructions.Contains(target) || target.Offset <= i.Offset)
                    throw new InvalidDataException("Malformed or cyclic control flow");
                pending.Enqueue(target);
            }
            if (i.OpCode.FlowControl is not (FlowControl.Return or FlowControl.Branch or FlowControl.Throw))
                pending.Enqueue(i.Next ?? throw new InvalidDataException("Control falls off method"));
        }
        return reachable;
    }
}
