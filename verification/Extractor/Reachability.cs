using Mono.Cecil;
using Mono.Cecil.Cil;

internal static class Reachability
{
    internal static HashSet<Instruction> Analyze(MethodDefinition method, FeatureProfile? selectedProfile = null)
    {
        FeatureProfile profile = selectedProfile ?? FeatureProfile.Scalar;
        profile.Validate();
        var instructions = method.Body.Instructions;
        foreach (Instruction instruction in instructions)
        {
            if (instruction.Operand is Instruction target &&
                !instructions.Contains(target))
                throw new InvalidDataException("Malformed or cyclic control flow");
        }
        HashSet<Instruction> reachable = [];
        HashSet<Instruction> processed = [];
        Queue<Instruction> pending = new();
        pending.Enqueue(instructions[0]);
        while (pending.TryDequeue(out Instruction? i))
        {
            if (!processed.Add(i)) continue;
            reachable.Add(i);
            if (i.OpCode.Code == Code.Call && i.Operand is MethodReference r && FeatureProfile.Getter(r) is Feature feature)
            {
                Instruction branch = i.Next ?? throw new InvalidDataException("Missing feature branch");
                if (branch.OpCode.Code is not (Code.Brfalse or Code.Brfalse_S or Code.Brtrue or Code.Brtrue_S))
                    throw new InvalidDataException("Feature must be consumed by an immediate conditional branch");
                bool taken = profile.Get(feature) == (branch.OpCode.Code is Code.Brtrue or Code.Brtrue_S);
                Instruction selectedTarget = taken
                    ? (Instruction)branch.Operand
                    : branch.Next ?? throw new InvalidDataException("Missing selected feature successor");
                if (selectedTarget.Offset <= branch.Offset)
                    throw new InvalidDataException("Malformed or cyclic control flow");
                // Mark this forced branch as covered, but process both successors
                // if an independent incoming edge later reaches it.
                reachable.Add(branch);
                pending.Enqueue(selectedTarget);
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
