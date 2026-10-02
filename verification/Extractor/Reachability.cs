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
        // Address-taken locals may be changed indirectly by calls or stores.
        // Never use them as constant facts, even before their address escapes.
        HashSet<int> addressed = instructions.Where(i => i.OpCode.Code is Code.Ldloca or Code.Ldloca_S)
            .Select(FeatureConstants.Local).ToHashSet();
        HashSet<Instruction> reachable = [];
        Dictionary<Instruction, FeatureConstants> incoming = new()
        {
            [instructions[0]] = new(method.Body.Variables.Count)
        };
        // The admitted graph is forward-only, so every predecessor has been
        // merged before an instruction is visited. Conflicting facts become unknown.
        foreach (Instruction i in instructions)
        {
            if (!incoming.TryGetValue(i, out FeatureConstants? state)) continue;
            reachable.Add(i);
            int? condition = state.Top;
            state = state.Copy();
            state.Step(i, method, profile, addressed);

            void Successor(Instruction target)
            {
                if (!instructions.Contains(target) || target.Offset <= i.Offset)
                    throw new InvalidDataException("Malformed or cyclic control flow");
                if (incoming.TryGetValue(target, out FeatureConstants? previous)) previous.Merge(state);
                else incoming[target] = state.Copy();
            }

            if (condition is int known && i.OpCode.Code is Code.Brfalse or Code.Brfalse_S or Code.Brtrue or Code.Brtrue_S)
            {
                bool taken = (known != 0) == (i.OpCode.Code is Code.Brtrue or Code.Brtrue_S);
                Successor(taken ? (Instruction)i.Operand
                    : i.Next ?? throw new InvalidDataException("Missing selected feature successor"));
                continue;
            }
            if (i.Operand is Instruction target) Successor(target);
            if (i.OpCode.FlowControl is not (FlowControl.Return or FlowControl.Branch or FlowControl.Throw))
                Successor(i.Next ?? throw new InvalidDataException("Control falls off method"));
        }
        return reachable;
    }
}
