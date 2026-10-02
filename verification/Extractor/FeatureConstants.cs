using Mono.Cecil;
using Mono.Cecil.Cil;

// A small forward analysis for fixed feature expressions. Unknown means any
// value, never false. This only selects reachability; emitted CIL is unchanged
// and the kernel still checks every executed instruction and feature query.
internal sealed class FeatureConstants
{
    private readonly List<int?> _stack;
    private readonly int?[] _locals;

    internal FeatureConstants(int locals)
    {
        _stack = [];
        // Leave locals unknown even with InitLocals: only explicit assignments
        // to unaddressed integer locals supply facts to this analysis.
        _locals = new int?[locals];
    }

    private FeatureConstants(List<int?> stack, int?[] locals)
    {
        _stack = stack;
        _locals = locals;
    }

    internal FeatureConstants Copy() => new([.. _stack], (int?[])_locals.Clone());

    internal void Merge(FeatureConstants other)
    {
        if (_stack.Count != other._stack.Count)
            throw new InvalidDataException("Inconsistent evaluation stack at control-flow merge");
        for (int i = 0; i < _stack.Count; i++)
            if (_stack[i] != other._stack[i]) _stack[i] = null;
        for (int i = 0; i < _locals.Length; i++)
            if (_locals[i] != other._locals[i]) _locals[i] = null;
    }

    internal int? Top => _stack.Count == 0 ? null : _stack[^1];

    private int? Pop()
    {
        if (_stack.Count == 0) throw new InvalidDataException("Invalid evaluation stack during reachability");
        int? value = _stack[^1];
        _stack.RemoveAt(_stack.Count - 1);
        return value;
    }

    internal void Step(Instruction instruction, MethodDefinition method, FeatureProfile profile, HashSet<int> addressed)
    {
        Code code = instruction.OpCode.Code;
        switch (code)
        {
            case Code.Ldc_I4_M1: _stack.Add(-1); return;
            case Code.Ldc_I4_0: _stack.Add(0); return;
            case Code.Ldc_I4_1: _stack.Add(1); return;
            case Code.Ldc_I4_2: _stack.Add(2); return;
            case Code.Ldc_I4_3: _stack.Add(3); return;
            case Code.Ldc_I4_4: _stack.Add(4); return;
            case Code.Ldc_I4_5: _stack.Add(5); return;
            case Code.Ldc_I4_6: _stack.Add(6); return;
            case Code.Ldc_I4_7: _stack.Add(7); return;
            case Code.Ldc_I4_8: _stack.Add(8); return;
            case Code.Ldc_I4: case Code.Ldc_I4_S:
                _stack.Add(Convert.ToInt32(instruction.Operand)); return;
            case Code.Ldloc_0: case Code.Ldloc_1: case Code.Ldloc_2: case Code.Ldloc_3:
            case Code.Ldloc: case Code.Ldloc_S:
                _stack.Add(_locals[Local(instruction)]); return;
            case Code.Stloc_0: case Code.Stloc_1: case Code.Stloc_2: case Code.Stloc_3:
            case Code.Stloc: case Code.Stloc_S:
                int local = Local(instruction);
                int? value = Pop();
                string type = method.Body.Variables[local].VariableType.FullName;
                _locals[local] = !addressed.Contains(local) &&
                    (type is "System.Int32" or "System.UInt32" || type == "System.Boolean" && value is 0 or 1)
                    ? value : null;
                return;
            case Code.Dup:
                int? top = Pop();
                _stack.Add(top);
                _stack.Add(top);
                return;
            case Code.And: case Code.Or: case Code.Xor: case Code.Ceq:
                int? right = Pop();
                int? left = Pop();
                _stack.Add(left is int a && right is int b ? code switch
                {
                    Code.And => a & b, Code.Or => a | b, Code.Xor => a ^ b,
                    Code.Ceq => a == b ? 1 : 0, _ => null
                } : null);
                return;
            case Code.Call: case Code.Newobj:
                MethodReference callee = (MethodReference)instruction.Operand;
                for (int i = 0; i < callee.Parameters.Count + (code == Code.Call && callee.HasThis ? 1 : 0); i++) Pop();
                if (FeatureProfile.Getter(callee) is Feature feature)
                    _stack.Add(profile.Get(feature) ? 1 : 0);
                else if (code == Code.Newobj || callee.ReturnType.MetadataType != MetadataType.Void)
                    _stack.Add(null);
                return;
            case Code.Ret:
                if (method.ReturnType.MetadataType != MetadataType.Void) Pop();
                return;
        }

        int pops = instruction.OpCode.StackBehaviourPop switch
        {
            StackBehaviour.Pop0 => 0,
            StackBehaviour.Pop1 or StackBehaviour.Popi or StackBehaviour.Popref => 1,
            StackBehaviour.Pop1_pop1 or StackBehaviour.Popi_pop1 or StackBehaviour.Popi_popi or
                StackBehaviour.Popi_popi8 or StackBehaviour.Popi_popr4 or StackBehaviour.Popi_popr8 or
                StackBehaviour.Popref_pop1 or StackBehaviour.Popref_popi => 2,
            StackBehaviour.Popi_popi_popi or StackBehaviour.Popref_popi_popi or
                StackBehaviour.Popref_popi_popi8 or StackBehaviour.Popref_popi_popr4 or
                StackBehaviour.Popref_popi_popr8 or StackBehaviour.Popref_popi_popref => 3,
            _ => throw new InvalidDataException($"Unsupported stack effect: {instruction}")
        };
        for (int i = 0; i < pops; i++) Pop();
        int pushes = instruction.OpCode.StackBehaviourPush switch
        {
            StackBehaviour.Push0 => 0,
            StackBehaviour.Push1 or StackBehaviour.Pushi or StackBehaviour.Pushi8 or
                StackBehaviour.Pushr4 or StackBehaviour.Pushr8 or StackBehaviour.Pushref => 1,
            _ => throw new InvalidDataException($"Unsupported stack effect: {instruction}")
        };
        for (int i = 0; i < pushes; i++) _stack.Add(null);
    }

    internal static int Local(Instruction instruction) => instruction.OpCode.Code switch
    {
        Code.Ldloc_0 or Code.Stloc_0 => 0, Code.Ldloc_1 or Code.Stloc_1 => 1,
        Code.Ldloc_2 or Code.Stloc_2 => 2, Code.Ldloc_3 or Code.Stloc_3 => 3,
        _ => ((VariableDefinition)instruction.Operand).Index
    };
}
