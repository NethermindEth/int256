namespace Nethermind.Int256;

public readonly partial struct UInt256
{
    private static bool AddScalar(in UInt256 a, in UInt256 b, out UInt256 res, bool detectOverflow)
    {

        ulong b0 = b.u0;
        if ((b.u1 | b.u2 | b.u3) == 0)
        {
            return AddScalarUInt64(in a, b0, out res);
        }

        // Addition commutes and the EVM puts the small operand on either side of the stack
        ulong a0 = a.u0;
        if ((a.u1 | a.u2 | a.u3) == 0)
        {
            return AddScalarUInt64(in b, a0, out res);
        }

        // Loads stay next to their use: the one-limb paths above share this method's prolog
        ulong carry = 0;
        AddWithCarry(a0, b0, ref carry, out ulong r0);
        AddWithCarry(a.u1, b.u1, ref carry, out ulong r1);
        AddWithCarry(a.u2, b.u2, ref carry, out ulong r2);
        AddWithCarry(a.u3, b.u3, ref carry, out ulong r3);
        StoreLimbs(out res, r0, r1, r2, r3);
        return carry != 0;
    }
}
