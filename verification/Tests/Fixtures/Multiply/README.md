# Multiplication verification fixtures

These preserve the original multiplication regression cases from
`verification/uint256-memory-safety`: one of the two positive variants and the five mutations.
Each negative proves that the compiled method cannot satisfy the complete
checked wrapping multiplication contract; the regression runner also rejects
the unmodified production proof and checks that no stale certificate remains.

The fixture-only software Multiply64 fallback now uses Math.BigMul, matching
the current production implementation. The previous fallback was checked
against the replacement and BigInteger for 10,081 edge/random products with
hardware intrinsics both enabled and disabled. Hardware branches and every
original mutation, initial-memory witness, and expected byte remain unchanged.

AlternativeOrder swaps two carry-counted additions. Its proof shares the
production execution proof and establishes equality of the resulting local
word snapshots. It is the one positive refactor fixture kept for this family;
the original ExtractedHelper positive was dropped.

Run from the repository root:

    dotnet run --file verification/MultiplyRegression.cs
