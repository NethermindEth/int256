# UInt256 verification with LeanCIL

This is an in-progress migration from `verification/uint256-memory-safety`
(`6c56716afa7860771c08815b8348e53313c7f8c8`), based on int256 `main`
(`5fa8d77429c0440754bbfc851788d1ae37aba07f`). It consumes LeanCIL at
`3ddec3df17a66bf475000a2c5c15e836ecab7a97` through a pinned Lake dependency.
CIL semantics, extraction, and verification infrastructure belong to LeanCIL;
this directory contains no copies of them.

**No compiled UInt256 method is certified by this branch yet.** The 38 ported
modules define UInt256 contracts and prove supporting arithmetic, representation,
calling-condition, overlap, write-preservation and profile-transport lemmas.
The build and axiom audit pass for 409 supporting theorems. Defining a contract
or transporting an assumed certificate does not prove the implementation meets it.
The `UInt256 verification contracts` CI workflow runs that build and audit;
it does not certify compiled methods. A local integration check against this pin
also verified LeanCIL's example Add with a proof importing
`UInt256.Representation`, including fresh builds, kernel replay, and axiom audit.

## Run

Install .NET SDK 10.0.402 or a compatible newer SDK, PowerShell 7, Git, and elan.
Lake selects Lean 4.35.0 using `lean-toolchain`.

From the repository root:

```powershell
pwsh -NoProfile -File verification/Verify.ps1
pwsh -NoProfile -File verification/Verify.ps1 -Action Extract -Method Add -Profile scalar
```

The first command builds the consumer library and audits all theorems in the
`UInt256Model` and `UInt256Proof` namespaces, allowing only `propext`,
`Classical.choice`, and `Quot.sound`. It produces no assembly certificate.
Equivalently, run `lake update`, `lake build`, and `lake env lean Audit.lean`
inside this directory.

The second command builds the pinned LeanCIL extractor and a fresh standard
Release int256 assembly, then invokes LeanCIL extraction. It currently exits
nonzero for the `Unsafe.SkipInit<T>` blocker below. Extraction records the explicit
assumption that `Nethermind.Int256.UInt256` has already initialized successfully;
it does not prove or execute its static constructor. `manifests/targets.json` preserves
the 87 selected signatures from the original branch as a migration inventory;
it does not register completed proof gates. Named custom profiles are retained
under `manifests/profiles`. Generated artifacts are ignored under `artifacts/`.

Once a compiled-method proof is available, use:

```powershell
pwsh -NoProfile -File verification/Verify.ps1 -Action Verify -Method Add -Profile scalar `
    -Proof proofs/AddScalar.lean -Theorem UInt256Proof.Add.scalar_correctness
```

The proof path and theorem above illustrate the interface; that proof does not yet
exist. Proof paths are relative to `verification/` and must be Lean sources inside
the package, outside ignored build/artifact directories. `Verify` builds the
assembly, extracts it afresh, and invokes LeanCIL with `--proof-root` pointing at
this package. LeanCIL rebuilds the proof and its imports, replays the kernel,
audits axioms, and binds source identity into `verified.json`. Selecting a theorem
does not establish that it expresses the full public contract; that remains a
review requirement for each registered gate.

## Upstream status

- [LeanCIL #25](https://github.com/NethermindEth/LeanCIL/issues/25) and
  [#26](https://github.com/NethermindEth/LeanCIL/issues/26) are fixed in the pinned
  revision: explicit initialization assumptions and consumer proof packages.
- [LeanCIL #34](https://github.com/NethermindEth/LeanCIL/issues/34) blocks scalar
  Add extraction. Its reachable `StoreLimbs` helper calls
  `Unsafe.SkipInit<UInt256>`, which is not modeled. A minimal four-limb store fails
  with `Unsupported generic method signature or body`; removing only `SkipInit`
  makes the reproducer extract. Supporting this operation must preserve memory
  without assuming bytes have become initialized.

Neither the production assembly nor LeanCIL is patched to bypass these checks.
The old generated artifacts, custom extractor, runner, selected-gate generators,
and method-specific execution proofs are not brought into this migration.
They remain available at the source revision above. Copying old generated CIL
would not verify the current assembly.

## Porting boundary

The allocation-aware contracts under `UInt256/Safety` use LeanCIL's invocation
certificates. Passed UInt256 values now use 32-byte aggregates, and the output
field-store lemma uses LeanCIL's byte-offset field instruction. Arithmetic
contracts under `UInt256/Methods` retain the original unchecked-model
specifications for reference; they are not allocation-safety certificates or
proofs about the new extractor's general aggregate instructions.

After the remaining upstream blocker is resolved, pin the supporting LeanCIL revision,
extract fresh methods, and port execution proofs against those exact definitions.
Each public gate must require the full independent arithmetic and safety contract,
including initial operands under arbitrary valid overlap, normal finite return,
caller-byte preservation, and the claimed feature-family coverage. Re-run the
original mutation/refutation cases before claiming equivalent verification scope.
Further extraction or proof-composition gaps should be reproduced upstream rather
than hidden behind consumer copies of CIL infrastructure.
