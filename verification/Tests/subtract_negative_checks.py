"""Concrete full-contract refutations of wrapping-subtraction fixtures."""

from pathlib import Path
import shutil
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from common import ROOT, VERIFY, run
from support import (build_extract, copy_source, model_refutation, native_witness,
                     require_production_report, require_semantic_rejection)


def check_fixture(name, byte_values, left, right, out, address, actual, expected):
    initial = "".join(f"if address = {offset} then {value} else " for offset, value in sorted(byte_values.items())) + "0"
    with tempfile.TemporaryDirectory(prefix=f"int256-subtract-negative-{name}-") as temporary:
        destination = Path(temporary)
        run(["git", "clone", "--shared", "--no-checkout", "--quiet", str(ROOT), str(destination)], ROOT)
        proof = copy_source(destination)
        assembly, _, _ = build_extract(destination, name, "Subtract")
        assignments = "".join(f"bytes[{offset}] = {value};" for offset, value in byte_values.items())
        native_witness(destination, assembly,
            'using System; using System.Runtime.CompilerServices; using Nethermind.Int256;\n'
            'byte[] bytes = new byte[128];' + assignments + '\n'
            f'ref UInt256 left = ref Unsafe.As<byte, UInt256>(ref bytes[{left}]);\n'
            f'ref UInt256 right = ref Unsafe.As<byte, UInt256>(ref bytes[{right}]);\n'
            f'ref UInt256 output = ref Unsafe.As<byte, UInt256>(ref bytes[{out}]);\n'
            'UInt256.Subtract(in left, in right, out output);\n'
            f'if (bytes[{address}] != {actual}) Environment.Exit(1);\n'
            f'Console.WriteLine("PASS: native {name} witness: actual {actual}, expected {expected}");\n')
        lake = shutil.which("lake")
        if not lake:
            raise RuntimeError("Lean 4.34.1 / lake must be on PATH")
        model_refutation(proof, lake, initial, left, right, out, address, actual, expected, "Subtract")
        stale = proof / "generated/subtract"
        stale.mkdir(parents=True, exist_ok=True)
        for artifact in ("Extracted.lean", "artifact.json", "report.json"):
            shutil.copy2(VERIFY / "generated/subtract" / artifact, stale / artifact)
        output = run([sys.executable, str(proof / "verify.py"), "--method", "Subtract", "--fixture", name],
                     destination, succeeds=False)
        require_semantic_rejection(output, "UInt256/Methods/Subtract/Entry.lean")
        if "Verification failed:" not in output:
            raise RuntimeError("Negative fixture did not reach the public verifier failure")
        if (proof / "generated/subtract/report.json").exists():
            raise RuntimeError("Failed fixture retained a success report")
        print(f"PASS: {name} rejected at the final entry proof", flush=True)


def main():
    sys.stdout.reconfigure(encoding="utf-8")
    require_production_report("Subtract")
    check_fixture("WrongBorrow", {32: 1, 40: 1},
                  0, 32, 64, 72, 255, 254)
    check_fixture("WrongAliasing", {0: 5, 8: 7, 64: 1, 72: 1},
                  0, 64, 8, 16, 3, 6)


if __name__ == "__main__":
    main()
