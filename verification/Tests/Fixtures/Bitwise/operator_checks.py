"""Check returned bitwise values through the same public contract as production."""

import argparse
import json
from pathlib import Path
import shutil
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[3]))
sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

from common import PROFILE_NAMES, ROOT, run
from methods import method_manifest
from support import isolated_run, initial_bytes_expression, mutation_proof, native_witness, require_diagnostic_rejection, selected_fixture_baseline, template_refutation

OPERATIONS = {
    "OperatorXor": ("Xor", "xor", "^"),
    "OperatorAnd": ("And", "and", "&"),
    "OperatorOr": ("Or", "or", "|"),
    "OperatorNot": ("Not", None, "~"),
}
DIRECTORY = Path(__file__).parent


def check_workspace(method, profile):
    dependency, operation, symbol = OPERATIONS[method]
    lake = shutil.which("lake")
    if not lake:
        raise RuntimeError("Pinned Lean / lake must be on PATH")
    manifest = method_manifest(method)
    public, report_path, baseline = selected_fixture_baseline(method, profile, "BitwiseHelper")
    run(public + ["--fixture", "BitwiseEarlyStore"], ROOT)
    positive = json.loads(report_path.read_text(encoding="utf-8"))
    if positive["leanSourceSha256"] != baseline["leanSourceSha256"]:
        raise RuntimeError("Private output fixture changed handwritten proofs")
    intended = method_manifest(dependency)["entry"]
    original = next(body for body in baseline["artifact"]["methods"] if body["signature"] == intended)
    changed = next(body for body in positive["artifact"]["methods"] if body["signature"] == intended)
    if changed["instructions"] == original["instructions"]:
        raise RuntimeError("Private output fixture did not change the actual selected dependency")
    print("PASS: early output stores preserve returned arithmetic and caller bytes")

    witnesses = json.loads((DIRECTORY / "Witnesses.json").read_text(encoding="utf-8"))
    for case in witnesses["returnNegativeCases"]:
        witness = dict(witnesses["negativeCases"][case])
        if method in {"OperatorAnd", "OperatorOr"}:
            witness.update(actualReturn=0, expectedReturn=1)
        elif method == "OperatorNot":
            witness.update(actualReturn=1, expectedReturn=(1 << 256) - 2)
        left, right = witness["leftBase"], witness["rightBase"]
        arguments = f"[.object {left}]" if operation is None else f"[.object {left},.object {right}]"
        expected = (f"~~~byteValue initial {left}" if operation is None else
                    f"UInt256Model.Bitwise.applyBinary .{operation} (byteValue initial {left}) (byteValue initial {right})")
        contract = (f"UInt256Model.Bitwise.NotReturnContract Extracted.program Extracted.entryIndex initial {left}" if operation is None else
                    f"UInt256Model.Bitwise.ReturnContract Extracted.program Extracted.entryIndex .{operation} initial {left} {right}")
        parameters = f"initial {left}" if operation is None else f".{operation} initial {left} {right}"
        refutation = "UInt256Proof.Bitwise." + ("not_return_observation_refuted" if operation is None else "return_observation_refuted")
        work = ROOT / "artifacts/bitwise-return-negatives" / method / case
        work.mkdir(parents=True)
        mutation_target = intended if operation == "xor" else (
            f"System.UInt64 Nethermind.Int256.UInt256::Word{dependency}(System.UInt64"
            + (")" if operation is None else ",System.UInt64)"))
        bundle, proof = mutation_proof(work, DIRECTORY / "Nethermind.Int256.csproj", case,
                                       method, profile, baseline, intended=mutation_target)
        template_refutation(proof, lake, DIRECTORY / "ReturnRefutationTemplate.lean.in",
                            {"INITIAL": initial_bytes_expression(witness), "LEFT": witness["leftBase"],
                             "RIGHT": witness["rightBase"], "ARGUMENTS": arguments, "EXPECTED_EXPRESSION": expected,
                             "CONTRACT": contract, "PARAMETERS": parameters, "REFUTATION": refutation, "ACTUAL": witness["actualReturn"],
                             "EXPECTED": witness["expectedReturn"]}, "ReturnRefutation",
                            "UInt256Proof.Bitwise.ReturnWitness.refuted", manifest["approvedAxioms"], register=True)
        assignments = "\n".join(f"bytes[{int(address)}] = {int(value)};"
                                for address, value in witness["initialBytes"].items())
        native_witness(work, bundle["assembly"], f'''using System;
using System.Runtime.CompilerServices;
using Nethermind.Int256;
byte[] bytes = new byte[192];
{assignments}
byte[] before = (byte[])bytes.Clone();
ref UInt256 left = ref Unsafe.As<byte, UInt256>(ref bytes[{witness["leftBase"]}]);
ref UInt256 right = ref Unsafe.As<byte, UInt256>(ref bytes[{witness["rightBase"]}]);
UInt256 result = {"~left" if operation is None else "left " + symbol + " right"};
Console.WriteLine($"Native returned bitwise witness: {{result.u0}}");
return result.u0 == {witness["actualReturn"]} && result.u1 == 0 && result.u2 == 0 && result.u3 == 0
    && bytes.AsSpan().SequenceEqual(before) ? 0 : 1;
''')
        output = run(public + ["--fixture", case], ROOT, succeeds=False)
        require_diagnostic_rejection(output, "UInt256/Methods/SelectedGate.lean",
                                     r"Tactic `first` failed:.*|Tactic `introN` failed:.*|Tactic `apply` failed:.*")
        if report_path.exists():
            raise RuntimeError("Failed returned-value verification retained a report")
        print(f"PASS: {case}, returned-value full-contract refutation and public rejection")


def main():
    sys.stdout.reconfigure(encoding="utf-8")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--method", choices=tuple(OPERATIONS), default="OperatorXor")
    parser.add_argument("--profile", choices=PROFILE_NAMES, default="scalar")
    parser.add_argument("--workspace", action="store_true", help=argparse.SUPPRESS)
    args = parser.parse_args()
    if args.workspace:
        check_workspace(args.method, args.profile)
    else:
        isolated_run(__file__, ["--method", args.method, "--profile", args.profile], "int256-bitwise-return-")


if __name__ == "__main__":
    main()
