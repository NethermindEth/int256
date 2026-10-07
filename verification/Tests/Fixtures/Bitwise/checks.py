"""Check bitwise mutations through fresh extraction and the public proof gate."""

import argparse
import json
from pathlib import Path
import shutil
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[3]))
sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

from common import PROFILE_NAMES, ROOT, expected_profile, VERIFY, run, method_manifest
from support import isolated_run, require_diagnostic_rejection, initial_bytes_expression, template_refutation, mutation_proof, selected_fixture_baseline, native_witness

METHOD = "Xor"
MODULE = "UInt256/Methods/Bitwise/Xor.lean"
WITNESSES = Path(__file__).with_name("Witnesses.json")


def semantic_rejection(output):
    """Called only after the same extracted program's full refutation passes."""
    require_diagnostic_rejection(output, MODULE,
        r"Tactic `introN` failed:.*|Tactic `apply` failed:.*|`simp` made no progress")


def refute(proof, lake, witness, approved):
    initial = initial_bytes_expression(witness)
    substitutions = {"INITIAL": initial, "LEFT": witness["leftBase"],
                     "RIGHT": witness["rightBase"], "OUT": witness["outputBase"],
                     "ADDRESS": witness["witnessAddress"], "ACTUAL": witness["actualByte"],
                     "EXPECTED": witness["expectedByte"]}
    template_refutation(proof, lake, Path(__file__).with_name("RefutationTemplate.lean.in"),
                        substitutions, "Refutation", "UInt256Proof.Bitwise.Witness.refuted", approved, register=True)


def native_check(work, assembly, witness):
    assignments = "\n".join(f"bytes[{int(address)}] = {int(value)};"
                            for address, value in witness["initialBytes"].items())
    source = f'''using System;
using System.Runtime.CompilerServices;
using Nethermind.Int256;
byte[] bytes = new byte[192];
{assignments}
ref UInt256 left = ref Unsafe.As<byte, UInt256>(ref bytes[{witness["leftBase"]}]);
ref UInt256 right = ref Unsafe.As<byte, UInt256>(ref bytes[{witness["rightBase"]}]);
ref UInt256 output = ref Unsafe.As<byte, UInt256>(ref bytes[{witness["outputBase"]}]);
UInt256.Xor(in left, in right, out output);
byte result = bytes[{witness["witnessAddress"]}];
Console.WriteLine($"Native bitwise witness: {{result}}");
return result == {witness["actualByte"]} ? 0 : 1;
'''
    native_witness(work, assembly, source)


def check_workspace(profile, cases):
    lake = shutil.which("lake")
    if not lake:
        raise RuntimeError("Pinned Lean / lake must be on PATH")
    manifest = method_manifest(METHOD)
    public, report_path, baseline = selected_fixture_baseline(METHOD, profile, "BitwiseHelper")
    project = WITNESSES.parent / "Nethermind.Int256.csproj"
    for case, witness in cases.items():
        work = ROOT / "artifacts/bitwise-negatives" / case
        work.mkdir(parents=True)
        bundle, proof = mutation_proof(work, project, case, METHOD, profile, baseline)
        refute(proof, lake, witness, manifest["approvedAxioms"])
        if witness["profiles"] == "all":
            native_check(work, bundle["assembly"], witness)
        output = run(public + ["--fixture", case], ROOT, succeeds=False)
        semantic_rejection(output)
        if report_path.exists():
            raise RuntimeError("Failed verification retained a successful report")
        print(f"PASS: {case}, independent full-contract refutation and public rejection")


def main():
    sys.stdout.reconfigure(encoding="utf-8")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--profile", choices=PROFILE_NAMES, default="scalar")
    parser.add_argument("--workspace", action="store_true", help=argparse.SUPPRESS)
    args = parser.parse_args()
    cases = json.loads(WITNESSES.read_text(encoding="utf-8"))["negativeCases"]
    # Accelerated-only witnesses are selected once the profile exposes that feature.
    cases = {name: witness for name, witness in cases.items()
             if witness["profiles"] == "all" or expected_profile(args.profile)["Vector256Accelerated"]}
    if args.workspace:
        check_workspace(args.profile, cases)
        return
    isolated_run(__file__, ["--profile", args.profile], "int256-bitwise-negative-")



if __name__ == "__main__":
    main()
