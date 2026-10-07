"""Check comparison mutations through fresh extraction and the public proof gate."""

import argparse
import json
from pathlib import Path
import shutil
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[3]))
sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

from common import PROFILE_NAMES, ROOT, expected_profile, VERIFY, run, method_manifest
from support import isolated_run, require_diagnostic_rejection, initial_bytes_expression, template_refutation, mutation_proof, selected_fixture_baseline, native_witness

METHOD = "LtUInt256UInt256"
MODULE = "UInt256/Methods/Compare/Less.lean"
WITNESSES = Path(__file__).with_name("Witnesses.json")


def semantic_rejection(output):
    """Called only after the same extracted program's full refutation passes."""
    require_diagnostic_rejection(output, MODULE, "omega could not prove the goal:")


def refute(proof, lake, witness, approved):
    initial = initial_bytes_expression(witness)
    substitutions = {"INITIAL": initial, "LEFT": witness["leftBase"],
                     "RIGHT": witness["rightBase"], "ACTUAL": witness["actualResult"],
                     "EXPECTED": "true" if witness["expectedResult"] else "false"}
    template_refutation(proof, lake, Path(__file__).with_name("RefutationTemplate.lean.in"),
                        substitutions, "Refutation", "UInt256Proof.Compare.Witness.refuted", approved, register=True)


def native_check(work, assembly, witness):
    assignments = "\n".join(f"bytes[{int(address)}] = {int(value)};"
                            for address, value in witness["initialBytes"].items())
    source = f'''using System;
using System.Runtime.CompilerServices;
using Nethermind.Int256;
byte[] bytes = new byte[128];
{assignments}
UInt256 left = Unsafe.ReadUnaligned<UInt256>(ref bytes[{witness["leftBase"]}]);
UInt256 right = Unsafe.ReadUnaligned<UInt256>(ref bytes[{witness["rightBase"]}]);
bool result = left < right;
Console.WriteLine($"Native comparison witness: {{result}}");
return result == {str(bool(witness["actualResult"])).lower()} ? 0 : 1;
'''
    native_witness(work, assembly, source)


def check_workspace(profile, cases):
    lake = shutil.which("lake")
    if not lake:
        raise RuntimeError("Pinned Lean / lake must be on PATH")
    manifest = method_manifest(METHOD)
    public, report_path, baseline = selected_fixture_baseline(METHOD, profile, "ComparisonAlternative")
    project = WITNESSES.parent / "Nethermind.Int256.csproj"
    for case, witness in cases.items():
        work = ROOT / "artifacts/comparison-negatives" / case
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
    isolated_run(__file__, ["--profile", args.profile], "int256-compare-negative-")



if __name__ == "__main__":
    main()
