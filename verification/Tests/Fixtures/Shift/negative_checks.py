"""Fresh Shift fixtures, full-contract refutations and public verifier rejection."""

import argparse
import json
from pathlib import Path
import shutil
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[3]))
sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

from common import PROFILE_NAMES, ROOT, VERIFY, run, method_manifest
from support import isolated_run, require_diagnostic_rejection, initial_bytes_expression, template_refutation, mutation_proof, selected_fixture_baseline

DIRECTORY = Path(__file__).resolve().parent
METHODS = {"Lsh": "left", "Rsh": "right", "LeftShift": "left", "RightShift": "right",
           "OperatorLsh": "left", "OperatorRsh": "right"}


def semantic_rejection(output, direction, operator):
    """A diagnostic is accepted only after its full-contract refutation passes."""
    module = ("OperatorLshExecution" if direction == "left" else "OperatorRshExecution") if operator else (
        "Entry" if direction == "left" else "RshExecution")
    require_diagnostic_rejection(output, f"UInt256/Methods/Shift/{module}.lean",
        r"unsolved goals|`simp` made no progress|omega could not prove the goal:|"
        r"Tactic `introN` failed: There are no additional binders or `let` bindings in the goal to introduce")


def refute(proof, lake, witness, approved, operator):
    initial = initial_bytes_expression(witness)
    substitutions = {"INITIAL": initial, "DIRECTION": witness["direction"],
                     "INPUT": witness["inputBase"], "OUTPUT": witness["outputBase"],
                     "COUNT": witness["count"], "ADDRESS": witness["address"],
                     "ACTUAL": witness["actualByte"], "EXPECTED": witness["expectedByte"]}
    if operator:
        substitutions.update(ACTUAL=witness["operatorActual"], EXPECTED=witness["operatorExpected"])
    template = "OperatorRefutationTemplate.lean.in" if operator else "RefutationTemplate.lean.in"
    template_refutation(proof, lake, DIRECTORY / template, substitutions,
                        "UInt256.Methods.Shift.Witness", "UInt256Proof.Shift.Witness.refuted", approved)


def check_workspace(method, profile, safety=False):
    lake = shutil.which("lake")
    if not lake:
        raise RuntimeError("Pinned Lean / lake must be on PATH")
    manifest = method_manifest(method)
    direction = METHODS[method]
    operator = method.startswith("Operator")
    public, report_path, baseline = selected_fixture_baseline(method, profile,
        "LshHelper" if direction == "left" else None, safety=safety)
    if method == "OperatorLsh":
        run(public + ["--fixture", "LshEarlyStore"], ROOT)
        alternative = json.loads(report_path.read_text(encoding="utf-8"))
        if alternative["leanSourceSha256"] != baseline["leanSourceSha256"]:
            raise RuntimeError("Private-output fixture changed handwritten proofs")
        if alternative["generatedProgramSha256"] == baseline["generatedProgramSha256"]:
            raise RuntimeError("Private-output fixture did not change its actual extracted program")
        print("PASS: OperatorLsh/LshEarlyStore, private output preserves the public contract")
    cases = json.loads((DIRECTORY / "Witnesses.json").read_text(encoding="utf-8"))["negativeCases"]
    project = DIRECTORY / "Nethermind.Int256.csproj"
    intended = method_manifest("Lsh" if direction == "left" else "Rsh")["entry"]
    for case, witness in cases.items():
        if witness["direction"] != direction or (operator and "operatorActual" not in witness):
            continue
        work = ROOT / "artifacts/shift-negatives" / method / case
        work.mkdir(parents=True)
        bundle, proof = mutation_proof(work, project, case, method, profile, baseline, intended)
        refute(proof, lake, witness, manifest["approvedAxioms"], operator)
        output = run(public + ["--fixture", case], ROOT, succeeds=False)
        semantic_rejection(output, direction, operator)
        if report_path.exists():
            raise RuntimeError("Failed verification retained a successful report")
        print(f"PASS: {method}/{case}, full-contract refutation and public rejection")


def main():
    sys.stdout.reconfigure(encoding="utf-8")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--method", choices=METHODS, default="Lsh")
    parser.add_argument("--profile", choices=PROFILE_NAMES, default="scalar")
    parser.add_argument("--safety", action="store_true", help="Require combined arithmetic and memory-safety verification")
    parser.add_argument("--workspace", action="store_true", help=argparse.SUPPRESS)
    args = parser.parse_args()
    if args.workspace:
        check_workspace(args.method, args.profile, args.safety)
        return
    arguments = ["--method", args.method, "--profile", args.profile]
    if args.safety:
        arguments.append("--safety")
    isolated_run(__file__, arguments, "int256-shift-negative-")



if __name__ == "__main__":
    main()
