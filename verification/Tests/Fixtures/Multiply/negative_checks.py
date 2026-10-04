"""Fresh Multiply fixtures, all-fuel contract refutations and public rejection."""

import argparse
import json
from pathlib import Path
import shutil
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[3]))
sys.path.insert(0, str(Path(__file__).resolve().parents[2]))

from common import PROFILE_NAMES, ROOT, run
from methods import method_manifest
from support import (
    initial_bytes_expression,
    isolated_run,
    mutation_proof,
    require_changed_method,
    require_diagnostic_rejection,
    selected_fixture_baseline,
    template_refutation,
)

DIRECTORY = Path(__file__).resolve().parent
ARGUMENTS = "Nethermind.Int256.UInt256&,Nethermind.Int256.UInt256&,Nethermind.Int256.UInt256&"
INTENDED = {
    "WrongCarry": "System.UInt64 Nethermind.Int256.UInt256::AddAndCountCarry(System.UInt64,System.UInt64,System.UInt64&)",
    "WrongCrossProduct": f"System.Void Nethermind.Int256.UInt256::MultiplyLimbs2x2({ARGUMENTS})",
    "WrongHighLow": f"System.Void Nethermind.Int256.UInt256::Multiply({ARGUMENTS})",
    "WrongAliasing": "System.Void Nethermind.Int256.UInt256::MultiplyByUInt64(Nethermind.Int256.UInt256&,System.UInt64,Nethermind.Int256.UInt256&)",
    "WrongBmiHigh": "System.UInt64 Nethermind.Int256.UInt256::Multiply64(System.UInt64,System.UInt64,System.UInt64&)",
}


def refute(proof, lake, witness, approved):
    substitutions = {
        "INITIAL": initial_bytes_expression(witness),
        "LEFT": witness["leftBase"],
        "RIGHT": witness["rightBase"],
        "OUTPUT": witness["outputBase"],
        "ADDRESS": witness["address"],
        "ACTUAL": witness["actualByte"],
        "EXPECTED": witness["expectedByte"],
    }
    template_refutation(
        proof, lake, DIRECTORY / "RefutationTemplate.lean.in", substitutions,
        "UInt256.Methods.Multiply.Witness", "UInt256Proof.Multiply.Witness.refuted", approved,
    )


def check_workspace(profile):
    lake = shutil.which("lake")
    if not lake:
        raise RuntimeError("Pinned Lean / lake must be on PATH")
    manifest = method_manifest("Multiply")
    public, report_path, baseline = selected_fixture_baseline("Multiply", profile, "AlternativeOrder")
    alternative = json.loads(report_path.read_text(encoding="utf-8"))
    intended = f"System.Void Nethermind.Int256.UInt256::MultiplyLimbs4x4({ARGUMENTS})"
    require_changed_method(alternative["artifact"], baseline["artifact"], intended)
    run(public + ["--fixture", "ExtractedHelper"], ROOT)
    helper = json.loads(report_path.read_text(encoding="utf-8"))
    if helper["leanSourceSha256"] != baseline["leanSourceSha256"]:
        raise RuntimeError("Helper fixture changed handwritten proofs")
    if helper["generatedProgramSha256"] == baseline["generatedProgramSha256"]:
        raise RuntimeError("Helper fixture did not change the actual extracted program")
    require_changed_method(helper["artifact"], baseline["artifact"], intended)
    print(f"PASS: Multiply/{profile}, both equivalent implementation variants")
    witnesses = json.loads((DIRECTORY / "witnesses.json").read_text(encoding="utf-8"))
    for witness in witnesses:
        if witness["profile"] != profile:
            continue
        case = witness["case"]
        work = ROOT / "artifacts/multiply-negatives" / profile / case
        work.mkdir(parents=True)
        _, proof = mutation_proof(work, DIRECTORY / "Nethermind.Int256.csproj", case,
                                  "Multiply", profile, baseline, INTENDED[case])
        refute(proof, lake, witness, manifest["approvedAxioms"])
        output = run(public + ["--fixture", case], ROOT, succeeds=False)
        require_diagnostic_rejection(
            output, "UInt256/Methods/Multiply/Entry.lean",
            r"unsolved goals|`simp` made no progress|omega could not prove the goal:|"
            r"Tactic `introN` failed: There are no additional binders or `let` bindings in the goal to introduce",
        )
        if report_path.exists():
            raise RuntimeError("Failed verification retained a successful report")
        print(f"PASS: Multiply/{profile}/{case}, full-contract refutation and public rejection")


def main():
    sys.stdout.reconfigure(encoding="utf-8")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--profile", choices=PROFILE_NAMES, default="scalar")
    parser.add_argument("--workspace", action="store_true", help=argparse.SUPPRESS)
    args = parser.parse_args()
    if args.workspace:
        check_workspace(args.profile)
        return
    isolated_run(__file__, ["--profile", args.profile], "int256-multiply-negative-")


if __name__ == "__main__":
    main()
