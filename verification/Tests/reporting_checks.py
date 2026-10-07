"""Reporting fixtures: unchanged public proofs and independent all-fuel refutations."""

import argparse
import json
from pathlib import Path
import shutil
import sys
import tempfile
import xml.etree.ElementTree as ET

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from common import verifier_command, ROOT, PROFILES, run, sha
from common import copy_source, require_semantic_rejection
from simd_checks import positive_applicable, target_changed, applicable, witness
from common import theorem_audits

METHODS = ("AddOverflow", "SubtractUnderflow")
_cases = ET.parse(ROOT / "verification/Tests/Fixtures/Reporting/Cases.props").findall("ItemGroup/ReportingCase")
POSITIVES = tuple(case.attrib["Include"] for case in _cases if case.attrib["Suite"] == "positive")
NEGATIVES = tuple(case.attrib["Include"] for case in _cases if case.attrib["Suite"] == "negative")


def report_path(proof, method, profile):
    return proof / "generated/operations" / method / profile / "report.json"


def legacy(method):
    return "Add" if method == "AddOverflow" else "Subtract"


def checked_fixture(destination, proof, method, profile, case):
    run([*verifier_command(proof.parent), "--method", method,
         "--profile", profile, "--fixture", case], destination)
    report = json.loads(report_path(proof, method, profile).read_text(encoding="utf-8"))
    if (report["source"]["kind"] != "fixture" or report["source"].get("case") != case
            or report["source"]["fixture"] != "verification/Tests/Fixtures/Reporting/Public.cs"
            or report["executionProfile"]["Name"] != profile):
        raise RuntimeError("Reporting fixture provenance mismatch")
    if any(kind == "resource limit" for _, kind in report["summaryRejections"]):
        raise RuntimeError("Reporting fixture exhausted optional proof resources")
    if case == "ReversedStore" and not any("storeLimbsIndex" in name for name, _ in report["summaryRejections"]):
        raise RuntimeError("Reversed storage did not exercise transactional raw fallback")
    return report


def refute(proof, lake, method, initial, out, address=None, actual=1, expected=0):
    operation = ".add" if method == "AddOverflow" else ".subtract"
    observation = "outcome.2" if address is None else f"outcome.1 (.byte {address})"
    observed = f"[.i32 {actual}]" if address is None else f"some (.i8 {actual})"
    comparison = (f"((if flag {operation} (byteValue witnessBytes 0) (byteValue witnessBytes 64) then 1 else 0) : W32)"
                  if address is None else
                  f"writeBytes (byteMemory witnessBytes) {out} (result {operation} (byteValue witnessBytes 0) (byteValue witnessBytes 64)).toNat 32 (.byte {address})")
    expected_value = str(expected) if address is None else f"some (.i8 {expected})"
    lemma = "flag_observation_refuted" if address is None else "byte_observation_refuted"
    arguments = str(actual) if address is None else f"{address} (some (.i8 {actual}))"
    source = f"""import Extracted
import UInt256.Methods.Reporting.Refutation
import CIL.SymbolicExecution
open CIL UInt256Model UInt256Proof.Reporting
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace ReportingWitness
def witnessBytes : Bytes := fun address => {initial}
def observed := (invoke Extracted.program (executionBound Extracted.program Extracted.entryIndex)
  Extracted.entryIndex [.object 0, .object 64, .object {out}] (byteMemory witnessBytes)).map
    (fun outcome => {observation})
theorem model_observed : observed = some ({observed}) := by decide
theorem model_expected : ({comparison}) = {expected_value} := by decide
theorem model_not_correct : ¬ Contract {operation} Extracted.program Extracted.entryIndex
    witnessBytes 0 64 {out} := by
  apply {lemma} Extracted.program Extracted.entryIndex
    (executionBound Extracted.program Extracted.entryIndex) {operation} witnessBytes 0 64 {out}
    {arguments} model_observed
  rw [model_expected]
  decide
#print axioms model_not_correct
end ReportingWitness
"""
    (proof / "ReportingWitness.lean").write_text(source, encoding="utf-8")
    config = proof / "lakefile.toml"
    text = config.read_text(encoding="utf-8")
    if 'name = "ReportingWitness"' not in text:
        config.write_text(text+'\n[[lean_lib]]\nname = "ReportingWitness"\n', encoding="utf-8")
    output = run([lake, "build", "ReportingWitness"], proof)
    theorem_audits(output, ["ReportingWitness.model_not_correct"],
                  {"propext", "Classical.choice", "Quot.sound"})


def negative(destination, proof, lake, method, profile, case, baseline):
    project = proof / "Tests/Fixtures/Reporting/Nethermind.Int256.csproj"
    run(["dotnet", "build", str(project), "-c", "Release", "--no-incremental",
         f"-p:FixtureCase={case}", "-p:EnforceCodeStyleInBuild=true",
         "-p:GenerateDocumentationFile=true"], destination)
    dll = project.parent / "bin/Release/net10.0/Nethermind.Int256.dll"
    run(["dotnet", "run", "--project", str(proof/"Extractor"), "-c", "Release", "--",
         str(dll), str(proof/"generated"), method, profile], destination)
    artifact = json.loads((proof/"generated/artifact.json").read_text(encoding="utf-8"))
    if artifact["profile"]["Name"] != profile:
        raise RuntimeError("Counterexample profile mismatch")
    before = [[(i["opcode"],i["operand"]) for i in m["instructions"]] for m in baseline["artifact"]["methods"]]
    after = [[(i["opcode"],i["operand"]) for i in m["instructions"]] for m in artifact["methods"]]
    if before == after:
        raise RuntimeError("Semantic negative did not change reachable CIL")
    for relative, digest in baseline["leanSourceSha256"].items():
        if sha(proof/relative) != digest:
            raise RuntimeError("Semantic negative changed handwritten proofs")
    if case == "WrongFlag":
        refute(proof, lake, method, "0", 128)
    else:
        a,b,out,(address,actual) = witness(case,legacy(method))
        number = lambda words: sum(word << (64*i) for i,word in enumerate(words))
        value = (number(a)+number(b) if method == "AddOverflow" else number(a)-number(b)) % 2**256
        expected = (value >> (8*(address-out))) & 255
        if actual == expected:
            raise RuntimeError("Witness fails to distinguish full contract")
        initial = (f"if address < 32 then BitVec.ofNat 8 (({a} : List Nat)[address / 8]! / 256^(address % 8)) "
                   f"else if 64 ≤ address ∧ address < 96 then BitVec.ofNat 8 (({b} : List Nat)[(address-64) / 8]! / 256^(address % 8)) else 0")
        refute(proof,lake,method,initial,out,address,actual,expected)
    output = run([*verifier_command(proof.parent),"--method",method,"--profile",profile,
                  "--fixture",case], destination,succeeds=False)
    entry = "AddEntry" if method == "AddOverflow" else "SubtractEntry"
    require_semantic_rejection(output,f"UInt256/Methods/Reporting/{entry}.lean")
    if report_path(proof,method,profile).exists():
        raise RuntimeError("Rejected reporting fixture retained a success report")
    print(f"PASS: {method}/{profile}/{case}, full contract independently refuted",flush=True)


def main():
    sys.stdout.reconfigure(encoding="utf-8")
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--method",choices=METHODS+("all",),default="all")
    parser.add_argument("--profile",choices=PROFILES+("all",),default="all")
    parser.add_argument("--case",choices=POSITIVES+NEGATIVES+("all",),default="all")
    args=parser.parse_args()
    methods=METHODS if args.method=="all" else (args.method,)
    profiles=PROFILES if args.profile=="all" else (args.profile,)
    lake=shutil.which("lake")
    if not lake: raise RuntimeError("Pinned Lean/lake must be on PATH")
    with tempfile.TemporaryDirectory(prefix="int256-reporting-") as temporary:
        destination=Path(temporary)
        run(["git","clone","--shared","--no-checkout","--quiet",str(ROOT),str(destination)],ROOT)
        proof=copy_source(destination)
        for method in methods:
            for profile in profiles:
                run([*verifier_command(proof.parent),"--method",method,"--profile",profile],destination)
                production=json.loads(report_path(proof,method,profile).read_text(encoding="utf-8"))
                if production["source"]["kind"] != "production": raise RuntimeError("Fresh production baseline required")
                baseline=checked_fixture(destination,proof,method,profile,"Baseline")
                for case in POSITIVES[1:]:
                    if (args.case not in ("all",case)
                            or (profile == "scalar" and case == "ExtractedHelper")
                            or not positive_applicable(case,legacy(method),profile)): continue
                    report=checked_fixture(destination,proof,method,profile,case)
                    if report["leanSourceSha256"] != baseline["leanSourceSha256"]: raise RuntimeError("Positive changed handwritten proofs")
                    target_changed(case,legacy(method),profile,baseline["artifact"],report["artifact"])
                for case in NEGATIVES:
                    if args.case not in ("all",case) or (case != "WrongFlag" and not applicable(case,legacy(method),profile)): continue
                    negative(destination,proof,lake,method,profile,case,baseline)


if __name__=="__main__": main()
