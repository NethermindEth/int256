"""Shared isolation, witnesses and rejection gates for verification regressions."""

import json
from pathlib import Path
import re
import shutil
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from common import BUILD_DIRECTORIES, ROOT, VERIFY, run, sha
from verify import source_inputs


def copy_source(destination):
    shutil.copytree(ROOT / "src", destination / "src",
                    ignore=shutil.ignore_patterns(*BUILD_DIRECTORIES, "TestResults"))
    for name in ("global.json", "README.md", ".editorconfig"):
        shutil.copy2(ROOT / name, destination / name)
    for source in ROOT.iterdir():
        if source.is_file() and source.suffix.lower() in {".props", ".targets", ".config"}:
            shutil.copy2(source, destination / source.name)
    proof = destination / "verification"
    shutil.copytree(VERIFY, proof, ignore=shutil.ignore_patterns(*BUILD_DIRECTORIES))
    workflows = destination / ".github/workflows"
    workflows.mkdir(parents=True)
    for workflow in (ROOT / ".github/workflows").glob("verify-uint256*.yml"):
        shutil.copy2(workflow, workflows / workflow.name)
    return proof


def build_fixture(destination, name, method="Add"):
    project = destination / "verification/Tests/Fixtures/Nethermind.Int256.csproj"
    source = project.parent / method / f"{name}.cs"
    if not source.is_file():
        raise RuntimeError(f"Fixture maintenance failure: missing {name}")
    run(["dotnet", "build", str(project), "-c", "Release",
         f"-p:FixtureSource={source}", f"-p:FixtureMethod={method}", "-p:EnforceCodeStyleInBuild=true",
         "-p:GenerateDocumentationFile=true"], destination)
    return project.parent / "bin/Release/net10.0/Nethermind.Int256.dll"


def build_extract(destination, name, method="Add"):
    assembly = build_fixture(destination, name, method)
    output = destination / "verification/generated"
    result = run(["dotnet", "run", "--project", str(VERIFY / "Extractor"), "-c", "Release", "--",
                  str(assembly), str(output), method], ROOT)
    return assembly, output, result


def require_semantic_rejection(output, module):
    # A kernel-checked model refutation precedes this check. Tactic failures can
    # phrase the remaining semantic obligation differently. Require a printed
    # goal or the final simplifier's no-progress diagnostic in the expected
    # execution module; syntax/import failures alone cannot satisfy this gate.
    normalized = output.replace("\\", "/")
    errors = [block for block in re.split(r"(?=^error: )", normalized, flags=re.MULTILINE)
              if block.startswith("error: ")]
    relevant = [block for block in errors if block.startswith(f"error: {module}:")]
    no_progress = r":\d+:\d+: `simp` made no progress(?:\n|$)"
    if not any("⊢" in block or re.search(no_progress, block) for block in relevant):
        raise RuntimeError("Mutation failed outside the expected semantic proof obligation")
    if any(limit in block for block in errors for limit in
           ("maximum number of heartbeats", "maximum recursion depth", "maximum number of steps exceeded",
            "deep recursion", "stack overflow")):
        raise RuntimeError("Mutation rejection was inconclusive due to exhausted proof resources")


def model_refutation(proof, lake, initial, left, right, out, address, actual, expected, method="Add"):
    """Kernel-check a concrete refutation of the unchanged full contract."""
    contract = "Contract" if method == "Add" else "SubtractContract"
    operation = "+" if method == "Add" else "-"
    source = f'''import Extracted
import UInt256.Methods.{method}.Contract
import CIL.SymbolicExecution
open CIL UInt256Model
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
namespace UInt256Proof
def witnessBytes : Bytes := fun address => {initial}
def observed := (invoke Extracted.program (executionBound Extracted.program Extracted.entryIndex) Extracted.entryIndex
  [.object {left}, .object {right}, .object {out}] (byteMemory witnessBytes)).map
    (fun result => result.1 (.byte {address}))
theorem model_observed : observed = some (some (.i8 {actual})) := by decide
theorem model_expected : writeBytes (byteMemory witnessBytes) {out}
    (byteValue witnessBytes {left} {operation} byteValue witnessBytes {right}).toNat 32 (.byte {address}) =
      some (.i8 {expected}) := by decide
theorem model_not_correct : ¬ {contract} Extracted.program Extracted.entryIndex witnessBytes {left} {right} {out} := by
  rintro ⟨fuel, final, hr, hm⟩
  have ho := model_observed
  unfold observed at ho
  cases he : invoke Extracted.program (executionBound Extracted.program Extracted.entryIndex)
      Extracted.entryIndex [.object {left}, .object {right}, .object {out}]
      (byteMemory witnessBytes) with
  | none => simp [he] at ho
  | some result =>
    have unique := invoke_result_unique Extracted.program fuel
      (executionBound Extracted.program Extracted.entryIndex) Extracted.entryIndex
      [.object {left}, .object {right}, .object {out}] (byteMemory witnessBytes)
      (final, []) result hr he
    rw [← unique] at he
    rw [he] at ho
    simp only [Option.map_some] at ho
    have ha : final (.byte {address}) = some (.i8 {actual}) := Option.some.inj ho
    have he := hm {address}
    rw [model_expected] at he
    have different : (some (.i8 {actual}) : Option Value) ≠ some (.i8 {expected}) := by decide
    exact different (ha.symm.trans he)
#print axioms model_not_correct
end UInt256Proof
'''
    (proof / "Refutation.lean").write_text(source, encoding="utf-8")
    with (proof / "lakefile.toml").open("a", encoding="utf-8") as configuration:
        configuration.write('\n[[lean_lib]]\nname = "Refutation"\n')
    output = run([lake, "build", "Refutation"], proof)
    audits = re.findall(r"'UInt256Proof.model_not_correct' depends on axioms: \[([^]]*)\]", output)
    if len(audits) != 1:
        raise RuntimeError("Missing kernel refutation axiom audit")
    permitted = set(json.loads((proof / f"manifests/{method.lower()}.json").read_text(encoding="utf-8"))["approvedAxioms"])
    if {item.strip() for item in audits[0].split(",") if item.strip()} - permitted:
        raise RuntimeError("Unapproved axioms in model refutation")
    print(f"PASS: kernel refutes the full contract at byte {address}: actual {actual}, expected {expected}")


def require_production_report(method="Add"):
    generated = VERIFY / ("generated" if method == "Add" else "generated/subtract")
    baseline = generated / "Extracted.lean"
    report_path = generated / "report.json"
    if not baseline.is_file() or not report_path.is_file():
        raise RuntimeError(f"Freshly verify production {method} before negative checks")
    report = json.loads(report_path.read_text(encoding="utf-8"))
    if (report.get("status") != "verified" or report.get("source", {}).get("kind") != "production"
            or report["sourceInputs"] != source_inputs()
            or report["generatedProgramSha256"] != sha(baseline)
            or any(sha(VERIFY / name) != digest for name, digest in report["leanSourceSha256"].items())):
        raise RuntimeError(f"Fresh current {method} production report required")
    return baseline


def native_witness(destination, assembly, source):
    witness = destination / "Witness"
    witness.mkdir()
    (witness / "Witness.csproj").write_text(
        '<Project Sdk="Microsoft.NET.Sdk"><PropertyGroup><OutputType>Exe</OutputType>'
        '<TargetFramework>net10.0</TargetFramework></PropertyGroup><ItemGroup>'
        f'<Reference Include="Nethermind.Int256"><HintPath>{assembly.as_posix()}</HintPath>'
        '</Reference></ItemGroup></Project>', encoding="utf-8")
    (witness / "Program.cs").write_text(source, encoding="utf-8")
    run(["dotnet", "run", "--project", str(witness), "-c", "Release"], destination)
