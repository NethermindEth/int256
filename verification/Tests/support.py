"""Shared isolation, witnesses and rejection gates for verification regressions."""

import json
from pathlib import Path
import re
import shutil
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from common import verifier_command, BUILD_DIRECTORIES, PROFILE_DIRECTORY, PROFILES, ROOT, VERIFY, expected_profile, generated_directory, run, sha, source_files, check_calling_convention, method_manifest
from common import check_proof_snapshot, safety_gate, source_inputs
from common import build_artifact
from common import theorem_audits, rejection_check


def isolated_run(script, arguments, prefix):
    with tempfile.TemporaryDirectory(prefix=prefix) as temporary:
        destination = Path(temporary) / "source"
        run(["git", "clone", "--shared", "--no-checkout", str(ROOT), str(destination)], ROOT)
        copy_source(destination)
        target = destination / Path(script).resolve().relative_to(ROOT)
        run([sys.executable, str(target), "--workspace", *arguments], destination)


def require_diagnostic_rejection(output, module, diagnostic):
    """Use only after an independent full-contract refutation has passed."""
    rejection_check("diagnostic", output, module, diagnostic)


def reject_resource_failure(output):
    rejection_check("resources", output)


def initial_bytes_expression(witness):
    initial = "0"
    for address, value in reversed(list(witness["initialBytes"].items())):
        initial = f"if address = {int(address)} then {int(value)} else {initial}"
    return initial


def require_changed_method(artifact, baseline, signature):
    """Require a compiled change in the intended reachable method."""
    bodies = [next((body for body in source["methods"] if body["signature"] == signature), None)
              for source in (artifact, baseline)]
    if any(body is None for body in bodies):
        raise RuntimeError(f"Fixture omitted the intended compiled operation: {signature}")
    instructions = [[(item["opcode"], item.get("scope"), item.get("operand"))
                     for item in body["instructions"]] for body in bodies]
    if instructions[0] == instructions[1]:
        raise RuntimeError("Fixture did not change the intended compiled operation")


def selected_fixture_baseline(method, profile, positive=None, *, safety=False):
    public = [*verifier_command(ROOT), "--method", method, "--profile", profile]
    directory = generated_directory(method, profile)
    if safety:
        public.append("--safety")
        directory /= "safety"
    report_path = directory / "report.json"

    def read_report():
        report = json.loads(report_path.read_text(encoding="utf-8"))
        if safety and (report.get("evidenceKind") != "arithmetic-and-memory-safety"
                       or report.get("safety") != safety_gate(method, profile)):
            raise RuntimeError("Fixture prerequisite lacks the selected combined safety evidence")
        return report

    run(public, ROOT)
    production = read_report()
    if production["source"]["kind"] != "production" or production["sourceInputs"] != source_inputs():
        raise RuntimeError("Fresh production prerequisite was not established")
    run(public + ["--fixture", "Baseline"], ROOT)
    baseline = read_report()
    if baseline["leanSourceSha256"] != production["leanSourceSha256"]:
        raise RuntimeError("Fixture baseline changed handwritten proofs")
    if positive:
        run(public + ["--fixture", positive], ROOT)
        alternative = read_report()
        if alternative["leanSourceSha256"] != baseline["leanSourceSha256"]:
            raise RuntimeError("Equivalent fixture changed handwritten proofs")
        if alternative["generatedProgramSha256"] == baseline["generatedProgramSha256"]:
            raise RuntimeError("Equivalent fixture did not change its actual extracted program")
    return public, report_path, baseline


def template_refutation(proof, lake, template, substitutions, module, theorem, approved, register=False):
    source = Path(template).read_text(encoding="utf-8")
    for name, value in substitutions.items():
        source = source.replace(f"@{name}@", str(value))
    if re.search(r"@[A-Z_]+@", source):
        raise RuntimeError("Unresolved refutation template input")
    (proof / (module.replace(".", "/") + ".lean")).write_text(source, encoding="utf-8")
    if register:
        with (proof / "lakefile.toml").open("a", encoding="utf-8") as config:
            config.write(f'\n[[lean_lib]]\nname = "{module}"\n')
    output = run([lake, "build", f"+{module}:olean"], proof)
    theorem_audits(output, [theorem], approved)


def mutation_proof(work, project, case, method, profile, baseline, intended=None):
    """Fresh fixture extraction with identical proofs and a changed target body."""
    manifest = method_manifest(method)
    source = manifest.get("verification", {}).get("fixtureSources", {}).get(case, f"{case}.cs")
    bundle = build_artifact(project, work, method, project.parent / source, True, case)
    proof = work / "proof"
    proof.mkdir()
    sources = list(source_files(VERIFY, {".lean"}))
    for source in sources:
        target = proof / source.relative_to(VERIFY)
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, target)
    for name in ("lakefile.toml", "lean-toolchain"):
        shutil.copy2(VERIFY / name, proof / name)
    check_proof_snapshot(proof, [source.relative_to(VERIFY) for source in sources] +
                         [Path("lakefile.toml"), Path("lean-toolchain")], bundle["sourceInputs"])
    extracted = proof / "generated"
    selector = profile if profile in PROFILES else "@" + str(PROFILE_DIRECTORY / f"{profile}.json")
    run(["dotnet", str(bundle["extractor"]), str(bundle["assembly"]), str(extracted),
         manifest["entry"], selector, str(VERIFY / "manifests/api-coverage.json")], ROOT)
    artifact = json.loads((extracted / "artifact.json").read_text(encoding="utf-8"))
    entry = artifact["methods"][artifact["entryIndex"]]
    if (entry["signature"] != manifest["entry"] or artifact["profile"] != expected_profile(profile)
            or artifact["sha256"] != bundle["assemblySha256"]):
        raise RuntimeError("Mutation extraction identity changed")
    check_calling_convention(entry, manifest["callingConvention"])
    signature = intended or manifest["entry"]
    require_changed_method(artifact, baseline["artifact"], signature)
    if sha(extracted / "Extracted.lean") == baseline["generatedProgramSha256"]:
        raise RuntimeError("Mutation did not change the extracted program")
    hashes = baseline["leanSourceSha256"]
    if {path.relative_to(proof).as_posix(): sha(path) for path in source_files(proof, {".lean"})
            if path.relative_to(proof).as_posix() in hashes} != hashes:
        raise RuntimeError("Mutation changed handwritten proofs")
    return bundle, proof


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
    # A kernel-checked full-contract refutation must precede this diagnostic gate.
    rejection_check("semantic", output, module)


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
    permitted = set(json.loads((proof / f"manifests/{method.lower()}.json").read_text(encoding="utf-8"))["approvedAxioms"])
    theorem_audits(output, ["UInt256Proof.model_not_correct"], permitted)
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
    output = run(["dotnet", "build", str(witness / "Witness.csproj"), "-c", "Release",
                  "-p:EnforceCodeStyleInBuild=true", "-p:GenerateDocumentationFile=true"], destination)
    if "IDE0005" in output:
        raise RuntimeError("Native witness contains unused imports")
    run(["dotnet", str(witness / "bin/Release/net10.0/Witness.dll")], destination)
