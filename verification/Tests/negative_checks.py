"""Isolated arithmetic, stale-output and fail-closed extraction regressions."""

from pathlib import Path
import json
import re
import shutil
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from common import BUILD_DIRECTORIES, ROOT, VERIFY, run, sha
from verify import source_inputs


def copy_source(destination):
    shutil.copytree(ROOT / "src", destination / "src",
                    ignore=shutil.ignore_patterns(*BUILD_DIRECTORIES, "TestResults"))
    for name in ("global.json", "README.md", ".editorconfig"):
        shutil.copy2(ROOT / name, destination / name)
    proof = destination / "verification"
    shutil.copytree(VERIFY, proof, ignore=shutil.ignore_patterns(*BUILD_DIRECTORIES))
    workflows = destination / ".github/workflows"
    workflows.mkdir(parents=True)
    shutil.copy2(ROOT / ".github/workflows/verify-uint256.yml", workflows / "verify-uint256.yml")
    return proof


def build_fixture(destination, name):
    project = destination / "verification/Tests/Fixtures/Nethermind.Int256.csproj"
    source = project.parent / "Add" / f"{name}.cs"
    if not source.is_file():
        raise RuntimeError(f"Fixture maintenance failure: missing {name}")
    run(["dotnet", "build", str(project), "-c", "Release",
         f"-p:FixtureSource={source}", "-p:EnforceCodeStyleInBuild=true",
         "-p:GenerateDocumentationFile=true"], destination)
    return project.parent / "bin/Release/net10.0/Nethermind.Int256.dll"


def build_extract(destination, name):
    assembly = build_fixture(destination, name)
    output = destination / "verification/generated"
    result = run(["dotnet", "run", "--project", str(VERIFY / "Extractor"), "-c", "Release", "--",
                  str(assembly), str(output)], ROOT)
    return assembly, output, result


def require_semantic_rejection(output, module):
    # A kernel-checked model refutation precedes this check. Tactic failures can
    # phrase the remaining semantic obligation differently; require its goal
    # and expected execution module rather than a particular tactic message.
    if module not in output.replace("\\", "/") or "error:" not in output or "⊢" not in output:
        raise RuntimeError("Mutation failed outside the expected semantic proof obligation")
    if any(limit in output for limit in ("maximum number of heartbeats", "maximum recursion depth",
                                         "deep recursion", "stack overflow")):
        raise RuntimeError("Mutation rejection was inconclusive due to exhausted proof resources")


def model_refutation(proof, lake, initial, left, right, out, address, actual, expected):
    """Kernel-check a concrete refutation of the unchanged full contract."""
    source = f'''import Extracted
import UInt256.Methods.Add.Contract
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
    (byteValue witnessBytes {left} + byteValue witnessBytes {right}).toNat 32 (.byte {address}) =
      some (.i8 {expected}) := by decide
theorem model_not_correct : ¬ Contract Extracted.program Extracted.entryIndex witnessBytes {left} {right} {out} := by
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
    permitted = set(json.loads((proof / "manifests/add.json").read_text(encoding="utf-8"))["approvedAxioms"])
    if {item.strip() for item in audits[0].split(",") if item.strip()} - permitted:
        raise RuntimeError("Unapproved axioms in model refutation")
    print(f"PASS: kernel refutes the full contract at byte {address}: actual {actual}, expected {expected}")


def check_aliasing(lake):
    with tempfile.TemporaryDirectory(prefix="int256-aliasing-") as temporary:
        destination = Path(temporary)
        proof = copy_source(destination)
        assembly, _, _ = build_extract(destination, "WrongAliasing")
        witness = destination / "Witness"
        witness.mkdir()
        (witness / "Witness.csproj").write_text(
            '<Project Sdk="Microsoft.NET.Sdk"><PropertyGroup><OutputType>Exe</OutputType>'
            '<TargetFramework>net10.0</TargetFramework></PropertyGroup><ItemGroup>'
            f'<Reference Include="Nethermind.Int256"><HintPath>{assembly.as_posix()}</HintPath>'
            '</Reference></ItemGroup></Project>', encoding="utf-8")
        (witness / "Program.cs").write_text(
            'using System;\nusing Nethermind.Int256;\n'
            'UInt256 a = new(42, 1, 0, 0), b = new(1, 0, 0, 0);\n'
            'UInt256.Add(in a, in b, out a);\n'
            'Console.WriteLine($"Aliasing witness: limbs {a.u0},{a.u1},{a.u2},{a.u3}; expected 43,1,0,0");\n'
            'if (a.u0 != 1 || a.u1 != 1 || a.u2 != 0 || a.u3 != 0) Environment.Exit(1);\n',
            encoding="utf-8")
        run(["dotnet", "run", "--project", str(witness), "-c", "Release"], destination)
        model_refutation(proof, lake, "if address = 0 then 42 else if address = 8 ∨ address = 32 then 1 else 0",
                         0, 32, 8, 16, 0, 1)
        output = run([lake, "build", "Audit"], proof, succeeds=False)
        require_semantic_rejection(output, "UInt256/Methods/Add/Helpers.lean")
        print("PASS: early output write has a concrete aliasing counterexample and fails the proof")


def main():
    sys.stdout.reconfigure(encoding="utf-8")
    lake = shutil.which("lake")
    if not lake:
        raise RuntimeError("Lean 4.34.1 / lake must be on PATH")
    baseline = VERIFY / "generated/Extracted.lean"
    report_path = VERIFY / "generated/report.json"
    if not baseline.exists() or not report_path.exists():
        raise RuntimeError("Freshly verify production Add before negative checks")
    report = json.loads(report_path.read_text(encoding="utf-8"))
    if (report.get("status") != "verified" or report.get("source", {}).get("kind") != "production"
            or report["sourceInputs"] != source_inputs()
            or report["generatedProgramSha256"] != sha(baseline)
            or any(sha(VERIFY / name) != digest for name, digest in report["leanSourceSha256"].items())):
        raise RuntimeError("Production verification report is stale or belongs to a fixture")
    run([lake, "build", "Audit"], VERIFY)
    check_aliasing(lake)
    with tempfile.TemporaryDirectory(prefix="int256-carry-") as temporary:
        destination = Path(temporary)
        proof = copy_source(destination)
        assembly, generated, _ = build_extract(destination, "WrongCarry")
        if sha(generated / "Extracted.lean") == sha(baseline):
            raise RuntimeError("Mutation did not change imported program")
        witness = destination / "Witness"
        witness.mkdir()
        (witness / "Witness.csproj").write_text(
            '<Project Sdk="Microsoft.NET.Sdk"><PropertyGroup><OutputType>Exe</OutputType>'
            '<TargetFramework>net10.0</TargetFramework></PropertyGroup><ItemGroup>'
            f'<Reference Include="Nethermind.Int256"><HintPath>{assembly.as_posix()}</HintPath>'
            '</Reference></ItemGroup></Project>', encoding="utf-8")
        (witness / "Program.cs").write_text(
            'using System;\nusing Nethermind.Int256;\n'
            'UInt256 a = new(ulong.MaxValue, 1, 0, 0), b = new(1, 1, 0, 0);\n'
            'UInt256.Add(a, b, out UInt256 r);\n'
            'Console.WriteLine($"Mutation witness: limbs {r.u0},{r.u1},{r.u2},{r.u3}; expected 0,3,0,0");\n'
            'if (r.u0 != 0 || r.u1 != 2 || r.u2 != 0 || r.u3 != 0) Environment.Exit(1);\n',
            encoding="utf-8")
        run(["dotnet", "run", "--project", str(witness), "-c", "Release"], destination)
        model_refutation(proof, lake,
                         "if address < 8 then 255 else if address = 8 ∨ address = 32 ∨ address = 40 then 1 else 0",
                         0, 32, 64, 72, 2, 3)
        output = run([lake, "build", "Audit"], proof, succeeds=False)
        require_semantic_rejection(output, "UInt256/Methods/Add/HelperContracts.lean")
        print("PASS: compilable wrong arithmetic changes extraction and fails the correctness proof")
        # Seed all three old success artifacts. The public command must consume
        # its new build/extraction, fail on the changed code, and remove the old report.
        for name in ("Extracted.lean", "artifact.json", "report.json"):
            shutil.copy2(VERIFY / "generated" / name, generated / name)
        output = run([sys.executable, str(proof / "verify.py"), "--fixture", "WrongCarry"], destination, succeeds=False)
        require_semantic_rejection(output, "UInt256/Methods/Add/HelperContracts.lean")
        if "Verification failed:" not in output:
            raise RuntimeError("Stale regression did not reach fresh proof checking")
        if (generated / "report.json").exists():
            raise RuntimeError("Stale successful report survived failed verification")
        print("PASS: stale extraction and report cannot verify a changed assembly")
    with tempfile.TemporaryDirectory(prefix="int256-unsupported-") as temporary:
        destination = Path(temporary)
        copy_source(destination)
        assembly = build_fixture(destination, "Unsupported")
        output = run(["dotnet", "run", "--project", str(VERIFY / "Extractor"), "-c", "Release", "--",
                      str(assembly), str(destination / "verification/generated")], ROOT, succeeds=False)
        if "Unsupported instruction:" not in output or "mul" not in output:
            raise RuntimeError("Unsupported CIL failed for an unexpected reason")
        print("PASS: reachable unsupported mul rejected explicitly")
    fixture = VERIFY / "Tests/RegressionFixture"
    run(["dotnet", "build", str(fixture), "-c", "Release",
         "-p:EnforceCodeStyleInBuild=true", "-p:GenerateDocumentationFile=true"], ROOT)
    with tempfile.TemporaryDirectory(prefix="int256-metadata-") as temporary:
        destination = Path(temporary)
        copy_source(destination)
        assembly = build_fixture(destination, "Baseline")
        for mode, diagnostic in (("unresolved", "MissingAddHelper"),
                                 ("recursion", "Recursive managed dependency"),
                                 ("layout", "Unsupported field"),
                                 ("cycle", "Malformed or cyclic control flow"),
                                 ("framework", "Unsupported assembly identity"),
                                 ("configuration", "Unsupported assembly identity")):
            mutated = destination / f"{mode}.dll"
            run(["dotnet", "run", "--project", str(fixture), "-c", "Release", "--no-build", "--",
                 mode, str(assembly), str(mutated)], ROOT)
            output = run(["dotnet", "run", "--project", str(VERIFY / "Extractor"), "-c", "Release", "--",
                          str(mutated), str(destination / mode)], ROOT, succeeds=False)
            if diagnostic not in output:
                raise RuntimeError(f"{mode} fixture failed for an unexpected reason")
            print(f"PASS: {mode} extraction fixture rejected explicitly")
    run([lake, "build", "Audit"], VERIFY)


if __name__ == "__main__":
    main()
