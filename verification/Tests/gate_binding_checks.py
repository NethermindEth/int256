"""Kernel-reject weakened handwritten gates even when their axiom audit is clean."""

import copy
from pathlib import Path
import re
import shutil
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from common import ROOT, VERIFY, generated_directory, run, source_files
from gate_templates import audit_module
from methods import api_entries
from support import isolated_run, reject_resource_failure
from verify import main as verify_one, source_inputs, check_proof_snapshot


def check_safety_bindings(proof, lake):
    relative = Path("UInt256/Methods/Shift/SafetyAudit.lean")
    target = proof / relative
    original_bytes = target.read_bytes()
    original = original_bytes.decode("utf-8").replace("\r\n", "\n")
    command = [lake, "build", "+UInt256.Methods.Shift.SafetyAudit:olean"]
    run(command, proof)
    weakened = ("namespace GateBinding\ntheorem weakened : True := True.intro\n"
                "#print axioms weakened\nend GateBinding\n")
    try:
        for role, name in (("selected", "checked_shift_contract"),
                           ("family", "checked_shift_family_contract")):
            source = f"UInt256Proof.Shift.Safety.{name}"
            if original.count(source) != 1:
                raise RuntimeError(f"Expected one safety {role} contract application")
            module = original.replace("\ntheorem ", "\n" + weakened + "\ntheorem ", 1)
            module = module.replace(source, "GateBinding.weakened")
            target.write_text(module, encoding="utf-8", newline="\n")
            output = run(command, proof, succeeds=False)
            reject_resource_failure(output)
            lines = module.splitlines()
            binding = "checked_shift_binding" if role == "selected" else "checked_shift_family_binding"
            start = next(i for i, line in enumerate(lines, 1)
                         if line.startswith(f"theorem UInt256Proof.Shift.Safety.{binding}"))
            end = next(i for i, line in enumerate(lines, 1)
                       if line == f"#print axioms UInt256Proof.Shift.Safety.{binding}")
            errors = re.findall(r"error: ([^\n]+\.lean):(\d+):\d+:", output.replace("\\", "/"))
            if ("'GateBinding.weakened' does not depend on any axioms" not in output
                    or not errors or any(path != relative.as_posix() or not start <= int(line) < end
                                         for path, line in errors)):
                raise RuntimeError(f"Weak safety {role} gate did not fail its exact contract binding")
            print(f"PASS: clean-axiom safety {role} theorem cannot replace the combined contract")
    finally:
        target.write_bytes(original_bytes)
    run(command, proof)


def check_workspace():
    verify_one(["--method", "Lsh", "--safety"])
    inputs = source_inputs()
    lake = shutil.which("lake")
    with tempfile.TemporaryDirectory(prefix="int256-gate-binding-proof-") as temporary:
        proof = Path(temporary)
        sources = list(source_files(VERIFY, {".lean"}))
        for source in sources:
            target = proof / source.relative_to(VERIFY)
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(source, target)
        for name in ("lakefile.toml", "lean-toolchain"):
            shutil.copy2(VERIFY / name, proof / name)
        copied = [p.relative_to(VERIFY) for p in sources] + [Path("lakefile.toml"), Path("lean-toolchain")]
        check_proof_snapshot(proof, copied, inputs)
        (proof / "generated").mkdir()
        shutil.copy2(generated_directory("Lsh") / "safety/Extracted.lean", proof / "generated/Extracted.lean")
        entry = api_entries()["Lsh"]
        target = proof / "UInt256/Methods/SelectedGate.lean"
        target.write_text(audit_module(entry), encoding="utf-8", newline="\n")
        run([lake, "build", "+UInt256.Methods.SelectedGate:olean"], proof)
        for role in ("selected", "family"):
            changed = copy.deepcopy(entry)
            gate = changed["verification"]
            index = 0 if role == "selected" else gate["auditedTheorems"].index(gate["familyCoverage"]["theorem"])
            gate["auditedTheorems"][index] = "GateBinding.weakened"
            if role == "family":
                gate["familyCoverage"]["theorem"] = "GateBinding.weakened"
            module = audit_module(changed)
            module = module.replace("namespace UInt256Proof.Selected", 
                "namespace GateBinding\ntheorem weakened : True := True.intro\n"
                "#print axioms weakened\nend GateBinding\nnamespace UInt256Proof.Selected")
            target.write_text(module, encoding="utf-8", newline="\n")
            output = run([lake, "build", "+UInt256.Methods.SelectedGate:olean"], proof, succeeds=False)
            reject_resource_failure(output)
            normalized = output.replace("\\", "/")
            binding = "bound_contract" if role == "selected" else "bound_family_contract"
            lines = module.splitlines()
            start = next(i for i, line in enumerate(lines, 1) if line.startswith(f"theorem {binding} :"))
            end = next(i for i, line in enumerate(lines, 1) if line == f"#print axioms {binding}")
            errors = re.findall(r"error: ([^\n]+\.lean):(\d+):\d+:", normalized)
            if ("'GateBinding.weakened' does not depend on any axioms" not in output
                    or not errors or any(path != "UInt256/Methods/SelectedGate.lean"
                                         or not start <= int(line) < end for path, line in errors)):
                raise RuntimeError(f"Weak {role} gate did not fail its exact contract binding")
            print(f"PASS: clean-axiom {role} theorem cannot replace the public contract")
        check_safety_bindings(proof, lake)
        check_proof_snapshot(proof, copied, inputs)
        if inputs != source_inputs():
            raise RuntimeError("Inputs changed during binding checks")


if __name__ == "__main__":
    sys.stdout.reconfigure(encoding="utf-8")
    if sys.argv[1:] == ["--workspace"]:
        check_workspace()
    elif not sys.argv[1:]:
        isolated_run(__file__, [], "int256-gate-binding-")
    else:
        raise SystemExit("Usage: python verification/Tests/gate_binding_checks.py")
