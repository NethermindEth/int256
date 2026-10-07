"""Compiled probes and all-fuel public safety refutations for hazardous fixtures.

Production combined safety/functional certification remains separate.
"""

import argparse
from contextlib import nullcontext
import json
from pathlib import Path
import shutil
import sys
import tempfile

sys.path[:0] = [str(Path(__file__).resolve().parents[3])]
from common import ROOT, VERIFY, run, sha, source_files
from common import source_inputs
from common import build_artifact
from common import theorem_audits

CASES = {
    "AlignedLoad": None,
    "Interior": "values == [.scalar (.i64 1)]",
    "UnalignedVector": "values == [.scalar (.i64 1)]",
    "ReusedLocal": None,
    "EndThenInterior": "values == [.scalar (.i64 1)]",
    "Overread": ".memory .outsideAllocation (.address ⟨0, 32⟩) 8",
    "InvalidThenRepaired": ".memory .invalidReference (.address ⟨0, 0⟩) 0",
    "AggregateHome": "values == [.scalar (.i64 17)]",
    "AggregateOverread": ".memory .outsideAllocation (.address ⟨2, 32⟩) 8",
    "StaticLookup": "values == [.scalar (.i64 42)]",
    "StaticOverread": ".memory .outsideAllocation (.address ⟨1, 0⟩) 32",
    "InitializedVector": "values == [.scalar (.i64 7)]",
    "UninitializedVector": ".memory .uninitialized (.address ⟨1, 0⟩) 32",
    "MaskedVectorOverread": ".memory .outsideAllocation (.address ⟨0, 8⟩) 32",
    "VectorOutsideView": ".memory .unreadable (.address ⟨0, 8⟩) 32",
    "WriteThenRestore": ".memory .unwritable (.address ⟨0, 0⟩) 8",
    "InvalidNativeOffset": ".memory .invalidReference (.address ⟨0, 0⟩) 0",
    "EscapedLocal": None,
}
POSITIVE = {"UnalignedVector", "Interior", "EndThenInterior", "AggregateHome", "StaticLookup", "InitializedVector"}
UNSUPPORTED = {case: "Unsupported method metadata: System.UInt64& Nethermind.Int256.UInt256::Expired()"
               for case in ("EscapedLocal", "ReusedLocal")}
UNSUPPORTED["AlignedLoad"] = ("Unsupported external dependency: System.Void* "
                            "System.Runtime.CompilerServices.Unsafe::AsPointer<Nethermind.Int256.UInt256>(!!0&)")
PROBE = "System.UInt64 Nethermind.Int256.UInt256::Probe(Nethermind.Int256.UInt256&)"


def public_refutation(case, entry, fault_site):
    if case in POSITIVE:
        return ""
    rule = CASES[case].replace("⟨2, 32⟩", "⟨3, 32⟩")
    if case in {"StaticOverread", "UninitializedVector"}:
        rule = rule.replace("⟨1, 0⟩", "⟨2, 0⟩")
    fault = f"⟨{fault_site[0]}, {fault_site[1]}, {rule}⟩"
    return f'''
def publicMemory : Memory := {{ memory with
  allocations := fun id => if id = 0 ∨ id = 1 then memory.allocations 0 else none
  cells := fun id offset => if id = 0 then memory.cells 0 offset else ⟨0, false⟩
  views := [⟨0, 0, 32, true, false⟩, ⟨1, 0, 32, true, true⟩]
  nextIdentity := 2 }}
theorem public_memory_wellFormed : publicMemory.WellFormed := by
  constructor
  · intro id a ha
    simp only [publicMemory, memory] at ha
    split at ha
    · simp only [ite_true, Option.some.injEq] at ha
      subst a
      constructor
      · rcases (by assumption : id = 0 ∨ id = 1) with h | h <;> subst id <;> decide
      · simp [Allocation.WellFormed, nativeLimit]
    · cases ha
  · intro view hv
    simp [publicMemory] at hv
    rcases hv with h | h <;> subst view
    · exact ⟨_, rfl, by decide⟩
    · exact ⟨_, rfl, by decide⟩
theorem public_valid_call :
    ValidCall publicMemory [⟨⟨0, 0⟩, 32⟩, ⟨⟨0, 0⟩, 32⟩] [⟨⟨1, 0⟩, 32⟩] := by
  refine ⟨public_memory_wellFormed, ?_, ?_⟩
  · intro input hi
    simp at hi
    subst input
    exact ⟨_, rfl⟩
  · intro output ho
    simp only [List.mem_singleton] at ho
    subst output
    rfl
def publicArguments : List Value := [
  .reference (.address ⟨0, 0⟩), .reference (.address ⟨0, 0⟩), .reference (.address ⟨1, 0⟩)]
theorem public_static_world :
    StaticWorldValid (programStaticDescriptors Extracted.program) publicMemory := by
  apply empty_static_world_valid
  · simp [programStaticDescriptors, Extracted.program, cil_code, nativeLimit]
  · simp [programStaticDescriptors, Extracted.program, cil_code]
  · rfl

theorem public_fault_witness :
    invoke Extracted.program 64 {entry} publicArguments publicMemory = .error {fault} := by rfl
theorem public_counterexample :
    (ValidCall publicMemory [⟨⟨0, 0⟩, 32⟩, ⟨⟨0, 0⟩, 32⟩] [⟨⟨1, 0⟩, 32⟩] ∧
      StaticWorldValid (programStaticDescriptors Extracted.program) publicMemory) ∧
    ∀ fuel result, invoke Extracted.program fuel {entry} publicArguments publicMemory ≠ .ok result := by
  refine ⟨⟨public_valid_call, public_static_world⟩, ?_⟩
  exact invoke_fault_refutes_success Extracted.program 64 {entry} publicArguments publicMemory
    {fault} (by decide) public_fault_witness
#print axioms public_counterexample
'''


def proof_source(index, case, entry, fault_site):
    if case in UNSUPPORTED:
        raise ValueError("Unsupported extraction cannot supply a semantic proof")
    input_base = 8 if case == "UnalignedVector" else 0
    match = ("| .ok (_, values) => " + CASES[case] + "\n  | .error _ => false"
             if case in POSITIVE else
             "| .error fault => fault.fault == " + CASES[case] + "\n  | .ok _ => false")
    return f'''import Extracted
import CIL.Safety.Execution
import CIL.Safety.Calling
import CIL.Safety.FuelLemmas
import CIL.Safety.ExecutionStaticWorld
namespace CompiledSafety
open CIL.Safety
def memory : Memory := {{
  allocations := fun id => if id = 0 then
    some {{ kind := .callerStack, layout := {{ size := {40 if case in {'VectorOutsideView', 'UnalignedVector'} else 32}, alignment := 8 }}, sentinels := [32] }}
    else none
  cells := fun _ offset => {{ bits := if offset = 8 then 1 else 0, initialized := true }}
  views := [⟨0, {input_base}, 32, true, false⟩]
  nextIdentity := 1 }}
theorem memory_wellFormed : memory.WellFormed := by
  constructor
  · intro id a ha
    simp only [memory] at ha
    split at ha
    · simp only [Option.some.injEq] at ha
      subst a
      subst id
      constructor
      · decide
      · simp [Allocation.WellFormed, nativeLimit]
    · cases ha
  · intro view hv
    simp only [memory, List.mem_singleton] at hv
    subst view
    exact ⟨_, rfl, by decide⟩
theorem valid_start : ValidCall memory [⟨⟨0, {input_base}⟩, 32⟩] [] := by
  refine ⟨memory_wellFormed, ?_, ?_⟩
  · intro input hi
    simp only [List.mem_singleton] at hi
    subst input
    exact ⟨_, rfl⟩
  · simp
theorem static_world :
    StaticWorldValid (programStaticDescriptors Extracted.program) memory := by
  apply empty_static_world_valid
  · simp [programStaticDescriptors, Extracted.program, cil_code, nativeLimit]
  · simp [programStaticDescriptors, Extracted.program, cil_code]
  · rfl

theorem actual_probe :
    (ValidCall memory [⟨⟨0, {input_base}⟩, 32⟩] [] ∧
      StaticWorldValid (programStaticDescriptors Extracted.program) memory) ∧
    (match invoke Extracted.program 64 {index} [.reference (.address ⟨0, {input_base}⟩)] memory with
  {match}) = true := by
  exact ⟨⟨valid_start, static_world⟩, rfl⟩
#print axioms actual_probe
{public_refutation(case, entry, fault_site)}
end CompiledSafety
'''


def main():
    sys.stdout.reconfigure(encoding="utf-8")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--case", action="append", choices=CASES)
    parser.add_argument("--work", type=Path, help="Retain a new isolated build/proof directory for diagnosis")
    args = parser.parse_args()
    if args.output:
        args.output.unlink(missing_ok=True)
    cases = list(dict.fromkeys(args.case or CASES))
    lake = shutil.which("lake")
    if not lake:
        raise RuntimeError("Pinned Lean / lake must be on PATH")
    project = Path(__file__).parent / "Nethermind.Int256.csproj"
    receipts = []
    inputs = source_inputs()
    if args.work:
        args.work.mkdir(parents=True, exist_ok=False)
    context = nullcontext(str(args.work.resolve())) if args.work else tempfile.TemporaryDirectory(prefix="int256-compiled-safety-")
    with context as temporary:
        work = Path(temporary)
        bundle = build_artifact(project, work / "shared", "Add", fixture=project,
                                simd_fixture=True, fixture_name=cases[0])
        for case in cases:
            if inputs != source_inputs():
                raise RuntimeError("Compiled safety probe inputs changed")
            artifacts = work / case / "artifacts"
            if case == cases[0]:
                assembly = bundle["assembly"]
            else:
                run(["dotnet", "build", str(project), "-c", "Release", "--no-incremental",
                     f"-p:FixtureCase={case}", f"-p:ArtifactsPath={artifacts}",
                     "-p:EnforceCodeStyleInBuild=true", "-p:GenerateDocumentationFile=true"], ROOT)
                assembly = artifacts / "bin/Nethermind.Int256/release/Nethermind.Int256.dll"
            proof = work / case / "proof"
            proof.mkdir(parents=True)
            for source in source_files(VERIFY / "CIL", {".lean"}):
                destination = proof / source.relative_to(VERIFY)
                destination.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(source, destination)
            shutil.copy2(VERIFY / "lean-toolchain", proof)
            (proof / "lakefile.toml").write_text(
                'name = "compiled_safety_probe"\nversion = "0.1.0"\n'
                '[[lean_lib]]\nname = "CIL"\n[[lean_lib]]\nname = "Extracted"\nsrcDir = "generated"\n'
                '[[lean_lib]]\nname = "ProbeAudit"\n', encoding="utf-8")
            generated = proof / "generated"
            extraction = run(["dotnet", str(bundle["extractor"]), str(assembly), str(generated), "Add", "scalar"],
                             ROOT, succeeds=case not in UNSUPPORTED)
            if case in UNSUPPORTED:
                if UNSUPPORTED[case] not in extraction or (generated / "artifact.json").exists():
                    raise RuntimeError("Unsupported safety fixture failed for an unrelated reason or issued an artifact")
                receipts.append({"case": case, "assemblySha256": sha(assembly),
                                 "extractorSha256": bundle["extractorSha256"],
                                 "unsupportedFeature": ("raw-pointer conversion for aligned SIMD load"
                                                        if case == "AlignedLoad" else "byref-returning helper"),
                                 "diagnostic": UNSUPPORTED[case], "publicRefutation": False})
                print(f"PASS: explicitly unsupported {case}", flush=True)
                continue
            artifact = json.loads((generated / "artifact.json").read_text(encoding="utf-8"))
            matches = [(index, body) for index, body in enumerate(artifact["methods"]) if body["signature"] == PROBE]
            if len(matches) != 1:
                raise RuntimeError("Compiled fixture lacks the intended reachable probe")
            index, body = matches[0]
            instructions = body["instructions"]
            examined = instructions
            fault_method = index
            if case.startswith("Aggregate"):
                snapshot = [method for method in artifact["methods"] if method["signature"] ==
                            "System.UInt64 Nethermind.Int256.UInt256::ReadSnapshot(Nethermind.Int256.UInt256)"]
                if len(snapshot) != 1 or not any(i["opcode"] == "newobj" for i in instructions):
                    raise RuntimeError("Compiler removed the constructor/snapshot helper")
                examined = snapshot[0]["instructions"]
                fault_method = artifact["methods"].index(snapshot[0])
                if not any(i["opcode"] in {"ldarga", "ldarga.s"} for i in examined):
                    raise RuntimeError("Compiler removed aggregate argument address access")
                if case == "AggregateHome" and not any(i["opcode"] == "stind.i8" for i in examined):
                    raise RuntimeError("Compiler removed private snapshot mutation")
            adds = [i for i in examined if i["opcode"] == "call" and "Unsafe::Add<System.UInt64>" in i["operand"]]
            vector_initialization = case in {"InitializedVector", "UninitializedVector"}
            expected_adds = 0 if case in {"AggregateHome", "WriteThenRestore", "InvalidNativeOffset", "UnalignedVector"} or case.startswith("Static") or vector_initialization else (2 if case in {"InvalidThenRepaired", "EndThenInterior"} else 1)
            if len(adds) != expected_adds:
                raise RuntimeError("Compiler changed the intended reference arithmetic")
            if case.startswith("Static"):
                data = artifact["staticData"]
                width = 32 if case == "StaticLookup" else 16
                if len(data) != 1 or data[0]["size"] != width or data[0]["packing"] != 1 or len(data[0]["bytes"]) != 2 * width:
                    raise RuntimeError("Compiled static fixture lacks the intended extracted RVA layout")
                if not any(i["opcode"] == "ldobj" and "Vector256" in i.get("operand", "") for i in examined):
                    raise RuntimeError("Compiler removed the vector read from static bytes")
            elif case == "UnalignedVector":
                if not any(i["opcode"] == "ldobj" and "Vector256" in i.get("operand", "") for i in examined):
                    raise RuntimeError("Compiler removed the unaligned vector read")
            elif case == "InvalidNativeOffset":
                if not any(i["opcode"] == "call" and "Unsafe::Add<System.Runtime.Intrinsics.Vector256" in i.get("operand", "")
                           and "System.UIntPtr" in i.get("operand", "") for i in examined):
                    raise RuntimeError("Compiler removed native-width vector reference arithmetic")
            elif case == "WriteThenRestore":
                stores = [pc for pc, i in enumerate(examined) if i["opcode"] == "stind.i8"]
                if len(stores) != 2 or not any(i["opcode"] == "xor" for i in examined[:stores[0]]):
                    raise RuntimeError("Compiler removed the modifying write and restoring write")
            elif case in {"MaskedVectorOverread", "VectorOutsideView"}:
                load = next((pc for pc, i in enumerate(examined) if i["opcode"] == "ldobj"
                             and "Vector256" in i.get("operand", "")), None)
                mask = next((pc for pc, i in enumerate(examined) if i["opcode"] == "call"
                             and "op_BitwiseAnd" in i.get("operand", "")), None)
                if load is None or mask is None or load >= mask:
                    raise RuntimeError("Compiler removed the vector load followed by lane masking")
            elif vector_initialization:
                if body["InitLocals"] or not any(i["opcode"] == "call" and "Unsafe::SkipInit" in i.get("operand", "") for i in examined):
                    raise RuntimeError("Compiled initialization fixture lacks genuinely uninitialized storage")
                stores = sum(i["opcode"] == "stind.i8" for i in examined)
                if stores != (4 if case == "InitializedVector" else 1):
                    raise RuntimeError("Compiler changed the intended initialization writes")
                if not any(i["opcode"] == "ldobj" and "Vector256" in i.get("operand", "") for i in examined):
                    raise RuntimeError("Compiler removed the full vector read")
            elif case != "AggregateHome" and not any(i["opcode"] == "ldind.i8" for i in examined):
                raise RuntimeError("Compiler removed the actual memory load")
            entry = artifact["methods"][artifact["entryIndex"]]["instructions"]
            call = next((i for i, instruction in enumerate(entry) if instruction.get("operand") == PROBE), None)
            if call is None or entry[call + 1]["opcode"] != "pop":
                raise RuntimeError("Entry does not call and discard the compiled probe result")
            public = case not in POSITIVE
            fault_pc = next((pc for pc, instruction in enumerate(examined) if
                             (case == "InvalidNativeOffset" and instruction["opcode"] == "call" and
                              "Unsafe::Add<System.Runtime.Intrinsics.Vector256" in instruction.get("operand", "")) or
                             (case == "InvalidThenRepaired" and instruction["opcode"] == "call" and
                              "Unsafe::Add<System.UInt64>" in instruction.get("operand", "")) or
                             (case in {"StaticOverread", "UninitializedVector", "MaskedVectorOverread", "VectorOutsideView"} and instruction["opcode"] == "ldobj") or
                             (case == "WriteThenRestore" and instruction["opcode"] == "stind.i8") or
                             (case not in {"InvalidThenRepaired", "StaticOverread", "WriteThenRestore"} and instruction["opcode"] == "ldind.i8")), None)
            if public and fault_pc is None:
                raise RuntimeError("Compiled negative fixture lacks the intended fault site")
            (proof / "ProbeAudit.lean").write_text(
                proof_source(index, case, artifact["entryIndex"], (fault_method, fault_pc)), encoding="utf-8")
            adjacent = case == "Overread"
            if adjacent:
                shutil.copy2(Path(__file__).with_name("AdjacentAudit.lean"), proof / "AdjacentAudit.lean")
                with (proof / "lakefile.toml").open("a", encoding="utf-8") as config:
                    config.write('\n[[lean_lib]]\nname = "AdjacentAudit"\n')
            output = run([lake, "build", "+AdjacentAudit:olean" if adjacent else "+ProbeAudit:olean"], proof)
            names = ["CompiledSafety.actual_probe"]
            if public:
                names.append("CompiledSafety.public_counterexample")
            if adjacent:
                names.extend("CompiledSafety." + name for name in (
                    "adjacent_public_placement", "adjacent_boundary_same_address",
                    "adjacent_access_distinguished", "adjacent_compiled_counterexample",
                    "result_only_same_bytes", "result_only_observation"))
            audits = theorem_audits(output, names,
                                    ["propext", "Classical.choice", "Quot.sound"])
            receipts.append({"case": case, "assemblySha256": sha(assembly), "extractorSha256": bundle["extractorSha256"],
                             "generatedProgramSha256": sha(generated / "Extracted.lean"),
                             "bindingSha256": sha(proof / "ProbeAudit.lean"), "probe": body,
                             "publicRefutation": public, "audits": audits,
                             **({"adjacentPlacementChecked": True, "arithmeticCorrectUnsafeChecked": True,
                                 "adjacentBindingSha256": sha(proof / "AdjacentAudit.lean")} if adjacent else {})})
            print(f"PASS: compiled {case} probe", flush=True)
    if inputs != source_inputs():
        raise RuntimeError("Compiled safety probe inputs changed during checking")
    report = {"kind": "compiled-safety-probes", "productionCombined": False,
              "fullPublicRefutation": any(r["publicRefutation"] for r in receipts),
              "cases": cases, "startingStateChecked": all(case not in UNSUPPORTED for case in cases),
              "sourceInputs": inputs, "receipts": receipts}
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, indent=2), encoding="utf-8")


if __name__ == "__main__":
    main()
