"""Equality alternatives and independently refuted mutations through the public verifier."""

import argparse
import json
from pathlib import Path
import shutil
import sys
import xml.etree.ElementTree as ET

sys.path.insert(0, str(Path(__file__).resolve().parents[3]))
sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
from common import PROFILE_NAMES, ROOT, VERIFY, expected_profile, run, method_manifest, method_names
from support import (isolated_run, initial_bytes_expression, mutation_proof, native_witness,
                     require_diagnostic_rejection, selected_fixture_baseline, template_refutation)

DIRECTORY = Path(__file__).parent
METHODS = tuple(name for name in method_names() if name.startswith(("Eq", "Ne", "Equals")))
REFERENCE = ("EqUInt256UInt256", "NeUInt256UInt256", "EqualsUInt256Ref", "EqualsUInt256Value")
SCALARS = {"System.Int32": ("s32", 32, "int"), "System.UInt32": ("u32", 32, "uint"),
           "System.Int64": ("s64", 64, "long"), "System.UInt64": ("u64", 64, "ulong")}
CASES = ET.parse(DIRECTORY / "Cases.props").findall("ItemGroup/EqualityCase")
NEGATIVES = json.loads((DIRECTORY / "Witnesses.json").read_text(encoding="utf-8"))["negativeCases"]


def shape(method):
    calling = method_manifest(method)["callingConvention"]
    if method in REFERENCE:
        return {"kind": "snapshot" if method == "EqualsUInt256Value" else "reference",
                "negate": method.startswith("Ne"), "instance": not calling["static"]}
    parameters = calling["parameters"]
    scalar = next((parameter["type"] for parameter in parameters if parameter["type"] in SCALARS), None)
    if scalar is None:
        raise RuntimeError("Unsupported equality fixture calling convention")
    kind, width, csharp = SCALARS[scalar]
    return {"kind": "scalar", "scalarKind": kind, "width": width, "csharp": csharp,
            "negate": method.startswith("Ne"), "instance": not calling["static"],
            "scalarFirst": calling["static"] and parameters[0]["type"] == scalar}


def applicable(case, method, profile):
    descriptor = shape(method)
    if case == "Baseline": return True
    if case == "Renamed": return True
    if case == "EquivalentScalar":
        features = expected_profile(profile)
        return not features["Vector256Accelerated"] and (method not in REFERENCE or not features["Sse41"])
    if case == "EquivalentReduction":
        features = expected_profile(profile)
        return features["Vector256Accelerated"] or (method in REFERENCE and features["Sse41"])
    group = NEGATIVES[case]["group"]
    return ((group == "reference" and method in REFERENCE)
            or (group == "snapshot" and descriptor["kind"] == "snapshot")
            or (group == "signed" and descriptor.get("scalarKind", "").startswith("s"))
            or (group == "inequality" and descriptor["negate"]))


def witness(case, method):
    descriptor = shape(method)
    data = dict(NEGATIVES[case])
    if "widths" in data:
        data.update(data["widths"][str(descriptor["width"])])
        scalar_type = "System.Int32" if descriptor["width"] == 32 else "System.Int64"
        data["changedSignature"] = f"System.Boolean Nethermind.Int256.UInt256::Equals({scalar_type})"
    left, right = data["leftBase"], data["rightBase"]
    number = lambda base: sum(int(data["initialBytes"].get(str(base+i), 0)) << (8*i) for i in range(32))
    left_value = number(left)
    if descriptor["kind"] == "scalar":
        bits = data["scalarBits"]
        scalar = bits - 2**descriptor["width"] if descriptor["scalarKind"].startswith("s") and bits >= 2**(descriptor["width"]-1) else bits
        equal = left_value == scalar
    else:
        data["snapshot"] = data.get("snapshot", number(right))
        equal = left_value == (data["snapshot"] if descriptor["kind"] == "snapshot" else number(right))
    data["expectedResult"] = equal != descriptor["negate"]
    data["actualResult"] = data.get("actualResult", data.get("actualEquality") != descriptor["negate"])
    if data["actualResult"] == data["expectedResult"]:
        raise RuntimeError("Equality witness does not contradict the complete contract")
    return data


def refute(proof, lake, method, data, approved):
    descriptor = shape(method)
    left, right = data["leftBase"], data["rightBase"]
    common = "Extracted.program Extracted.entryIndex initial"
    if descriptor["kind"] == "scalar":
        width, kind = descriptor["width"], descriptor["scalarKind"]
        word = f"(BitVec.ofNat {width} {data['scalarBits']})"
        scalar = f"(Scalar.{kind} {word})"
        argument = f".i{width} {word}"
        first, negate = str(descriptor["scalarFirst"]).lower(), str(descriptor["negate"]).lower()
        arguments = f"[{argument}, .object {left}]" if descriptor["scalarFirst"] else f"[.object {left}, {argument}]"
        contract = f"ScalarContract {common} {left} {scalar} {first} {negate}"
        expectation = f"((decide (((byteValue initial {left}).toNat : Int) = Scalar.number {scalar})) != {negate})"
    elif descriptor["kind"] == "snapshot":
        bits = f"(BitVec.ofNat 256 {data['snapshot']})"
        arguments = f"[.object {left}, .v256 {bits}]"
        contract = f"SnapshotContract {common} {left} {bits}"
        expectation = f"decide (byteValue initial {left} = {bits})"
    else:
        arguments = f"[.object {left}, .object {right}]"
        contract = f"{'InequalityContract' if descriptor['negate'] else 'Contract'} {common} {left} {right}"
        expectation = f"decide (byteValue initial {left} {'≠' if descriptor['negate'] else '='} byteValue initial {right})"
    substitutions = {"INITIAL": initial_bytes_expression(data), "ARGUMENTS": arguments,
                     "CONTRACT": contract, "EXPECTATION": expectation,
                     "ACTUAL": int(data["actualResult"]), "EXPECTED": str(data["expectedResult"]).lower()}
    template_refutation(proof, lake, DIRECTORY / "RefutationTemplate.lean.in", substitutions,
                        "Refutation", "UInt256Proof.Equality.Witness.refuted", approved, register=True)


def native_check(work, assembly, method, data):
    descriptor = shape(method)
    assignments = "\n".join(f"bytes[{int(address)}] = {int(value)};" for address,value in data["initialBytes"].items())
    if descriptor["kind"] == "scalar":
        scalar = f"unchecked(({descriptor['csharp']}){data['scalarBits']}UL)"
        if descriptor["instance"]: expression = f"left.Equals({scalar})"
        else:
            operands = (scalar, "left") if descriptor["scalarFirst"] else ("left", scalar)
            expression = f"{operands[0]} {'!=' if descriptor['negate'] else '=='} {operands[1]}"
    elif descriptor["kind"] == "snapshot":
        value = data["snapshot"]
        snapshot = ", ".join(f"{(value >> (64*i)) & (2**64-1)}UL" for i in range(4))
        expression = f"left.Equals(new UInt256({snapshot}))"
    elif descriptor["instance"]: expression = "left.Equals(in right)"
    else: expression = f"left {'!=' if descriptor['negate'] else '=='} right"
    source = f'''using System;
using System.Runtime.CompilerServices;
using Nethermind.Int256;
byte[] bytes = new byte[128];
{assignments}
byte[] original = (byte[])bytes.Clone();
ref UInt256 left = ref Unsafe.As<byte, UInt256>(ref bytes[{data['leftBase']}]);
ref UInt256 right = ref Unsafe.As<byte, UInt256>(ref bytes[{data['rightBase']}]);
bool result = {expression};
Console.WriteLine($"Native equality witness: {{result}}; Vector256={{System.Runtime.Intrinsics.Vector256.IsHardwareAccelerated}}; SSE41={{System.Runtime.Intrinsics.X86.Sse41.IsSupported}}");
for (int i = 0; i < bytes.Length; ++i) if (bytes[i] != original[i]) return 2;
return result == {str(data['actualResult']).lower()} ? 0 : 1;
'''
    native_witness(work, assembly, source)


def check_workspace(method, profile, selected):
    lake = shutil.which("lake")
    if not lake: raise RuntimeError("Pinned Lean / lake must be on PATH")
    manifest = method_manifest(method)
    public, report_path, baseline = selected_fixture_baseline(method, profile)
    project = DIRECTORY / "Nethermind.Int256.csproj"
    for case in CASES:
        name = case.attrib["Include"]
        if name == "Baseline" or selected not in ("all",name) or not applicable(name,method,profile): continue
        if case.attrib["Suite"] == "positive":
            run(public + ["--fixture",name],ROOT)
            report = json.loads(report_path.read_text(encoding="utf-8"))
            if report["leanSourceSha256"] != baseline["leanSourceSha256"] or report["generatedProgramSha256"] == baseline["generatedProgramSha256"]:
                raise RuntimeError("Equivalent equality fixture did not change CIL with identical proofs")
            print(f"PASS: {method}/{profile}/{name}, same complete public proof")
            continue
        data = witness(name,method)
        work = ROOT / "artifacts/equality-fixtures" / method / name
        work.mkdir(parents=True)
        bundle, proof = mutation_proof(work,project,name,method,profile,baseline,data.get("changedSignature"))
        refute(proof,lake,method,data,manifest["approvedAxioms"])
        native_check(work,bundle["assembly"],method,data)
        output = run(public + ["--fixture",name],ROOT,succeeds=False)
        module = ("SelectedGate" if shape(method)["kind"] == "scalar" else
                  "Equality/Snapshot" if method == "EqualsUInt256Value" else
                  "Equality/Unequal" if method.startswith("Ne") else "Equality/Equal")
        require_diagnostic_rejection(output,f"UInt256/Methods/{module}.lean",
            r"unsolved goals|`simp` made no progress|Tactic `[^`]+` failed:.*|omega could not prove the goal:")
        if report_path.exists(): raise RuntimeError("Rejected equality fixture retained a success report")
        print(f"PASS: {method}/{profile}/{name}, full-contract refutation and public rejection")


def main():
    sys.stdout.reconfigure(encoding="utf-8")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--method",choices=METHODS,default="EqUInt256UInt256")
    parser.add_argument("--profile",choices=PROFILE_NAMES,default="scalar")
    parser.add_argument("--case",choices=tuple(c.attrib["Include"] for c in CASES)+("all",),default="all")
    parser.add_argument("--workspace",action="store_true",help=argparse.SUPPRESS)
    args=parser.parse_args()
    if args.case != "all" and not applicable(args.case,args.method,args.profile):
        parser.error("Fixture case does not apply to this exact method/profile")
    if args.workspace: check_workspace(args.method,args.profile,args.case)
    else: isolated_run(__file__,["--method",args.method,"--profile",args.profile,"--case",args.case],"int256-equality-fixture-")


if __name__ == "__main__": main()
