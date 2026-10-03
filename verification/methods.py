"""Exact selected API descriptors and checked proof gates for the shared runner."""

import copy
import json
from pathlib import Path

MANIFESTS = Path(__file__).resolve().parent / "manifests"
LEGACY = ("Add", "Subtract")


def api_entries():
    manifest = json.loads((MANIFESTS / "api-coverage.json").read_text(encoding="utf-8"))
    if manifest.get("schemaVersion") != 1:
        raise RuntimeError("Unsupported API coverage manifest schema")
    entries = [entry for entry in manifest["entries"] if entry["selection"] == "selected"]
    names = [entry["id"] for entry in entries]
    signatures = [entry["signature"] for entry in entries]
    if len(set(names)) != len(names) or len(set(signatures)) != len(signatures):
        raise RuntimeError("Ambiguous selected API identity")
    if any(not name.isascii() or not name.isalnum() or name in LEGACY for name in names):
        raise RuntimeError("Invalid selected API selector")
    return {entry["id"]: entry for entry in entries}


def method_names():
    return LEGACY + tuple(api_entries())


def method_manifest(name):
    if name in LEGACY:
        return json.loads((MANIFESTS / f"{name.lower()}.json").read_text(encoding="utf-8"))
    entry = api_entries().get(name)
    if entry is None:
        raise ValueError(f"Unknown verification method: {name}")
    gate = entry.get("verification")
    if gate is None:
        raise RuntimeError(f"Selected API proof is not implemented yet: {name}")
    required = ("auditTarget", "auditedTheorems", "contract", "profileCoverage")
    if (any(not gate.get(key) for key in required)
            or gate["profileCoverage"] not in {"program-agreement", "all-valid-profiles"}):
        raise RuntimeError(f"Incomplete verification gate: {name}")
    if (type(gate.get("allProfiles", False)) is not bool
            or not isinstance(gate["auditedTheorems"], list)
            or any(not isinstance(item, str) or not item for item in gate["auditedTheorems"])
            or len(set(gate["auditedTheorems"])) != len(gate["auditedTheorems"])):
        raise RuntimeError(f"Invalid verification audit requirements: {name}")
    if gate.get("allProfiles", False) != (gate["profileCoverage"] == "all-valid-profiles"):
        raise RuntimeError(f"Unbound all-profile contract gate: {name}")
    if gate.get("allProfiles") and (gate.get("allProfilesTheorem") not in gate["auditedTheorems"][1:]):
        raise RuntimeError(f"Missing audited all-profile contract gate: {name}")
    if "template" in gate:
        names = ["UInt256Proof.Selected.checked_contract", "UInt256Proof.Selected.checked_profile_contract"]
        if gate.get("allProfiles", False):
            names.append("UInt256Proof.Selected.checked_all_profiles_contract")
            if gate["allProfilesTheorem"] != names[-1]:
                raise RuntimeError(f"Typed all-profile audit identity differs: {name}")
        if gate["auditTarget"] != "+UInt256.Methods.SelectedGate:olean" or gate["auditedTheorems"] != names:
            raise RuntimeError(f"Typed template audit identities differ: {name}")
    manifest = copy.deepcopy(json.loads((MANIFESTS / "add.json").read_text(encoding="utf-8")))
    manifest.update(entry=entry["signature"], callingConvention=entry["callingConvention"],
                    verification=gate, excluded=["zkEVM build", "JIT and native machine code"])
    manifest["callingAssumptions"][0] = (
        "Live readable UInt256 reference inputs; live writable output references where declared; "
        "by-value operands are initial snapshots with their declared widths")
    return manifest


def check_calling_convention(actual, expected):
    if actual.get("isStatic") != expected["static"] or actual.get("returnType") != expected["returns"]:
        raise RuntimeError("Extracted entry static/return convention differs from its selected contract")
    parameters = actual.get("parameters", [])
    if len(parameters) != len(expected["parameters"]):
        raise RuntimeError("Extracted entry parameter count changed")
    for parameter, selected in zip(parameters, expected["parameters"]):
        if (parameter.get("type"), parameter.get("IsIn"), parameter.get("IsOut")) != (
                selected["type"], selected["isIn"], selected["isOut"]):
            raise RuntimeError("Extracted entry parameter type/direction changed")
    if actual.get("hasThis") != (not expected["static"]):
        raise RuntimeError("Extracted implicit receiver convention changed")
