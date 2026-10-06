"""Exact selected API descriptors and checked proof gates for the shared runner."""

import copy
import json
from pathlib import Path

MANIFESTS = Path(__file__).resolve().parent / "manifests"
LEGACY = ("Add", "Subtract")


def resolve_fixture_groups(entries, groups):
    """Expand explicitly registered shared fixture data for the public runner."""
    if not isinstance(groups, dict):
        raise RuntimeError("Invalid shared fixture groups")
    for group, data in groups.items():
        if (not isinstance(group, str) or not group.isascii() or not group.isalnum()
                or not isinstance(data, dict) or set(data) != {"cases", "source"}
                or not isinstance(data["cases"], list) or not data["cases"]
                or any(not isinstance(case, str) or not case.isascii() or not case.isalnum()
                       for case in data["cases"])
                or len(set(data["cases"])) != len(data["cases"])
                or not isinstance(data["source"], str)
                or Path(data["source"]).name != data["source"] or not data["source"].endswith(".cs")):
            raise RuntimeError(f"Invalid shared fixture group: {group}")
    for entry in entries:
        gate = entry.get("verification")
        if not gate:
            continue
        group = gate.get("fixtureGroup")
        if isinstance(group, str) and group in groups:
            if "fixtureCases" in gate or "fixtureSources" in gate:
                raise RuntimeError(f"Shared fixture group has per-API overrides: {entry['id']}")
            data = groups[group]
            gate["fixtureCases"] = list(data["cases"])
            gate["fixtureSources"] = dict.fromkeys(data["cases"], data["source"])


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
    resolve_fixture_groups(entries, manifest.get("fixtureGroups", {}))
    return {entry["id"]: entry for entry in entries}


def method_names():
    return LEGACY + tuple(api_entries())


def native_limitations(methods):
    """Keep observed native failures separate from the proved CIL contracts."""
    if any(method not in LEGACY and method_manifest(method)["verification"].get(
            "familyCoverage", {}).get("kind") == "multiply-dispatch-storage" for method in methods):
        return [{"kind": "runtime-jit-struct-copy", "status": "observed-failure",
                 "runtime": ".NET 10.0.12", "architecture": "Windows x64",
                 "currentMain": {"commit": "d90dbf43be153cc7ba7f49bb271e0b7e56a81891",
                                 "standaloneCopy": "fails", "multiplicationDefaultTiered": "fails",
                                 "multiplicationFullyOptimized": "passes"},
                 "condition": "Hardware intrinsics disabled; partially overlapping input/output",
                 "witness": "verification/Tests/NativeMultiplyWitness/Program.cs",
                 "minimalWitness": "verification/Tests/NativeStructCopyWitness/Program.cs",
                 "scope": "The CIL proof does not establish native partial-overlap correctness",
                 "notes": "verification/UInt256/Methods/Multiply/README.md"}]
    return []


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
    family = gate.get("familyCoverage")
    from common import MULTIPLY_PROFILES, PROFILES
    families = {"vector256-storage": ["scalar", "x64-vector256"],
                "vector-reduction": ["scalar", "x64-sse41", "x64-vector256"],
                "relational-dispatch": ["scalar", "x64-vector256", "x64-avx2", "x64-avx512"],
                "multiply-dispatch-storage": list(MULTIPLY_PROFILES),
                "feature-class": list(PROFILES)}
    if family is not None and (
            not isinstance(family, dict)
            or set(family) != {"kind", "theorem", "representatives"}
            or not isinstance(family["kind"], str)
            or family["kind"] not in families
            or family["representatives"] != families[family["kind"]]
            or family["theorem"] not in gate["auditedTheorems"][1:]
            or gate.get("allProfiles", False)):
        raise RuntimeError(f"Unbound feature-family contract gate: {name}")
    if "template" in gate:
        names = ["UInt256Proof.Selected.checked_contract", "UInt256Proof.Selected.checked_profile_contract"]
        if gate.get("allProfiles", False):
            names.append("UInt256Proof.Selected.checked_all_profiles_contract")
            if gate["allProfilesTheorem"] != names[-1]:
                raise RuntimeError(f"Typed all-profile audit identity differs: {name}")
        elif family:
            names.append("UInt256Proof.Selected.checked_family_contract")
            if family["kind"] != "vector256-storage" or family["theorem"] != names[-1]:
                raise RuntimeError(f"Typed family audit identity differs: {name}")
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
