"""Checks for exact API selection, metadata matching and fail-closed reporting."""

import copy
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch
import xml.etree.ElementTree as ET

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import common
import support


class MethodChecks(unittest.TestCase):
    def test_workspace_bridge_never_caches_file_checks(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / "verification").mkdir()
            for name in ("global.json", ".editorconfig", "verification/lean-toolchain"):
                (root / name).write_text("initial", encoding="utf-8")
            source = root / "verification/Test.lean"
            source.write_text("initial", encoding="utf-8")
            inputs = common.source_inputs(root)
            self.assertEqual(common.check_proof_snapshot(source.parent, [Path("Test.lean")], inputs),
                             {"Test.lean": common.sha(source)})
            source.write_text("changed", encoding="utf-8")
            self.assertNotEqual(common.source_inputs(root), inputs)
            with self.assertRaisesRegex(RuntimeError, "snapshot"):
                common.check_proof_snapshot(source.parent, [Path("Test.lean")], inputs)
            source.unlink()
            self.assertNotIn("verification/Test.lean", common.source_inputs(root))
            with self.assertRaises(RuntimeError):
                common.check_proof_snapshot(source.parent, [Path("Test.lean")], inputs)

    def test_combined_fixture_baseline_uses_safety_reports_and_identical_proofs(self):
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary)
            report_path = directory / "safety/report.json"
            report_path.parent.mkdir()
            inputs = {"source": "current"}
            commands = []

            def run(arguments, _):
                commands.append(arguments)
                case = arguments[-1] if "--fixture" in arguments else None
                report_path.write_text(json.dumps({
                    "source": {"kind": "fixture" if case else "production"},
                    "sourceInputs": inputs, "leanSourceSha256": {"proof": "unchanged"},
                    "generatedProgramSha256": case or "production",
                    "evidenceKind": "arithmetic-and-memory-safety",
                    "safety": common.safety_gate("Lsh", "scalar"),
                }), encoding="utf-8")

            with patch.object(support, "generated_directory", return_value=directory), \
                 patch.object(support, "source_inputs", return_value=inputs), \
                 patch.object(support, "run", side_effect=run):
                public, path, baseline = support.selected_fixture_baseline("Lsh", "scalar", "LshHelper", safety=True)
            self.assertEqual(path, report_path)
            self.assertEqual(baseline["source"]["kind"], "fixture")
            self.assertIn("--safety", public)
            self.assertEqual(len(commands), 3)
            self.assertTrue(all("--safety" in command for command in commands))

    def test_combined_fixture_baseline_rejects_arithmetic_only_or_wrong_safety_gate(self):
        for invalid_case in (None, "Baseline", "LshHelper"):
            for wrong_gate in (False, True):
                with self.subTest(case=invalid_case, wrong_gate=wrong_gate), tempfile.TemporaryDirectory() as temporary:
                    directory = Path(temporary)
                    report_path = directory / "safety/report.json"
                    report_path.parent.mkdir()
                    inputs = {"source": "current"}

                    def run(arguments, _):
                        case = arguments[-1] if "--fixture" in arguments else None
                        report = {
                            "source": {"kind": "fixture" if case else "production"},
                            "sourceInputs": inputs, "leanSourceSha256": {"proof": "unchanged"},
                            "generatedProgramSha256": case or "production",
                            "evidenceKind": "arithmetic-and-memory-safety",
                            "safety": common.safety_gate("Lsh", "scalar"),
                        }
                        if case == invalid_case:
                            if wrong_gate:
                                report["safety"] = common.safety_gate("Rsh", "scalar")
                            else:
                                report.pop("evidenceKind")
                        report_path.write_text(json.dumps(report), encoding="utf-8")

                    with patch.object(support, "generated_directory", return_value=directory), \
                         patch.object(support, "source_inputs", return_value=inputs), \
                         patch.object(support, "run", side_effect=run):
                        with self.assertRaisesRegex(RuntimeError, "lacks the selected combined safety evidence"):
                            support.selected_fixture_baseline("Lsh", "scalar", "LshHelper", safety=True)


    def test_multiply_family_requires_each_arithmetic_and_storage_combination(self):
        for actual in (list(common.MULTIPLY_PROFILES), list(common.MULTIPLY_PROFILES)[::2],
                       list(common.MULTIPLY_PROFILES)[:-1]):
            entry = copy.deepcopy(common.api_entries()["Multiply"])
            entry["verification"]["familyCoverage"]["representatives"] = actual
            with self.subTest(representatives=actual), \
                 patch.object(common, "api_entries", return_value={"Multiply": entry}):
                if actual == list(common.MULTIPLY_PROFILES):
                    common.method_manifest("Multiply")
                else:
                    with self.assertRaisesRegex(RuntimeError, "feature-family"):
                        common.method_manifest("Multiply")

    def test_shared_equality_fixtures_match_compiled_registry_and_real_source(self):
        directory = common.VERIFY / "Tests/Fixtures/Equality"
        cases = [case.attrib["Include"] for case in ET.parse(directory / "Cases.props").findall("ItemGroup/EqualityCase")]
        entries = [entry for entry in common.api_entries().values()
                   if entry.get("verification", {}).get("fixtureGroup") == "Equality"]
        self.assertEqual(len(entries), 24)
        for entry in entries:
            with self.subTest(api=entry["id"]):
                gate = entry["verification"]
                self.assertEqual(gate["fixtureCases"], cases)
                self.assertEqual(gate["fixtureSources"], dict.fromkeys(cases, "Public.cs"))
                self.assertTrue((directory / "Public.cs").is_file())

    def test_shared_fixture_registry_rejects_ambiguous_cases_and_overrides(self):
        for cases, override in ((["Baseline", "Baseline"], False), (["Baseline"], True), ([], False)):
            entry = {"id": "EqUInt256UInt256", "verification": {"fixtureGroup": "Equality"}}
            if override:
                entry["verification"]["fixtureCases"] = cases
            with self.subTest(cases=cases, override=override), self.assertRaises(RuntimeError):
                common.resolve_fixture_groups([entry], {"Equality": {"cases": cases, "source": "Public.cs"}})

    def test_mutation_extraction_uses_registered_source_without_marker_file(self):
        project = common.VERIFY / "Tests/Fixtures/Equality/Nethermind.Int256.csproj"
        with patch.object(support, "build_artifact", side_effect=RuntimeError("stop after source selection")) as build:
            with self.assertRaisesRegex(RuntimeError, "stop after source selection"):
                support.mutation_proof(Path("unused"), project, "WrongLane", "EqUInt256UInt256", "scalar", {})
        self.assertEqual(build.call_args.args[3], project.parent / "Public.cs")

    def test_relational_family_cannot_drop_or_reorder_representatives(self):
        representatives = ["scalar", "x64-vector256", "x64-avx2", "x64-avx512"]
        for actual in (representatives, representatives[:-1], representatives[::-1]):
            entry = copy.deepcopy(common.api_entries()["LtUInt256UInt256"])
            gate = entry["verification"]
            theorem = "UInt256Proof.Compare.checked_less_family_contract"
            if theorem not in gate["auditedTheorems"]:
                gate["auditedTheorems"].append(theorem)
            gate["familyCoverage"] = {"kind": "relational-dispatch", "theorem": theorem,
                                      "representatives": actual}
            with self.subTest(representatives=actual), \
                 patch.object(common, "api_entries", return_value={entry["id"]: entry}):
                if actual == representatives:
                    common.method_manifest(entry["id"])
                else:
                    with self.assertRaisesRegex(RuntimeError, "feature-family"):
                        common.method_manifest(entry["id"])

    def test_family_coverage_requires_audited_gate_and_both_representatives(self):
        for mutation in ("unaudited", "one-profile", "unknown-kind", "nonstring-kind", "unknown-field", "universal"):
            entry = copy.deepcopy(common.api_entries()["Lsh"])
            gate = entry["verification"]
            family = gate["familyCoverage"]
            if mutation == "unaudited":
                family["theorem"] = "Unchecked"
            elif mutation == "one-profile":
                family["representatives"] = ["scalar"]
            elif mutation == "unknown-kind":
                family["kind"] = "assumed"
            elif mutation == "nonstring-kind":
                family["kind"] = []
            elif mutation == "unknown-field":
                family["assumption"] = True
            else:
                gate.update(allProfiles=True, profileCoverage="all-valid-profiles",
                            allProfilesTheorem=gate["auditedTheorems"][1])
            with self.subTest(mutation=mutation), patch.object(common, "api_entries", return_value={"Lsh": entry}):
                with self.assertRaisesRegex(RuntimeError, "feature-family"):
                    common.method_manifest("Lsh")
    def test_refutation_templates_are_freshness_inputs(self):
        inputs = common.source_inputs()
        for relative in ("Compare/RefutationTemplate.lean.in", "Bitwise/RefutationTemplate.lean.in",
                         "Shift/RefutationTemplate.lean.in", "Shift/OperatorRefutationTemplate.lean.in"):
            path = common.VERIFY / "Tests/Fixtures" / relative
            self.assertEqual(inputs[path.relative_to(common.ROOT).as_posix()], common.sha(path))

    def test_axiom_audits_accept_lean_line_wrapping(self):
        name = "UInt256Proof.Compare.checked_three_way_all_profiles_contract"
        approved = ["propext", "Classical.choice", "Quot.sound"]
        output = f"info: Audit.lean:1:0: '{name}' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n"
        self.assertEqual(common.theorem_audits(output, [name], approved), {name: approved})
        self.assertEqual(common.theorem_audits(
            f"'{name}' does not depend on any axioms", [name], approved), {name: []})

    def test_wrapped_audit_still_rejects_unapproved_and_duplicate_axioms(self):
        for axioms in ("propext,\n sorryAx", "propext,\n propext"):
            with self.subTest(axioms=axioms), self.assertRaisesRegex(RuntimeError, "Unapproved or duplicate"):
                common.theorem_audits(f"'Gate' depends on axioms: [{axioms}]", ["Gate"], ["propext"])

    def test_audit_cannot_cross_a_diagnostic_or_accept_duplicates(self):
        for output in ("'Gate' depends on axioms: [propext,\nerror: missing close\n]",
                       "'Gate' depends on axioms: [propext]\n'Gate' depends on axioms: [propext]"):
            with self.subTest(output=output), self.assertRaisesRegex(RuntimeError, "Missing or ambiguous"):
                common.theorem_audits(output, ["Gate"], ["propext"])

    def test_metadata_directions_and_receiver_are_contract_inputs(self):
        expected = common.api_entries()["LtUInt256UInt256"]["callingConvention"]
        actual = {"isStatic": expected["static"], "returnType": expected["returns"],
                  "hasThis": not expected["static"], "parameters": [
                      {"Name": "renamed", "type": item["type"],
                       "IsIn": item["isIn"], "IsOut": item["isOut"]}
                      for item in expected["parameters"]]}
        common.check_calling_convention(actual, expected)
        mutations = [("isStatic", False), ("returnType", "System.Void"), ("hasThis", True)]
        for key, value in mutations:
            changed = copy.deepcopy(actual)
            changed[key] = value
            with self.subTest(key=key), self.assertRaises(RuntimeError):
                common.check_calling_convention(changed, expected)
        for key, value in (("type", "System.UInt64"), ("IsIn", False), ("IsOut", True)):
            changed = copy.deepcopy(actual)
            changed["parameters"][0][key] = value
            with self.subTest(key=key), self.assertRaises(RuntimeError):
                common.check_calling_convention(changed, expected)


    def test_unknown_selector_cannot_escape_generated_directory(self):
        for selector in ("../Add", "Unknown", "System.Void::Add"):
            with self.subTest(selector=selector), self.assertRaises(ValueError):
                common.generated_directory(selector)

    def test_distinct_entries_have_distinct_reports(self):
        directories = [common.generated_directory(name) for name in common.method_names()]
        self.assertEqual(len(directories), len(set(directories)))

    def test_universal_coverage_requires_its_distinct_audited_gate(self):
        for mutation in ("missing", "unaudited", "duplicate", "nonboolean"):
            entry = copy.deepcopy(common.api_entries()["LtUInt256UInt64"])
            gate = entry["verification"]
            if mutation == "missing":
                gate.pop("allProfilesTheorem")
            elif mutation == "unaudited":
                gate["allProfilesTheorem"] = "UInt256Proof.Unchecked"
            elif mutation == "duplicate":
                gate["auditedTheorems"] = [gate["auditedTheorems"][0]] * 2
                gate["allProfilesTheorem"] = gate["auditedTheorems"][0]
            else:
                gate["allProfiles"] = 1
            with self.subTest(mutation=mutation), patch.object(common, "api_entries", return_value={"LtUInt256UInt64": entry}):
                with self.assertRaises(RuntimeError):
                    common.method_manifest("LtUInt256UInt64")


if __name__ == "__main__":
    unittest.main()
