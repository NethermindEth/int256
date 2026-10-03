"""Semantic rejection diagnostics must not hide maintenance or resource failures."""

import unittest

from support import require_diagnostic_rejection, require_semantic_rejection


MODULE = "UInt256/Methods/Add/Entry.lean"
GOAL = f"error: {MODULE}:1:1: unsolved goals\n⊢ False\n"


class RejectionChecks(unittest.TestCase):
    def test_family_diagnostic_requires_public_gate_and_exact_module(self):
        diagnostic = "omega could not prove the goal:"
        output = f"error: {MODULE}:1:1: {diagnostic}\nProof checking failure: failed\n"
        require_diagnostic_rejection(output, MODULE, diagnostic)
        for changed in (output.replace(MODULE, "Other.lean"),
                        output.replace("Proof checking failure:", "Extraction failure:"),
                        output + "error: Other.lean:1:1: unknown identifier\n"):
            with self.subTest(output=changed), self.assertRaises(RuntimeError):
                require_diagnostic_rejection(changed, MODULE, diagnostic)

    def test_family_diagnostic_rejects_every_resource_marker(self):
        output = f"error: {MODULE}:1:1: unsolved goals\nProof checking failure: failed\n"
        for marker in ("maximum number of heartbeats", "maximum recursion depth",
                       "maximum number of steps exceeded", "deep recursion", "stack overflow",
                       "out of memory", "allocation failed", "killed", "timed out"):
            with self.subTest(marker=marker), self.assertRaisesRegex(RuntimeError, "exhausted"):
                require_diagnostic_rejection(output + marker.upper(), MODULE, "unsolved goals")

    def test_family_diagnostic_does_not_accept_other_tactic_failures(self):
        output = f"error: {MODULE}:1:1: unknown identifier\nProof checking failure: failed\n"
        with self.assertRaisesRegex(RuntimeError, "Missing expected"):
            require_diagnostic_rejection(output, MODULE, "unsolved goals|`simp` made no progress")

    def test_expected_goal_and_build_wrapper(self):
        require_semantic_rejection(GOAL + "error: build failed\n", MODULE)

    def test_expected_no_progress(self):
        require_semantic_rejection(f"error: {MODULE}:1:1: `simp` made no progress\n", MODULE)

    def test_expected_intro_goal(self):
        require_semantic_rejection(f"error: {MODULE}:1:1: Tactic `introN` failed: no binders\n⊢ False\n", MODULE)

    def test_expected_storage_operand_goal(self):
        require_semantic_rejection(f"error: {MODULE}:1:1: Extracted storage operands differ from the required result:\n⊢ False\n", MODULE)

    def test_storage_operand_diagnostic_requires_goal(self):
        with self.assertRaisesRegex(RuntimeError, "outside"):
            require_semantic_rejection(f"error: {MODULE}:1:1: Extracted storage operands differ from the required result:\n", MODULE)

    def test_mixed_syntax_failure(self):
        with self.assertRaisesRegex(RuntimeError, "maintenance"):
            require_semantic_rejection(GOAL + "error: Other.lean:1:1: unexpected token\n", MODULE)

    def test_mixed_import_failure(self):
        with self.assertRaisesRegex(RuntimeError, "maintenance"):
            require_semantic_rejection(GOAL + "error: Other.lean:1:1: unknown module prefix\n", MODULE)

    def test_syntax_with_printed_goal(self):
        with self.assertRaisesRegex(RuntimeError, "maintenance"):
            require_semantic_rejection(f"error: {MODULE}:1:1: unexpected token\n⊢ False\n", MODULE)

    def test_wrong_module(self):
        with self.assertRaisesRegex(RuntimeError, "outside"):
            require_semantic_rejection(GOAL.replace(MODULE, "Other.lean"), MODULE)

    def test_resource_limit(self):
        for marker in ("maximum number of heartbeats", "maximum recursion depth",
                       "maximum number of steps exceeded", "deep recursion", "stack overflow",
                       "out of memory", "allocation failed", "killed", "timed out"):
            with self.subTest(marker=marker), self.assertRaisesRegex(RuntimeError, "exhausted"):
                require_semantic_rejection(GOAL + f"fatal error: {marker.upper()}\n", MODULE)

    def test_optional_summary_resource_limit(self):
        with self.assertRaisesRegex(RuntimeError, "exhausted"):
            require_semantic_rejection("info: optional summary maximum number of heartbeats\n" + GOAL, MODULE)


if __name__ == "__main__":
    unittest.main()
