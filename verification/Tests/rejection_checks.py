"""Semantic rejection diagnostics must not hide maintenance or resource failures."""

import unittest

from support import require_semantic_rejection


MODULE = "UInt256/Methods/Add/Entry.lean"
GOAL = f"error: {MODULE}:1:1: unsolved goals\n⊢ False\n"


class RejectionChecks(unittest.TestCase):
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
                       "maximum number of steps exceeded", "deep recursion", "stack overflow"):
            with self.subTest(marker=marker), self.assertRaisesRegex(RuntimeError, "exhausted"):
                require_semantic_rejection(GOAL + f"error: {MODULE}:2:1: {marker}\n", MODULE)

    def test_optional_summary_resource_limit(self):
        with self.assertRaisesRegex(RuntimeError, "exhausted"):
            require_semantic_rejection("info: optional summary maximum number of heartbeats\n" + GOAL, MODULE)


if __name__ == "__main__":
    unittest.main()
