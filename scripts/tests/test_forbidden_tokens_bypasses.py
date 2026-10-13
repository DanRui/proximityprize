"""forbidden_tokens.py must not be bypassed by modifier, comment or paren variants.

Each source below is accepted by Lean 4 and introduces an unproven axiom or a
vacuous `: True` placebo, so the precheck must reject it.
"""
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

SCRIPT = Path(__file__).resolve().parents[1] / "forbidden_tokens.py"


def run_precheck(source: str) -> subprocess.CompletedProcess:
    with tempfile.TemporaryDirectory() as tmp:
        path = Path(tmp) / "Probe.lean"
        path.write_text(source, encoding="utf-8")
        return subprocess.run([sys.executable, str(SCRIPT), str(path)],
                              capture_output=True, text=True)


class ForbiddenTokenBypasses(unittest.TestCase):
    def assert_rejected(self, source: str, needle: str):
        result = run_precheck(source)
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn(needle, result.stderr)

    def test_noncomputable_axiom_is_rejected(self):
        self.assert_rejected("private noncomputable axiom fooA : 1 = 2\n",
                             "forbidden custom axiom declaration fooA")

    def test_unsafe_axiom_is_rejected(self):
        self.assert_rejected("unsafe axiom fooB : 1 = 2\n",
                             "forbidden custom axiom declaration fooB")

    def test_comment_separator_after_axiom_is_rejected(self):
        self.assert_rejected("axiom/-c-/fooC : 1 = 2\n",
                             "forbidden custom axiom declaration fooC")

    def test_parenthesized_true_placebo_is_rejected(self):
        self.assert_rejected("theorem x_residual : (True) := trivial\n",
                             "forbidden vacuous placebo")

    def test_nested_parenthesized_true_placebo_is_rejected(self):
        self.assert_rejected("theorem y : ((True)) := trivial\n",
                             "forbidden vacuous placebo")

    def test_axiom_named_in_comment_is_not_flagged(self):
        result = run_precheck("-- noncomputable axiom fooD : 1 = 2\n"
                              "/- unsafe axiom fooE : 1 = 2 -/\n"
                              "theorem real : (1 : Nat) + 1 = 2 := rfl\n"
                              "theorem pair : (True ∧ (1 = 1)) := ⟨trivial, rfl⟩\n")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)


if __name__ == "__main__":
    unittest.main()
