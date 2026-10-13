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

    def test_bare_noncomputable_axiom_is_rejected(self):
        self.assert_rejected("noncomputable axiom fooN : 1 = 2\n",
                             "forbidden custom axiom declaration fooN")

    def test_partial_axiom_is_rejected(self):
        # Lean v4.30.0-rc2 (repo toolchain) accepts `partial axiom`.
        self.assert_rejected("partial axiom fooP : 1 = 2\n",
                             "forbidden custom axiom declaration fooP")

    def test_nonrec_axiom_is_rejected(self):
        # Lean v4.30.0-rc2 accepts `nonrec axiom` and `#print axioms` lists it.
        self.assert_rejected("nonrec axiom fooR : 1 = 2\n",
                             "forbidden custom axiom declaration fooR")

    def test_protected_axiom_in_namespace_is_rejected(self):
        self.assert_rejected("namespace X\nprotected axiom fooQ : 1 = 2\nend X\n",
                             "forbidden custom axiom declaration fooQ")

    def test_docstring_attribute_and_modifiers_before_axiom_is_rejected(self):
        self.assert_rejected(
            "/-- d -/ @[simp] private noncomputable axiom fooS : 1 = 2\n",
            "forbidden custom axiom declaration fooS")

    def test_comment_separator_after_axiom_is_rejected(self):
        self.assert_rejected("axiom/-c-/fooC : 1 = 2\n",
                             "forbidden custom axiom declaration fooC")

    def test_parenthesized_true_placebo_is_rejected(self):
        self.assert_rejected("theorem x_residual : (True) := trivial\n",
                             "forbidden vacuous placebo")

    def test_nested_parenthesized_true_placebo_is_rejected(self):
        self.assert_rejected("theorem y : ((True)) := trivial\n",
                             "forbidden vacuous placebo")

    def test_true_only_conjunction_placebo_is_rejected(self):
        self.assert_rejected("theorem z : True ∧ True := ⟨trivial, trivial⟩\n",
                             "forbidden vacuous placebo")

    def test_bracketed_true_only_conjunction_placebo_is_rejected(self):
        self.assert_rejected("theorem w : (True ∧ (True)) := ⟨trivial, trivial⟩\n",
                             "forbidden vacuous placebo")

    def test_true_only_implication_and_disjunction_placebos_are_rejected(self):
        self.assert_rejected("theorem v : True → True := id\n", "forbidden vacuous placebo")
        self.assert_rejected("theorem u : True ∨ True := Or.inl trivial\n",
                             "forbidden vacuous placebo")

    def test_true_only_obligation_def_is_rejected(self):
        self.assert_rejected("def foo_residual : Prop := True\n"
                             "abbrev bar_residual : (True ∧ True) := ⟨trivial, trivial⟩\n",
                             "obligation-like name bar_residual")

    def test_axiom_named_in_comment_is_not_flagged(self):
        result = run_precheck("-- noncomputable axiom fooD : 1 = 2\n"
                              "/- unsafe axiom fooE : 1 = 2 -/\n"
                              "theorem real : (1 : Nat) + 1 = 2 := rfl\n"
                              "theorem pair : (True ∧ (1 = 1)) := ⟨trivial, rfl⟩\n")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)


    # --- axioms split across lines / comments (all compile with Lean v4.30.0-rc2
    # and `#print axioms bad` lists the axiom) ---------------------------------
    def test_axiom_name_on_next_line_is_rejected(self):
        self.assert_rejected("axiom\n  unproved : False\ntheorem bad : False := unproved\n",
                             "forbidden custom axiom declaration unproved")

    def test_axiom_multiline_comment_separator_is_rejected(self):
        self.assert_rejected("axiom/- separator\n-/unproved : False\n"
                             "theorem bad : False := unproved\n",
                             "forbidden custom axiom declaration unproved")

    def test_axiom_line_comment_then_name_is_rejected(self):
        self.assert_rejected("axiom -- trailing\n\n   unprovedL : False\n",
                             "forbidden custom axiom declaration unprovedL")

    def test_modifiers_and_axiom_split_over_lines_is_rejected(self):
        self.assert_rejected("private\nnoncomputable\naxiom\n/- a -/ /- b -/\n  unprovedM : False\n",
                             "forbidden custom axiom declaration unprovedM")

    def test_guillemet_axiom_name_is_rejected(self):
        self.assert_rejected("axiom «weird name» : False\n",
                             "forbidden custom axiom declaration «weird name»")

    def test_split_axiom_reports_keyword_line(self):
        result = run_precheck("theorem ok : 1 = 1 := rfl\naxiom\n  unprovedN : False\n")
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn(":2: forbidden custom axiom declaration unprovedN", result.stderr)

    # --- module-file modifiers: Lean v4.30.0-rc2 accepts exactly `public`,
    # `private`, `protected`, `noncomputable`, `unsafe`, `partial`, `nonrec`,
    # `meta` (and combinations) before `axiom`; `scoped`/`local` do not parse.
    def test_public_axiom_in_module_is_rejected(self):
        self.assert_rejected("module\nimport Init\npublic axiom unproved : False\n"
                             "public theorem bad : False := unproved\n",
                             "forbidden custom axiom declaration unproved")

    def test_every_accepted_module_modifier_is_rejected(self):
        for mods in ("public", "private", "protected", "noncomputable", "unsafe", "partial",
                     "nonrec", "meta", "public meta", "private meta", "public noncomputable",
                     "public partial", "public nonrec", "public unsafe"):
            with self.subTest(mods=mods):
                self.assert_rejected(
                    f"module\nimport Init\nnamespace X\n{mods} axiom fooMod : False\nend X\n",
                    "forbidden custom axiom declaration fooMod")

    def test_public_true_placebo_is_rejected(self):
        self.assert_rejected("module\nimport Init\npublic theorem p_residual : True := trivial\n",
                             "forbidden vacuous placebo")

    def test_public_obligation_def_is_rejected(self):
        self.assert_rejected("public abbrev q_residual : True ∧ True := ⟨trivial, trivial⟩\n",
                             "obligation-like name q_residual")

    def test_print_axioms_and_identifiers_containing_axiom_are_not_flagged(self):
        result = run_precheck("def axiomCount : Nat := 1\ndef Foo.axiom_ok : Nat := 2\n"
                              "theorem real : (1 : Nat) = 1 := rfl\n#print axioms real\n")
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    # --- `True` rebound locally: these are real propositions (each compiles
    # with Lean v4.30.0-rc2 and `#print axioms` reports no axioms), so they must
    # NOT be flagged as placebos. ---------------------------------------------
    def assert_clean(self, source: str):
        result = run_precheck(source)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_true_bound_by_binder_is_not_a_placebo(self):
        for src in (
            "theorem identity_prop (True : Prop) : True → True := fun h => h\n",
            "theorem t {True : Prop} : True → True := fun h => h\n",
            "theorem t ⦃True : Prop⦄ : True → True := fun h => h\n",
            "theorem t {{True : Prop}} : True → True := fun h => h\n",
            "theorem t (P True : Prop) : True → True := fun h => h\n",
            "theorem t (True : Prop) (h : True) : True := h\n",
            "theorem t (True : Prop := False) : True → True := fun h => h\n",
            "theorem t (True: Prop): True → True := fun h => h\n",
            "theorem t («True» : Prop) : True → True := fun h => h\n",
            "theorem t\n  (True : Prop) :\n  True → True := fun h => h\n",
            "theorem t (_x : Nat) (True : Prop) : True ∧ True → True := fun h => h.1\n",
            "lemma t (True : Prop) : (True ∧ (True)) → True := fun h => h.1\n",
        ):
            with self.subTest(src=src):
                self.assert_clean(src)

    def test_true_bound_by_variable_is_not_a_placebo(self):
        for src in (
            "variable (True : Prop) in\ntheorem t : True → True := fun h => h\n",
            "section\nvariable (True : Prop)\ntheorem t : True → True := fun h => h\nend\n",
            "section\nvariable {n : Nat}\n  {True : Prop}\ntheorem t : True → True := fun h => h\nend\n",
        ):
            with self.subTest(src=src):
                self.assert_clean(src)

    def test_true_redeclared_in_namespace_is_not_a_placebo(self):
        # Inside `namespace F`, `True` resolves to `F.True` (`#check @F.t` shows
        # `F.True → F.True`).
        self.assert_clean("namespace F\ndef True : Prop := False\n"
                          "theorem t : True → True := fun h => h\nend F\n")

    def test_shadowed_true_obligation_def_is_not_flagged(self):
        self.assert_clean("abbrev foo_residual (True : Prop) : True → True := fun h => h\n")

    def test_builtin_true_still_rejected_next_to_unrelated_binders(self):
        # Binders that merely *use* `True` or have similar names do not rebind it.
        self.assert_rejected("theorem t (h : True) : True := h\n", "forbidden vacuous placebo")
        self.assert_rejected("theorem t (Trueish : Prop) : True ∧ True := ⟨trivial, trivial⟩\n",
                             "forbidden vacuous placebo")
        self.assert_rejected("theorem t (x : Nat) {α : Type} : (True) := trivial\n",
                             "forbidden vacuous placebo")
        self.assert_rejected("theorem t (f : True → True) : True → True := f\n",
                             "forbidden vacuous placebo")

    def test_binder_in_other_declaration_does_not_mask_placebo(self):
        self.assert_rejected("theorem a (True : Prop) : True → True := fun h => h\n"
                             "theorem b_residual : True := trivial\n",
                             "forbidden vacuous placebo `theorem/lemma b_residual")


if __name__ == "__main__":
    unittest.main()
