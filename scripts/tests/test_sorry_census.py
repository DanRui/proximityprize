"""Sorry/admit census must not treat string text as comments or as holes."""
import sys
from pathlib import Path
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import sorry_census


def kinds(source: str) -> list[tuple[str, str, str]]:
    with tempfile.TemporaryDirectory() as directory:
        root = Path(directory)
        folder = root / "ArkLib"
        folder.mkdir()
        (folder / "Probe.lean").write_text(source)
        rows = sorry_census.census(root)
    return [(row["token"], row["kind"], row["decl"]) for row in rows]


class SorryCensusStrings(unittest.TestCase):
    def test_live_sorry_and_admit_are_holes(self):
        self.assertEqual(
            kinds("theorem t : True := sorry\nlemma u : False := admit\n"),
            [("sorry", "hole", "theorem t"), ("admit", "hole", "lemma u")])

    def test_comments_and_docstrings_are_not_holes(self):
        source = (
            "/-- uses sorry in prose -/\n"
            "theorem t : True := trivial\n"
            "-- admit is only a word here\n"
            "/- nested /- sorry -/ still admit -/\n"
        )
        self.assertEqual(
            [(token, kind) for token, kind, _decl in kinds(source)],
            [("sorry", "doc"), ("admit", "doc"), ("sorry", "doc"), ("admit", "doc")])

    def test_line_comment_does_not_hide_the_next_line(self):
        self.assertEqual(
            kinds("theorem t : True := by\n  -- sorry\n  sorry\n"),
            [("sorry", "doc", "theorem t"), ("sorry", "hole", "theorem t")])

    def test_dashes_inside_string_do_not_hide_sorry(self):
        source = 'theorem t : String := "a -- b" ++ sorry\n'
        self.assertEqual(kinds(source), [("sorry", "hole", "theorem t")])

    def test_block_opener_inside_string_does_not_hide_sorry(self):
        source = (
            "theorem t : True := by\n"
            '  let _ := "open /-"\n'
            "  sorry\n"
            '  let _ := "-/"\n'
        )
        self.assertEqual(kinds(source), [("sorry", "hole", "theorem t")])

    def test_sorry_inside_string_literal_is_not_a_hole(self):
        self.assertEqual(
            kinds('def msg := "do not sorry or admit this"\n'),
            [("sorry", "doc", "def msg"), ("admit", "doc", "def msg")])

    def test_escaped_quote_keeps_later_sorry_live(self):
        source = 'theorem t : String := "a \\" -- " ++ sorry\n'
        self.assertEqual(kinds(source), [("sorry", "hole", "theorem t")])

    def test_char_literal_quote_does_not_swallow_sorry(self):
        source = "theorem t : True := by let _ := '\"'; exact sorry\n"
        self.assertEqual(kinds(source), [("sorry", "hole", "theorem t")])

    def test_multiline_string_does_not_start_a_comment(self):
        source = (
            "theorem t : True := by\n"
            '  let _ := "hello\n'
            '/- not a comment"\n'
            "  sorry\n"
        )
        self.assertEqual(kinds(source), [("sorry", "hole", "theorem t")])

    def test_string_gap_does_not_let_a_later_block_opener_hide_sorry(self):
        source = (
            "theorem t : True := by\n"
            '  let _ := "a\\\n'
            '/- "\n'
            "  sorry\n"
            '  let _ := "-/"\n'
        )
        self.assertEqual(kinds(source), [("sorry", "hole", "theorem t")])

    def test_sorry_inside_a_continued_string_is_not_a_hole(self):
        source = 'def msg := "keep\\\n  sorry here"\n'
        self.assertEqual(kinds(source), [("sorry", "doc", "def msg")])

    def test_raw_string_internal_quote_does_not_hide_sorry(self):
        source = 'theorem t : True := by let _ := r#"foo " -- bar"#; exact sorry\n'
        self.assertEqual(kinds(source), [("sorry", "hole", "theorem t")])

    def test_raw_string_text_is_not_a_hole(self):
        self.assertEqual(
            kinds('def msg := r##"sorry and admit"##\n'),
            [("sorry", "doc", "def msg"), ("admit", "doc", "def msg")])

    def test_identifier_ending_in_r_is_not_a_raw_string(self):
        plain = 'theorem t : String := foor"a -- b" ++ sorry\n'
        self.assertEqual(kinds(plain), [("sorry", "hole", "theorem t")])
        # `foo_1r` is an identifier, so the `"` closes before `--` and the sorry
        # is a comment. A raw string would keep going until `"#` and leave sorry live.
        numbered = 'theorem t : True := by let _ := foo_1r#"a " -- "# ++ sorry\n'
        self.assertEqual(kinds(numbered), [("sorry", "doc", "theorem t")])

    def test_raw_string_after_a_numeric_token(self):
        for literal in ('1_0r#"a " -- b"#', '0x1r#"a " -- b"#'):
            with self.subTest(literal=literal):
                source = f"theorem t : True := by let _ := {literal}; exact sorry\n"
                self.assertEqual(kinds(source), [("sorry", "hole", "theorem t")])

    def test_interpolated_sorry_is_a_hole_and_literal_sorry_is_not(self):
        source = (
            'theorem t : String := s!"{sorry}"\n'
            'theorem u : String := s!"sorry"\n'
            'theorem v : String := s!"\\{sorry}"\n'
        )
        self.assertEqual(
            kinds(source),
            [
                ("sorry", "hole", "theorem t"),
                ("sorry", "doc", "theorem u"),
                ("sorry", "doc", "theorem v"),
            ])

    def test_interpolation_tracks_comments_and_nested_braces(self):
        source = (
            'theorem t : String := s!"{-- sorry\nexact sorry}"\n'
            'theorem u : String := m!"{({admit})}"\n'
            'theorem v : String := println! "{sorry}"\n'
        )
        self.assertEqual(
            kinds(source),
            [
                ("sorry", "doc", "theorem t"),
                ("sorry", "hole", "theorem t"),
                ("admit", "hole", "theorem u"),
                ("sorry", "hole", "theorem v"),
            ])

    def test_comment_inside_interpolation_can_contain_a_brace(self):
        source = 'theorem t : String := s!"{/- } -/ sorry}"\n'
        self.assertEqual(kinds(source), [("sorry", "hole", "theorem t")])


if __name__ == "__main__":
    unittest.main()
