from __future__ import annotations

import pathlib
import sys
import tempfile
import unittest


REPO_ROOT = pathlib.Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_ROOT / "scripts"))

import check_comparator_installation as comparator_check  # noqa: E402


class CheckComparatorInstallationTests(unittest.TestCase):
    def test_solve_two_plus_two_replaces_placeholder(self) -> None:
        with tempfile.TemporaryDirectory() as tmpdir:
            workspace = pathlib.Path(tmpdir)
            submission = workspace / "Submission.lean"
            submission.write_text(
                "namespace Submission\n\n"
                "theorem two_plus_two_eq_four : (2 : Nat) + 2 = 4 := by\n"
                "  sorry\n\n"
                "end Submission\n",
                encoding="utf-8",
            )
            comparator_check.solve_two_plus_two(workspace)
            content = submission.read_text(encoding="utf-8")
            self.assertIn("  norm_num\n", content)
            self.assertNotIn("  sorry\n", content)


if __name__ == "__main__":
    unittest.main()
