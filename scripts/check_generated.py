#!/usr/bin/env python3
from __future__ import annotations

import pathlib
import subprocess
import sys


REPO_ROOT = pathlib.Path(__file__).resolve().parent.parent


def main() -> int:
    result = subprocess.run(
        [sys.executable, "scripts/generate_projects.py", "--check"],
        cwd=REPO_ROOT,
        check=False,
    )
    if result.returncode != 0:
        return result.returncode

    repo_check = subprocess.run(
        ["git", "rev-parse", "--is-inside-work-tree"],
        cwd=REPO_ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    if repo_check.returncode != 0:
        return 0

    diff = subprocess.run(
        ["git", "diff", "--exit-code", "--", "generated"],
        cwd=REPO_ROOT,
        check=False,
    )
    return diff.returncode


if __name__ == "__main__":
    raise SystemExit(main())
