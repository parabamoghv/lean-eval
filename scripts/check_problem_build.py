#!/usr/bin/env python3
from __future__ import annotations

import pathlib
import re
import sys

import generate_projects as gp


ALLOWED_WARNING_FRAGMENT = "declaration uses `sorry`"
WARNING_RE = re.compile(r"warning:")


def main() -> int:
    manifest_path = pathlib.Path("manifests/problems.toml")
    try:
        problems = gp.load_manifest(manifest_path)
        gp.validate_problems(problems)
        modules = gp.unique_modules(problems)
        completed = gp.run(
            ["lake", "build", *modules],
            cwd=gp.REPO_ROOT,
            capture_output=True,
            error_prefix="Problem module build failed",
        )
    except gp.GenerationError as exc:
        print(str(exc), file=sys.stderr)
        return 1

    output = "\n".join(part for part in [completed.stdout, completed.stderr] if part)
    disallowed_warnings = []
    for line in output.splitlines():
        if WARNING_RE.search(line) and ALLOWED_WARNING_FRAGMENT not in line:
            disallowed_warnings.append(line)

    if disallowed_warnings:
        print("Disallowed build warnings found:", file=sys.stderr)
        for line in disallowed_warnings:
            print(line, file=sys.stderr)
        return 1

    print("Problem modules built cleanly aside from expected `sorry` warnings.")
    return 0
