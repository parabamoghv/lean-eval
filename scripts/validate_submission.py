#!/usr/bin/env python3
"""
Validate that a submission only edits participant-owned files.
"""

from __future__ import annotations

import argparse
import json
import pathlib
import re
import subprocess
import sys

import generate_projects as gp


ALLOWED_PATTERNS = [
    re.compile(r"^generated/[^/]+/Solution\.lean$"),
    re.compile(r"^generated/[^/]+/Submission\.lean$"),
    re.compile(r"^generated/[^/]+/Submission/.+\.lean$"),
]


def changed_files_from_git(base_ref: str, head_ref: str) -> list[str]:
    result = subprocess.run(
        ["git", "diff", "--name-only", f"{base_ref}..{head_ref}"],
        cwd=gp.REPO_ROOT,
        check=False,
        text=True,
        capture_output=True,
    )
    if result.returncode != 0:
        stderr = (result.stderr or result.stdout).strip()
        raise gp.GenerationError(f"git diff failed:\n{stderr}")
    return [line.strip() for line in result.stdout.splitlines() if line.strip()]


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument("--base", help="Base git ref for changed-file validation.")
    parser.add_argument("--head", help="Head git ref for changed-file validation.")
    parser.add_argument(
        "--file",
        action="append",
        default=[],
        help="Explicit changed file path. Can be passed multiple times.",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="Emit machine-readable JSON output.",
    )
    return parser.parse_args()


def validate_changed_files(files: list[str]) -> tuple[list[str], list[str]]:
    problems = gp.load_manifest(gp.DEFAULT_MANIFEST)
    valid_problem_ids = {problem.id for problem in problems}
    allowed: list[str] = []
    forbidden: list[str] = []
    for file_path in files:
        normalized = pathlib.PurePosixPath(file_path).as_posix()
        if not any(pattern.fullmatch(normalized) for pattern in ALLOWED_PATTERNS):
            forbidden.append(normalized)
            continue
        parts = normalized.split("/")
        if len(parts) < 3 or parts[1] not in valid_problem_ids:
            forbidden.append(normalized)
            continue
        allowed.append(normalized)
    return allowed, forbidden


def main() -> int:
    args = parse_args()
    try:
        if args.file:
            changed_files = args.file
        elif args.base and args.head:
            changed_files = changed_files_from_git(args.base, args.head)
        else:
            raise gp.GenerationError("Provide either --base/--head or one or more --file arguments.")

        allowed, forbidden = validate_changed_files(changed_files)
    except gp.GenerationError as exc:
        if args.json:
            print(json.dumps({"status": "error", "message": str(exc)}, indent=2))
        else:
            print(str(exc), file=sys.stderr)
        return 1

    status = 0 if not forbidden else 1
    payload = {
        "status": "ok" if status == 0 else "forbidden_changes",
        "changed_files": changed_files,
        "allowed_files": allowed,
        "forbidden_files": forbidden,
    }
    if args.json:
        print(json.dumps(payload, indent=2))
    else:
        if forbidden:
            print("Forbidden submission changes detected:", file=sys.stderr)
            for file_path in forbidden:
                print(file_path, file=sys.stderr)
        else:
            print("Submission changes are limited to participant-owned files.")
    return status


if __name__ == "__main__":
    raise SystemExit(main())
