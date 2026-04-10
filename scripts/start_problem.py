#!/usr/bin/env python3
"""
Copy a generated single-problem workspace to a destination directory.

This gives participants a clean local starting point for one problem without needing to
manually copy files around.
"""

from __future__ import annotations

import argparse
import pathlib
import shutil
import sys


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("problem_id", help="Problem identifier, for example: two_plus_two")
    parser.add_argument(
        "destination",
        nargs="?",
        help="Destination directory. Defaults to ./workspaces/<problem_id>.",
    )
    args = parser.parse_args()

    source = pathlib.Path("generated") / args.problem_id
    if not source.is_dir():
        print(f"Problem workspace not found: {source}", file=sys.stderr)
        return 1

    destination = (
        pathlib.Path(args.destination)
        if args.destination
        else pathlib.Path("workspaces") / args.problem_id
    )
    if destination.exists():
        print(f"Destination already exists: {destination}", file=sys.stderr)
        return 1

    destination.parent.mkdir(parents=True, exist_ok=True)
    shutil.copytree(source, destination)
    print(f"Created workspace: {destination}")
    print("Next steps:")
    print(f"  cd {destination}")
    print("  lake update")
    print("  lake test")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

