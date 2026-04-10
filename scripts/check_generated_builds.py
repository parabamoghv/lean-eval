#!/usr/bin/env python3
from __future__ import annotations

import argparse
import pathlib
import subprocess
import sys


REPO_ROOT = pathlib.Path(__file__).resolve().parent.parent
GENERATED_ROOT = REPO_ROOT / "generated"


def generated_workspaces() -> list[pathlib.Path]:
    if not GENERATED_ROOT.is_dir():
        return []
    workspaces: list[pathlib.Path] = []
    for path in sorted(GENERATED_ROOT.iterdir()):
        if not path.is_dir():
            continue
        if (path / "lakefile.toml").is_file():
            workspaces.append(path)
    return workspaces


def run(cmd: list[str], cwd: pathlib.Path) -> None:
    completed = subprocess.run(cmd, cwd=cwd, check=False)
    if completed.returncode != 0:
        raise RuntimeError(
            f"Command failed with exit code {completed.returncode}: {' '.join(cmd)}"
        )


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--problem",
        action="append",
        default=[],
        help="Only build the named generated workspace. May be passed multiple times.",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    selected = set(args.problem)
    workspaces = generated_workspaces()
    if selected:
        workspaces = [workspace for workspace in workspaces if workspace.name in selected]
        missing = sorted(selected - {workspace.name for workspace in workspaces})
        if missing:
            for name in missing:
                print(f"Unknown generated workspace: {name}", file=sys.stderr)
            return 1

    if not workspaces:
        print("No generated workspaces found.", file=sys.stderr)
        return 1

    try:
        for workspace in workspaces:
            print(f"==> Building generated workspace `{workspace.name}`")
            run(["lake", "build"], cwd=workspace)
    except RuntimeError as exc:
        print(str(exc), file=sys.stderr)
        return 1

    print(f"Built {len(workspaces)} generated workspace(s).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
