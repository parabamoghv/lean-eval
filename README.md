# Formal Math Eval

This repository is a comparator-based Lean formal mathematics eval.
The benchmark is designed so that each problem is checked by
[`leanprover/comparator`](https://github.com/leanprover/comparator), and the score is
computed solely from comparator results.

## Premise

The trusted benchmark repository contains:

- the official problem statements
- problem metadata
- generator scripts that materialize comparator workspaces
- validation and scoring scripts
- leaderboard code and submission automation

A submission is an untrusted commit based on the benchmark repository. We validate that
the commit only changes allowed solution files, then run comparator on every problem. A
problem counts as solved if and only if comparator accepts the submitted solution.

This keeps the trust story simple:

- trusted: benchmark statements, metadata, invariant files, scoring logic
- untrusted: participant solution files
- score: comparator pass or fail, aggregated across problems

## What Participants Can Use

Participants may use Mathlib freely.

If a solution needs helper code that is not already available from Mathlib, that code must
be inlined into the submission itself. In particular, submissions are expected to be
self-contained apart from Lean, Mathlib, and the trusted benchmark files.

Multi-file submissions are explicitly allowed. A participant's `Solution.lean` may import
additional local modules from the submission area for that problem.

## Current Repository Shape

The long-term authoring goal is low ceremony:

- benchmark authors write many problem statements in a few shared Lean files
- a generator splits those statements into one comparator workspace per problem
- participants work against those generated workspaces or equivalent hosted views

This repository already contains:

- a shared problem-bank module in `FormalMathEval/EasyProblems.lean`
- a metadata manifest in `manifests/problems.toml`
- an `@[eval_problem]` marker on benchmark theorems in source Lean files
- a sample generated comparator workspace in `generated/two_plus_two/`
- starter scripts and docs for generation, validation, scoring, and private submissions

The hard parts we are deliberately deferring are documented in `PLAN.md`.

## Problem Metadata

The metadata model is:

- `id`: stable problem identifier
- `title`: display title
- `test`: whether the problem should be reported separately as a system-test / easy problem
- `module`: source module in the shared problem bank
- `theorem`: theorem name in that module
- `author`: required
- `notes`: optional free-form notes
- `source`: optional source link or citation
- `informal_solution`: optional link to an informal proof or discussion

Each manifest entry is expected to correspond 1-to-1 with a theorem marked
`@[eval_problem]` in the source Lean modules. The `@[eval_problem]` attribute also
checks at Lean compile time that `manifests/problems.toml` contains a corresponding
entry.

Comparator uses one fixed allowed-axioms policy across the entire benchmark.

## Single-Problem Workflow

We want it to be easy for someone to start on a single problem with minimal setup and a
working `lake test`.

The sample workspace at `generated/two_plus_two/` demonstrates the intended shape:

- `Challenge.lean` is the trusted problem statement
- `Solution.lean` is the participant-facing entrypoint
- `Submission.lean` and `Submission/` are participant-editable helper modules
- `config.json` configures comparator
- `lake test` runs comparator through `WorkspaceTest.lean`

The generator emits this structure automatically for every problem.

Generate all committed workspaces from the manifest:

```bash
python scripts/generate_projects.py
```

Check whether committed generated output is up to date:

```bash
python scripts/generate_projects.py --check
```

Generate one workspace only:

```bash
python scripts/generate_projects.py --problem two_plus_two
```

Validate the manifest and `@[eval_problem]` inventory:

```bash
python scripts/validate_manifest.py
```

Validate that a submission only changes participant-owned files:

```bash
python scripts/validate_submission.py --file generated/two_plus_two/Solution.lean
```

Score the current repo state by counting attempted problems and successful `lake test`
runs on attempted problems:

```bash
python scripts/run_eval.py
python scripts/run_eval.py --json
```

The scorer automatically prefers `workspaces/<problem-id>/` when it exists, and falls back to
`generated/<problem-id>/` otherwise.

To run an end-to-end local workflow check as a one-liner, including:
- clean-state verification,
- zero-attempt scoring,
- one incorrect `two_plus_two` attempt,
- one correct `two_plus_two` attempt,
- and automatic cleanup,

run:

```bash
python scripts/check_eval_workflow.py
```

There is also a helper command to copy out a single-problem workspace:

```bash
python scripts/start_problem.py two_plus_two
```

That creates `workspaces/two_plus_two/` as a local starting point.

## Local Development

To build the top-level problem bank:

```bash
lake update
lake build
python scripts/validate_manifest.py
python scripts/check_problem_build.py
python scripts/generate_projects.py
```

To try the sample single-problem workspace:

```bash
cd generated/two_plus_two
lake update
lake test
```

Or, to work in a copied local workspace:

```bash
python scripts/start_problem.py two_plus_two
cd workspaces/two_plus_two
lake update
lake test
```

`lake test` expects comparator to be installed and visible as `comparator`, or via:

```bash
COMPARATOR_BIN=/path/to/comparator lake test
```

Comparator itself also requires the usual external setup described in the upstream
repository, including `landrun` and `lean4export`.

To check a local comparator installation against the generated starter problem:

```bash
python scripts/check_comparator_installation.py
```

## Submission Model

The benchmark is intended to support private submissions from day one.

The target experience is:

- a participant prepares a private commit against the public benchmark base
- the submission service checks that only allowed files changed
- the service runs the benchmark privately
- only the resulting score and public metadata are published

The concrete automation plan for this is tracked in `PLAN.md`.

## Generator Checks

For CI, the intended guardrail is:

```bash
python scripts/check_generated.py
```

That verifies generated workspaces are current and fails if `generated/` would differ from
committed output.

Problem module warnings are checked separately with:

```bash
python scripts/check_problem_build.py
```

## Starter Problems

The benchmark currently includes deliberately easy starter problems, all marked with
`test = true` so they can be reported separately from the main benchmark:

- `two_plus_two`
- `list_append_singleton_length`

That problem exists to verify the pipeline and to make it easy to get onto the leaderboard
with a first successful submission.
