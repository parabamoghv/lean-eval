# PLAN

This file tracks the pieces that should be designed carefully rather than improvised in the
first scaffold pass.

## High-Priority Next Decisions

### 0. Theorem Pretty-Printing In Generated Challenges

This is partially addressed.

The generator now slices theorem statements from the trusted authored source files using
Lean declaration ranges, so generated `Challenge.lean` and `Solution.lean` preserve the
notation the author wrote in source.

Residual risk:

- the fallback theorem type emitted by the extractor is still elaborated, so future generator
  paths that rely on `theoremType` directly may reintroduce ugly output
- the current source-slicing approach assumes theorem proofs are written in the simple
  `:= by` style used by benchmark source files

Follow-up needed:

- support a wider range of theorem source layouts if authors start using them
- decide whether the manifest/generator contract should explicitly require `:= by` proofs in
  benchmark source files

### 1. Source-of-Truth Authoring Format

We want benchmark authors to write many problems in a few shared Lean files, not to
hand-maintain one comparator package per problem.

Open questions:

- Should metadata live in Lean doc-comments, a TOML sidecar, or both?
- Should each source theorem be written directly with `by sorry`, or should the source
  file contain only statement declarations that the generator re-emits?
- How should the generator extract theorem statements robustly enough to avoid accidental
  proof leakage into generated workspaces?

Recommended direction:

- keep theorem statements in shared Lean files
- keep metadata in a TOML manifest for V1
- generate comparator workspaces from parsed theorem declarations once we pick an
  extraction strategy we trust

### 2. Submission File Policy

We need a precise whitelist for what a participant commit may change.

Proposed model:

- allowed:
  `solutions/<problem-id>/Solution.lean`
  `solutions/<problem-id>/Submission.lean`
  `solutions/<problem-id>/Submission/**/*.lean`
- forbidden:
  benchmark statements
  manifests
  generator code
  leaderboard code
  CI and deployment code
  comparator configs

Open questions:

- Do we want to allow non-Lean files in submissions, such as generated data tables?
- If so, under what size limits and in which directories?

### 3. Private Submission Service

The user asked to start at the "private submissions from day one" model instead of a
public-only workflow.

We need to design:

- how users authenticate
- whether submissions arrive as private GitHub repos, patch bundles, or uploaded tarballs
- how the service pins the benchmark base commit
- how private evaluation workers are isolated
- what proof artifacts are retained
- what public metadata appears on the leaderboard

Recommended direction:

- start with GitHub-based private submissions against a pinned public base commit
- require a commit SHA and a repository URL or installation-based access
- evaluate in an isolated worker that checks changed files before any Lean build occurs
- publish only score, model name, submission timestamp, and an optional paper/repo link

### 4. Generator Output

The generator should emit one independent problem workspace per problem.

Each workspace should include:

- `Challenge.lean`
- `Solution.lean`
- `Submission.lean`
- `Submission/`
- `config.json`
- `lakefile.toml`
- `lean-toolchain`
- `WorkspaceTest.lean`
- a short problem README

Open questions:

- Should generated workspaces live in the repo, or be purely build artifacts?
- Should we also generate a one-command "single problem starter repo" tarball or template?
- Should `lake test` always mean comparator, or should we also expose a faster local
  pre-check?

### 5. Leaderboard Site

We need a static or mostly-static leaderboard that supports:

- overall score
- solved-count view
- per-problem breakdown
- links to source and informal solution
- model metadata
- submission history

Open questions:

- static site generated from JSON, or a thin dynamic frontend backed by a database?
- should failed private submissions remain entirely invisible, or show aggregate stats?

Recommended direction:

- JSON results artifacts checked into a separate public results repo or branch
- static site generated from those artifacts

## Problem Curation

We should curate an initial batch of roughly 15 to 25 problems with:

- broad topic coverage
- statements already expressible in Mathlib
- clear references
- optional informal proof links
- difficulty high enough that current frontier models do not saturate the benchmark

Candidate families to investigate:

- concrete algebra and number theory statements
- equivalence theorems where the statement is compact but the formalization is nontrivial
- results with published formalization-adjacent proofs that help humans but do not make the
  Lean proof trivial

The current repository only includes the trivial test problem `two_plus_two`.

## Immediate Follow-Up Work

### Repo Scaffolding

- add invariant-file validation for participant commits
- add result schemas for per-problem and per-submission outputs
- extend CI beyond the current repository health checks as the submission pipeline lands
- keep `lake exe lean-eval` as the only intended user-facing entrypoint
- treat the current `lean-eval` shell-out implementation as transitional only
- migrate operational tooling from Python scripts to native Lean implementations over time,
  so manifest validation, generation, submission checks, scoring, and related repo
  automation live inside the Lean toolchain rather than behind Python wrappers

### UX

- add a `scripts/start_problem.py` command that materializes a local cloneable workspace for
  a selected problem
- add a `scripts/check_submission.py` command for local dry runs before upload
- decide whether participants work directly in this repo or in generated per-problem repos

### Trust / Security

- specify exactly when untrusted files may be read or built
- pin comparator, `lean4export`, and `landrun` versions
- decide whether we want optional nanoda checking enabled by default
- document the exact threat model for the hosted submission service
