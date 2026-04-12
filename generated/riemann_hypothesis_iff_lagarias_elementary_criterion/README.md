# `riemann_hypothesis_iff_lagarias_elementary_criterion`

Lagarias criterion is equivalent to RH

- Problem ID: `riemann_hypothesis_iff_lagarias_elementary_criterion`
- Test Problem: no
- Submitter: Kim Morrison
- Notes: Lagarias' elementary divisor-sum criterion stated using Mathlib's RiemannHypothesis, harmonic numbers, and sigma notation.
- Source: https://arxiv.org/abs/math/0008177
- Informal solution: Prove that the Riemann hypothesis is equivalent to the inequality σ(n) ≤ H_n + exp(H_n) log(H_n) for all positive integers n.

Do not modify `Challenge.lean` or `Solution.lean`. Those files are part of the
trusted benchmark and fixed by the repository.

Write your solution in `Submission.lean` and any additional local modules under
`Submission/`.

Participants may use Mathlib freely. Any helper code not already available in
Mathlib must be inlined into the submission workspace.

Multi-file submissions are allowed through `Submission.lean` and additional local
modules under `Submission/`.

`lake test` runs comparator for this problem. The command expects a comparator
binary in `PATH`, or in the `COMPARATOR_BIN` environment variable.
