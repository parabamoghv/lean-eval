# `cyclotomic_integer_house_le_two`

Real cyclotomic integer with house at most 2

- Problem ID: `cyclotomic_integer_house_le_two`
- Test Problem: no
- Author: Kim Morrison
- Notes: The <= 2 branch of Theorem 1.0.5 from Calegari--Morrison--Snyder, stated using Mathlib's NumberField.house.
- Source: https://arxiv.org/pdf/1004.0665
- Informal solution: If the house is at most 2, then it equals 2 cos(pi / m) for some positive integer m.

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
