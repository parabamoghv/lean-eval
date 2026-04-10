import ChallengeDeps
import Submission

open FormalMathEval.Topology

theorem pi1_circle_mulEquiv_int :
    Nonempty (HomotopyGroup.Pi 1 Circle (1 : Circle) ≃* Multiplicative ℤ) := by
  exact @Submission.pi1_circle_mulEquiv_int
