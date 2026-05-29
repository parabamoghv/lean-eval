import ChallengeDeps
import Submission

open LeanEval.ComplexAnalysis
open Function

theorem mandelbrot_connected : IsConnected Mandelbrot := by
  exact Submission.mandelbrot_connected
