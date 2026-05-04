import ChallengeDeps
import Submission

open LeanEval.Topology
open Set (Icc Ioo)

theorem contractibleSpace_houseWithTwoRooms : ContractibleSpace HouseWithTwoRooms := by
  exact Submission.contractibleSpace_houseWithTwoRooms
