import ProofGapLean.Prelude.Core
import Mathlib.Tactic.Linarith

namespace ProofGap.Exercise154_2

def leftDomain : Set ℝ := {x | 0 < x + 2}
def rightDomain : Set ℝ := {x | 0 < x - 2}
def domain : Set ℝ := leftDomain ∩ rightDomain

/-- Source: `proof_gap/exercise_154_2/1.txt`. -/
theorem gap1 : leftDomain = Set.Ioi (-2) := by
  ext x
  simp only [leftDomain, Set.mem_setOf_eq, Set.mem_Ioi]
  constructor <;> intro h <;> linarith

/-- Source: `proof_gap/exercise_154_2/2.txt`. -/
theorem gap2 : rightDomain = Set.Ioi 2 := by
  ext x
  simp only [rightDomain, Set.mem_setOf_eq, Set.mem_Ioi]
  constructor <;> intro h <;> linarith

/-- Source: `proof_gap/exercise_154_2/3.txt`. -/
theorem gap3 : domain = Set.Ioi (-2) ∩ Set.Ioi 2 := by
  rw [domain, gap1, gap2]

/-- Source: `proof_gap/exercise_154_2/4.txt`. -/
theorem gap4 : Set.Ioi (-2 : ℝ) ∩ Set.Ioi 2 = Set.Ioi 2 := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_Ioi]
  constructor
  · exact fun h => h.2
  · intro h
    constructor <;> linarith

/-- Source: `proof_gap/exercise_154_2/5.txt`. -/
theorem gap5 : domain = Set.Ioi 2 := by
  rw [gap3, gap4]

end ProofGap.Exercise154_2
