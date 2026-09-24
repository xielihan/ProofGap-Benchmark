import ProofGapLean.Prelude.Core
import Mathlib.Tactic.Linarith

namespace ProofGap.Exercise154_2

def leftDomain : Set ℝ := {x | 0 < x + 2}
def rightDomain : Set ℝ := {x | 0 < x - 2}
def domain : Set ℝ := leftDomain ∩ rightDomain

/-- Exercise 154_2, gap 1. -/
theorem gap1 : leftDomain = Set.Ioi (-2) := by
  ext x
  simp only [leftDomain, Set.mem_setOf_eq, Set.mem_Ioi]
  constructor <;> intro h <;> linarith

/-- Exercise 154_2, gap 2. -/
theorem gap2 : rightDomain = Set.Ioi 2 := by
  ext x
  simp only [rightDomain, Set.mem_setOf_eq, Set.mem_Ioi]
  constructor <;> intro h <;> linarith

/-- Exercise 154_2, gap 3. -/
theorem gap3 : domain = Set.Ioi (-2) ∩ Set.Ioi 2 := by
  rw [domain, gap1, gap2]

/-- Exercise 154_2, gap 4. -/
theorem gap4 : Set.Ioi (-2 : ℝ) ∩ Set.Ioi 2 = Set.Ioi 2 := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_Ioi]
  constructor
  · exact fun h => h.2
  · intro h
    constructor <;> linarith

/-- Exercise 154_2, gap 5. -/
theorem gap5 : domain = Set.Ioi 2 := by
  rw [gap3, gap4]

end ProofGap.Exercise154_2
