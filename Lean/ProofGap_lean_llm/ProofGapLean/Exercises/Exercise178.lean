import ProofGapLean.Prelude.Sequences
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise178

def y (x : ℝ) : ℝ := x ^ 2
def domain : Set ℝ := Set.Icc 1 2
def valueSet : Set ℝ := {t | ∃ x ∈ domain, t = y x}

/-- Exercise 178, gap 1. -/
theorem gap1 : ContinuousOn y domain := by
  exact (continuous_id.pow 2).continuousOn

/-- Exercise 178, gap 2. -/
theorem gap2 : MonotoneOn y domain := by
  intro a ha b hb hab
  change a ∈ Set.Icc (1 : ℝ) 2 at ha
  change b ∈ Set.Icc (1 : ℝ) 2 at hb
  unfold y
  nlinarith [ha.1, hb.1]

/-- Exercise 178, gap 3. -/
theorem gap3 : y 1 = 1 := by
  norm_num [y]

/-- Exercise 178, gap 4. -/
theorem gap4 : y 2 = 4 := by
  norm_num [y]

/-- Exercise 178, gap 5; replace the free family `E_x` by the stated domain. -/
theorem gap5 : valueSet = Set.Icc 1 4 := by
  ext t
  constructor
  · rintro ⟨x, ⟨hxlo, hxhi⟩, rfl⟩
    unfold y
    constructor <;> nlinarith
  · rintro ⟨htlo, hthi⟩
    have ht0 : 0 ≤ t := by linarith
    have hsqrt0 := Real.sqrt_nonneg t
    have hsqrt_sq := Real.sq_sqrt ht0
    have hsqrtlo : 1 ≤ Real.sqrt t := by nlinarith
    have hsqrthi : Real.sqrt t ≤ 2 := by nlinarith
    refine ⟨Real.sqrt t, ⟨hsqrtlo, hsqrthi⟩, ?_⟩
    unfold y
    exact hsqrt_sq.symm

end ProofGap.Exercise178
