import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Filter Topology

namespace ProofGap.Exercise186

noncomputable section

def y (x : ℝ) : ℝ := Real.sqrt (x - x ^ 2)
def domain : Set ℝ := Set.Icc 0 1
def valueSet : Set ℝ := {t | ∃ x ∈ domain, t = y x}

/-- Source: `proof_gap/exercise_186/1.txt`. -/
theorem gap1 : ∀ x : ℝ,
    y x = Real.sqrt (1 / 4 - (x - 1 / 2) ^ 2) := by
  intro x
  unfold y
  congr 1
  ring

/-- Source: `proof_gap/exercise_186/2.txt`. -/
theorem gap2 : y (1 / 2) = 1 / 2 := by
  rw [gap1]
  norm_num only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, sub_zero]
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 1 / 4 by norm_num)
  have hs0 := Real.sqrt_nonneg (1 / 4)
  nlinarith

/-- Source: `proof_gap/exercise_186/3.txt`. -/
theorem gap3 : Tendsto y (𝓝 0) (𝓝 0) := by
  have hc : ContinuousAt y 0 := by
    unfold y
    fun_prop
  convert hc.tendsto using 1 <;> norm_num [y]

/-- Source: `proof_gap/exercise_186/4.txt`; positivity holds only in the interior. -/
theorem gap4 : ∀ x : ℝ, x ∈ Set.Ioo 0 1 → 0 < y x := by
  intro x hx
  unfold y
  apply Real.sqrt_pos.2
  nlinarith [mul_pos hx.1 (sub_pos.mpr hx.2)]

/-- Source: `proof_gap/exercise_186/5.txt`; remove the shadowed existential y. -/
theorem gap5 : sInf valueSet = 0 := by
  have hleast : IsLeast valueSet 0 := by
    constructor
    · refine ⟨0, ⟨by norm_num, by norm_num⟩, ?_⟩
      norm_num [y]
    · rintro t ⟨x, hx, rfl⟩
      exact Real.sqrt_nonneg _
  exact hleast.csInf_eq

/-- Source: `proof_gap/exercise_186/6.txt`; the natural square-root domain includes both zero endpoints. -/
theorem gap6 : valueSet = Set.Icc 0 (1 / 2) := by
  ext t
  constructor
  · rintro ⟨x, ⟨hx0, hx1⟩, rfl⟩
    constructor
    · exact Real.sqrt_nonneg _
    · rw [gap1]
      apply Real.sqrt_le_iff.mpr
      constructor
      · norm_num
      · nlinarith [sq_nonneg (x - 1 / 2)]
  · rintro ⟨ht0, htmax⟩
    let s : ℝ := Real.sqrt (1 / 4 - t ^ 2)
    let x : ℝ := 1 / 2 - s
    have hrad : 0 ≤ 1 / 4 - t ^ 2 := by nlinarith
    have hs : s ^ 2 = 1 / 4 - t ^ 2 := by
      dsimp [s]
      exact Real.sq_sqrt hrad
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hsmax : s ≤ 1 / 2 := by nlinarith
    have hxdom : x ∈ domain := by
      constructor
      · dsimp [x]
        linarith
      · dsimp [x]
        linarith
    have hpoly : x - x ^ 2 = t ^ 2 := by
      dsimp [x]
      nlinarith
    refine ⟨x, hxdom, ?_⟩
    unfold y
    rw [hpoly, Real.sqrt_sq_eq_abs, abs_of_nonneg ht0]

end

end ProofGap.Exercise186
