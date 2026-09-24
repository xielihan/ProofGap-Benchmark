import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise450

noncomputable section

def root (n : ℕ) (x : ℝ) : ℝ := Real.rpow x (1 / (n : ℝ))
def f (x : ℝ) : ℝ :=
  (root 3 (1 + x / 3) - root 4 (1 + x / 4)) /
    (1 - Real.sqrt (1 - x / 2))
def HasLimitAt (g : ℝ → ℝ) (a L : ℝ) : Prop :=
  Filter.Tendsto g (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds L)

/-- Source: `proof_gap/exercise_450/1.txt`; encode the radical expression without ellipses. -/
private theorem exercise450_limit : HasLimitAt f 0 (7 / 36) := by
  let g : ℝ → ℝ := fun x =>
    root 3 (1 + x / 3) - root 4 (1 + x / 4)
  let h : ℝ → ℝ := fun x => 1 - Real.sqrt (1 - x / 2)

  have hi3 : HasDerivAt (fun x : ℝ => 1 + x / 3) (1 / 3) 0 := by
    convert
      ((hasDerivAt_id (x := (0 : ℝ))).div_const (3 : ℝ)).const_add (1 : ℝ)
      using 1 <;> norm_num
  have hi4 : HasDerivAt (fun x : ℝ => 1 + x / 4) (1 / 4) 0 := by
    convert
      ((hasDerivAt_id (x := (0 : ℝ))).div_const (4 : ℝ)).const_add (1 : ℝ)
      using 1 <;> norm_num

  have ho3 : HasDerivAt (fun y : ℝ => root 3 y) (1 / 3) 1 := by
    simpa [root] using
      (Real.hasDerivAt_rpow_const (x := (1 : ℝ)) (p := (1 / (3 : ℝ))) (by norm_num))
  have ho4 : HasDerivAt (fun y : ℝ => root 4 y) (1 / 4) 1 := by
    simpa [root] using
      (Real.hasDerivAt_rpow_const (x := (1 : ℝ)) (p := (1 / (4 : ℝ))) (by norm_num))
  have ho3_at :
      HasDerivAt (fun y : ℝ => root 3 y) (1 / 3) (1 + (0 : ℝ) / 3) := by
    simpa only [zero_div, add_zero] using ho3
  have ho4_at :
      HasDerivAt (fun y : ℝ => root 4 y) (1 / 4) (1 + (0 : ℝ) / 4) := by
    simpa only [zero_div, add_zero] using ho4

  have hd3 : HasDerivAt (fun x : ℝ => root 3 (1 + x / 3)) (1 / 9) 0 := by
    convert ho3_at.comp 0 hi3 using 1 <;> norm_num
  have hd4 : HasDerivAt (fun x : ℝ => root 4 (1 + x / 4)) (1 / 16) 0 := by
    convert ho4_at.comp 0 hi4 using 1 <;> norm_num
  have hg : HasDerivAt g (7 / 144) 0 := by
    dsimp [g]
    convert hd3.sub hd4 using 1 <;> norm_num

  have hii : HasDerivAt (fun x : ℝ => 1 - x / 2) (-1 / 2) 0 := by
    convert
      ((hasDerivAt_id (x := (0 : ℝ))).div_const (2 : ℝ)).const_sub (1 : ℝ)
      using 1 <;> norm_num
  have hos : HasDerivAt Real.sqrt (1 / 2) 1 := by
    simpa using Real.hasDerivAt_sqrt (show (1 : ℝ) ≠ 0 by norm_num)
  have hos_at : HasDerivAt Real.sqrt (1 / 2) (1 - (0 : ℝ) / 2) := by
    simpa only [zero_div, sub_zero] using hos
  have hds : HasDerivAt (fun x : ℝ => Real.sqrt (1 - x / 2)) (-1 / 4) 0 := by
    convert hos_at.comp 0 hii using 1 <;> norm_num
  have hh : HasDerivAt h (1 / 4) 0 := by
    dsimp [h]
    convert hds.const_sub (1 : ℝ) using 1 <;> norm_num

  have hg0 : g 0 = 0 := by
    norm_num [g, root]
  have hh0 : h 0 = 0 := by
    norm_num [h]

  have hglim :
      Filter.Tendsto
        (fun x : ℝ => (x - 0)⁻¹ * (g x - g 0))
        (nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ)
        (nhds (7 / 144)) := by
    exact (hasDerivAt_iff_tendsto_slope).1 hg
  have hhlim :
      Filter.Tendsto
        (fun x : ℝ => (x - 0)⁻¹ * (h x - h 0))
        (nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ)
        (nhds (1 / 4)) := by
    exact (hasDerivAt_iff_tendsto_slope).1 hh
  have hquot := hglim.div hhlim (show (1 / 4 : ℝ) ≠ 0 by norm_num)

  have heq :
      (fun x : ℝ =>
          (x - 0)⁻¹ * (g x - g 0) /
            ((x - 0)⁻¹ * (h x - h 0))) =ᶠ[
        nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ] f := by
    apply Filter.Eventually.of_forall
    intro x
    rw [hg0, hh0]
    simp only [sub_zero]
    change (x⁻¹ * g x) / (x⁻¹ * h x) = g x / h x
    by_cases hx0 : x = 0
    · subst x
      simp [hg0, hh0]
    · by_cases hhx : h x = 0
      · simp [hhx]
      · field_simp [hx0, hhx]
        <;> ring

  unfold HasLimitAt
  convert hquot.congr' heq using 1 <;> norm_num

theorem gap1 : HasLimitAt f 0 (7 / 36) := by
  exact exercise450_limit

/-- Source: `proof_gap/exercise_450/2.txt`. -/
theorem gap2 : HasLimitAt f 0 (7 / 36) := by
  exact exercise450_limit

end

end ProofGap.Exercise450
