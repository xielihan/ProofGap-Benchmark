import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise1104_2

noncomputable section

def Approx (x y ε : ℝ) : Prop := |x - y| < ε

private theorem sqrt34_bounds :
    (58309 / 10000 : ℝ) < Real.sqrt 34 ∧
      Real.sqrt 34 < (5831 / 1000 : ℝ) := by
  have hs : 0 ≤ Real.sqrt (34 : ℝ) := Real.sqrt_nonneg 34
  have hs2 : (Real.sqrt (34 : ℝ)) ^ 2 = 34 :=
    Real.sq_sqrt (by norm_num)
  constructor
  · have hsq : (58309 / 10000 : ℝ) ^ 2 < 34 := by norm_num
    by_contra h
    have hle : Real.sqrt (34 : ℝ) ≤ 58309 / 10000 := le_of_not_gt h
    have hprod :
        (Real.sqrt 34 - 58309 / 10000) *
            (Real.sqrt 34 + 58309 / 10000) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hle) (by nlinarith)
    nlinarith
  · have hsq : 34 < (5831 / 1000 : ℝ) ^ 2 := by norm_num
    by_contra h
    have hle : (5831 / 1000 : ℝ) ≤ Real.sqrt 34 := le_of_not_gt h
    have hprod :
        0 ≤ (Real.sqrt 34 - 5831 / 1000) *
            (Real.sqrt 34 + 5831 / 1000) :=
      mul_nonneg (sub_nonneg.mpr hle) (by nlinarith)
    nlinarith

theorem gap1 (y₀ : ℝ) (hy : 0 < y₀) :
    HasDerivAt Real.sqrt (1 / (2 * Real.sqrt y₀)) y₀ := by
  exact Real.hasDerivAt_sqrt hy.ne'

theorem gap2 (a : ℝ) (ha : 0 < a) :
    HasDerivAt (fun x : ℝ => Real.sqrt (a ^ 2 + x))
      (1 / (2 * a)) 0 := by
  have hinner : HasDerivAt (fun x : ℝ => x + a ^ 2) 1 0 :=
    (hasDerivAt_id (𝕜 := ℝ) (0 : ℝ)).add_const (a ^ 2)
  have houter :
      HasDerivAt Real.sqrt (1 / (2 * Real.sqrt (0 + a ^ 2)))
        (0 + a ^ 2) :=
    Real.hasDerivAt_sqrt (by simp [ha.ne'])
  have hsqrt : Real.sqrt (a ^ 2) = a := by
    rw [Real.sqrt_sq_eq_abs, abs_of_pos ha]
  simpa [Function.comp_def, hsqrt, add_comm] using (houter.comp 0 hinner)

theorem gap3 :
    Real.sqrt 34 = Real.sqrt (6 ^ 2 - 2) := by
  norm_num

theorem gap4 :
    Approx (Real.sqrt (6 ^ 2 - 2)) (6 - (2 / (2 * 6) : ℝ))
      (3 / 1000 : ℝ) := by
  unfold Approx
  have harg : (6 : ℝ) ^ 2 - 2 = 34 := by norm_num
  have hcenter : (6 - (2 / (2 * 6) : ℝ)) = 35 / 6 := by norm_num
  rw [harg, hcenter, abs_lt]
  constructor <;> linarith [sqrt34_bounds.1, sqrt34_bounds.2]

theorem gap5 :
    Approx (6 - (2 / (2 * 6) : ℝ)) (5833 / 1000 : ℝ)
      (1 / 1000 : ℝ) := by
  norm_num [Approx, abs_lt]

theorem gap6 :
    Approx (Real.sqrt 34) (5833 / 1000 : ℝ)
      (3 / 1000 : ℝ) := by
  unfold Approx
  rw [abs_lt]
  constructor <;> linarith [sqrt34_bounds.1, sqrt34_bounds.2]

theorem gap7 :
    Approx (Real.sqrt 34) (5831 / 1000 : ℝ)
      (1 / 1000 : ℝ) := by
  unfold Approx
  rw [abs_lt]
  constructor <;> linarith [sqrt34_bounds.1, sqrt34_bounds.2]

end

end ProofGap.Exercise1104_2
