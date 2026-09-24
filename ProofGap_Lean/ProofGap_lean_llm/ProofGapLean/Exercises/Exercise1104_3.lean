import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise1104_3

noncomputable section

def Approx (x y ε : ℝ) : Prop := |x - y| < ε

private lemma sqrt120_bounds :
    (109544 / 10000 : ℝ) < Real.sqrt 120 ∧
      Real.sqrt 120 < (109546 / 10000 : ℝ) := by
  have hs0 : 0 ≤ Real.sqrt 120 := Real.sqrt_nonneg 120
  have hsq : (Real.sqrt 120) ^ 2 = 120 :=
    Real.sq_sqrt (by norm_num)
  constructor
  · by_contra h
    have hle : Real.sqrt 120 ≤ (109544 / 10000 : ℝ) := le_of_not_gt h
    have hmul := mul_self_le_mul_self hs0 hle
    nlinarith
  · by_contra h
    have hle : (109546 / 10000 : ℝ) ≤ Real.sqrt 120 := le_of_not_gt h
    have hc : 0 ≤ (109546 / 10000 : ℝ) := by norm_num
    have hmul := mul_self_le_mul_self hc hle
    nlinarith

theorem gap1 (y₀ : ℝ) (hy : 0 < y₀) :
    HasDerivAt Real.sqrt (1 / (2 * Real.sqrt y₀)) y₀ := by
  exact Real.hasDerivAt_sqrt (ne_of_gt hy)

theorem gap2 (a : ℝ) (ha : 0 < a) :
    HasDerivAt (fun x : ℝ => Real.sqrt (a ^ 2 + x))
      (1 / (2 * a)) 0 := by
  have ha2 : 0 < a ^ 2 := by
    nlinarith [sq_nonneg a]
  have hinner : HasDerivAt (fun x : ℝ => a ^ 2 + x) 1 0 :=
    (hasDerivAt_id (0 : ℝ)).const_add (a ^ 2)
  have houter :
      HasDerivAt Real.sqrt
        (1 / (2 * Real.sqrt (a ^ 2 + 0))) (a ^ 2 + 0) :=
    gap1 (a ^ 2 + 0) (by simpa using ha2)
  have hcomp := houter.comp (0 : ℝ) hinner
  simpa [Function.comp_def, Real.sqrt_sq_eq_abs, abs_of_pos ha] using hcomp

theorem gap3 :
    Real.sqrt 120 = Real.sqrt (11 ^ 2 - 1) := by
  norm_num

theorem gap4 :
    Approx (Real.sqrt (11 ^ 2 - 1)) (11 - (1 / (2 * 11) : ℝ))
      (2 / 10000 : ℝ) := by
  unfold Approx
  rw [← gap3, abs_lt]
  obtain ⟨hl, hu⟩ := sqrt120_bounds
  constructor <;> linarith

theorem gap5 :
    Approx (11 - (1 / (2 * 11) : ℝ)) (109546 / 10000 : ℝ)
      (1 / 10000 : ℝ) := by
  unfold Approx
  rw [abs_lt]
  constructor <;> norm_num

theorem gap6 :
    Approx (Real.sqrt 120) (109546 / 10000 : ℝ)
      (2 / 10000 : ℝ) := by
  unfold Approx
  rw [abs_lt]
  obtain ⟨hl, hu⟩ := sqrt120_bounds
  constructor <;> linarith

theorem gap7 :
    Approx (Real.sqrt 120) (109545 / 10000 : ℝ)
      (1 / 10000 : ℝ) := by
  unfold Approx
  rw [abs_lt]
  obtain ⟨hl, hu⟩ := sqrt120_bounds
  constructor <;> linarith

end

end ProofGap.Exercise1104_3
