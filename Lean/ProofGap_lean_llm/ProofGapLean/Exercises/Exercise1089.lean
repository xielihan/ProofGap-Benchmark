import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1089

noncomputable section

def y (a x : ℝ) : ℝ := Real.arcsin (x / a)
def regular (a x : ℝ) : Prop := a ≠ 0 ∧ x ^ 2 < a ^ 2
def differentialAt (a x dx : ℝ) : ℝ := deriv (y a) x * dx

private theorem Real.sign_ofNegative {a : ℝ} (h : a < 0) :
    Real.sign a = -1 := by
  simp [Real.sign, h]

private theorem Real.sign_ofPositive {a : ℝ} (h : 0 < a) :
    Real.sign a = 1 := by
  have hn : ¬a < 0 := not_lt_of_ge (le_of_lt h)
  simp [Real.sign, hn, h]

theorem gap1 (a x : ℝ) (h : regular a x) :
    HasDerivAt (y a)
      ((|a| / Real.sqrt (a ^ 2 - x ^ 2)) * (1 / a)) x := by
  rcases h with ⟨ha, hsq⟩
  have ha_sq : 0 < a ^ 2 := by
    simpa [pow_two] using (mul_self_pos.mpr ha)
  have hquot_sq : (x / a) ^ 2 < 1 := by
    rw [div_pow]
    exact (div_lt_one ha_sq).2 hsq
  have hquot : x / a ∈ Set.Ioo (-1) 1 := by
    constructor <;>
      nlinarith [sq_nonneg (x / a - 1), sq_nonneg (x / a + 1)]
  have hne_neg : x / a ≠ -1 := ne_of_gt hquot.1
  have hne_pos : x / a ≠ 1 := ne_of_lt hquot.2
  have hrad : 0 < 1 - (x / a) ^ 2 := sub_pos.mpr hquot_sq
  have hdiff : 0 < a ^ 2 - x ^ 2 := sub_pos.mpr hsq
  have hrel :
      a ^ 2 * (1 - (x / a) ^ 2) = a ^ 2 - x ^ 2 := by
    field_simp [ha] <;> ring
  have hscale :
      |a| * Real.sqrt (1 - (x / a) ^ 2) =
        Real.sqrt (a ^ 2 - x ^ 2) := by
    calc
      |a| * Real.sqrt (1 - (x / a) ^ 2) =
          Real.sqrt (a ^ 2) * Real.sqrt (1 - (x / a) ^ 2) := by
            rw [Real.sqrt_sq_eq_abs]
      _ = Real.sqrt (a ^ 2 * (1 - (x / a) ^ 2)) := by
            rw [Real.sqrt_mul (sq_nonneg a)]
      _ = Real.sqrt (a ^ 2 - x ^ 2) := by rw [hrel]
  have hcoef :
      1 / Real.sqrt (1 - (x / a) ^ 2) =
        |a| / Real.sqrt (a ^ 2 - x ^ 2) := by
    apply (div_eq_div_iff
      (ne_of_gt (Real.sqrt_pos.2 hrad))
      (ne_of_gt (Real.sqrt_pos.2 hdiff))).2
    simpa using hscale.symm
  have hchain :
      HasDerivAt (fun z : ℝ => Real.arcsin (z / a))
        ((1 / Real.sqrt (1 - (x / a) ^ 2)) * (1 / a)) x := by
    simpa using
      ((Real.hasDerivAt_arcsin hne_neg hne_pos).comp x
        ((hasDerivAt_id x).div_const a))
  simpa only [y, hcoef] using hchain

theorem gap2 (a x : ℝ) (h : regular a x) :
    (|a| / Real.sqrt (a ^ 2 - x ^ 2)) * (1 / a) =
      Real.sign a / Real.sqrt (a ^ 2 - x ^ 2) := by
  rcases h with ⟨ha, _⟩
  have hsign : |a| * (1 / a) = Real.sign a := by
    rcases lt_or_gt_of_ne ha with ha_neg | ha_pos
    · rw [abs_of_neg ha_neg, Real.sign_ofNegative ha_neg]
      field_simp [ha] <;> ring
    · rw [abs_of_pos ha_pos, Real.sign_ofPositive ha_pos]
      field_simp [ha] <;> ring
  calc
    (|a| / Real.sqrt (a ^ 2 - x ^ 2)) * (1 / a) =
        (|a| * (1 / a)) / Real.sqrt (a ^ 2 - x ^ 2) := by ring
    _ = Real.sign a / Real.sqrt (a ^ 2 - x ^ 2) := by rw [hsign]

theorem gap3 (a x : ℝ) (h : regular a x) :
    HasDerivAt (y a)
      (Real.sign a / Real.sqrt (a ^ 2 - x ^ 2)) x := by
  simpa only [gap2 a x h] using gap1 a x h

theorem gap4 (a x dx : ℝ) (h : regular a x) :
    differentialAt a x dx =
      Real.sign a / Real.sqrt (a ^ 2 - x ^ 2) * dx := by
  unfold differentialAt
  rw [(gap3 a x h).deriv]

end

end ProofGap.Exercise1089
