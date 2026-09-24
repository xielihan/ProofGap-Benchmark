import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise970

noncomputable section

def y (x : ℝ) : ℝ := Real.arccos (1 / Real.cosh x)

def expandedDerivative (x : ℝ) : ℝ :=
  -(1 / Real.sqrt (1 - 1 / Real.cosh x ^ 2)) *
    (-(Real.sinh x / Real.cosh x ^ 2))

def finalDerivative (x : ℝ) : ℝ :=
  Real.sign (Real.sinh x) / Real.cosh x

private lemma hyperbolic_noncritical {x : ℝ} (hx : x ≠ 0) :
    1 < Real.cosh x ∧ Real.sinh x ≠ 0 := by
  have hexp_pos : 0 < Real.exp x := Real.exp_pos x
  have hexp_ne : Real.exp x ≠ 1 := by
    intro hexp
    rcases lt_or_gt_of_ne hx with hxneg | hxpos
    · have hlt : Real.exp x < Real.exp 0 := Real.exp_lt_exp.mpr hxneg
      simpa [hexp] using hlt
    · have hlt : Real.exp 0 < Real.exp x := Real.exp_lt_exp.mpr hxpos
      simpa [hexp] using hlt
  have hdiff_ne : Real.exp x - 1 ≠ 0 := sub_ne_zero.mpr hexp_ne
  have hnum_pos :
      0 < (Real.exp x - 1) * (Real.exp x - 1) :=
    mul_self_pos.mpr hdiff_ne
  have hfrac_pos :
      0 < ((Real.exp x - 1) * (Real.exp x - 1)) /
        (2 * Real.exp x) :=
    div_pos hnum_pos (mul_pos (by norm_num) hexp_pos)
  have halgebra :
      (Real.exp x + (Real.exp x)⁻¹) / 2 - 1 =
        ((Real.exp x - 1) * (Real.exp x - 1)) /
          (2 * Real.exp x) := by
    field_simp [ne_of_gt hexp_pos] <;> ring
  have hcosh_gt : 1 < Real.cosh x := by
    rw [Real.cosh_eq, Real.exp_neg]
    nlinarith [halgebra, hfrac_pos]
  refine ⟨hcosh_gt, ?_⟩
  intro hsinh
  have hidentity := Real.cosh_sq_sub_sinh_sq x
  rw [hsinh] at hidentity
  nlinarith [Real.cosh_pos x]

theorem gap1 (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt y (expandedDerivative x) x := by
  have hcritical := hyperbolic_noncritical hx
  have hcosh_gt : 1 < Real.cosh x := hcritical.1
  have hcosh_pos : 0 < Real.cosh x := Real.cosh_pos x
  have hcosh_ne : Real.cosh x ≠ 0 := ne_of_gt hcosh_pos
  have harg_pos : 0 < 1 / Real.cosh x := one_div_pos.mpr hcosh_pos
  have harg_lt : 1 / Real.cosh x < 1 := by
    apply (div_lt_iff₀ hcosh_pos).2
    simpa using hcosh_gt
  have harg_neg_lt : (-1 : ℝ) < 1 / Real.cosh x :=
    lt_trans (by norm_num) harg_pos
  have harg_ne_neg_one : 1 / Real.cosh x ≠ (-1 : ℝ) := ne_of_gt harg_neg_lt
  have harg_ne_one : 1 / Real.cosh x ≠ (1 : ℝ) := ne_of_lt harg_lt
  have hneg : HasDerivAt (fun t : ℝ => -t) (-1) x := by
    simpa using (hasDerivAt_id x).neg
  have hnegexp :
      HasDerivAt (fun t : ℝ => Real.exp (-t)) (-Real.exp (-x)) x := by
    simpa using (Real.hasDerivAt_exp (-x)).comp x hneg
  have hformula :
      HasDerivAt
        (fun t : ℝ => (Real.exp t + Real.exp (-t)) / 2)
        ((Real.exp x - Real.exp (-x)) / 2) x := by
    simpa [sub_eq_add_neg] using
      ((Real.hasDerivAt_exp x).add hnegexp).div_const (2 : ℝ)
  have hcoshDeriv :
      HasDerivAt (fun t : ℝ => Real.cosh t) (Real.sinh x) x := by
    simpa only [Real.cosh_eq, Real.sinh_eq] using hformula
  have hinnerRaw :=
    (hasDerivAt_const x (1 : ℝ)).div hcoshDeriv hcosh_ne
  have hinnerDeriv :
      HasDerivAt (fun t : ℝ => 1 / Real.cosh t)
        (-(Real.sinh x / Real.cosh x ^ 2)) x := by
    simpa only [zero_mul, one_mul, zero_sub, neg_div] using hinnerRaw
  have harccosDeriv :=
    Real.hasDerivAt_arccos harg_ne_neg_one harg_ne_one
  have hcomp := harccosDeriv.comp x hinnerDeriv
  unfold y expandedDerivative
  simpa [Function.comp_apply, one_div, inv_pow] using hcomp

theorem gap2 (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt y (finalDerivative x) x := by
  have hcritical := hyperbolic_noncritical hx
  have hcosh_pos : 0 < Real.cosh x := Real.cosh_pos x
  have hcosh_ne : Real.cosh x ≠ 0 := ne_of_gt hcosh_pos
  have hsinh_ne : Real.sinh x ≠ 0 := hcritical.2
  have hrad :
      1 - 1 / Real.cosh x ^ 2 =
        (Real.sinh x / Real.cosh x) ^ 2 := by
    field_simp [hcosh_ne]
    nlinarith [Real.cosh_sq_sub_sinh_sq x]
  have hexpanded_eq : expandedDerivative x = finalDerivative x := by
    unfold expandedDerivative finalDerivative
    rcases lt_or_gt_of_ne hsinh_ne with hsinh_neg | hsinh_pos
    · have hquot_neg : Real.sinh x / Real.cosh x < 0 :=
        div_neg_of_neg_of_pos hsinh_neg hcosh_pos
      have hsqrt :
          Real.sqrt (1 - 1 / Real.cosh x ^ 2) =
            -(Real.sinh x / Real.cosh x) := by
        rw [hrad, Real.sqrt_sq_eq_abs, abs_of_neg hquot_neg]
      rw [hsqrt, Real.sign_of_neg hsinh_neg]
      field_simp [hcosh_ne, hsinh_ne]
    · have hquot_pos : 0 < Real.sinh x / Real.cosh x :=
        div_pos hsinh_pos hcosh_pos
      have hsqrt :
          Real.sqrt (1 - 1 / Real.cosh x ^ 2) =
            Real.sinh x / Real.cosh x := by
        rw [hrad, Real.sqrt_sq_eq_abs, abs_of_pos hquot_pos]
      rw [hsqrt, Real.sign_of_pos hsinh_pos]
      field_simp [hcosh_ne, hsinh_ne]
  simpa [hexpanded_eq] using gap1 x hx

end

end ProofGap.Exercise970
