import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise951

noncomputable section

def y (x : ℝ) : ℝ :=
  Real.log (Real.exp x + Real.sqrt (1 + Real.exp (2 * x)))

def expandedDerivative (x : ℝ) : ℝ :=
  (Real.exp x + Real.exp (2 * x) / Real.sqrt (1 + Real.exp (2 * x))) /
    (Real.exp x + Real.sqrt (1 + Real.exp (2 * x)))

def finalDerivative (x : ℝ) : ℝ :=
  Real.exp x / Real.sqrt (1 + Real.exp (2 * x))

private theorem expandedDerivative_eq_final (x : ℝ) :
    expandedDerivative x = finalDerivative x := by
  unfold expandedDerivative finalDerivative
  have hexp2 : Real.exp (2 * x) = Real.exp x * Real.exp x := by
    rw [show 2 * x = x + x by ring, Real.exp_add]
  rw [hexp2]
  have hexp : 0 < Real.exp x := Real.exp_pos x
  have hrad : 0 < 1 + Real.exp x * Real.exp x :=
    add_pos zero_lt_one (mul_pos hexp hexp)
  have hsqrt : 0 < Real.sqrt (1 + Real.exp x * Real.exp x) :=
    Real.sqrt_pos.2 hrad
  have hden :
      0 < Real.exp x + Real.sqrt (1 + Real.exp x * Real.exp x) :=
    add_pos hexp hsqrt
  field_simp [ne_of_gt hsqrt, ne_of_gt hden] <;> ring

theorem gap1 (x : ℝ) : HasDerivAt y (expandedDerivative x) x := by
  have hsqrt_alt (t : ℝ) :
      Real.sqrt (1 + Real.exp (2 * t)) =
        Real.exp ((1 / 2 : ℝ) * Real.log (1 + Real.exp (2 * t))) := by
    have hrad_t : 0 < 1 + Real.exp (2 * t) :=
      add_pos zero_lt_one (Real.exp_pos (2 * t))
    have hsquare :
        (Real.sqrt (1 + Real.exp (2 * t))) ^ 2 = 1 + Real.exp (2 * t) :=
      Real.sq_sqrt (le_of_lt hrad_t)
    have he_square :
        (Real.exp ((1 / 2 : ℝ) * Real.log (1 + Real.exp (2 * t)))) ^ 2 =
          1 + Real.exp (2 * t) := by
      rw [pow_two, ← Real.exp_add]
      rw [show
        (1 / 2 : ℝ) * Real.log (1 + Real.exp (2 * t)) +
            (1 / 2 : ℝ) * Real.log (1 + Real.exp (2 * t)) =
          Real.log (1 + Real.exp (2 * t)) by ring]
      exact Real.exp_log hrad_t
    have hs_nonneg := Real.sqrt_nonneg (1 + Real.exp (2 * t))
    have he_pos :=
      Real.exp_pos ((1 / 2 : ℝ) * Real.log (1 + Real.exp (2 * t)))
    nlinarith
  have hy : y = fun t : ℝ =>
      Real.log
        (Real.exp t +
          Real.exp ((1 / 2 : ℝ) * Real.log (1 + Real.exp (2 * t)))) := by
    funext t
    unfold y
    rw [hsqrt_alt t]
  have hrad : 0 < 1 + Real.exp (2 * x) :=
    add_pos zero_lt_one (Real.exp_pos (2 * x))
  have hsqrt : 0 < Real.sqrt (1 + Real.exp (2 * x)) :=
    Real.sqrt_pos.2 hrad
  have hden :
      0 < Real.exp x + Real.sqrt (1 + Real.exp (2 * x)) :=
    add_pos (Real.exp_pos x) hsqrt
  have h_linear : HasDerivAt (fun t : ℝ => 2 * t) 2 x := by
    convert (hasDerivAt_id x).const_mul 2 using 1 <;> ring
  have h_exp2 :
      HasDerivAt (fun t : ℝ => Real.exp (2 * t))
        (2 * Real.exp (2 * x)) x := by
    convert (Real.hasDerivAt_exp (2 * x)).comp x h_linear using 1 <;> ring
  have h_rad :
      HasDerivAt (fun t : ℝ => 1 + Real.exp (2 * t))
        (2 * Real.exp (2 * x)) x := by
    simpa only [zero_add] using
      (hasDerivAt_const x (1 : ℝ)).add h_exp2
  have h_log_rad :
      HasDerivAt (fun t : ℝ => Real.log (1 + Real.exp (2 * t)))
        ((2 * Real.exp (2 * x)) / (1 + Real.exp (2 * x))) x :=
    h_rad.log (ne_of_gt hrad)
  have h_half :
      HasDerivAt
        (fun t : ℝ =>
          (1 / 2 : ℝ) * Real.log (1 + Real.exp (2 * t)))
        ((1 / 2 : ℝ) *
          ((2 * Real.exp (2 * x)) / (1 + Real.exp (2 * x)))) x :=
    h_log_rad.const_mul (1 / 2 : ℝ)
  have h_alt_sqrt :
      HasDerivAt
        (fun t : ℝ =>
          Real.exp ((1 / 2 : ℝ) * Real.log (1 + Real.exp (2 * t))))
        (Real.exp ((1 / 2 : ℝ) * Real.log (1 + Real.exp (2 * x))) *
          ((1 / 2 : ℝ) *
            ((2 * Real.exp (2 * x)) / (1 + Real.exp (2 * x))))) x := by
    simpa only [Function.comp_apply] using
      (Real.hasDerivAt_exp
        ((1 / 2 : ℝ) * Real.log (1 + Real.exp (2 * x)))).comp x h_half
  have h_sum :
      HasDerivAt
        (fun t : ℝ =>
          Real.exp t +
            Real.exp ((1 / 2 : ℝ) * Real.log (1 + Real.exp (2 * t))))
        (Real.exp x +
          Real.exp ((1 / 2 : ℝ) * Real.log (1 + Real.exp (2 * x))) *
            ((1 / 2 : ℝ) *
              ((2 * Real.exp (2 * x)) / (1 + Real.exp (2 * x))))) x :=
    (Real.hasDerivAt_exp x).add h_alt_sqrt
  have hsum_pos :
      0 < Real.exp x +
        Real.exp ((1 / 2 : ℝ) * Real.log (1 + Real.exp (2 * x))) :=
    add_pos (Real.exp_pos x)
      (Real.exp_pos ((1 / 2 : ℝ) * Real.log (1 + Real.exp (2 * x))))
  have h_outer :
      HasDerivAt
        (fun t : ℝ =>
          Real.log
            (Real.exp t +
              Real.exp ((1 / 2 : ℝ) * Real.log (1 + Real.exp (2 * t)))))
        ((Real.exp x +
            Real.exp ((1 / 2 : ℝ) * Real.log (1 + Real.exp (2 * x))) *
              ((1 / 2 : ℝ) *
                ((2 * Real.exp (2 * x)) / (1 + Real.exp (2 * x))))) /
          (Real.exp x +
            Real.exp ((1 / 2 : ℝ) * Real.log (1 + Real.exp (2 * x))))) x :=
    h_sum.log (ne_of_gt hsum_pos)
  rw [expandedDerivative_eq_final, hy]
  unfold finalDerivative
  convert h_outer using 1
  rw [← hsqrt_alt x]
  have hexp2 : Real.exp (2 * x) = Real.exp x * Real.exp x := by
    rw [show 2 * x = x + x by ring, Real.exp_add]
  have hsquare :
      (Real.sqrt (1 + Real.exp (2 * x))) ^ 2 = 1 + Real.exp (2 * x) :=
    Real.sq_sqrt (le_of_lt hrad)
  field_simp [ne_of_gt hrad, ne_of_gt hsqrt, ne_of_gt hden] <;>
    nlinarith [hsquare, hexp2]

theorem gap2 (x : ℝ) : expandedDerivative x = finalDerivative x := by
  exact expandedDerivative_eq_final x

theorem gap3 (x : ℝ) : HasDerivAt y (finalDerivative x) x := by
  simpa only [gap2] using gap1 x

end

end ProofGap.Exercise951
