import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise960

noncomputable section

def y (x : ℝ) : ℝ :=
  Real.arctan (Real.exp x) -
    Real.log (Real.sqrt (Real.exp (2 * x) / (Real.exp (2 * x) + 1)))

def expandedDerivative (x : ℝ) : ℝ :=
  Real.exp x / (1 + Real.exp (2 * x)) -
    (1 / 2 : ℝ) * (2 - 2 * Real.exp (2 * x) / (Real.exp (2 * x) + 1))

def finalDerivative (x : ℝ) : ℝ :=
  (Real.exp x - 1) / (Real.exp (2 * x) + 1)

theorem gap1 (x : ℝ) : HasDerivAt y (expandedDerivative x) x := by
  have h_exp_two :
      Real.exp (2 * x) = Real.exp x * Real.exp x := by
    rw [show 2 * x = x + x by ring, Real.exp_add]
  have h_atan :
      HasDerivAt (fun t : ℝ => Real.arctan (Real.exp t))
        (Real.exp x / (1 + Real.exp (2 * x))) x := by
    convert
      (Real.hasDerivAt_arctan (x := Real.exp x)).comp x
        (Real.hasDerivAt_exp (x := x)) using 1 <;>
      simp only [h_exp_two] <;>
      ring
  have h_linear : HasDerivAt (fun t : ℝ => 2 * t) 2 x := by
    convert (hasDerivAt_id x).const_mul (2 : ℝ) using 1 <;> ring
  have h_exp :
      HasDerivAt (fun t : ℝ => Real.exp (2 * t))
        (2 * Real.exp (2 * x)) x := by
    convert
      (Real.hasDerivAt_exp (x := 2 * x)).comp x h_linear using 1 <;>
      ring
  have h_den :
      HasDerivAt (fun t : ℝ => Real.exp (2 * t) + 1)
        (2 * Real.exp (2 * x)) x := by
    convert
      h_exp.add (hasDerivAt_const (x := x) (c := (1 : ℝ))) using 1 <;>
      ring
  have hden_pos : 0 < Real.exp (2 * x) + 1 :=
    add_pos (Real.exp_pos _) zero_lt_one
  have hden_ne : Real.exp (2 * x) + 1 ≠ 0 := ne_of_gt hden_pos
  have h_log_den :
      HasDerivAt (fun t : ℝ => Real.log (Real.exp (2 * t) + 1))
        (2 * Real.exp (2 * x) / (Real.exp (2 * x) + 1)) x := by
    exact h_den.log hden_ne
  have hy_eq :
      y = fun t : ℝ =>
        Real.arctan (Real.exp t) -
          (t - (1 / 2 : ℝ) * Real.log (Real.exp (2 * t) + 1)) := by
    funext t
    unfold y
    have ht_den_pos : 0 < Real.exp (2 * t) + 1 :=
      add_pos (Real.exp_pos _) zero_lt_one
    have ht_den_ne : Real.exp (2 * t) + 1 ≠ 0 := ne_of_gt ht_den_pos
    have ht_ratio_pos :
        0 < Real.exp (2 * t) / (Real.exp (2 * t) + 1) :=
      div_pos (Real.exp_pos _) ht_den_pos
    have ht_num_ne : Real.exp (2 * t) ≠ 0 := ne_of_gt (Real.exp_pos _)
    rw [Real.log_sqrt (le_of_lt ht_ratio_pos)]
    rw [Real.log_div ht_num_ne ht_den_ne, Real.log_exp]
    ring
  have h_half_log :
      HasDerivAt
        (fun t : ℝ => (1 / 2 : ℝ) * Real.log (Real.exp (2 * t) + 1))
        ((1 / 2 : ℝ) *
          (2 * Real.exp (2 * x) / (Real.exp (2 * x) + 1))) x :=
    h_log_den.const_mul (1 / 2 : ℝ)
  have h_alt :
      HasDerivAt
        (fun t : ℝ =>
          Real.arctan (Real.exp t) -
            (t - (1 / 2 : ℝ) * Real.log (Real.exp (2 * t) + 1)))
        (Real.exp x / (1 + Real.exp (2 * x)) -
          (1 - (1 / 2 : ℝ) *
            (2 * Real.exp (2 * x) / (Real.exp (2 * x) + 1)))) x :=
    h_atan.sub ((hasDerivAt_id x).sub h_half_log)
  have hleft_ne : 1 + Real.exp (2 * x) ≠ 0 :=
    ne_of_gt (add_pos zero_lt_one (Real.exp_pos _))
  have hcoeff :
      Real.exp x / (1 + Real.exp (2 * x)) -
          (1 - (1 / 2 : ℝ) *
            (2 * Real.exp (2 * x) / (Real.exp (2 * x) + 1))) =
        expandedDerivative x := by
    unfold expandedDerivative
    field_simp [hleft_ne, hden_ne]
  rw [hy_eq, ← hcoeff]
  exact h_alt

theorem gap2 (x : ℝ) : expandedDerivative x = finalDerivative x := by
  unfold expandedDerivative finalDerivative
  have h_exp_pos : 0 < Real.exp (2 * x) := Real.exp_pos _
  have h_left : 1 + Real.exp (2 * x) ≠ 0 :=
    ne_of_gt (add_pos zero_lt_one h_exp_pos)
  have h_right : Real.exp (2 * x) + 1 ≠ 0 :=
    ne_of_gt (add_pos h_exp_pos zero_lt_one)
  field_simp [h_left, h_right] <;> ring

theorem gap3 (x : ℝ) : HasDerivAt y (finalDerivative x) x := by
  simpa only [gap2 x] using gap1 x

end

end ProofGap.Exercise960
