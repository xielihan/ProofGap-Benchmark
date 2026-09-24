import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1087

noncomputable section

def y (a x : ℝ) : ℝ :=
  (1 / (2 * a)) * Real.log |(x - a) / (x + a)|

def regular (a x : ℝ) : Prop :=
  a ≠ 0 ∧ x - a ≠ 0 ∧ x + a ≠ 0

def differentialAt (a x dx : ℝ) : ℝ := deriv (y a) x * dx

theorem gap1 (a x : ℝ) (h : regular a x) :
    HasDerivAt (y a)
      ((1 / (2 * a)) * (1 / (x - a) - 1 / (x + a))) x := by
  rcases h with ⟨ha, hsub, hadd⟩
  change HasDerivAt
    (fun t : ℝ => (1 / (2 * a)) * Real.log |(t - a) / (t + a)|)
    ((1 / (2 * a)) * (1 / (x - a) - 1 / (x + a))) x
  have hnum : HasDerivAt (fun t : ℝ => t - a) 1 x :=
    (hasDerivAt_id x).sub_const a
  have hden : HasDerivAt (fun t : ℝ => t + a) 1 x :=
    (hasDerivAt_id x).add_const a
  have hquot :
      HasDerivAt (fun t : ℝ => (t - a) / (t + a))
        ((1 * (x + a) - (x - a) * 1) / (x + a) ^ 2) x :=
    hnum.div hden hadd
  have hqne : (x - a) / (x + a) ≠ 0 := div_ne_zero hsub hadd
  have hlog :
      HasDerivAt (fun t : ℝ => Real.log ((t - a) / (t + a)))
        (1 / (x - a) - 1 / (x + a)) x := by
    convert (Real.hasDerivAt_log hqne).comp x hquot using 1
    field_simp [hsub, hadd, hqne]
  simpa only [Real.log_abs] using hlog.const_mul (1 / (2 * a))

theorem gap2 (a x : ℝ) (h : regular a x) :
    (1 / (2 * a)) * (1 / (x - a) - 1 / (x + a)) =
      1 / (x ^ 2 - a ^ 2) := by
  rcases h with ⟨ha, hsub, hadd⟩
  have hquad : x ^ 2 - a ^ 2 ≠ 0 := by
    intro hz
    apply (mul_ne_zero hsub hadd)
    calc
      (x - a) * (x + a) = x ^ 2 - a ^ 2 := by ring
      _ = 0 := hz
  field_simp [ha, hsub, hadd, hquad] <;> ring

theorem gap3 (a x : ℝ) (h : regular a x) :
    HasDerivAt (y a) (1 / (x ^ 2 - a ^ 2)) x := by
  rw [← gap2 a x h]
  exact gap1 a x h

theorem gap4 (a x dx : ℝ) (h : regular a x) :
    differentialAt a x dx = dx / (x ^ 2 - a ^ 2) := by
  unfold differentialAt
  rw [(gap3 a x h).deriv]
  simp only [one_div, div_eq_mul_inv]
  ring

end

end ProofGap.Exercise1087
