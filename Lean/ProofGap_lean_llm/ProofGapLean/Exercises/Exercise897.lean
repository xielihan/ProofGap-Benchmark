import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise897

noncomputable section

def asinhArg (x : ℝ) : ℝ := x + Real.sqrt (1 + x ^ 2)
def y (x : ℝ) : ℝ :=
  x * Real.log (asinhArg x) ^ 2 -
    2 * Real.sqrt (1 + x ^ 2) * Real.log (asinhArg x) + 2 * x

def expandedDerivative (x : ℝ) : ℝ :=
  Real.log (asinhArg x) ^ 2 +
    (2 * x / Real.sqrt (1 + x ^ 2)) * Real.log (asinhArg x) -
    (2 * x / Real.sqrt (1 + x ^ 2)) * Real.log (asinhArg x) -
    2 * Real.sqrt (1 + x ^ 2) * (1 / Real.sqrt (1 + x ^ 2)) + 2

def finalDerivative (x : ℝ) : ℝ := Real.log (asinhArg x) ^ 2

theorem gap1 (x : ℝ) : deriv y x = expandedDerivative x := by
  have hqpos : 0 < 1 + x ^ 2 := by positivity
  have hqne : 1 + x ^ 2 ≠ 0 := ne_of_gt hqpos
  have hsne : Real.sqrt (1 + x ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hqpos)
  have hsq : Real.sqrt (1 + x ^ 2) ^ 2 = 1 + x ^ 2 :=
    Real.sq_sqrt (le_of_lt hqpos)
  have hprod :
      (x + Real.sqrt (1 + x ^ 2)) *
          (Real.sqrt (1 + x ^ 2) - x) = 1 := by
    calc
      (x + Real.sqrt (1 + x ^ 2)) *
          (Real.sqrt (1 + x ^ 2) - x) =
          Real.sqrt (1 + x ^ 2) ^ 2 - x ^ 2 := by ring
      _ = 1 := by rw [hsq]; ring
  have ha : x + Real.sqrt (1 + x ^ 2) ≠ 0 := by
    intro h
    rw [h] at hprod
    norm_num at hprod
  have hargne : asinhArg x ≠ 0 := by
    simpa [asinhArg] using ha
  have hinner :
      HasDerivAt (fun t : ℝ => 1 + t ^ 2) (2 * x) x := by
    convert
      (hasDerivAt_const (x := x) (c := (1 : ℝ))).add
        ((hasDerivAt_id x).pow 2) using 1 <;>
      norm_num <;> ring
  have hsqrt_exp (t : ℝ) :
      Real.sqrt (1 + t ^ 2) =
        Real.exp (Real.log (1 + t ^ 2) / 2) := by
    have htpos : 0 < 1 + t ^ 2 := by positivity
    have htsq : Real.sqrt (1 + t ^ 2) ^ 2 = 1 + t ^ 2 :=
      Real.sq_sqrt (le_of_lt htpos)
    have hexpsq :
        Real.exp (Real.log (1 + t ^ 2) / 2) ^ 2 = 1 + t ^ 2 := by
      calc
        Real.exp (Real.log (1 + t ^ 2) / 2) ^ 2 =
            Real.exp
              (Real.log (1 + t ^ 2) / 2 +
                Real.log (1 + t ^ 2) / 2) := by
              rw [pow_two, ← Real.exp_add]
        _ = Real.exp (Real.log (1 + t ^ 2)) := by
              congr 1
              ring
        _ = 1 + t ^ 2 := Real.exp_log htpos
    have hsnonneg : 0 ≤ Real.sqrt (1 + t ^ 2) := Real.sqrt_nonneg _
    have hepos : 0 < Real.exp (Real.log (1 + t ^ 2) / 2) := Real.exp_pos _
    nlinarith
  have hlogq :
      HasDerivAt (fun t : ℝ => Real.log (1 + t ^ 2))
        (2 * x / (1 + x ^ 2)) x := by
    convert (Real.hasDerivAt_log hqne).comp x hinner using 1
    ring
  have hhalf :
      HasDerivAt (fun t : ℝ => Real.log (1 + t ^ 2) / 2)
        (x / (1 + x ^ 2)) x := by
    convert hlogq.const_mul (1 / 2 : ℝ) using 1 <;>
      ring
  have hexp :
      HasDerivAt
        (fun t : ℝ => Real.exp (Real.log (1 + t ^ 2) / 2))
        (Real.exp (Real.log (1 + x ^ 2) / 2) *
          (x / (1 + x ^ 2))) x := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_exp (Real.log (1 + x ^ 2) / 2)).comp x hhalf
  have hcoef :
      Real.exp (Real.log (1 + x ^ 2) / 2) *
          (x / (1 + x ^ 2)) =
        x / Real.sqrt (1 + x ^ 2) := by
    rw [← hsqrt_exp x]
    calc
      Real.sqrt (1 + x ^ 2) * (x / (1 + x ^ 2)) =
          Real.sqrt (1 + x ^ 2) *
            (x / Real.sqrt (1 + x ^ 2) ^ 2) := by rw [hsq]
      _ = x / Real.sqrt (1 + x ^ 2) := by
        field_simp [hsne] <;> ring
  have hsqrt :
      HasDerivAt (fun t : ℝ => Real.sqrt (1 + t ^ 2))
        (x / Real.sqrt (1 + x ^ 2)) x := by
    have hfun :
        (fun t : ℝ => Real.sqrt (1 + t ^ 2)) =
          (fun t : ℝ => Real.exp (Real.log (1 + t ^ 2) / 2)) := by
      funext t
      exact hsqrt_exp t
    rw [hfun]
    simpa only [hcoef] using hexp
  have harg :
      HasDerivAt asinhArg
        (1 + x / Real.sqrt (1 + x ^ 2)) x := by
    simpa [asinhArg] using (hasDerivAt_id x).add hsqrt
  have hlog :
      HasDerivAt (fun t : ℝ => Real.log (asinhArg t))
        (1 / Real.sqrt (1 + x ^ 2)) x := by
    convert (Real.hasDerivAt_log hargne).comp x harg using 1 <;>
      simp [asinhArg] <;>
      field_simp [ha, hsne, hargne] <;>
      ring
  have hfirst := (hasDerivAt_id x).mul (hlog.pow 2)
  have hsecond := (hsqrt.const_mul 2).mul hlog
  have hthird := (hasDerivAt_id x).const_mul 2
  have htotal := (hfirst.sub hsecond).add hthird
  have hy : HasDerivAt y (expandedDerivative x) x := by
    convert htotal using 1 <;>
      simp [expandedDerivative] <;>
      ring
  exact hy.deriv
theorem gap2 (x : ℝ) : expandedDerivative x = finalDerivative x := by
  unfold expandedDerivative finalDerivative
  have hqpos : 0 < 1 + x ^ 2 := by positivity
  have hsne : Real.sqrt (1 + x ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hqpos)
  field_simp [hsne] <;> ring
theorem gap3 (x : ℝ) : deriv y x = finalDerivative x := by
  rw [gap1 x, gap2 x]

end

end ProofGap.Exercise897
