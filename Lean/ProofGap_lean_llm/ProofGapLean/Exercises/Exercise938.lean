import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise938

noncomputable section

def s (x : ℝ) : ℝ :=
  Real.sqrt (1 - x ^ 2)

def y (x : ℝ) : ℝ :=
  Real.arccos x / x +
    (1 / 2) * Real.log ((1 - s x) / (1 + s x))

def expandedDerivative (x : ℝ) : ℝ :=
  ((-x / s x) - Real.arccos x) / x ^ 2 +
    (1 / 2) *
      ((x / s x) / (1 - s x) + (x / s x) / (1 + s x))

def finalDerivative (x : ℝ) : ℝ :=
  -Real.arccos x / x ^ 2

/-- Source: `proof_gap/exercise_938/1.txt`; require `|x| < 1` for the
square-root and arccosine derivatives and `x ≠ 0` for the quotient and
positive logarithm argument. -/
private lemma s_interval_facts (x : ℝ) (hinside : |x| < 1) (hx : x ≠ 0) :
    0 < 1 - x ^ 2 ∧
      0 < s x ∧
      (s x) ^ 2 = 1 - x ^ 2 ∧
      1 - s x ≠ 0 ∧
      1 + s x ≠ 0 := by
  rcases abs_lt.mp hinside with ⟨hxlow, hxhigh⟩
  have hprod : 0 < (1 - x) * (1 + x) :=
    mul_pos (sub_pos.mpr hxhigh) (by linarith)
  have hrad : 0 < 1 - x ^ 2 := by
    nlinarith [hprod]
  have hspos : 0 < s x := by
    simpa only [s] using Real.sqrt_pos.2 hrad
  have hsq : (s x) ^ 2 = 1 - x ^ 2 := by
    simpa only [s] using Real.sq_sqrt (le_of_lt hrad)
  have hsm : 1 - s x ≠ 0 := by
    intro hzero
    apply hx
    nlinarith [hsq, sq_nonneg x]
  have hsp : 1 + s x ≠ 0 := ne_of_gt (by linarith)
  exact ⟨hrad, hspos, hsq, hsm, hsp⟩

theorem gap1 (x : ℝ) (hinside : |x| < 1) (hx : x ≠ 0) :
    HasDerivAt y (expandedDerivative x) x := by
  rcases s_interval_facts x hinside hx with
    ⟨hrad, hspos, hsq, hsm, hsp⟩
  have hsne : s x ≠ 0 := ne_of_gt hspos
  have hinner :
      HasDerivAt (fun z : ℝ => 1 - z ^ 2) (-2 * x) x := by
    convert
      (hasDerivAt_const x (1 : ℝ)).sub
        ((hasDerivAt_id x).mul (hasDerivAt_id x)) using 1
    · ext z
      simp [pow_two]
    · simp only [id_eq]
      ring
  have hsderiv : HasDerivAt s (-x / s x) x := by
    convert
      (Real.hasDerivAt_sqrt (ne_of_gt hrad)).comp x hinner using 1 <;>
      simp only [s] <;>
      field_simp [hsne] <;>
      ring
  have hxm1 : x ≠ (-1 : ℝ) :=
    ne_of_gt (abs_lt.mp hinside).1
  have hxp1 : x ≠ (1 : ℝ) :=
    ne_of_lt (abs_lt.mp hinside).2
  have hacos : HasDerivAt Real.arccos (-1 / s x) x := by
    simpa only [s, neg_div] using
      (Real.hasDerivAt_arccos hxm1 hxp1)
  have hfirst :
      HasDerivAt (fun z : ℝ => Real.arccos z / z)
        (((-x / s x) - Real.arccos x) / x ^ 2) x := by
    convert (hacos.div (hasDerivAt_id x) hx) using 1 <;>
      simp only [id_eq] <;>
      field_simp [hsne, hx] <;>
      ring
  have hnum :
      HasDerivAt (fun z : ℝ => 1 - s z) (x / s x) x := by
    convert (hasDerivAt_const x (1 : ℝ)).sub hsderiv using 1 <;>
      ring
  have hden :
      HasDerivAt (fun z : ℝ => 1 + s z) (-x / s x) x := by
    convert (hasDerivAt_const x (1 : ℝ)).add hsderiv using 1 <;>
      ring
  have hu_ne : (1 - s x) / (1 + s x) ≠ 0 := div_ne_zero hsm hsp
  have hlog :
      HasDerivAt
        (fun z : ℝ => Real.log ((1 - s z) / (1 + s z)))
        ((x / s x) / (1 - s x) + (x / s x) / (1 + s x)) x := by
    convert
      (Real.hasDerivAt_log hu_ne).comp x (hnum.div hden hsp) using 1 <;>
      field_simp [hsne, hsm, hsp] <;>
      ring
  simpa only [y, expandedDerivative, zero_mul, zero_add] using
    hfirst.add ((hasDerivAt_const x (1 / 2 : ℝ)).mul hlog)

/-- Source: `proof_gap/exercise_938/2.txt`; these hypotheses make every
factor `x`, `s x`, and `1-s x` in the cancellation nonzero. -/
theorem gap2 (x : ℝ) (hinside : |x| < 1) (hx : x ≠ 0) :
    expandedDerivative x = finalDerivative x := by
  rcases s_interval_facts x hinside hx with
    ⟨hrad, hspos, hsq, hsm, hsp⟩
  have hsne : s x ≠ 0 := ne_of_gt hspos
  have hsprod : (1 - s x) * (1 + s x) = x ^ 2 := by
    calc
      (1 - s x) * (1 + s x) = 1 - (s x) ^ 2 := by ring
      _ = x ^ 2 := by nlinarith [hsq]
  have hsum :
      (1 / 2 : ℝ) *
          ((x / s x) / (1 - s x) + (x / s x) / (1 + s x)) =
        x / (s x * x ^ 2) := by
    rw [← hsprod]
    field_simp [hsne, hsm, hsp] <;>
      ring
  unfold expandedDerivative finalDerivative
  rw [hsum]
  field_simp [hx, hsne] <;>
    ring

/-- Source: `proof_gap/exercise_938/3.txt`; retain the punctured open interval
on which the original logarithmic quotient is real and differentiable. -/
theorem gap3 (x : ℝ) (hinside : |x| < 1) (hx : x ≠ 0) :
    HasDerivAt y (finalDerivative x) x := by
  have h := gap1 x hinside hx
  rw [gap2 x hinside hx] at h
  exact h

end

end ProofGap.Exercise938
