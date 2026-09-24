import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise889

noncomputable section

def y (x : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.log (1 + x) -
    (1 / 4 : ℝ) * Real.log (1 + x ^ 2) -
      1 / (2 * (1 + x))

def expandedDerivative (x : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (1 / (1 + x)) -
    x / (2 * (1 + x ^ 2)) +
      1 / (2 * (1 + x) ^ 2)

def finalDerivative (x : ℝ) : ℝ :=
  1 / ((1 + x) ^ 2 * (1 + x ^ 2))

theorem gap1 (x : ℝ) (hx : -1 < x) :
    deriv y x = expandedDerivative x := by
  have h1 : 1 + x ≠ 0 := by
    linarith
  have h2 : 1 + x ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg x]
  have hlin : HasDerivAt (fun t : ℝ => 1 + t) 1 x := by
    simpa using (hasDerivAt_id x).const_add (1 : ℝ)
  have hquad : HasDerivAt (fun t : ℝ => 1 + t ^ 2) (2 * x) x := by
    convert ((hasDerivAt_id x).pow 2).const_add (1 : ℝ) using 1 <;>
      simp <;> ring_nf
  have hloglin := (Real.hasDerivAt_log h1).comp x hlin
  have hlogquad := (Real.hasDerivAt_log h2).comp x hquad
  have hden : HasDerivAt (fun t : ℝ => 2 * (1 + t)) 2 x := by
    convert hlin.const_mul (2 : ℝ) using 1 <;> ring
  have hrec :=
    (hasDerivAt_const x (1 : ℝ)).div hden
      (mul_ne_zero (by norm_num) h1)
  unfold y expandedDerivative
  convert
    (((hloglin.const_mul (1 / 2 : ℝ)).sub
      (hlogquad.const_mul (1 / 4 : ℝ))).sub hrec).deriv using 1 <;>
    field_simp [h1, h2] <;> ring

theorem gap2 (x : ℝ) (hx : -1 < x) :
    expandedDerivative x = finalDerivative x := by
  have h1 : 1 + x ≠ 0 := by
    linarith
  have h2 : 1 + x ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg x]
  unfold expandedDerivative finalDerivative
  field_simp [h1, h2] <;> ring

theorem gap3 (x : ℝ) (hx : -1 < x) :
    deriv y x = finalDerivative x := by
  calc
    deriv y x = expandedDerivative x := gap1 x hx
    _ = finalDerivative x := gap2 x hx

end

end ProofGap.Exercise889
