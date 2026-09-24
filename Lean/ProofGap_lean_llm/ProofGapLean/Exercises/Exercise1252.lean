import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1252

noncomputable section

def f (x : ℝ) : ℝ := x ^ 2
def g (x : ℝ) : ℝ := x ^ 3

private theorem deriv_formulas (x : ℝ) :
    deriv f x = 2 * x ∧ deriv g x = 3 * x ^ 2 := by
  have hid : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
  have hsq : HasDerivAt (fun y : ℝ => y * y) (x + x) x := by
    simpa only [mul_one, one_mul] using hid.mul hid
  constructor
  · have hfun : f = fun y : ℝ => y * y := by
      funext y
      simp only [f]
      ring
    have hcoef : (2 : ℝ) * x = x + x := by ring
    have hf : HasDerivAt f (2 * x) x := by
      rw [hfun, hcoef]
      exact hsq
    exact hf.deriv
  · have hcube : HasDerivAt (fun y : ℝ => (y * y) * y)
        ((x + x) * x + x * x) x := by
      simpa only [mul_one, one_mul] using hsq.mul hid
    have hfun : g = fun y : ℝ => (y * y) * y := by
      funext y
      simp only [g]
      ring
    have hcoef : (3 : ℝ) * x ^ 2 = (x + x) * x + x * x := by ring
    have hg : HasDerivAt g (3 * x ^ 2) x := by
      rw [hfun, hcoef]
      exact hcube
    exact hg.deriv

theorem gap1 :
    ContinuousOn (deriv f) (Set.Icc (-1 : ℝ) 1) := by
  have hderiv : deriv f = fun x : ℝ => 2 * x := by
    funext x
    exact (deriv_formulas x).1
  rw [hderiv]
  exact (continuous_const.mul continuous_id).continuousOn

theorem gap2 :
    ContinuousOn (deriv g) (Set.Icc (-1 : ℝ) 1) := by
  have hderiv : deriv g = fun x : ℝ => 3 * x ^ 2 := by
    funext x
    exact (deriv_formulas x).2
  rw [hderiv]
  exact (continuous_const.mul (continuous_id.pow 2)).continuousOn

theorem gap3 :
    g (-1) ≠ g 1 := by
  norm_num [g]

theorem gap4 (x : ℝ) (hx : x = 0) :
    deriv f x ^ 2 + deriv g x ^ 2 = 4 * x ^ 2 + 9 * x ^ 4 := by
  rw [(deriv_formulas x).1, (deriv_formulas x).2]
  ring

theorem gap5 (x : ℝ) (hx : x = 0) :
    (4 : ℝ) * x ^ 2 + 9 * x ^ 4 = 0 := by
  rw [hx]
  norm_num

theorem gap6 (x : ℝ) (hx : x = 0) :
    deriv f x ^ 2 + deriv g x ^ 2 = 0 := by
  exact (gap4 x hx).trans (gap5 x hx)

theorem gap7 :
    (f 1 - f (-1)) / (g 1 - g (-1)) = 0 := by
  norm_num [f, g]

theorem gap8 (ξ : ℝ) :
    deriv f ξ / deriv g ξ = (2 * ξ) / (3 * ξ ^ 2) := by
  rw [(deriv_formulas ξ).1, (deriv_formulas ξ).2]

theorem gap9 (ξ : ℝ) (hξ : ξ ≠ 0) :
    (2 * ξ) / (3 * ξ ^ 2) ≠ 0 := by
  apply div_ne_zero
  · exact mul_ne_zero (by norm_num) hξ
  · exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hξ)

theorem gap10 (ξ : ℝ) (hξ : ξ ≠ 0) :
    deriv f ξ / deriv g ξ ≠ 0 := by
  rw [gap8 ξ]
  exact gap9 ξ hξ

theorem gap11 (ξ : ℝ) (hξ : ξ ≠ 0) :
    (f 1 - f (-1)) / (g 1 - g (-1)) ≠ deriv f ξ / deriv g ξ := by
  rw [gap7]
  exact Ne.symm (gap10 ξ hξ)

theorem gap12 :
    ¬∃ ξ ∈ Set.Ioo (-1 : ℝ) 1,
      deriv g ξ ≠ 0 ∧
      (f 1 - f (-1)) / (g 1 - g (-1)) = deriv f ξ / deriv g ξ := by
  rintro ⟨ξ, hξ, hg, heq⟩
  have hξ0 : ξ ≠ 0 := by
    intro hzero
    apply hg
    rw [(deriv_formulas ξ).2, hzero]
    norm_num
  exact (gap11 ξ hξ0) heq

end

end ProofGap.Exercise1252
