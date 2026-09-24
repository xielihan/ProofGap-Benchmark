import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1424

noncomputable section

private theorem Real.sign_ofNegative {x : ℝ} (h : x < 0) :
    _root_.Real.sign x = -1 := by
  simp [_root_.Real.sign, h]

private theorem Real.sign_ofPositive {x : ℝ} (h : 0 < x) :
    _root_.Real.sign x = 1 := by
  simp [_root_.Real.sign, h, not_lt_of_ge h.le]

theorem gap1 (f P P₁ Q : ℝ → ℝ)
    (hf : ∀ x, f x = P x / Q x)
    (hderiv : ∀ x, deriv f x = P₁ x / Q x ^ 2)
    (hP₁ : Differentiable ℝ P₁) (hQ : Differentiable ℝ Q) (x : ℝ)
    (hQx : Q x ≠ 0) :
    deriv (deriv f) x =
      (deriv P₁ x * Q x ^ 2 - 2 * Q x * deriv Q x * P₁ x) / Q x ^ 4 := by
  have hP₁x : HasDerivAt P₁ (deriv P₁ x) x := (hP₁ x).hasDerivAt
  have hQx' : HasDerivAt Q (deriv Q x) x := (hQ x).hasDerivAt
  have hden : HasDerivAt (fun y => Q y ^ 2) (2 * Q x * deriv Q x) x := by
    convert hQx'.pow 2 using 1 <;> ring
  have hfun : deriv f = fun y => P₁ y / Q y ^ 2 := by
    funext y
    exact hderiv y
  rw [hfun]
  change deriv (P₁ / fun y => Q y ^ 2) x = _
  have hquot := hP₁x.div hden (pow_ne_zero 2 hQx)
  rw [hquot.deriv]
  field_simp
  <;> ring

theorem gap2 (f P₁ Q : ℝ → ℝ) (x₀ : ℝ)
    (hsecond : ∀ x, deriv (deriv f) x =
      (deriv P₁ x * Q x ^ 2 - 2 * Q x * deriv Q x * P₁ x) / Q x ^ 4)
    (hP₁ : P₁ x₀ = 0) (hQ : Q x₀ ≠ 0) :
    deriv (deriv f) x₀ = deriv P₁ x₀ / Q x₀ ^ 2 := by
  rw [hsecond x₀, hP₁]
  field_simp
  <;> ring

theorem gap3 (Q : ℝ → ℝ) (x₀ : ℝ) (hQ : Q x₀ ≠ 0) :
    0 < Q x₀ ^ 2 := by
  exact sq_pos_of_ne_zero hQ

theorem gap4 (f P₁ Q : ℝ → ℝ) (x₀ : ℝ)
    (hvalue : deriv (deriv f) x₀ = deriv P₁ x₀ / Q x₀ ^ 2)
    (hQ : Q x₀ ≠ 0) :
    Real.sign (deriv (deriv f) x₀) = Real.sign (deriv P₁ x₀) := by
  rw [hvalue]
  have hden : 0 < Q x₀ ^ 2 := gap3 Q x₀ hQ
  rcases lt_trichotomy (deriv P₁ x₀) 0 with hneg | hzero | hpos
  · have hquot : deriv P₁ x₀ / Q x₀ ^ 2 < 0 :=
      div_neg_of_neg_of_pos hneg hden
    rw [Real.sign_ofNegative hquot, Real.sign_ofNegative hneg]
  · rw [hzero]
    simp
  · have hquot : 0 < deriv P₁ x₀ / Q x₀ ^ 2 := div_pos hpos hden
    rw [Real.sign_ofPositive hquot, Real.sign_ofPositive hpos]

theorem gap5 (f P₁ Q : ℝ → ℝ) (x₀ : ℝ)
    (hvalue : deriv (deriv f) x₀ = deriv P₁ x₀ / Q x₀ ^ 2)
    (hQ : Q x₀ ≠ 0) :
    Real.sign (deriv (deriv f) x₀) = Real.sign (deriv P₁ x₀) := by
  exact gap4 f P₁ Q x₀ hvalue hQ

end
end ProofGap.Exercise1424
