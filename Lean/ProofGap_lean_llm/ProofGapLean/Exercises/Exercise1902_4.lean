import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1902_4

noncomputable section

def q (a b c x : ℝ) : ℝ := a * x ^ 2 + 2 * b * x + c
def integrand (a b c α β γ x : ℝ) : ℝ :=
  (α * x ^ 2 + 2 * β * x + γ) / q a b c x ^ 2
def rationalPrimitive (c α β γ x : ℝ) : ℝ :=
  α / (3 * c ^ 2) * x ^ 3 + β / c ^ 2 * x ^ 2 + γ / c ^ 2 * x

theorem gap1 (a b c α β γ x : ℝ) (ha : a = 0) (hb : b = 0)
    (hc : c ≠ 0) :
    HasDerivAt (rationalPrimitive c α β γ)
      (integrand a b c α β γ x) x := by
  have h2 : HasDerivAt (fun y : ℝ => y * y) (x + x) x := by
    convert (hasDerivAt_id x).mul (hasDerivAt_id x) using 1 <;>
      simp only [id_eq] <;>
      ring
  have h3 : HasDerivAt (fun y : ℝ => y * y * y) (3 * x ^ 2) x := by
    convert h2.mul (hasDerivAt_id x) using 1 <;>
      simp only [id_eq] <;>
      ring
  have ht1 :
      HasDerivAt
        (fun y : ℝ => α / (3 * c ^ 2) * (y * y * y))
        (α / (3 * c ^ 2) * (3 * x ^ 2)) x :=
    h3.const_mul (α / (3 * c ^ 2))
  have ht2 :
      HasDerivAt
        (fun y : ℝ => β / c ^ 2 * (y * y))
        (β / c ^ 2 * (x + x)) x :=
    h2.const_mul (β / c ^ 2)
  have ht3 :
      HasDerivAt
        (fun y : ℝ => γ / c ^ 2 * y)
        (γ / c ^ 2) x := by
    simpa only [id_eq, mul_one] using
      (hasDerivAt_id x).const_mul (γ / c ^ 2)
  have ht12 :
      HasDerivAt
        (fun y : ℝ =>
          α / (3 * c ^ 2) * (y * y * y) + β / c ^ 2 * (y * y))
        (α / (3 * c ^ 2) * (3 * x ^ 2) + β / c ^ 2 * (x + x)) x := by
    exact ht1.add ht2
  have hG :
      HasDerivAt
        (fun y : ℝ =>
          α / (3 * c ^ 2) * (y * y * y) +
            β / c ^ 2 * (y * y) + γ / c ^ 2 * y)
        (α / (3 * c ^ 2) * (3 * x ^ 2) +
          β / c ^ 2 * (x + x) + γ / c ^ 2) x := by
    exact ht12.add ht3
  have hfun :
      (fun y : ℝ =>
        α / (3 * c ^ 2) * (y * y * y) +
          β / c ^ 2 * (y * y) + γ / c ^ 2 * y) =
        rationalPrimitive c α β γ := by
    funext y
    simp only [rationalPrimitive, pow_two]
    ring
  have heq :
      integrand a b c α β γ x =
        α / (3 * c ^ 2) * (3 * x ^ 2) +
          β / c ^ 2 * (x + x) + γ / c ^ 2 := by
    simp [integrand, q, ha, hb]
    field_simp [hc]
    ring
  rw [hfun] at hG
  rw [heq]
  exact hG

theorem gap2 (a b c : ℝ) (ha : a = 0) (hb : b = 0) :
    b ^ 2 - a * c = 0 := by
  simp [ha, hb]

theorem gap3 (a b c α β γ : ℝ) (ha : a = 0) (hb : b = 0) :
    b ^ 2 - a * c = 0 ∨ a * γ + c * α = 2 * b * β := by
  exact Or.inl (gap2 a b c ha hb)

theorem gap4 (a b c α β γ : ℝ) (ha : a = 0) (hb : b = 0)
    (hc : c ≠ 0) :
    ∃ R : ℝ → ℝ, ∀ x,
      HasDerivAt R (integrand a b c α β γ x) x := by
  refine ⟨rationalPrimitive c α β γ, ?_⟩
  intro x
  exact gap1 a b c α β γ x ha hb hc

end

end ProofGap.Exercise1902_4
