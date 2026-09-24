import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1902_1

noncomputable section

def x₀ (a b : ℝ) : ℝ := -b / a
def q (a b c x : ℝ) : ℝ := a * x ^ 2 + 2 * b * x + c
def numerator (α β γ x : ℝ) : ℝ := α * x ^ 2 + 2 * β * x + γ
def integrand (a b c α β γ x : ℝ) : ℝ :=
  numerator α β γ x / q a b c x ^ 2
def domain (a b : ℝ) : Set ℝ := {x | x ≠ x₀ a b}
def rationalPrimitive (a b α β γ x : ℝ) : ℝ :=
  -α / (a ^ 2 * (x - x₀ a b)) -
    (α * x₀ a b + β) / (a ^ 2 * (x - x₀ a b) ^ 2) -
    (α * x₀ a b ^ 2 + 2 * β * x₀ a b + γ) /
      (3 * a ^ 2 * (x - x₀ a b) ^ 3)

theorem gap1 (a b c x : ℝ) (ha : a ≠ 0) (hdisc : b ^ 2 - a * c = 0) :
    q a b c x = a * (x - x₀ a b) ^ 2 := by
  unfold q x₀
  field_simp [ha]
  nlinarith [hdisc]

theorem gap2 (a b : ℝ) (ha : a ≠ 0) :
    x₀ a b ∈ Set.univ := by
  simp

theorem gap3 (a b c α β γ x : ℝ) (ha : a ≠ 0)
    (hdisc : b ^ 2 - a * c = 0) (hx : x ∈ domain a b) :
    integrand a b c α β γ x =
      (α * (x - x₀ a b) ^ 2 +
          2 * α * x₀ a b * (x - x₀ a b) +
          α * x₀ a b ^ 2 +
          2 * β * (x - x₀ a b) + 2 * β * x₀ a b + γ) /
        (a ^ 2 * (x - x₀ a b) ^ 4) := by
  have hne : x ≠ x₀ a b := by
    simpa [domain] using hx
  have hd : x - x₀ a b ≠ 0 := sub_ne_zero.mpr hne
  unfold integrand numerator
  rw [gap1 a b c x ha hdisc]
  field_simp [ha, hd] <;> ring

theorem gap4 (a b c α β γ x : ℝ) (ha : a ≠ 0)
    (hdisc : b ^ 2 - a * c = 0) (hx : x ∈ domain a b) :
    integrand a b c α β γ x =
      α / (a ^ 2 * (x - x₀ a b) ^ 2) +
        (2 * α * x₀ a b + 2 * β) /
          (a ^ 2 * (x - x₀ a b) ^ 3) +
        (α * x₀ a b ^ 2 + 2 * β * x₀ a b + γ) /
          (a ^ 2 * (x - x₀ a b) ^ 4) := by
  have hne : x ≠ x₀ a b := by
    simpa [domain] using hx
  have hd : x - x₀ a b ≠ 0 := sub_ne_zero.mpr hne
  rw [gap3 a b c α β γ x ha hdisc hx]
  field_simp [ha, hd] <;> ring

theorem gap5 (a b c α β γ x : ℝ) (ha : a ≠ 0)
    (hdisc : b ^ 2 - a * c = 0) (hx : x ∈ domain a b) :
    HasDerivAt (rationalPrimitive a b α β γ)
      (integrand a b c α β γ x) x := by
  have hne : x ≠ x₀ a b := by
    simpa [domain] using hx
  have hd : x - x₀ a b ≠ 0 := sub_ne_zero.mpr hne
  have hsub : HasDerivAt (fun y : ℝ => y - x₀ a b) 1 x := by
    simpa using (hasDerivAt_id x).sub_const (x₀ a b)
  have hsub2 :
      HasDerivAt (fun y : ℝ => (y - x₀ a b) ^ 2)
        (2 * (x - x₀ a b)) x := by
    simpa [pow_two, two_mul] using hsub.mul hsub
  have hsub3 :
      HasDerivAt (fun y : ℝ => (y - x₀ a b) ^ 3)
        (3 * (x - x₀ a b) ^ 2) x := by
    convert hsub2.mul hsub using 1 <;> ring
  have hden1_ne : a ^ 2 * (x - x₀ a b) ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 ha) hd
  have hden2_ne : a ^ 2 * (x - x₀ a b) ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 ha) (pow_ne_zero 2 hd)
  have hden3_ne : (3 * a ^ 2) * (x - x₀ a b) ^ 3 ≠ 0 := by
    exact mul_ne_zero
      (mul_ne_zero (by norm_num) (pow_ne_zero 2 ha))
      (pow_ne_zero 3 hd)
  have hterm1 :=
    (hasDerivAt_const x (-α)).div
      (hsub.const_mul (a ^ 2)) hden1_ne
  have hterm2 :=
    (hasDerivAt_const x (α * x₀ a b + β)).div
      (hsub2.const_mul (a ^ 2)) hden2_ne
  have hterm3 :=
    (hasDerivAt_const x
      (α * x₀ a b ^ 2 + 2 * β * x₀ a b + γ)).div
      (hsub3.const_mul (3 * a ^ 2)) hden3_ne
  have hprimitive :
      HasDerivAt (rationalPrimitive a b α β γ)
        (α / (a ^ 2 * (x - x₀ a b) ^ 2) +
          (2 * α * x₀ a b + 2 * β) /
            (a ^ 2 * (x - x₀ a b) ^ 3) +
          (α * x₀ a b ^ 2 + 2 * β * x₀ a b + γ) /
            (a ^ 2 * (x - x₀ a b) ^ 4)) x := by
    unfold rationalPrimitive
    convert (hterm1.sub hterm2).sub hterm3 using 1 <;>
      field_simp [ha, hd] <;> ring
  rw [gap4 a b c α β γ x ha hdisc hx]
  exact hprimitive

theorem gap6 (a b c α β γ : ℝ) (ha : a ≠ 0)
    (hdisc : b ^ 2 - a * c = 0) :
    ∃ R : ℝ → ℝ, ∀ x ∈ domain a b,
      HasDerivAt R (integrand a b c α β γ x) x := by
  refine ⟨rationalPrimitive a b α β γ, ?_⟩
  intro x hx
  exact gap5 a b c α β γ x ha hdisc hx

end

end ProofGap.Exercise1902_1
