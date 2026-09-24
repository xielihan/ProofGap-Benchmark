import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1902_2

noncomputable section

def q (a b c x : ℝ) : ℝ := a * x ^ 2 + 2 * b * x + c
def numerator (α β γ x : ℝ) : ℝ := α * x ^ 2 + 2 * β * x + γ
def integrand (a b c α β γ x : ℝ) : ℝ :=
  numerator α β γ x / q a b c x ^ 2
def domain (a b c : ℝ) : Set ℝ := {x | q a b c x ≠ 0}
def rationalPrimitive (a b c α β x : ℝ) : ℝ :=
  ((-α / a) * x - β / a) / q a b c x
def CoeffIdentity (a b c α β γ A B C D : ℝ) : Prop :=
  ∀ x, numerator α β γ x =
    A * q a b c x - (2 * a * x + 2 * b) * (A * x + B) +
      (C * x + D) * q a b c x

theorem gap1 (a b c α β γ : ℝ) (ha : a ≠ 0)
    (hdisc : b ^ 2 - a * c ≠ 0) :
    ∃ A B C D : ℝ, CoeffIdentity a b c α β γ A B C D := by
  let d : ℝ :=
    (2 * b * β - a * γ - c * α) / (2 * (b ^ 2 - a * c))
  refine ⟨d - α / a, (b * d - β) / a, 0, d, ?_⟩
  intro x
  dsimp [numerator, q, d]
  field_simp [ha, hdisc] <;> ring

theorem gap2 (a b c α β γ A B C D : ℝ) (ha : a ≠ 0)
    (h : CoeffIdentity a b c α β γ A B C D) :
    C = 0 := by
  unfold CoeffIdentity at h
  have hm1 := h (-1)
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  norm_num [numerator, q] at hm1 h0 h1 h2
  ring_nf at hm1 h0 h1 h2
  have hac : a * C = 0 := by
    linarith [hm1, h0, h1, h2]
  exact (mul_eq_zero.mp hac).resolve_left ha

theorem gap3 (a b c α β γ A B C D : ℝ) (ha : a ≠ 0)
    (hdisc : b ^ 2 - a * c ≠ 0)
    (h : CoeffIdentity a b c α β γ A B C D) :
    D = (2 * b * β - a * γ - c * α) /
      (2 * (b ^ 2 - a * c)) := by
  have hC : C = 0 := gap2 a b c α β γ A B C D ha h
  unfold CoeffIdentity at h
  have hm1 := h (-1)
  have h0 := h 0
  have h1 := h 1
  norm_num [numerator, q, hC] at hm1 h0 h1
  ring_nf at hm1 h0 h1
  have halpha : α = a * (D - A) := by
    linarith [hm1, h0, h1]
  have hbeta : β = b * D - a * B := by
    linarith [hm1, h1]
  have hgamma : γ = c * (A + D) - 2 * b * B := by
    linarith [h0]
  have hden : 2 * (b ^ 2 - a * c) ≠ 0 :=
    mul_ne_zero (by norm_num) hdisc
  apply (eq_div_iff hden).2
  rw [halpha, hbeta, hgamma]
  ring

theorem gap4 (a b c α β γ A B C D : ℝ) (ha : a ≠ 0)
    (hdisc : b ^ 2 - a * c ≠ 0)
    (hrel : a * γ + c * α = 2 * b * β)
    (h : CoeffIdentity a b c α β γ A B C D) :
    D = 0 := by
  rw [gap3 a b c α β γ A B C D ha hdisc h]
  have hn : 2 * b * β - a * γ - c * α = 0 := by
    linarith [hrel]
  rw [hn]
  simp

theorem gap5 (a b c α β γ x : ℝ) (ha : a ≠ 0)
    (hrel : a * γ + c * α = 2 * b * β)
    (hx : x ∈ domain a b c) :
    HasDerivAt (rationalPrimitive a b c α β)
      (integrand a b c α β γ x) x := by
  have hxq : q a b c x ≠ 0 := by
    simpa [domain] using hx
  have hid : HasDerivAt (fun y : ℝ => y) 1 x := by
    simpa only [id_eq] using (hasDerivAt_id x)
  have hu :
      HasDerivAt (fun y : ℝ => (-α / a) * y - β / a) (-α / a) x := by
    convert (hid.const_mul (-α / a)).sub_const (β / a) using 1 <;>
      ring
  have hmul :
      HasDerivAt ((fun y : ℝ => y) * (fun y : ℝ => y))
        (1 * x + x * 1) x :=
    hid.mul hid
  have hfun :
      (fun y : ℝ => y ^ 2) =
        ((fun y : ℝ => y) * (fun y : ℝ => y)) := by
    funext y
    simp [pow_two]
  have hsquare : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    rw [hfun]
    simpa only [one_mul, mul_one, two_mul] using hmul
  have hq : HasDerivAt (q a b c) (2 * a * x + 2 * b) x := by
    unfold q
    convert
      ((hsquare.const_mul a).add
        (hid.const_mul (2 * b))).add_const c using 1 <;>
      ring
  have hnum_eq :
      (-α / a) * q a b c x -
          ((-α / a) * x - β / a) * (2 * a * x + 2 * b) =
        numerator α β γ x := by
    unfold q numerator
    field_simp [ha]
    nlinarith [hrel]
  have hd :
      HasDerivAt
        (fun y : ℝ => ((-α / a) * y - β / a) / q a b c y)
        (((-α / a) * q a b c x -
            ((-α / a) * x - β / a) * (2 * a * x + 2 * b)) /
          q a b c x ^ 2) x :=
    hu.div hq hxq
  rw [hnum_eq] at hd
  simpa only [rationalPrimitive, integrand] using hd

theorem gap6 (a b c α β γ : ℝ) (ha : a ≠ 0)
    (hdisc : b ^ 2 - a * c ≠ 0)
    (hrel : a * γ + c * α = 2 * b * β) :
    ∃ R : ℝ → ℝ, ∀ x ∈ domain a b c,
      HasDerivAt R (integrand a b c α β γ x) x := by
  refine ⟨rationalPrimitive a b c α β, ?_⟩
  intro x hx
  exact gap5 a b c α β γ x ha hrel hx

end

end ProofGap.Exercise1902_2
