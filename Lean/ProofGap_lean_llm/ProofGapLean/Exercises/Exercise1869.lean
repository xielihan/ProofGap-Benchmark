import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue

open Set Real

namespace ProofGap.Exercise1869

noncomputable section

def domain : Set ℝ := Set.Ioo 0 2

def integrand (x : ℝ) : ℝ :=
  (x ^ 3 + 1) / (x ^ 3 - 5 * x ^ 2 + 6 * x)

def divisionRewrite (x : ℝ) : ℝ :=
  1 + (5 * x ^ 2 - 6 * x + 1) / (x ^ 3 - 5 * x ^ 2 + 6 * x)

def factoredRewrite (x : ℝ) : ℝ :=
  1 + (5 * x ^ 2 - 6 * x + 1) / (x * (x - 2) * (x - 3))

def partialFractionRewrite (x : ℝ) : ℝ :=
  1 + 1 / (6 * x) - 9 / (2 * (x - 2)) + 28 / (3 * (x - 3))

def antiderivatives (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | DifferentiableOn ℝ F domain ∧ ∀ x ∈ domain, deriv F x = g x}

def primitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ K : ℝ, ∀ x ∈ domain, F x = p x + K}

def primitive (x : ℝ) : ℝ :=
  x + (1 / 6 : ℝ) * Real.log |x| -
    (9 / 2 : ℝ) * Real.log |x - 2| +
    (28 / 3 : ℝ) * Real.log |x - 3|

private theorem integrand_eq_partialFractionRewrite_on_domain
    (x : ℝ) (hx : x ∈ domain) :
    integrand x = partialFractionRewrite x := by
  rcases hx with ⟨hx0p, hx2p⟩
  have hx0 : x ≠ 0 := ne_of_gt hx0p
  have hx2 : x ≠ 2 := ne_of_lt hx2p
  have hx3 : x ≠ 3 := by linarith
  have hfactor :
      x ^ 3 - 5 * x ^ 2 + 6 * x = x * (x - 2) * (x - 3) := by
    ring
  unfold integrand partialFractionRewrite
  rw [hfactor]
  field_simp [hx0, sub_ne_zero.mpr hx2, sub_ne_zero.mpr hx3]
  <;> ring

private theorem primitive_hasDerivAt_integrand
    (x : ℝ) (hx : x ∈ domain) : HasDerivAt primitive (integrand x) x := by
  rcases hx with ⟨hx0p, hx2p⟩
  have hx0 : x ≠ 0 := ne_of_gt hx0p
  have hx2 : x ≠ 2 := ne_of_lt hx2p
  have hx3 : x ≠ 3 := by linarith
  have hx2' : x - 2 ≠ 0 := sub_ne_zero.mpr hx2
  have hx3' : x - 3 ≠ 0 := sub_ne_zero.mpr hx3
  have hlog0 := Real.hasDerivAt_log hx0
  have hlog2 :=
    (Real.hasDerivAt_log hx2').comp x ((hasDerivAt_id x).sub_const 2)
  have hlog3 :=
    (Real.hasDerivAt_log hx3').comp x ((hasDerivAt_id x).sub_const 3)
  have hprim :
      HasDerivAt primitive
        (1 + (1 / 6 : ℝ) * x⁻¹ -
          (9 / 2 : ℝ) * (x - 2)⁻¹ +
          (28 / 3 : ℝ) * (x - 3)⁻¹) x := by
    convert
      ((((hasDerivAt_id x).add (hlog0.const_mul (1 / 6 : ℝ))).sub
        (hlog2.const_mul (9 / 2 : ℝ))).add
        (hlog3.const_mul (28 / 3 : ℝ))) using 1 <;>
      simp only [Function.comp_apply, id_eq, mul_one]
    all_goals
      first
      | (funext y; simp [primitive, Real.log_abs] <;> ring)
      | ring
  have hcoef :
      1 + (1 / 6 : ℝ) * x⁻¹ -
          (9 / 2 : ℝ) * (x - 2)⁻¹ +
          (28 / 3 : ℝ) * (x - 3)⁻¹ = partialFractionRewrite x := by
    unfold partialFractionRewrite
    field_simp [hx0, hx2', hx3']
    <;> ring
  rw [integrand_eq_partialFractionRewrite_on_domain x ⟨hx0p, hx2p⟩, ← hcoef]
  exact hprim

theorem gap1 (x : ℝ) (hx0 : x ≠ 0) (hx2 : x ≠ 2) (hx3 : x ≠ 3) :
    integrand x = divisionRewrite x := by
  unfold integrand divisionRewrite
  have hfactor :
      x ^ 3 - 5 * x ^ 2 + 6 * x = x * (x - 2) * (x - 3) := by
    ring
  rw [hfactor]
  field_simp [hx0, sub_ne_zero.mpr hx2, sub_ne_zero.mpr hx3]
  <;> ring

theorem gap2 (x : ℝ) (hx0 : x ≠ 0) (hx2 : x ≠ 2) (hx3 : x ≠ 3) :
    divisionRewrite x = factoredRewrite x := by
  unfold divisionRewrite factoredRewrite
  rw [show x ^ 3 - 5 * x ^ 2 + 6 * x = x * (x - 2) * (x - 3) by ring]

theorem gap3 (x : ℝ) (hx0 : x ≠ 0) (hx2 : x ≠ 2) (hx3 : x ≠ 3) :
    integrand x = factoredRewrite x := by
  exact (gap1 x hx0 hx2 hx3).trans (gap2 x hx0 hx2 hx3)

theorem gap4 :
    ∃ A B C : ℝ, ∀ x, x ≠ 0 → x ≠ 2 → x ≠ 3 →
      (5 * x ^ 2 - 6 * x + 1) / (x * (x - 2) * (x - 3)) =
        A / x + B / (x - 2) + C / (x - 3) := by
  refine ⟨(1 / 6 : ℝ), -(9 / 2 : ℝ), (28 / 3 : ℝ), ?_⟩
  intro x hx0 hx2 hx3
  field_simp [hx0, sub_ne_zero.mpr hx2, sub_ne_zero.mpr hx3]
  <;> ring

theorem gap5 (A B C : ℝ)
    (h : ∀ x, x ≠ 0 → x ≠ 2 → x ≠ 3 →
      (5 * x ^ 2 - 6 * x + 1) / (x * (x - 2) * (x - 3)) =
        A / x + B / (x - 2) + C / (x - 3)) :
    ∀ x, 5 * x ^ 2 - 6 * x + 1 =
      A * (x - 2) * (x - 3) + B * x * (x - 3) + C * x * (x - 2) := by
  have h1 := h 1 (by norm_num) (by norm_num) (by norm_num)
  have h4 := h 4 (by norm_num) (by norm_num) (by norm_num)
  have h5 := h 5 (by norm_num) (by norm_num) (by norm_num)
  norm_num [div_eq_mul_inv] at h1 h4 h5
  have hA : A = (1 / 6 : ℝ) := by
    linarith [h1, h4, h5]
  have hB : B = -(9 / 2 : ℝ) := by
    linarith [h1, h4, h5]
  have hC : C = (28 / 3 : ℝ) := by
    linarith [h1, h4, h5]
  intro x
  rw [hA, hB, hC]
  ring

theorem gap6 (A B C : ℝ)
    (h : ∀ x, 5 * x ^ 2 - 6 * x + 1 =
      A * (x - 2) * (x - 3) + B * x * (x - 3) + C * x * (x - 2)) :
    1 = 6 * A := by
  have h0 := h 0
  norm_num at h0
  linarith

theorem gap7 (A : ℝ) (h : 1 = 6 * A) : A = (1 / 6 : ℝ) := by
  linarith

theorem gap8 (A B C : ℝ)
    (h : ∀ x, 5 * x ^ 2 - 6 * x + 1 =
      A * (x - 2) * (x - 3) + B * x * (x - 3) + C * x * (x - 2)) :
    9 = -2 * B := by
  have h2 := h 2
  norm_num at h2
  linarith

theorem gap9 (B : ℝ) (h : 9 = -2 * B) : B = -(9 / 2 : ℝ) := by
  linarith

theorem gap10 (A B C : ℝ)
    (h : ∀ x, 5 * x ^ 2 - 6 * x + 1 =
      A * (x - 2) * (x - 3) + B * x * (x - 3) + C * x * (x - 2)) :
    28 = 3 * C := by
  have h3 := h 3
  norm_num at h3
  linarith

theorem gap11 (C : ℝ) (h : 28 = 3 * C) : C = (28 / 3 : ℝ) := by
  linarith

theorem gap12 :
    antiderivatives integrand = antiderivatives partialFractionRewrite := by
  ext F
  change
    (DifferentiableOn ℝ F domain ∧ ∀ x ∈ domain, deriv F x = integrand x) ↔
      (DifferentiableOn ℝ F domain ∧
        ∀ x ∈ domain, deriv F x = partialFractionRewrite x)
  constructor
  · rintro ⟨hF, hder⟩
    refine ⟨hF, ?_⟩
    intro x hx
    calc
      deriv F x = integrand x := hder x hx
      _ = partialFractionRewrite x := integrand_eq_partialFractionRewrite_on_domain x hx
  · rintro ⟨hF, hder⟩
    refine ⟨hF, ?_⟩
    intro x hx
    calc
      deriv F x = partialFractionRewrite x := hder x hx
      _ = integrand x := (integrand_eq_partialFractionRewrite_on_domain x hx).symm

theorem gap13 : antiderivatives integrand = primitiveFamily primitive := by
  ext F
  change
    (DifferentiableOn ℝ F domain ∧ ∀ x ∈ domain, deriv F x = integrand x) ↔
      ∃ K : ℝ, ∀ x ∈ domain, F x = primitive x + K
  constructor
  · rintro ⟨hF, hder⟩
    let K : ℝ := F 1 - primitive 1
    have hone : (1 : ℝ) ∈ domain := by
      constructor <;> norm_num
    have hsub : ∀ x ∈ domain,
        HasDerivAt (fun y => F y - primitive y) 0 x := by
      intro x hx
      have hFat : DifferentiableAt ℝ F x :=
        (hF x hx).differentiableAt (isOpen_Ioo.mem_nhds hx)
      convert hFat.hasDerivAt.sub (primitive_hasDerivAt_integrand x hx) using 1
      rw [hder x hx]
      ring
    have hdiff : DifferentiableOn ℝ (fun x => F x - primitive x) domain := by
      intro x hx
      exact (hsub x hx).differentiableAt.differentiableWithinAt
    have hzero :
        ∀ x ∈ domain, deriv (fun y => F y - primitive y) x = 0 := by
      intro x hx
      exact (hsub x hx).deriv
    refine ⟨K, ?_⟩
    intro x hx
    have heq : F x - primitive x = F 1 - primitive 1 :=
      isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo hdiff hzero hx hone
    dsimp [K]
    linarith
  · rintro ⟨K, hK⟩
    have hFat : ∀ x ∈ domain, HasDerivAt F (integrand x) x := by
      intro x hx
      have hev : F =ᶠ[nhds x] (fun y => primitive y + K) := by
        filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
        exact hK y hy
      exact ((primitive_hasDerivAt_integrand x hx).add_const K).congr_of_eventuallyEq hev
    refine ⟨?_, ?_⟩
    · intro x hx
      exact (hFat x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      exact (hFat x hx).deriv

end

end ProofGap.Exercise1869
