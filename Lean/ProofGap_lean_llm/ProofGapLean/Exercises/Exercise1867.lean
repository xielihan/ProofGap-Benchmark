import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.OrderClosed

open Set Real

namespace ProofGap.Exercise1867

noncomputable section

def domain : Set ℝ := Set.Ioo (-2) (-1)

def integrand (x : ℝ) : ℝ :=
  x / ((x + 1) * (x + 2) * (x + 3))

def partialFractions (x : ℝ) : ℝ :=
  -(1 / 2 : ℝ) / (x + 1) + 2 / (x + 2) - (3 / 2 : ℝ) / (x + 3)

def antiderivatives (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | DifferentiableOn ℝ F domain ∧ ∀ x ∈ domain, deriv F x = g x}

def primitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ K : ℝ, ∀ x ∈ domain, F x = p x + K}

def expandedPrimitive (x : ℝ) : ℝ :=
  -(1 / 2 : ℝ) * Real.log |x + 1| +
    2 * Real.log |x + 2| -
    (3 / 2 : ℝ) * Real.log |x + 3|

def combinedPrimitive (x : ℝ) : ℝ :=
  (1 / 2 : ℝ) *
    Real.log |(x + 2) ^ 4 / ((x + 1) * (x + 3) ^ 3)|

private theorem integrand_eq_partialFractions {x : ℝ}
    (hx1 : x + 1 ≠ 0) (hx2 : x + 2 ≠ 0) (hx3 : x + 3 ≠ 0) :
    integrand x = partialFractions x := by
  unfold integrand partialFractions
  field_simp [hx1, hx2, hx3]
  ring

private theorem expandedPrimitive_hasDerivAt (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt expandedPrimitive (integrand x) x := by
  have hx1 : x + 1 ≠ 0 := by
    have := hx.2
    linarith
  have hx2 : x + 2 ≠ 0 := by
    have := hx.1
    linarith
  have hx3 : x + 3 ≠ 0 := by
    have := hx.1
    linarith
  have hd1 : HasDerivAt (fun y : ℝ => Real.log |y + 1|) (x + 1)⁻¹ x := by
    simpa only [Real.log_abs, Function.comp_def, mul_one] using
      ((Real.hasDerivAt_log (x := x + 1) hx1).comp x
        ((hasDerivAt_id x).add_const 1))
  have hd2 : HasDerivAt (fun y : ℝ => Real.log |y + 2|) (x + 2)⁻¹ x := by
    simpa only [Real.log_abs, Function.comp_def, mul_one] using
      ((Real.hasDerivAt_log (x := x + 2) hx2).comp x
        ((hasDerivAt_id x).add_const 2))
  have hd3 : HasDerivAt (fun y : ℝ => Real.log |y + 3|) (x + 3)⁻¹ x := by
    simpa only [Real.log_abs, Function.comp_def, mul_one] using
      ((Real.hasDerivAt_log (x := x + 3) hx3).comp x
        ((hasDerivAt_id x).add_const 3))
  have hdpf0 :=
    ((hd1.const_mul (-(1 / 2 : ℝ))).add (hd2.const_mul 2)).sub
      (hd3.const_mul (3 / 2 : ℝ))
  have hdpf : HasDerivAt expandedPrimitive (partialFractions x) x := by
    exact hdpf0
  rw [integrand_eq_partialFractions hx1 hx2 hx3]
  exact hdpf

private theorem combinedPrimitive_hasDerivAt (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt combinedPrimitive (integrand x) x := by
  have hx1 : x + 1 ≠ 0 := by
    have := hx.2
    linarith
  have hx2 : x + 2 ≠ 0 := by
    have := hx.1
    linarith
  have hx3 : x + 3 ≠ 0 := by
    have := hx.1
    linarith
  have hden : (x + 1) * (x + 3) ^ 3 ≠ 0 :=
    mul_ne_zero hx1 (pow_ne_zero 3 hx3)
  have hratio : (x + 2) ^ 4 / ((x + 1) * (x + 3) ^ 3) ≠ 0 :=
    div_ne_zero (pow_ne_zero 4 hx2) hden
  have hnum :
      HasDerivAt (fun y : ℝ => (y + 2) ^ 4) (4 * (x + 2) ^ 3) x := by
    simpa using (((hasDerivAt_id x).add_const 2).pow 4)
  have hdenDeriv :
      HasDerivAt (fun y : ℝ => (y + 1) * (y + 3) ^ 3)
        ((x + 3) ^ 3 + (x + 1) * (3 * (x + 3) ^ 2)) x := by
    simpa using
      (((hasDerivAt_id x).add_const 1).mul
        (((hasDerivAt_id x).add_const 3).pow 3))
  have hquot :
      HasDerivAt
        (fun y : ℝ => (y + 2) ^ 4 / ((y + 1) * (y + 3) ^ 3))
        ((4 * (x + 2) ^ 3 * ((x + 1) * (x + 3) ^ 3) -
            (x + 2) ^ 4 *
              ((x + 3) ^ 3 + (x + 1) * (3 * (x + 3) ^ 2))) /
          ((x + 1) * (x + 3) ^ 3) ^ 2) x := by
    simpa using hnum.div hdenDeriv hden
  have hlog :
      HasDerivAt
        (fun y : ℝ =>
          Real.log ((y + 2) ^ 4 / ((y + 1) * (y + 3) ^ 3)))
        (((x + 2) ^ 4 / ((x + 1) * (x + 3) ^ 3))⁻¹ *
          ((4 * (x + 2) ^ 3 * ((x + 1) * (x + 3) ^ 3) -
              (x + 2) ^ 4 *
                ((x + 3) ^ 3 + (x + 1) * (3 * (x + 3) ^ 2))) /
            ((x + 1) * (x + 3) ^ 3) ^ 2)) x := by
    simpa only [Function.comp_apply] using
      ((Real.hasDerivAt_log
        (x := (x + 2) ^ 4 / ((x + 1) * (x + 3) ^ 3)) hratio).comp x hquot)
  convert hlog.const_mul (1 / 2 : ℝ) using 1
  · funext y
    simp only [combinedPrimitive, Real.log_abs]
  · unfold integrand
    field_simp [hx1, hx2, hx3, hden, hratio]
    <;> ring

private theorem antiderivatives_eq_primitiveFamily_of_hasDerivAt
    (p g : ℝ → ℝ)
    (hp : ∀ x ∈ domain, HasDerivAt p (g x) x) :
    antiderivatives g = primitiveFamily p := by
  ext F
  simp only [antiderivatives, primitiveFamily, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hFdiff, hFderiv⟩
    let q : ℝ → ℝ := fun y => F y - p y
    have hqhas (y : ℝ) (hy : y ∈ domain) : HasDerivAt q 0 y := by
      have hFdiffAt : DifferentiableAt ℝ F y :=
        (hFdiff y hy).differentiableAt (isOpen_Ioo.mem_nhds hy)
      have hFhas : HasDerivAt F (g y) y := by
        simpa [hFderiv y hy] using hFdiffAt.hasDerivAt
      simpa [q] using hFhas.sub (hp y hy)
    have hqdiff : DifferentiableOn ℝ q domain := by
      intro y hy
      exact (hqhas y hy).differentiableAt.differentiableWithinAt
    have hqderiv : ∀ y ∈ domain, deriv q y = 0 := by
      intro y hy
      exact (hqhas y hy).deriv
    have hx0 : (-3 / 2 : ℝ) ∈ domain := by
      norm_num [domain]
    have hconn : IsPreconnected domain := by
      have hc : Convex ℝ domain := by
        simpa [domain] using (convex_Ioo (-2 : ℝ) (-1 : ℝ))
      exact hc.isPreconnected
    refine ⟨F (-3 / 2) - p (-3 / 2), ?_⟩
    intro x hx
    have hc : q x = q (-3 / 2) :=
      isOpen_Ioo.is_const_of_deriv_eq_zero hconn hqdiff hqderiv hx hx0
    dsimp [q] at hc
    linarith
  · rintro ⟨K, hFK⟩
    have hFhas (x : ℝ) (hx : x ∈ domain) : HasDerivAt F (g x) x := by
      have hevent : F =ᶠ[nhds x] (fun y => p y + K) :=
        Filter.mem_of_superset (isOpen_Ioo.mem_nhds hx) (fun y hy => hFK y hy)
      exact (hevent.hasDerivAt_iff).2 ((hp x hx).add_const K)
    refine ⟨?_, ?_⟩
    · intro x hx
      exact (hFhas x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      exact (hFhas x hx).deriv

theorem gap1 (A B C x : ℝ)
    (h1 : x ≠ -1) (h2 : x ≠ -2) (h3 : x ≠ -3)
    (h : integrand x = A / (x + 1) + B / (x + 2) + C / (x + 3)) :
    x = A * (x + 2) * (x + 3) +
      B * (x + 1) * (x + 3) + C * (x + 1) * (x + 2) := by
  have hx1 : x + 1 ≠ 0 := by
    intro hx
    apply h1
    linarith
  have hx2 : x + 2 ≠ 0 := by
    intro hx
    apply h2
    linarith
  have hx3 : x + 3 ≠ 0 := by
    intro hx
    apply h3
    linarith
  unfold integrand at h
  field_simp [hx1, hx2, hx3] at h
  ring_nf at h ⊢
  exact h

theorem gap2 (A B C : ℝ)
    (h : ∀ x, x = A * (x + 2) * (x + 3) +
      B * (x + 1) * (x + 3) + C * (x + 1) * (x + 2)) :
    -1 = 2 * A := by
  have hx := h (-1)
  norm_num at hx ⊢
  simpa [mul_comm] using hx

theorem gap3 (A : ℝ) (h : -1 = 2 * A) : A = -(1 / 2 : ℝ) := by
  norm_num at h ⊢
  linarith

theorem gap4 (A B C : ℝ)
    (h : ∀ x, x = A * (x + 2) * (x + 3) +
      B * (x + 1) * (x + 3) + C * (x + 1) * (x + 2)) :
    -2 = -B := by
  have hx := h (-2)
  norm_num at hx ⊢
  exact hx

theorem gap5 (B : ℝ) (h : -2 = -B) : B = 2 := by
  linarith

theorem gap6 (A B C : ℝ)
    (h : ∀ x, x = A * (x + 2) * (x + 3) +
      B * (x + 1) * (x + 3) + C * (x + 1) * (x + 2)) :
    -3 = 2 * C := by
  have hx := h (-3)
  norm_num at hx ⊢
  simpa [mul_comm] using hx

theorem gap7 (C : ℝ) (h : -3 = 2 * C) : C = -(3 / 2 : ℝ) := by
  norm_num at h ⊢
  linarith

theorem gap8 :
    antiderivatives integrand = antiderivatives partialFractions := by
  ext F
  simp only [antiderivatives, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hF, hderiv⟩
    refine ⟨hF, ?_⟩
    intro x hx
    have hx1 : x + 1 ≠ 0 := by
      have := hx.2
      linarith
    have hx2 : x + 2 ≠ 0 := by
      have := hx.1
      linarith
    have hx3 : x + 3 ≠ 0 := by
      have := hx.1
      linarith
    exact (hderiv x hx).trans (integrand_eq_partialFractions hx1 hx2 hx3)
  · rintro ⟨hF, hderiv⟩
    refine ⟨hF, ?_⟩
    intro x hx
    have hx1 : x + 1 ≠ 0 := by
      have := hx.2
      linarith
    have hx2 : x + 2 ≠ 0 := by
      have := hx.1
      linarith
    have hx3 : x + 3 ≠ 0 := by
      have := hx.1
      linarith
    exact (hderiv x hx).trans (integrand_eq_partialFractions hx1 hx2 hx3).symm

theorem gap9 :
    antiderivatives integrand = primitiveFamily expandedPrimitive := by
  exact antiderivatives_eq_primitiveFamily_of_hasDerivAt
    expandedPrimitive integrand expandedPrimitive_hasDerivAt

theorem gap10 :
    primitiveFamily expandedPrimitive = primitiveFamily combinedPrimitive := by
  exact
    (antiderivatives_eq_primitiveFamily_of_hasDerivAt
      expandedPrimitive integrand expandedPrimitive_hasDerivAt).symm.trans
    (antiderivatives_eq_primitiveFamily_of_hasDerivAt
      combinedPrimitive integrand combinedPrimitive_hasDerivAt)

theorem gap11 :
    antiderivatives integrand = primitiveFamily combinedPrimitive := by
  exact gap9.trans gap10

end

end ProofGap.Exercise1867
