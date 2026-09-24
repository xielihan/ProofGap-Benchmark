import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.MeanValue

open Set Real

namespace ProofGap.Exercise1868

noncomputable section

def domain : Set ℝ := Set.Ioo (-2) 1

def integrand (x : ℝ) : ℝ := x ^ 10 / (x ^ 2 + x - 2)

def polynomialPart (x : ℝ) : ℝ :=
  x ^ 8 - x ^ 7 + 3 * x ^ 6 - 5 * x ^ 5 + 11 * x ^ 4 -
    21 * x ^ 3 + 43 * x ^ 2 - 85 * x + 171

def quotientRewrite (x : ℝ) : ℝ :=
  polynomialPart x + (-341 * x + 342) / (x ^ 2 + x - 2)

def partialFractionRewrite (x : ℝ) : ℝ :=
  polynomialPart x - 1024 / (3 * (x + 2)) + 1 / (3 * (x - 1))

def antiderivatives (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | DifferentiableOn ℝ F domain ∧ ∀ x ∈ domain, deriv F x = g x}

def primitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ domain, F x = p x + C}

def primitive (x : ℝ) : ℝ :=
  x ^ 9 / 9 - x ^ 8 / 8 + 3 * x ^ 7 / 7 - 5 * x ^ 6 / 6 +
    11 * x ^ 5 / 5 - 21 * x ^ 4 / 4 + 43 * x ^ 3 / 3 -
    85 * x ^ 2 / 2 + 171 * x +
    (1 / 3 : ℝ) * Real.log |(x - 1) / (x + 2) ^ 1024|

private theorem quotient_eq_partial (x : ℝ)
    (hx2 : x + 2 ≠ 0) (hx1 : x - 1 ≠ 0) :
    quotientRewrite x = partialFractionRewrite x := by
  unfold quotientRewrite partialFractionRewrite
  rw [show x ^ 2 + x - 2 = (x + 2) * (x - 1) by ring]
  field_simp [hx2, hx1]
  ring

private def simplePrimitive (x : ℝ) : ℝ :=
  x ^ 9 / 9 - x ^ 8 / 8 + 3 * x ^ 7 / 7 - 5 * x ^ 6 / 6 +
    11 * x ^ 5 / 5 - 21 * x ^ 4 / 4 + 43 * x ^ 3 / 3 -
    85 * x ^ 2 / 2 + 171 * x +
    (1 / 3 : ℝ) * (Real.log (x - 1) - 1024 * Real.log (x + 2))

private theorem primitive_eq_simple (x : ℝ) (hx : x ∈ domain) :
    primitive x = simplePrimitive x := by
  change -2 < x ∧ x < 1 at hx
  have hx1 : x - 1 ≠ 0 := by linarith
  have hx2 : x + 2 ≠ 0 := by linarith
  unfold primitive simplePrimitive
  rw [Real.log_abs, Real.log_div hx1 (pow_ne_zero 1024 hx2), Real.log_pow]
  ring

private theorem hasDerivAt_simple_on_domain (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt simplePrimitive (partialFractionRewrite x) x := by
  change -2 < x ∧ x < 1 at hx
  have hx1 : x - 1 ≠ 0 := by linarith
  have hx2 : x + 2 ≠ 0 := by linarith
  have hm1 : -1 + x ≠ 0 := by linarith
  have hp2 : 2 + x ≠ 0 := by linarith
  have h3m1 : -3 + x * 3 ≠ 0 := by
    intro h
    apply hx1
    linarith
  have h3p2 : 6 + x * 3 ≠ 0 := by
    intro h
    apply hx2
    linarith
  have hp9 := ((hasDerivAt_id x).pow 9).div_const 9
  have hp8 := ((hasDerivAt_id x).pow 8).div_const 8
  have hp7 := (((hasDerivAt_id x).pow 7).const_mul 3).div_const 7
  have hp6 := (((hasDerivAt_id x).pow 6).const_mul 5).div_const 6
  have hp5 := (((hasDerivAt_id x).pow 5).const_mul 11).div_const 5
  have hp4 := (((hasDerivAt_id x).pow 4).const_mul 21).div_const 4
  have hp3 := (((hasDerivAt_id x).pow 3).const_mul 43).div_const 3
  have hp2d := (((hasDerivAt_id x).pow 2).const_mul 85).div_const 2
  have hp1 := (hasDerivAt_id x).const_mul 171
  have hl1 : HasDerivAt (fun y : ℝ => Real.log (y - 1)) (x - 1)⁻¹ x := by
    convert (Real.hasDerivAt_log hx1).comp x ((hasDerivAt_id x).sub_const 1) using 1 <;>
      simp
  have hl2 : HasDerivAt (fun y : ℝ => Real.log (y + 2)) (x + 2)⁻¹ x := by
    convert (Real.hasDerivAt_log hx2).comp x ((hasDerivAt_id x).add_const 2) using 1 <;>
      simp
  have hs1 := hp9.sub hp8
  have hs2 := hs1.add hp7
  have hs3 := hs2.sub hp6
  have hs4 := hs3.add hp5
  have hs5 := hs4.sub hp4
  have hs6 := hs5.add hp3
  have hs7 := hs6.sub hp2d
  have hs8 := hs7.add hp1
  have hlogs := (hl1.sub (hl2.const_mul 1024)).const_mul (1 / 3 : ℝ)
  have htotal := hs8.add hlogs
  convert htotal using 1 <;>
    simp only [simplePrimitive, Function.comp_apply, id_eq] <;>
    norm_num <;>
    unfold partialFractionRewrite polynomialPart <;>
    field_simp [hx1, hx2, hm1, hp2, h3m1, h3p2] <;>
    ring

private theorem primitive_differentiableOn :
    DifferentiableOn ℝ primitive domain := by
  have hs : DifferentiableOn ℝ simplePrimitive domain := by
    intro x hx
    exact (hasDerivAt_simple_on_domain x hx).differentiableAt.differentiableWithinAt
  exact hs.congr (fun x hx => primitive_eq_simple x hx)

private theorem deriv_primitive_on_domain (x : ℝ) (hx : x ∈ domain) :
    deriv primitive x = partialFractionRewrite x := by
  change -2 < x ∧ x < 1 at hx
  have heq : primitive =ᶠ[nhds x] simplePrimitive := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    exact primitive_eq_simple y hy
  calc
    deriv primitive x = deriv simplePrimitive x := heq.deriv_eq
    _ = partialFractionRewrite x := (hasDerivAt_simple_on_domain x hx).deriv

private theorem differ_by_constant_on_domain
    (F p : ℝ → ℝ)
    (hF : DifferentiableOn ℝ F domain)
    (hp : DifferentiableOn ℝ p domain)
    (hderiv : ∀ x ∈ domain, deriv F x = deriv p x) :
    ∃ C : ℝ, ∀ x ∈ domain, F x = p x + C := by
  let H : ℝ → ℝ := fun x => F x - p x
  have hH : DifferentiableOn ℝ H domain := hF.sub hp
  have hzero : ∀ x ∈ domain, deriv H x = 0 := by
    intro x hx
    change -2 < x ∧ x < 1 at hx
    have hFa : DifferentiableAt ℝ F x :=
      (hF x hx).differentiableAt (Ioo_mem_nhds hx.1 hx.2)
    have hpa : DifferentiableAt ℝ p x :=
      (hp x hx).differentiableAt (Ioo_mem_nhds hx.1 hx.2)
    calc
      deriv H x = deriv F x - deriv p x := by
        simpa [H] using (hFa.hasDerivAt.sub hpa.hasDerivAt).deriv
      _ = 0 := by rw [hderiv x hx]; ring
  have h0 : (0 : ℝ) ∈ domain := by norm_num [domain]
  refine ⟨H 0, ?_⟩
  intro x hx
  have heq : H x = H 0 :=
    isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo hH hzero hx h0
  dsimp [H] at heq ⊢
  linarith

theorem gap1 (x : ℝ) (hx2 : x ≠ -2) (hx1 : x ≠ 1) :
    integrand x = quotientRewrite x := by
  have hx2' : x + 2 ≠ 0 := by
    intro h
    apply hx2
    linarith
  have hx1' : x - 1 ≠ 0 := by
    intro h
    apply hx1
    linarith
  have hden : x ^ 2 + x - 2 ≠ 0 := by
    rw [show x ^ 2 + x - 2 = (x + 2) * (x - 1) by ring]
    exact mul_ne_zero hx2' hx1'
  unfold integrand quotientRewrite
  rw [div_eq_mul_inv, div_eq_mul_inv]
  have hpoly :
      x ^ 10 = polynomialPart x * (x ^ 2 + x - 2) + (-341 * x + 342) := by
    unfold polynomialPart
    ring
  rw [hpoly, add_mul, mul_assoc, mul_inv_cancel₀ hden, mul_one]

theorem gap2 (A B x : ℝ) (hx2 : x ≠ -2) (hx1 : x ≠ 1)
    (h : (-341 * x + 342) / (x ^ 2 + x - 2) =
      A / (x + 2) + B / (x - 1)) :
    -341 * x + 342 = A * (x - 1) + B * (x + 2) := by
  have hx2' : x + 2 ≠ 0 := by
    intro hx
    apply hx2
    linarith
  have hx1' : x - 1 ≠ 0 := by
    intro hx
    apply hx1
    linarith
  have hfac : x ^ 2 + x - 2 = (x + 2) * (x - 1) := by ring
  rw [hfac] at h
  field_simp [hx2', hx1'] at h
  convert h using 1 <;> ring

theorem gap3 (A B : ℝ)
    (h : ∀ x, -341 * x + 342 = A * (x - 1) + B * (x + 2)) :
    1024 = -3 * A := by
  have h' := h (-2)
  norm_num at h' ⊢
  nlinarith [h']

theorem gap4 (A : ℝ) (h : 1024 = -3 * A) :
    A = -(1024 / 3 : ℝ) := by
  linarith

theorem gap5 (A B : ℝ)
    (h : ∀ x, -341 * x + 342 = A * (x - 1) + B * (x + 2)) :
    1 = 3 * B := by
  have h' := h 1
  norm_num at h' ⊢
  nlinarith [h']

theorem gap6 (B : ℝ) (h : 1 = 3 * B) : B = (1 / 3 : ℝ) := by
  linarith

theorem gap7 :
    antiderivatives integrand = antiderivatives partialFractionRewrite := by
  apply Set.ext
  intro F
  simp only [antiderivatives, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hFd, hder⟩
    refine ⟨hFd, ?_⟩
    intro x hx
    change -2 < x ∧ x < 1 at hx
    have hx2 : x ≠ -2 := by linarith
    have hx1 : x ≠ 1 := by linarith
    have hx2' : x + 2 ≠ 0 := by linarith
    have hx1' : x - 1 ≠ 0 := by linarith
    calc
      deriv F x = integrand x := hder x hx
      _ = quotientRewrite x := gap1 x hx2 hx1
      _ = partialFractionRewrite x := quotient_eq_partial x hx2' hx1'
  · rintro ⟨hFd, hder⟩
    refine ⟨hFd, ?_⟩
    intro x hx
    change -2 < x ∧ x < 1 at hx
    have hx2 : x ≠ -2 := by linarith
    have hx1 : x ≠ 1 := by linarith
    have hx2' : x + 2 ≠ 0 := by linarith
    have hx1' : x - 1 ≠ 0 := by linarith
    calc
      deriv F x = partialFractionRewrite x := hder x hx
      _ = quotientRewrite x := (quotient_eq_partial x hx2' hx1').symm
      _ = integrand x := (gap1 x hx2 hx1).symm

theorem gap8 : antiderivatives integrand = primitiveFamily primitive := by
  apply Set.ext
  intro F
  simp only [antiderivatives, primitiveFamily, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hFd, hder⟩
    apply differ_by_constant_on_domain F primitive hFd primitive_differentiableOn
    intro x hx
    change -2 < x ∧ x < 1 at hx
    have hx2 : x ≠ -2 := by linarith
    have hx1 : x ≠ 1 := by linarith
    have hx2' : x + 2 ≠ 0 := by linarith
    have hx1' : x - 1 ≠ 0 := by linarith
    calc
      deriv F x = integrand x := hder x hx
      _ = quotientRewrite x := gap1 x hx2 hx1
      _ = partialFractionRewrite x := quotient_eq_partial x hx2' hx1'
      _ = deriv primitive x := (deriv_primitive_on_domain x hx).symm
  · rintro ⟨C, hC⟩
    have hpc : DifferentiableOn ℝ (fun x => primitive x + C) domain :=
      primitive_differentiableOn.add_const C
    have hFd : DifferentiableOn ℝ F domain :=
      hpc.congr (fun x hx => hC x hx)
    refine ⟨hFd, ?_⟩
    intro x hx
    change -2 < x ∧ x < 1 at hx
    have hx2 : x ≠ -2 := by linarith
    have hx1 : x ≠ 1 := by linarith
    have hx2' : x + 2 ≠ 0 := by linarith
    have hx1' : x - 1 ≠ 0 := by linarith
    have heq : F =ᶠ[nhds x] (fun y => primitive y + C) := by
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
      exact hC y hy
    have hpa : DifferentiableAt ℝ primitive x :=
      (primitive_differentiableOn x hx).differentiableAt
        (Ioo_mem_nhds hx.1 hx.2)
    calc
      deriv F x = deriv (fun y => primitive y + C) x := heq.deriv_eq
      _ = deriv primitive x := (hpa.hasDerivAt.add_const C).deriv
      _ = partialFractionRewrite x := deriv_primitive_on_domain x hx
      _ = quotientRewrite x := (quotient_eq_partial x hx2' hx1').symm
      _ = integrand x := (gap1 x hx2 hx1).symm

end

end ProofGap.Exercise1868
