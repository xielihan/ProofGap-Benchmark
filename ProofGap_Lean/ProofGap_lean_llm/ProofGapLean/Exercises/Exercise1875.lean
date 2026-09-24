import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.MeanValue

open Set Real

namespace ProofGap.Exercise1875

noncomputable section

def domain : Set ℝ := Set.Ioo (-1) 1

def denominator (x : ℝ) : ℝ :=
  x ^ 5 + x ^ 4 - 2 * x ^ 3 - 2 * x ^ 2 + x + 1

def integrand (x : ℝ) : ℝ := 1 / denominator x

def factoredIntegrand (x : ℝ) : ℝ := 1 / ((x - 1) ^ 2 * (x + 1) ^ 3)

def partialFractions (x : ℝ) : ℝ :=
  -3 / (16 * (x - 1)) + 1 / (8 * (x - 1) ^ 2) +
    3 / (16 * (x + 1)) + 1 / (4 * (x + 1) ^ 2) +
    1 / (4 * (x + 1) ^ 3)

def antiderivatives (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | DifferentiableOn ℝ F domain ∧ ∀ x ∈ domain, deriv F x = g x}

def primitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ domain, F x = p x + C}

def expandedPrimitive (x : ℝ) : ℝ :=
  -(3 / 16 : ℝ) * Real.log |x - 1| - 1 / (8 * (x - 1)) +
    (3 / 16 : ℝ) * Real.log |x + 1| - 1 / (4 * (x + 1)) -
    1 / (8 * (x + 1) ^ 2)

def combinedPrimitive (x : ℝ) : ℝ :=
  (3 / 16 : ℝ) * Real.log |(x + 1) / (x - 1)| -
    (3 * x ^ 2 + 3 * x - 2) / (8 * (x - 1) * (x + 1) ^ 2)

private theorem integrand_eq_partialFractions (x : ℝ) (hx : x ∈ domain) :
    integrand x = partialFractions x := by
  rcases hx with ⟨hxlow, hxhigh⟩
  have hm : x - 1 ≠ 0 := by
    intro h
    linarith
  have hp : x + 1 ≠ 0 := by
    intro h
    linarith
  have hfactor : denominator x = (x - 1) ^ 2 * (x + 1) ^ 3 := by
    unfold denominator
    ring
  unfold integrand
  rw [hfactor]
  unfold partialFractions
  field_simp [hm, hp]
  ring

private theorem expandedPrimitive_hasDerivAt (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt expandedPrimitive (partialFractions x) x := by
  rcases hx with ⟨hxlow, hxhigh⟩
  have hm : x - 1 ≠ 0 := by
    intro h
    linarith
  have hp : x + 1 ≠ 0 := by
    intro h
    linarith
  have hmLog : HasDerivAt (fun y : ℝ => Real.log |y - 1|) (x - 1)⁻¹ x := by
    simpa only [Real.log_abs, Function.comp_apply, id_eq, mul_one] using
      (Real.hasDerivAt_log hm).comp x ((hasDerivAt_id x).sub_const 1)
  have hpLog : HasDerivAt (fun y : ℝ => Real.log |y + 1|) (x + 1)⁻¹ x := by
    simpa only [Real.log_abs, Function.comp_apply, id_eq, mul_one] using
      (Real.hasDerivAt_log hp).comp x ((hasDerivAt_id x).add_const 1)
  have hmDen :=
    (((hasDerivAt_const (x := x) (c := (8 : ℝ))).mul
      ((hasDerivAt_id x).sub_const 1)).inv
        (mul_ne_zero (by norm_num) hm))
  have hpDen :=
    (((hasDerivAt_const (x := x) (c := (4 : ℝ))).mul
      ((hasDerivAt_id x).add_const 1)).inv
        (mul_ne_zero (by norm_num) hp))
  have hpDenSq :=
    (((hasDerivAt_const (x := x) (c := (8 : ℝ))).mul
      (((hasDerivAt_id x).add_const 1).pow 2)).inv
        (mul_ne_zero (by norm_num) (pow_ne_zero 2 hp)))
  have H :=
    ((((hmLog.const_mul (-(3 / 16 : ℝ))).sub hmDen).add
      (hpLog.const_mul (3 / 16 : ℝ))).sub hpDen).sub hpDenSq
  convert H using 1
  · funext y
    simp [expandedPrimitive, one_div, mul_comm]
  · simp [partialFractions, one_div]
    field_simp [hm, hp]
    ring

private theorem expandedPrimitive_spec :
    DifferentiableOn ℝ expandedPrimitive domain ∧
      ∀ x ∈ domain, deriv expandedPrimitive x = partialFractions x := by
  constructor
  · intro x hx
    exact (expandedPrimitive_hasDerivAt x hx).differentiableAt.differentiableWithinAt
  · intro x hx
    exact (expandedPrimitive_hasDerivAt x hx).deriv

private theorem antiderivatives_eq_primitive
    (p g : ℝ → ℝ)
    (hp : DifferentiableOn ℝ p domain)
    (hp' : ∀ x ∈ domain, deriv p x = g x) :
    antiderivatives g = primitiveFamily p := by
  apply Set.ext
  intro F
  simp only [antiderivatives, primitiveFamily, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hF, hF'⟩
    have hdiff : DifferentiableOn ℝ (fun x => F x - p x) domain := hF.sub hp
    have hzero : ∀ x ∈ domain, deriv (fun y => F y - p y) x = 0 := by
      intro x hx
      have hFa : DifferentiableAt ℝ F x :=
        (hF x hx).differentiableAt (isOpen_Ioo.mem_nhds hx)
      have hpa : DifferentiableAt ℝ p x :=
        (hp x hx).differentiableAt (isOpen_Ioo.mem_nhds hx)
      calc
        deriv (fun y => F y - p y) x = deriv F x - deriv p x :=
          (hFa.hasDerivAt.sub hpa.hasDerivAt).deriv
        _ = 0 := by rw [hF' x hx, hp' x hx]; ring
    have hzero_mem : (0 : ℝ) ∈ domain := by norm_num [domain]
    refine ⟨F 0 - p 0, ?_⟩
    intro x hx
    have h : F x - p x = F 0 - p 0 :=
      isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo hdiff hzero
        hx hzero_mem
    calc
      F x = (F x - p x) + p x := by ring
      _ = (F 0 - p 0) + p x := by rw [h]
      _ = p x + (F 0 - p 0) := by ring
  · rintro ⟨C, hFC⟩
    have hsum : DifferentiableOn ℝ (fun x => p x + C) domain :=
      hp.add (differentiableOn_const (c := C))
    have hFd : DifferentiableOn ℝ F domain :=
      hsum.congr (fun x hx => hFC x hx)
    refine ⟨hFd, ?_⟩
    intro x hx
    have hpa : DifferentiableAt ℝ p x :=
      (hp x hx).differentiableAt (isOpen_Ioo.mem_nhds hx)
    have hev : F =ᶠ[nhds x] (fun y => p y + C) := by
      filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
      exact hFC y hy
    calc
      deriv F x = deriv (fun y => p y + C) x :=
        Filter.EventuallyEq.deriv_eq hev
      _ = deriv p x := (hpa.hasDerivAt.add_const C).deriv
      _ = g x := hp' x hx

private theorem expanded_eq_combined :
    Set.EqOn expandedPrimitive combinedPrimitive domain := by
  intro x hx
  rcases hx with ⟨hxlow, hxhigh⟩
  have hm : x - 1 ≠ 0 := by
    intro h
    linarith
  have hp : x + 1 ≠ 0 := by
    intro h
    linarith
  unfold expandedPrimitive combinedPrimitive
  rw [Real.log_abs, Real.log_abs, Real.log_abs, Real.log_div hp hm]
  field_simp [hm, hp]
  ring

private theorem primitiveFamily_congr {p q : ℝ → ℝ}
    (h : Set.EqOn p q domain) : primitiveFamily p = primitiveFamily q := by
  apply Set.ext
  intro F
  simp only [primitiveFamily, Set.mem_setOf_eq]
  constructor
  · rintro ⟨C, hF⟩
    refine ⟨C, ?_⟩
    intro x hx
    rw [hF x hx, h hx]
  · rintro ⟨C, hF⟩
    refine ⟨C, ?_⟩
    intro x hx
    rw [hF x hx, h hx]

theorem gap1 :
    ∀ x, x ≠ -1 → x ≠ 1 → integrand x = factoredIntegrand x := by
  intro x _ _
  unfold integrand factoredIntegrand denominator
  congr 1
  ring

theorem gap2 :
    ∃ A B C D E : ℝ, ∀ x, x ≠ -1 → x ≠ 1 →
      factoredIntegrand x =
        A / (x - 1) + B / (x - 1) ^ 2 + C / (x + 1) +
          D / (x + 1) ^ 2 + E / (x + 1) ^ 3 := by
  refine ⟨-(3 / 16 : ℝ), (1 / 8 : ℝ), (3 / 16 : ℝ), (1 / 4 : ℝ),
    (1 / 4 : ℝ), ?_⟩
  intro x hxneg hxpos
  have hm : x - 1 ≠ 0 := by
    intro h
    apply hxpos
    linarith
  have hp : x + 1 ≠ 0 := by
    intro h
    apply hxneg
    linarith
  unfold factoredIntegrand
  field_simp [hm, hp]
  ring

theorem gap3 :
    ∃ A B C D E : ℝ, ∀ x, 1 =
      A * (x - 1) * (x + 1) ^ 3 + B * (x + 1) ^ 3 +
        C * (x - 1) ^ 2 * (x + 1) ^ 2 +
        D * (x - 1) ^ 2 * (x + 1) + E * (x - 1) ^ 2 := by
  refine ⟨-(3 / 16 : ℝ), (1 / 8 : ℝ), (3 / 16 : ℝ), (1 / 4 : ℝ),
    (1 / 4 : ℝ), ?_⟩
  intro x
  ring

theorem gap4 : ∃ B : ℝ, 1 = 8 * B := by
  exact ⟨(1 / 8 : ℝ), by norm_num⟩

theorem gap5 : ∃ B : ℝ, B = (1 / 8 : ℝ) := by
  exact ⟨(1 / 8 : ℝ), rfl⟩

theorem gap6 : ∃ E : ℝ, 1 = 4 * E := by
  exact ⟨(1 / 4 : ℝ), by norm_num⟩

theorem gap7 : ∃ E : ℝ, E = (1 / 4 : ℝ) := by
  exact ⟨(1 / 4 : ℝ), rfl⟩

theorem gap8 : ∃ A B C D E : ℝ, -A + B + C + D + E = 1 := by
  refine ⟨-(3 / 16 : ℝ), (1 / 8 : ℝ), (3 / 16 : ℝ), (1 / 4 : ℝ),
    (1 / 4 : ℝ), ?_⟩
  norm_num

theorem gap9 : ∃ A B C D E : ℝ, 27 * A + 27 * B + 9 * C + 3 * D + E = 1 := by
  refine ⟨-(3 / 16 : ℝ), (1 / 8 : ℝ), (3 / 16 : ℝ), (1 / 4 : ℝ),
    (1 / 4 : ℝ), ?_⟩
  norm_num

theorem gap10 : ∃ A B C D E : ℝ, 3 * A - B + 9 * C - 9 * D + 9 * E = 1 := by
  refine ⟨-(3 / 16 : ℝ), (1 / 8 : ℝ), (3 / 16 : ℝ), (1 / 4 : ℝ),
    (1 / 4 : ℝ), ?_⟩
  norm_num

theorem gap11 : ∃ A : ℝ, A = -(3 / 16 : ℝ) := by
  exact ⟨-(3 / 16 : ℝ), rfl⟩

theorem gap12 : ∃ C : ℝ, C = (3 / 16 : ℝ) := by
  exact ⟨(3 / 16 : ℝ), rfl⟩

theorem gap13 : ∃ D : ℝ, D = (1 / 4 : ℝ) := by
  exact ⟨(1 / 4 : ℝ), rfl⟩

theorem gap14 :
    antiderivatives integrand = antiderivatives partialFractions := by
  apply Set.ext
  intro F
  simp only [antiderivatives, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hF, hderiv⟩
    refine ⟨hF, ?_⟩
    intro x hx
    calc
      deriv F x = integrand x := hderiv x hx
      _ = partialFractions x := integrand_eq_partialFractions x hx
  · rintro ⟨hF, hderiv⟩
    refine ⟨hF, ?_⟩
    intro x hx
    calc
      deriv F x = partialFractions x := hderiv x hx
      _ = integrand x := (integrand_eq_partialFractions x hx).symm

theorem gap15 :
    antiderivatives integrand = primitiveFamily expandedPrimitive := by
  exact gap14.trans
    (antiderivatives_eq_primitive expandedPrimitive partialFractions
      expandedPrimitive_spec.1 expandedPrimitive_spec.2)

theorem gap16 :
    antiderivatives integrand = primitiveFamily combinedPrimitive := by
  exact gap15.trans (primitiveFamily_congr expanded_eq_combined)

end

end ProofGap.Exercise1875
