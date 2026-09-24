import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

open Set Real

namespace ProofGap.Exercise1851

noncomputable section

def domain : Set ℝ :=
  Set.Ioo ((1 - Real.sqrt 21) / 2) ((1 + Real.sqrt 21) / 2)

def integrand (x : ℝ) : ℝ := x / Real.sqrt (5 + x - x ^ 2)

def splitIntegrand (x : ℝ) : ℝ :=
  (2 * x - 1) / (2 * Real.sqrt (5 + x - x ^ 2)) +
    1 / (2 * Real.sqrt (5 + x - x ^ 2))

def antiderivatives (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | DifferentiableOn ℝ F domain ∧ ∀ x ∈ domain, deriv F x = g x}

def primitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ domain, F x = p x + C}

def primitive (x : ℝ) : ℝ :=
  -Real.sqrt (5 + x - x ^ 2) +
    (1 / 2 : ℝ) * Real.arcsin ((2 * x - 1) / Real.sqrt 21)

private theorem primitive_hasDerivAt (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt primitive (splitIntegrand x) x := by
  change (1 - Real.sqrt 21) / 2 < x ∧
    x < (1 + Real.sqrt 21) / 2 at hx
  rcases hx with ⟨hxL, hxR⟩
  have hs : 0 < Real.sqrt 21 := Real.sqrt_pos.2 (by norm_num)
  have hs0 : Real.sqrt 21 ≠ 0 := ne_of_gt hs
  have hs2 : (Real.sqrt 21) ^ 2 = 21 :=
    Real.sq_sqrt (by norm_num)
  have hq : 0 < 5 + x - x ^ 2 := by
    nlinarith
  have hqroot : 0 < Real.sqrt (5 + x - x ^ 2) :=
    Real.sqrt_pos.2 hq
  have huL : -1 < (2 * x - 1) / Real.sqrt 21 := by
    apply (lt_div_iff₀ hs).2
    nlinarith
  have huR : (2 * x - 1) / Real.sqrt 21 < 1 := by
    apply (div_lt_iff₀ hs).2
    nlinarith
  have hurad : 0 < 1 - ((2 * x - 1) / Real.sqrt 21) ^ 2 := by
    have hp : 0 <
        (1 - (2 * x - 1) / Real.sqrt 21) *
          ((2 * x - 1) / Real.sqrt 21 + 1) :=
      mul_pos (sub_pos.2 huR) (by linarith)
    nlinarith
  have hpoly :
      HasDerivAt (fun y : ℝ => 5 + y - y ^ 2) (1 - 2 * x) x := by
    convert (((hasDerivAt_const x 5).add (hasDerivAt_id x)).sub
      ((hasDerivAt_id x).pow 2)) using 1 <;> simp [id_eq] <;> ring
  have hsqrt :
      HasDerivAt (fun y : ℝ => Real.sqrt (5 + y - y ^ 2))
        ((1 - 2 * x) / (2 * Real.sqrt (5 + x - x ^ 2))) x := by
    convert (Real.hasDerivAt_sqrt (ne_of_gt hq)).comp x hpoly using 1 <;> ring
  have hu :
      HasDerivAt (fun y : ℝ => (2 * y - 1) / Real.sqrt 21)
        (2 / Real.sqrt 21) x := by
    convert ((((hasDerivAt_id x).const_mul 2).sub_const 1).div_const
      (Real.sqrt 21)) using 1 <;> ring
  have harcsin0 :
      HasDerivAt Real.arcsin
        (1 / Real.sqrt (1 - ((2 * x - 1) / Real.sqrt 21) ^ 2))
        ((2 * x - 1) / Real.sqrt 21) :=
    Real.hasDerivAt_arcsin (ne_of_gt huL) (ne_of_lt huR)
  have harcsin :
      HasDerivAt
        (fun y : ℝ => Real.arcsin ((2 * y - 1) / Real.sqrt 21))
        ((1 / Real.sqrt (1 - ((2 * x - 1) / Real.sqrt 21) ^ 2)) *
          (2 / Real.sqrt 21)) x := by
    simpa only [Function.comp_apply] using harcsin0.comp x hu
  have hrel :
      21 * (1 - ((2 * x - 1) / Real.sqrt 21) ^ 2) =
        4 * (5 + x - x ^ 2) := by
    field_simp [hs0]
    nlinarith
  have hrootSq :
      (Real.sqrt (1 - ((2 * x - 1) / Real.sqrt 21) ^ 2) *
          Real.sqrt 21) ^ 2 =
        (2 * Real.sqrt (5 + x - x ^ 2)) ^ 2 := by
    calc
      (Real.sqrt (1 - ((2 * x - 1) / Real.sqrt 21) ^ 2) *
          Real.sqrt 21) ^ 2 =
          (Real.sqrt (1 - ((2 * x - 1) / Real.sqrt 21) ^ 2)) ^ 2 *
            (Real.sqrt 21) ^ 2 := by ring
      _ = (1 - ((2 * x - 1) / Real.sqrt 21) ^ 2) * 21 := by
        rw [Real.sq_sqrt (le_of_lt hurad), hs2]
      _ = 4 * (5 + x - x ^ 2) := by nlinarith
      _ = (2 * Real.sqrt (5 + x - x ^ 2)) ^ 2 := by
        have hsqrtSq : (Real.sqrt (5 + x - x ^ 2)) ^ 2 =
            5 + x - x ^ 2 := Real.sq_sqrt (le_of_lt hq)
        nlinarith
  have hroot :
      Real.sqrt (1 - ((2 * x - 1) / Real.sqrt 21) ^ 2) *
          Real.sqrt 21 =
        2 * Real.sqrt (5 + x - x ^ 2) := by
    have hleft : 0 ≤
        Real.sqrt (1 - ((2 * x - 1) / Real.sqrt 21) ^ 2) *
          Real.sqrt 21 :=
      mul_nonneg (Real.sqrt_nonneg _) (le_of_lt hs)
    have hright : 0 ≤ 2 * Real.sqrt (5 + x - x ^ 2) :=
      mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
    nlinarith
  have hcoef :
      (1 / 2 : ℝ) *
          ((1 / Real.sqrt (1 - ((2 * x - 1) / Real.sqrt 21) ^ 2)) *
            (2 / Real.sqrt 21)) =
        1 / (2 * Real.sqrt (5 + x - x ^ 2)) := by
    calc
      (1 / 2 : ℝ) *
          ((1 / Real.sqrt (1 - ((2 * x - 1) / Real.sqrt 21) ^ 2)) *
            (2 / Real.sqrt 21)) =
          1 / (Real.sqrt (1 - ((2 * x - 1) / Real.sqrt 21) ^ 2) *
            Real.sqrt 21) := by
              field_simp [ne_of_gt (Real.sqrt_pos.2 hurad), hs0]
              <;> ring
      _ = 1 / (2 * Real.sqrt (5 + x - x ^ 2)) := by rw [hroot]
  have hraw :
      HasDerivAt primitive
        (-((1 - 2 * x) / (2 * Real.sqrt (5 + x - x ^ 2))) +
          (1 / 2 : ℝ) *
            ((1 / Real.sqrt (1 - ((2 * x - 1) / Real.sqrt 21) ^ 2)) *
              (2 / Real.sqrt 21))) x := by
    convert hsqrt.neg.add (harcsin.const_mul (1 / 2 : ℝ)) using 1 <;>
      simp [primitive]
  convert hraw using 1
  rw [hcoef]
  unfold splitIntegrand
  ring

theorem gap1 : antiderivatives integrand = antiderivatives splitIntegrand := by
  have h : integrand = splitIntegrand := by
    funext x
    unfold integrand splitIntegrand
    ring
  rw [h]

theorem gap2 :
    antiderivatives splitIntegrand = primitiveFamily primitive := by
  ext F
  constructor
  · intro hF
    change DifferentiableOn ℝ F domain ∧
      ∀ x ∈ domain, deriv F x = splitIntegrand x at hF
    change ∃ C : ℝ, ∀ x ∈ domain, F x = primitive x + C
    rcases hF with ⟨hFdiff, hFderiv⟩
    have hFat : ∀ x ∈ domain, DifferentiableAt ℝ F x := by
      intro x hx
      exact (hFdiff x hx).differentiableAt (Ioo_mem_nhds hx.1 hx.2)
    have hdiff : DifferentiableOn ℝ (fun y => F y - primitive y) domain := by
      intro x hx
      exact (((hFat x hx).hasDerivAt).sub
        (primitive_hasDerivAt x hx)).differentiableAt.differentiableWithinAt
    have hzero : ∀ x ∈ domain,
        deriv (fun y => F y - primitive y) x = 0 := by
      intro x hx
      have hd := (((hFat x hx).hasDerivAt).sub
        (primitive_hasDerivAt x hx)).deriv
      rw [hFderiv x hx] at hd
      simpa using hd
    have hs : 0 < Real.sqrt 21 := Real.sqrt_pos.2 (by norm_num)
    have hs2 : (Real.sqrt 21) ^ 2 = 21 :=
      Real.sq_sqrt (by norm_num)
    have hs1 : 1 < Real.sqrt 21 := by
      nlinarith
    have h0 : (0 : ℝ) ∈ domain := by
      change (1 - Real.sqrt 21) / 2 < 0 ∧
        0 < (1 + Real.sqrt 21) / 2
      constructor <;> nlinarith
    refine ⟨F 0 - primitive 0, ?_⟩
    intro x hx
    have heq : F x - primitive x = F 0 - primitive 0 :=
      isOpen_Ioo.is_const_of_deriv_eq_zero
        isPreconnected_Ioo hdiff hzero hx h0
    linarith
  · intro hF
    change ∃ C : ℝ, ∀ x ∈ domain, F x = primitive x + C at hF
    change DifferentiableOn ℝ F domain ∧
      ∀ x ∈ domain, deriv F x = splitIntegrand x
    rcases hF with ⟨C, hFC⟩
    have hlocal : ∀ x ∈ domain,
        HasDerivAt F (splitIntegrand x) x := by
      intro x hx
      have hevent :
          Filter.EventuallyEq (nhds x) F (fun y => primitive y + C) := by
        filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
        exact hFC y hy
      exact ((primitive_hasDerivAt x hx).add_const C).congr_of_eventuallyEq hevent
    constructor
    · intro x hx
      exact (hlocal x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      exact (hlocal x hx).deriv

theorem gap3 : antiderivatives integrand = primitiveFamily primitive := by
  rw [gap1, gap2]

end

end ProofGap.Exercise1851
