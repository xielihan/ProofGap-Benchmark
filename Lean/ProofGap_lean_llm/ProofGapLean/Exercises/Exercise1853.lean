import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

open Set Real

namespace ProofGap.Exercise1853

noncomputable section

def radius : ℝ := Real.sqrt ((Real.sqrt 17 - 3) / 4)

def domain : Set ℝ := Set.Ioo (-radius) radius

def integrand (x : ℝ) : ℝ :=
  x / Real.sqrt (1 - 3 * x ^ 2 - 2 * x ^ 4)

def quadraticIntegrand (x : ℝ) : ℝ :=
  x / Real.sqrt ((17 - (4 * x ^ 2 + 3) ^ 2) / 8)

def antiderivatives (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | DifferentiableOn ℝ F domain ∧ ∀ x ∈ domain, deriv F x = g x}

def primitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ domain, F x = p x + C}

def primitive (x : ℝ) : ℝ :=
  (1 / (2 * Real.sqrt 2)) *
    Real.arcsin ((4 * x ^ 2 + 3) / Real.sqrt 17)

private theorem primitive_hasDerivAt (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt primitive (quadraticIntegrand x) x := by
  have hs17sq : (Real.sqrt 17) ^ 2 = (17 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hs17 : 3 < Real.sqrt 17 := by
    nlinarith [Real.sqrt_nonneg 17, hs17sq]
  have hs : 0 < Real.sqrt 17 := by linarith
  have hradNonneg : 0 ≤ (Real.sqrt 17 - 3) / 4 :=
    le_of_lt (div_pos (sub_pos.mpr hs17) (by norm_num))
  have hradSq : radius ^ 2 = (Real.sqrt 17 - 3) / 4 := by
    unfold radius
    exact Real.sq_sqrt hradNonneg
  change -radius < x ∧ x < radius at hx
  have habs : |x| < radius := (abs_lt).2 hx
  have hprod : 0 < (radius - |x|) * (radius + |x|) := by
    apply mul_pos (sub_pos.mpr habs)
    nlinarith [abs_nonneg x]
  have hxSq : x ^ 2 < radius ^ 2 := by
    nlinarith [hprod, sq_abs x]
  have hApos : 0 < 4 * x ^ 2 + 3 := by
    nlinarith [sq_nonneg x]
  have hAlt : 4 * x ^ 2 + 3 < Real.sqrt 17 := by
    nlinarith [hxSq, hradSq]
  have hfactor :
      0 < (Real.sqrt 17 - (4 * x ^ 2 + 3)) *
        (Real.sqrt 17 + (4 * x ^ 2 + 3)) := by
    exact mul_pos (sub_pos.mpr hAlt) (by linarith)
  have hB : 0 < 17 - (4 * x ^ 2 + 3) ^ 2 := by
    nlinarith [hfactor, hs17sq]
  have hu :
      (4 * x ^ 2 + 3) / Real.sqrt 17 ∈ Set.Ioo (-1 : ℝ) 1 := by
    constructor
    · have hupos : 0 < (4 * x ^ 2 + 3) / Real.sqrt 17 :=
        div_pos hApos hs
      linarith
    · exact (div_lt_one hs).2 hAlt
  have hinner :
      HasDerivAt
        (fun y : ℝ => (4 * y ^ 2 + 3) / Real.sqrt 17)
        ((8 * x) / Real.sqrt 17) x := by
    convert
      (((((hasDerivAt_id x).pow 2).const_mul 4).add_const 3).div_const
        (Real.sqrt 17)) using 1 <;>
      simp only [id] <;> ring
  have hraw :
      HasDerivAt
        (fun y : ℝ =>
          (1 / (2 * Real.sqrt 2)) *
            Real.arcsin ((4 * y ^ 2 + 3) / Real.sqrt 17))
        ((1 / (2 * Real.sqrt 2)) *
          ((1 / Real.sqrt
            (1 - ((4 * x ^ 2 + 3) / Real.sqrt 17) ^ 2)) *
            ((8 * x) / Real.sqrt 17))) x := by
    exact
      ((Real.hasDerivAt_arcsin (ne_of_gt hu.1) (ne_of_lt hu.2)).comp x hinner).const_mul
        (1 / (2 * Real.sqrt 2))
  have hone :
      1 - ((4 * x ^ 2 + 3) / Real.sqrt 17) ^ 2 =
        (17 - (4 * x ^ 2 + 3) ^ 2) / 17 := by
    rw [div_pow, hs17sq]
    ring
  have hsqrtInner :
      Real.sqrt (1 - ((4 * x ^ 2 + 3) / Real.sqrt 17) ^ 2) =
        Real.sqrt (17 - (4 * x ^ 2 + 3) ^ 2) / Real.sqrt 17 := by
    rw [hone, Real.sqrt_div (le_of_lt hB)]
  have hsqrt4 : Real.sqrt (4 : ℝ) = 2 := by
    calc
      Real.sqrt (4 : ℝ) = Real.sqrt ((2 : ℝ) ^ 2) := by norm_num
      _ = 2 := Real.sqrt_sq (by norm_num)
  have hsqrt8 : Real.sqrt (8 : ℝ) = 2 * Real.sqrt 2 := by
    calc
      Real.sqrt (8 : ℝ) = Real.sqrt ((4 : ℝ) * 2) := by norm_num
      _ = Real.sqrt 4 * Real.sqrt 2 := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
      _ = 2 * Real.sqrt 2 := by rw [hsqrt4]
  have hsqrtTarget :
      Real.sqrt ((17 - (4 * x ^ 2 + 3) ^ 2) / 8) =
        Real.sqrt (17 - (4 * x ^ 2 + 3) ^ 2) /
          (2 * Real.sqrt 2) := by
    rw [Real.sqrt_div (le_of_lt hB), hsqrt8]
  have hsqrtB : 0 < Real.sqrt (17 - (4 * x ^ 2 + 3) ^ 2) :=
    Real.sqrt_pos.2 hB
  have hsqrt2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt2sq : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hcoef :
      (1 / (2 * Real.sqrt 2)) *
          ((1 / Real.sqrt
            (1 - ((4 * x ^ 2 + 3) / Real.sqrt 17) ^ 2)) *
            ((8 * x) / Real.sqrt 17)) =
        quadraticIntegrand x := by
    rw [hsqrtInner]
    unfold quadraticIntegrand
    rw [hsqrtTarget]
    field_simp [ne_of_gt hs, ne_of_gt hsqrtB, ne_of_gt hsqrt2]
    nlinarith [hsqrt2sq]
  rw [← hcoef]
  simpa only [primitive] using hraw

theorem gap1 :
    antiderivatives integrand = antiderivatives quadraticIntegrand := by
  congr 1
  funext x
  simp only [integrand, quadraticIntegrand]
  congr 2
  ring

theorem gap2 :
    antiderivatives quadraticIntegrand = primitiveFamily primitive := by
  ext F
  constructor
  · rintro ⟨hDiff, hDeriv⟩
    have hpDiff : DifferentiableOn ℝ primitive domain := by
      intro x hx
      exact (primitive_hasDerivAt x hx).differentiableAt.differentiableWithinAt
    have hsubDiff :
        DifferentiableOn ℝ (fun x => F x - primitive x) domain :=
      hDiff.sub hpDiff
    have hsubDeriv :
        ∀ x ∈ domain, deriv (fun y => F y - primitive y) x = 0 := by
      intro x hx
      have hFat : DifferentiableAt ℝ F x :=
        (hDiff x hx).differentiableAt (isOpen_Ioo.mem_nhds hx)
      have hFd : HasDerivAt F (quadraticIntegrand x) x := by
        rw [← hDeriv x hx]
        exact hFat.hasDerivAt
      have hz := (hFd.sub (primitive_hasDerivAt x hx)).deriv
      simpa using hz
    have hs17sq : (Real.sqrt 17) ^ 2 = (17 : ℝ) :=
      Real.sq_sqrt (by norm_num)
    have hs17 : 3 < Real.sqrt 17 := by
      nlinarith [Real.sqrt_nonneg 17, hs17sq]
    have hradius : 0 < radius := by
      unfold radius
      apply Real.sqrt_pos.2
      exact div_pos (sub_pos.mpr hs17) (by norm_num)
    have hzero : (0 : ℝ) ∈ domain := by
      change -radius < (0 : ℝ) ∧ (0 : ℝ) < radius
      exact ⟨neg_lt_zero.mpr hradius, hradius⟩
    refine ⟨F 0 - primitive 0, ?_⟩
    intro x hx
    have hc :
        F x - primitive x = F 0 - primitive 0 :=
      isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
        hsubDiff hsubDeriv hx hzero
    linarith
  · rintro ⟨C, hEq⟩
    have hHas : ∀ x ∈ domain, HasDerivAt F (quadraticIntegrand x) x := by
      intro x hx
      have hlocal :
          F =ᶠ[nhds x] (fun y => primitive y + C) :=
        Filter.mem_of_superset (isOpen_Ioo.mem_nhds hx) (fun y hy => hEq y hy)
      exact ((primitive_hasDerivAt x hx).add_const C).congr_of_eventuallyEq
        hlocal
    constructor
    · intro x hx
      exact (hHas x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      exact (hHas x hx).deriv

theorem gap3 : antiderivatives integrand = primitiveFamily primitive := by
  rw [gap1, gap2]

end

end ProofGap.Exercise1853
