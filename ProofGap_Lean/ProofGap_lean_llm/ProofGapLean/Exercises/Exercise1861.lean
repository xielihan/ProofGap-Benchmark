import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

open Set Real

namespace ProofGap.Exercise1861

noncomputable section

def domain : Set ℝ := Set.Ioo (-1) 2

def integrand (x : ℝ) : ℝ := Real.sqrt (2 + x - x ^ 2)

def completedSquareIntegrand (x : ℝ) : ℝ :=
  Real.sqrt (9 / 4 - (x - 1 / 2) ^ 2)

def antiderivatives (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | DifferentiableOn ℝ F domain ∧ ∀ x ∈ domain, deriv F x = g x}

def primitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ domain, F x = p x + C}

def primitive (x : ℝ) : ℝ :=
  ((2 * x - 1) / 4) * Real.sqrt (2 + x - x ^ 2) +
    (9 / 8 : ℝ) * Real.arcsin ((2 * x - 1) / 3)

private theorem primitive_hasDerivAt {x : ℝ} (hx : x ∈ domain) :
    HasDerivAt primitive (completedSquareIntegrand x) x := by
  have hxBounds : -1 < x ∧ x < 2 := hx
  have hq : 0 < 2 + x - x ^ 2 := by
    have h₁ : 0 < x + 1 := by linarith
    have h₂ : 0 < 2 - x := by linarith
    nlinarith [mul_pos h₁ h₂]
  have hu : -1 < (2 * x - 1) / 3 ∧ (2 * x - 1) / 3 < 1 := by
    constructor <;> linarith
  have hd : 0 < 1 - ((2 * x - 1) / 3) ^ 2 := by
    have h₁ : 0 < 1 + (2 * x - 1) / 3 := by linarith
    have h₂ : 0 < 1 - (2 * x - 1) / 3 := by linarith
    nlinarith [mul_pos h₁ h₂]
  have hr : 0 < Real.sqrt (2 + x - x ^ 2) := Real.sqrt_pos.2 hq
  have ht : 0 < Real.sqrt (1 - ((2 * x - 1) / 3) ^ 2) :=
    Real.sqrt_pos.2 hd
  have hrsq :
      (Real.sqrt (2 + x - x ^ 2)) ^ 2 = 2 + x - x ^ 2 :=
    Real.sq_sqrt (le_of_lt hq)
  have htsq :
      (Real.sqrt (1 - ((2 * x - 1) / 3) ^ 2)) ^ 2 =
        1 - ((2 * x - 1) / 3) ^ 2 :=
    Real.sq_sqrt (le_of_lt hd)
  have hprod :
      (3 * Real.sqrt (1 - ((2 * x - 1) / 3) ^ 2) -
          2 * Real.sqrt (2 + x - x ^ 2)) *
        (3 * Real.sqrt (1 - ((2 * x - 1) / 3) ^ 2) +
          2 * Real.sqrt (2 + x - x ^ 2)) = 0 := by
    nlinarith [hrsq, htsq]
  have hrel :
      Real.sqrt (1 - ((2 * x - 1) / 3) ^ 2) =
        (2 / 3 : ℝ) * Real.sqrt (2 + x - x ^ 2) := by
    rcases mul_eq_zero.mp hprod with h | h
    · linarith
    · exfalso
      nlinarith
  have hlinear :
      HasDerivAt (fun y : ℝ => (2 * y - 1) / 4) (1 / 2) x := by
    convert (((hasDerivAt_id x).const_mul 2).sub_const 1).div_const 4 using 1 <;>
      ring
  have hqDeriv :
      HasDerivAt (fun y : ℝ => 2 + y - y ^ 2) (1 - 2 * x) x := by
    convert ((hasDerivAt_const x (2 : ℝ)).add (hasDerivAt_id x)).sub
      ((hasDerivAt_id x).pow 2) using 1 <;> simp [id] <;> ring
  have hsqrt :
      HasDerivAt (fun y : ℝ => Real.sqrt (2 + y - y ^ 2))
        ((1 - 2 * x) / (2 * Real.sqrt (2 + x - x ^ 2))) x := by
    convert (Real.hasDerivAt_sqrt (ne_of_gt hq)).comp x hqDeriv using 1 <;>
      ring
  have huDeriv :
      HasDerivAt (fun y : ℝ => (2 * y - 1) / 3) (2 / 3) x := by
    convert (((hasDerivAt_id x).const_mul 2).sub_const 1).div_const 3 using 1 <;>
      ring
  have harcsin :
      HasDerivAt (fun y : ℝ => Real.arcsin ((2 * y - 1) / 3))
        ((1 / Real.sqrt (1 - ((2 * x - 1) / 3) ^ 2)) * (2 / 3)) x := by
    exact
      (Real.hasDerivAt_arcsin (by linarith : (2 * x - 1) / 3 ≠ -1)
          (by linarith : (2 * x - 1) / 3 ≠ 1)).comp x huDeriv
  have hcoef :
      (1 / 2) * Real.sqrt (2 + x - x ^ 2) +
          ((2 * x - 1) / 4) *
            ((1 - 2 * x) / (2 * Real.sqrt (2 + x - x ^ 2))) +
        (9 / 8) *
          ((1 / Real.sqrt (1 - ((2 * x - 1) / 3) ^ 2)) * (2 / 3)) =
        Real.sqrt (2 + x - x ^ 2) := by
    rw [hrel]
    field_simp [ne_of_gt hr]
    nlinarith [hrsq]
  have hsum :=
    (hlinear.mul hsqrt).add (harcsin.const_mul (9 / 8 : ℝ))
  have hpraw :
      HasDerivAt primitive (Real.sqrt (2 + x - x ^ 2)) x := by
    simpa only [primitive, hcoef] using hsum
  convert hpraw using 1
  unfold completedSquareIntegrand
  congr 1
  ring

theorem gap1 :
    antiderivatives integrand = antiderivatives completedSquareIntegrand := by
  apply congrArg antiderivatives
  funext x
  unfold integrand completedSquareIntegrand
  congr 1
  ring

theorem gap2 :
    antiderivatives completedSquareIntegrand = primitiveFamily primitive := by
  ext F
  simp only [antiderivatives, primitiveFamily, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hFdiff, hFderiv⟩
    have hPrimDiff : DifferentiableOn ℝ primitive domain := by
      intro x hx
      exact (primitive_hasDerivAt hx).differentiableAt.differentiableWithinAt
    have hDiffDiff :
        DifferentiableOn ℝ (fun x => F x - primitive x) domain :=
      hFdiff.sub hPrimDiff
    have hDiffDeriv :
        ∀ x ∈ domain, deriv (fun y => F y - primitive y) x = 0 := by
      intro x hx
      have hFat : DifferentiableAt ℝ F x :=
        (hFdiff x hx).differentiableAt (isOpen_Ioo.mem_nhds hx)
      have hzero : HasDerivAt (fun y => F y - primitive y) 0 x := by
        convert hFat.hasDerivAt.sub (primitive_hasDerivAt hx) using 1
        rw [hFderiv x hx]
        ring
      exact hzero.deriv
    refine ⟨F 0 - primitive 0, ?_⟩
    intro x hx
    have hzeroMem : (0 : ℝ) ∈ domain := by
      constructor <;> norm_num [domain]
    have hxEq : F x - primitive x = F 0 - primitive 0 :=
      isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
        hDiffDiff hDiffDeriv hx hzeroMem
    linarith
  · rintro ⟨C, hFC⟩
    constructor
    · intro x hx
      have hevent : F =ᶠ[nhds x] (fun y => primitive y + C) := by
        filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
        exact hFC y hy
      have hhas :
          HasDerivAt F (completedSquareIntegrand x) x :=
        ((primitive_hasDerivAt hx).add_const C).congr_of_eventuallyEq hevent
      exact hhas.differentiableAt.differentiableWithinAt
    · intro x hx
      have hevent : F =ᶠ[nhds x] (fun y => primitive y + C) := by
        filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
        exact hFC y hy
      have hhas :
          HasDerivAt F (completedSquareIntegrand x) x :=
        ((primitive_hasDerivAt hx).add_const C).congr_of_eventuallyEq hevent
      exact hhas.deriv

theorem gap3 : antiderivatives integrand = primitiveFamily primitive := by
  rw [gap1, gap2]

end

end ProofGap.Exercise1861
