import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1975

noncomputable section

def branch : Set ℝ := Set.Ioi 0
def originalIntegrand (x : ℝ) :=
  Real.sqrt (x * (x + 1)) / (Real.sqrt x + Real.sqrt (x + 1))
def rationalizedIntegrand (x : ℝ) :=
  Real.sqrt (x * (x + 1)) * (Real.sqrt (x + 1) - Real.sqrt x) /
    ((x + 1) - x)
def expandedIntegrand (x : ℝ) :=
  (x + 1) * Real.sqrt x - x * Real.sqrt (x + 1)
def powerIntegrand (x : ℝ) :=
  x * Real.sqrt x + Real.sqrt x -
    (x + 1) * Real.sqrt (x + 1) + Real.sqrt (x + 1)
def primitive (x : ℝ) :=
  2 / 3 * ((x + 1) * Real.sqrt (x + 1) + x * Real.sqrt x) -
    2 / 5 *
      ((x + 1) ^ 2 * Real.sqrt (x + 1) - x ^ 2 * Real.sqrt x)
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def PrimitiveFamily : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = primitive x + C}

private theorem antiderivatives_ext {f g : ℝ → ℝ}
    (hfg : ∀ x ∈ branch, f x = g x) :
    AntiderivativesOn f = AntiderivativesOn g := by
  apply Set.ext
  intro F
  simp only [AntiderivativesOn, Set.mem_setOf_eq]
  constructor
  · intro hF x hx
    exact (hF x hx).congr_deriv (hfg x hx)
  · intro hF x hx
    exact (hF x hx).congr_deriv (hfg x hx).symm

private theorem original_eq_rationalized (x : ℝ) (hx : x ∈ branch) :
    originalIntegrand x = rationalizedIntegrand x := by
  change 0 < x at hx
  have hx0 : 0 ≤ x := le_of_lt hx
  have hx1 : 0 ≤ x + 1 := by nlinarith
  have hsx := Real.sq_sqrt hx0
  have hsx1 := Real.sq_sqrt hx1
  have hspos : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hs1pos : 0 < Real.sqrt (x + 1) := Real.sqrt_pos.2 (by nlinarith)
  have hsum : Real.sqrt x + Real.sqrt (x + 1) ≠ 0 :=
    ne_of_gt (add_pos hspos hs1pos)
  have hconj :
      (Real.sqrt (x + 1) - Real.sqrt x) *
          (Real.sqrt x + Real.sqrt (x + 1)) = 1 := by
    nlinarith
  unfold originalIntegrand rationalizedIntegrand
  rw [Real.sqrt_mul hx0]
  rw [show (x + 1) - x = 1 by ring, div_one]
  apply (div_eq_iff hsum).2
  calc
    Real.sqrt x * Real.sqrt (x + 1) =
        Real.sqrt x * Real.sqrt (x + 1) * 1 := by ring
    _ = Real.sqrt x * Real.sqrt (x + 1) *
        ((Real.sqrt (x + 1) - Real.sqrt x) *
          (Real.sqrt x + Real.sqrt (x + 1))) := by rw [hconj]
    _ = (Real.sqrt x * Real.sqrt (x + 1) *
          (Real.sqrt (x + 1) - Real.sqrt x)) *
          (Real.sqrt x + Real.sqrt (x + 1)) := by ring

private theorem rationalized_eq_expanded (x : ℝ) (hx : x ∈ branch) :
    rationalizedIntegrand x = expandedIntegrand x := by
  change 0 < x at hx
  have hx0 : 0 ≤ x := le_of_lt hx
  have hx1 : 0 ≤ x + 1 := by nlinarith
  have hsx := Real.sq_sqrt hx0
  have hsx1 := Real.sq_sqrt hx1
  unfold rationalizedIntegrand expandedIntegrand
  rw [Real.sqrt_mul hx0]
  rw [show (x + 1) - x = 1 by ring, div_one]
  calc
    Real.sqrt x * Real.sqrt (x + 1) *
        (Real.sqrt (x + 1) - Real.sqrt x) =
      Real.sqrt x * (Real.sqrt (x + 1)) ^ 2 -
        (Real.sqrt x) ^ 2 * Real.sqrt (x + 1) := by ring
    _ = (x + 1) * Real.sqrt x - x * Real.sqrt (x + 1) := by
      rw [hsx1, hsx]
      ring

private theorem expanded_eq_power (x : ℝ) (hx : x ∈ branch) :
    expandedIntegrand x = powerIntegrand x := by
  unfold expandedIntegrand powerIntegrand
  ring

private theorem primitive_hasDerivAt (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt primitive (powerIntegrand x) x := by
  change 0 < x at hx
  have hx1 : 0 < x + 1 := by nlinarith
  have hs0 : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hx)
  have hs10 : Real.sqrt (x + 1) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hx1)
  have hsq : (Real.sqrt x) ^ 2 = x :=
    Real.sq_sqrt (le_of_lt hx)
  have hsq1 : (Real.sqrt (x + 1)) ^ 2 = x + 1 :=
    Real.sq_sqrt (le_of_lt hx1)
  have hsx : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt x)) x :=
    Real.hasDerivAt_sqrt (ne_of_gt hx)
  have hlin : HasDerivAt (fun y : ℝ => y + 1) 1 x :=
    (hasDerivAt_id x).add_const 1
  have hs1 : HasDerivAt (fun y : ℝ => Real.sqrt (y + 1))
      (1 / (2 * Real.sqrt (x + 1))) x := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_sqrt (ne_of_gt hx1)).comp x hlin
  have hp1 : HasDerivAt
      (fun y : ℝ => (y + 1) * Real.sqrt (y + 1))
      (Real.sqrt (x + 1) + (x + 1) / (2 * Real.sqrt (x + 1))) x := by
    convert hlin.mul hs1 using 1 <;> ring
  have hp0 : HasDerivAt
      (fun y : ℝ => y * Real.sqrt y)
      (Real.sqrt x + x / (2 * Real.sqrt x)) x := by
    convert (hasDerivAt_id x).mul hsx using 1 <;> norm_num <;> ring
  have hp2 : HasDerivAt
      (fun y : ℝ => (y + 1) ^ 2 * Real.sqrt (y + 1))
      (2 * (x + 1) * Real.sqrt (x + 1) +
        (x + 1) ^ 2 / (2 * Real.sqrt (x + 1))) x := by
    convert (hlin.pow 2).mul hs1 using 1 <;> norm_num <;> ring
  have hp02 : HasDerivAt
      (fun y : ℝ => y ^ 2 * Real.sqrt y)
      (2 * x * Real.sqrt x + x ^ 2 / (2 * Real.sqrt x)) x := by
    convert ((hasDerivAt_id x).pow 2).mul hsx using 1 <;> norm_num <;> ring
  have hder : HasDerivAt primitive
      (2 / 3 *
          ((Real.sqrt (x + 1) + (x + 1) / (2 * Real.sqrt (x + 1))) +
            (Real.sqrt x + x / (2 * Real.sqrt x))) -
        2 / 5 *
          ((2 * (x + 1) * Real.sqrt (x + 1) +
              (x + 1) ^ 2 / (2 * Real.sqrt (x + 1))) -
            (2 * x * Real.sqrt x + x ^ 2 / (2 * Real.sqrt x)))) x := by
    simpa [primitive] using
      ((hp1.add hp0).const_mul (2 / 3)).sub
        ((hp2.sub hp02).const_mul (2 / 5))
  have hdiv0 : x / (2 * Real.sqrt x) = Real.sqrt x / 2 := by
    apply (div_eq_iff (mul_ne_zero (by norm_num) hs0)).2
    nlinarith
  have hdiv1 :
      (x + 1) / (2 * Real.sqrt (x + 1)) = Real.sqrt (x + 1) / 2 := by
    apply (div_eq_iff (mul_ne_zero (by norm_num) hs10)).2
    nlinarith
  have hdiv20 :
      x ^ 2 / (2 * Real.sqrt x) = x * Real.sqrt x / 2 := by
    apply (div_eq_iff (mul_ne_zero (by norm_num) hs0)).2
    calc
      x ^ 2 = x * (Real.sqrt x) ^ 2 := by
        rw [hsq]
        ring
      _ = (x * Real.sqrt x / 2) * (2 * Real.sqrt x) := by ring
  have hdiv21 :
      (x + 1) ^ 2 / (2 * Real.sqrt (x + 1)) =
        (x + 1) * Real.sqrt (x + 1) / 2 := by
    apply (div_eq_iff (mul_ne_zero (by norm_num) hs10)).2
    calc
      (x + 1) ^ 2 = (x + 1) * (Real.sqrt (x + 1)) ^ 2 := by
        rw [hsq1]
        ring
      _ = ((x + 1) * Real.sqrt (x + 1) / 2) *
          (2 * Real.sqrt (x + 1)) := by ring
  refine hder.congr_deriv ?_
  rw [hdiv0, hdiv1, hdiv20, hdiv21]
  unfold powerIntegrand
  ring

theorem gap1 :
    AntiderivativesOn originalIntegrand =
      AntiderivativesOn rationalizedIntegrand := by
  exact antiderivatives_ext original_eq_rationalized
theorem gap2 :
    AntiderivativesOn rationalizedIntegrand =
      AntiderivativesOn expandedIntegrand := by
  exact antiderivatives_ext rationalized_eq_expanded
theorem gap3 :
    AntiderivativesOn originalIntegrand =
      AntiderivativesOn expandedIntegrand := by
  exact gap1.trans gap2
theorem gap4 :
    AntiderivativesOn originalIntegrand =
      AntiderivativesOn powerIntegrand := by
  calc
    AntiderivativesOn originalIntegrand =
        AntiderivativesOn expandedIntegrand := gap3
    _ = AntiderivativesOn powerIntegrand :=
      antiderivatives_ext expanded_eq_power
theorem gap5 :
    AntiderivativesOn powerIntegrand = PrimitiveFamily := by
  apply Set.ext
  intro F
  change
    (∀ x ∈ branch, HasDerivAt F (powerIntegrand x) x) ↔
      ∃ C : ℝ, ∀ x ∈ branch, F x = primitive x + C
  constructor
  · intro hF
    have hdiff : ∀ x ∈ branch,
        HasDerivAt (fun y => F y - primitive y) 0 x := by
      intro x hx
      convert (hF x hx).sub (primitive_hasDerivAt x hx) using 1 <;> ring
    have hdiffable :
        DifferentiableOn ℝ (fun y => F y - primitive y) branch := by
      intro x hx
      exact (hdiff x hx).differentiableAt.differentiableWithinAt
    have hzero : ∀ x ∈ branch,
        deriv (fun y => F y - primitive y) x = 0 := by
      intro x hx
      exact (hdiff x hx).deriv
    have hopen : IsOpen branch := by
      simpa [branch] using isOpen_Ioi
    have hconv : Convex ℝ branch := by
      simpa [branch] using (convex_Ioi (0 : ℝ))
    have hpre : IsPreconnected branch := hconv.isPreconnected
    have hone : (1 : ℝ) ∈ branch := by
      norm_num [branch]
    refine ⟨F 1 - primitive 1, ?_⟩
    intro x hx
    have hsame :=
      hopen.is_const_of_deriv_eq_zero hpre hdiffable hzero hx hone
    linarith
  · rintro ⟨C, hC⟩
    intro x hx
    have hopen : IsOpen branch := by
      simpa [branch] using isOpen_Ioi
    have heq : Filter.EventuallyEq (nhds x) F
        (fun y => primitive y + C) := by
      filter_upwards [hopen.mem_nhds hx] with y hy
      exact hC y hy
    exact ((primitive_hasDerivAt x hx).add_const C).congr_of_eventuallyEq heq
theorem gap6 :
    AntiderivativesOn originalIntegrand = PrimitiveFamily := by
  exact gap4.trans gap5

end
end ProofGap.Exercise1975
