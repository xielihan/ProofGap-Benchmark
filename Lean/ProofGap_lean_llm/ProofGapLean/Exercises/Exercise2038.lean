import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2038
noncomputable section

def branch : Set ℝ := Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)
def integrand (x : ℝ) := Real.sin x * Real.cos x / (1 + Real.sin x ^ 4)
def tanReduced (x : ℝ) :=
  Real.tan x / Real.cos x ^ 2 /
    (1 / Real.cos x ^ 4 + Real.tan x ^ 4)
def squareReduced (x : ℝ) :=
  (1 / 2 : ℝ) * (1 / (2 * Real.tan x ^ 4 + 2 * Real.tan x ^ 2 + 1)) *
    deriv (fun y : ℝ => Real.tan y ^ 2) x
def primitive (x : ℝ) :=
  (1 / 2 : ℝ) * Real.arctan (1 + 2 * Real.tan x ^ 2)
def Family (f : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∀ x ∈ branch, HasDerivAt F (f x) x}
def Translates (p : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ C, ∀ x ∈ branch, F x = p x + C}

private theorem primitive_hasDerivAt (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt primitive (squareReduced x) x := by
  have hcos : Real.cos x ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo hx)
  have htanSqRaw := (Real.hasDerivAt_tan hcos).pow 2
  have htanSqDiff :
      DifferentiableAt ℝ (fun y : ℝ => Real.tan y ^ 2) x := by
    simpa using htanSqRaw.differentiableAt
  have htanSq :
      HasDerivAt (fun y : ℝ => Real.tan y ^ 2)
        (deriv (fun y : ℝ => Real.tan y ^ 2) x) x :=
    htanSqDiff.hasDerivAt
  have hinner :
      HasDerivAt (fun y : ℝ => 1 + 2 * Real.tan y ^ 2)
        (2 * deriv (fun y : ℝ => Real.tan y ^ 2) x) x := by
    simpa [add_comm] using
      ((htanSq.const_mul (2 : ℝ)).add_const (1 : ℝ))
  have harctan :
      HasDerivAt
        (fun y : ℝ => Real.arctan (1 + 2 * Real.tan y ^ 2))
        ((1 / (1 + (1 + 2 * Real.tan x ^ 2) ^ 2)) *
          (2 * deriv (fun y : ℝ => Real.tan y ^ 2) x)) x := by
    simpa only [Function.comp_def] using
      (Real.hasDerivAt_arctan (1 + 2 * Real.tan x ^ 2)).comp x hinner
  have hscaled := harctan.const_mul (1 / 2 : ℝ)
  have hA :
      2 * Real.tan x ^ 4 + 2 * Real.tan x ^ 2 + 1 ≠ 0 := by
    positivity
  have hOuter :
      1 + (1 + 2 * Real.tan x ^ 2) ^ 2 ≠ 0 := by
    positivity
  have hcoef :
      (1 / 2 : ℝ) *
          ((1 / (1 + (1 + 2 * Real.tan x ^ 2) ^ 2)) *
            (2 * deriv (fun y : ℝ => Real.tan y ^ 2) x)) =
        squareReduced x := by
    unfold squareReduced
    field_simp [hA, hOuter]
    <;> ring
  rw [← hcoef]
  simpa only [primitive] using hscaled

theorem gap1 (x : ℝ) (hx : x ∈ branch) : integrand x = tanReduced x := by
  have hcos : Real.cos x ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo hx)
  have hsinDen : 1 + Real.sin x ^ 4 ≠ 0 := by
    positivity
  have hdenEq :
      1 / Real.cos x ^ 4 + Real.tan x ^ 4 =
        (1 + Real.sin x ^ 4) / Real.cos x ^ 4 := by
    rw [Real.tan_eq_sin_div_cos]
    field_simp [hcos]
    <;> ring
  unfold integrand tanReduced
  rw [hdenEq, Real.tan_eq_sin_div_cos]
  field_simp [hcos, hsinDen]
  <;> ring
theorem gap2 (x : ℝ) (hx : x ∈ branch) : integrand x = squareReduced x := by
  have hcos : Real.cos x ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo hx)
  have hsec :
      1 / Real.cos x ^ 2 = 1 + Real.tan x ^ 2 := by
    rw [Real.tan_eq_sin_div_cos]
    field_simp [hcos]
    nlinarith [Real.sin_sq_add_cos_sq x]
  have hcos4 :
      1 / Real.cos x ^ 4 = (1 / Real.cos x ^ 2) ^ 2 := by
    field_simp [hcos]
    <;> ring
  have hnum :
      Real.tan x / Real.cos x ^ 2 =
        Real.tan x * (1 + Real.tan x ^ 2) := by
    calc
      Real.tan x / Real.cos x ^ 2 =
          Real.tan x * (1 / Real.cos x ^ 2) := by ring
      _ = Real.tan x * (1 + Real.tan x ^ 2) := by rw [hsec]
  have hderiv :
      deriv (fun y : ℝ => Real.tan y ^ 2) x =
        2 * Real.tan x * (1 / Real.cos x ^ 2) := by
    simpa using ((Real.hasDerivAt_tan hcos).pow 2).deriv
  have hA :
      2 * Real.tan x ^ 4 + 2 * Real.tan x ^ 2 + 1 ≠ 0 := by
    positivity
  have hB :
      (1 + Real.tan x ^ 2) ^ 2 + Real.tan x ^ 4 ≠ 0 := by
    positivity
  rw [gap1 x hx]
  unfold tanReduced squareReduced
  rw [hnum, hcos4, hderiv, hsec]
  field_simp [hA, hB]
  <;> ring
theorem gap3 : Family integrand = Translates primitive := by
  ext F
  constructor
  · intro hF
    have hg : ∀ x ∈ branch,
        HasDerivAt (fun y : ℝ => F y - primitive y) 0 x := by
      intro x hx
      have hp : HasDerivAt primitive (integrand x) x := by
        rw [gap2 x hx]
        exact primitive_hasDerivAt x hx
      simpa using (hF x hx).sub hp
    have hgdiff :
        DifferentiableOn ℝ (fun y : ℝ => F y - primitive y) branch := by
      intro x hx
      exact (hg x hx).differentiableAt.differentiableWithinAt
    have hgderiv : ∀ x ∈ branch,
        deriv (fun y : ℝ => F y - primitive y) x = 0 := by
      intro x hx
      exact (hg x hx).deriv
    have hopen : IsOpen branch := by
      simpa [branch] using
        (isOpen_Ioo : IsOpen (Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)))
    have hconn : IsPreconnected branch := by
      simpa [branch] using
        (isPreconnected_Ioo :
          IsPreconnected (Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)))
    have hzero : 0 ∈ branch := by
      rw [branch]
      constructor <;> nlinarith [Real.pi_pos]
    refine ⟨F 0 - primitive 0, ?_⟩
    intro x hx
    have hsame :
        F x - primitive x = F 0 - primitive 0 :=
      hopen.is_const_of_deriv_eq_zero hconn hgdiff hgderiv hx hzero
    linarith
  · rintro ⟨C, hFC⟩
    intro x hx
    have hp : HasDerivAt primitive (integrand x) x := by
      rw [gap2 x hx]
      exact primitive_hasDerivAt x hx
    have hbase :
        HasDerivAt (fun y : ℝ => primitive y + C) (integrand x) x := by
      simpa using hp.add_const C
    have hnhds : branch ∈ nhds x := by
      simpa [branch] using (isOpen_Ioo.mem_nhds hx)
    have hlocal :
        F =ᶠ[nhds x] (fun y : ℝ => primitive y + C) :=
      Filter.mem_of_superset hnhds (fun y hy => hFC y hy)
    exact hbase.congr_of_eventuallyEq hlocal

end
end ProofGap.Exercise2038
