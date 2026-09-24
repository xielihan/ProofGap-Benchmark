import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1733

noncomputable section

def domain : Set ℝ := Set.Ioi 1
def original (x : ℝ) : ℝ := 1 / ((x - 1) * (x + 3))
def partialFractions (x : ℝ) : ℝ := (1 / 4) * (1 / (x - 1) - 1 / (x + 3))
def primitive (x : ℝ) : ℝ := (1 / 4) * Real.log |(x - 1) / (x + 3)|
def AntiderivativesOn (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | DifferentiableOn ℝ F domain ∧ ∀ x ∈ domain, deriv F x = g x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ domain, F x = p x + C}

private def logPrimitive (x : ℝ) : ℝ :=
  (1 / 4) * (Real.log (x - 1) - Real.log (x + 3))

private theorem original_eq_partialFractions (x : ℝ) (hx : x ∈ domain) :
    original x = partialFractions x := by
  have hx' : 1 < x := hx
  have hOne : x - 1 ≠ 0 := (sub_pos.mpr hx').ne'
  have hThree : x + 3 ≠ 0 := by
    linarith
  unfold original partialFractions
  field_simp [hOne, hThree]
  ring

private theorem primitive_eq_logPrimitive (x : ℝ) (hx : x ∈ domain) :
    primitive x = logPrimitive x := by
  have hx' : 1 < x := hx
  have hOne : 0 < x - 1 := sub_pos.mpr hx'
  have hThree : 0 < x + 3 := by
    linarith
  unfold primitive logPrimitive
  rw [abs_of_pos (div_pos hOne hThree), Real.log_div hOne.ne' hThree.ne']

private theorem primitive_hasDerivAt (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt primitive (partialFractions x) x := by
  have hx' : 1 < x := hx
  have hOne : 0 < x - 1 := sub_pos.mpr hx'
  have hThree : 0 < x + 3 := by
    linarith
  have hLogOne :
      HasDerivAt (fun y : ℝ => Real.log (y - 1)) (1 / (x - 1)) x := by
    simpa [Function.comp_apply, one_div] using
      (Real.hasDerivAt_log hOne.ne').comp x
        ((hasDerivAt_id x).sub_const (1 : ℝ))
  have hLogThree :
      HasDerivAt (fun y : ℝ => Real.log (y + 3)) (1 / (x + 3)) x := by
    simpa [Function.comp_apply, one_div] using
      (Real.hasDerivAt_log hThree.ne').comp x
        ((hasDerivAt_id x).add_const (3 : ℝ))
  have hLog : HasDerivAt logPrimitive (partialFractions x) x := by
    unfold logPrimitive partialFractions
    exact (hLogOne.sub hLogThree).const_mul (1 / 4 : ℝ)
  have hOpen : IsOpen domain := isOpen_Ioi
  have hDomain : domain ∈ nhds x := hOpen.mem_nhds hx
  have hEq : primitive =ᶠ[nhds x] logPrimitive := by
    filter_upwards [hDomain] with y hy
    exact primitive_eq_logPrimitive y hy
  exact hLog.congr_of_eventuallyEq hEq

theorem gap1 (x : ℝ) : 1 = (1 / 4) * (x + 3 - (x - 1)) := by
  ring

theorem gap2 : AntiderivativesOn original = AntiderivativesOn partialFractions := by
  ext F
  constructor
  · rintro ⟨hDiff, hDeriv⟩
    refine ⟨hDiff, ?_⟩
    intro x hx
    exact (hDeriv x hx).trans (original_eq_partialFractions x hx)
  · rintro ⟨hDiff, hDeriv⟩
    refine ⟨hDiff, ?_⟩
    intro x hx
    exact (hDeriv x hx).trans (original_eq_partialFractions x hx).symm

theorem gap3 : AntiderivativesOn partialFractions = PrimitiveFamily primitive := by
  ext F
  constructor
  · rintro ⟨hDiff, hDeriv⟩
    have hPrimitiveDiff : DifferentiableOn ℝ primitive domain := by
      intro x hx
      exact (primitive_hasDerivAt x hx).differentiableAt.differentiableWithinAt
    have hDifferenceDiff :
        DifferentiableOn ℝ (fun x => F x - primitive x) domain :=
      hDiff.sub hPrimitiveDiff
    have hOpen : IsOpen domain := isOpen_Ioi
    have hConnected : IsPreconnected domain := by
      unfold domain
      exact isPreconnected_Ioi
    have hDifferenceDeriv :
        ∀ x ∈ domain, deriv (fun y => F y - primitive y) x = 0 := by
      intro x hx
      have hDomain : domain ∈ nhds x := hOpen.mem_nhds hx
      have hFx : DifferentiableAt ℝ F x :=
        (hDiff x hx).differentiableAt hDomain
      have hPx : DifferentiableAt ℝ primitive x :=
        (primitive_hasDerivAt x hx).differentiableAt
      calc
        deriv (fun y => F y - primitive y) x =
            deriv F x - deriv primitive x := deriv_sub hFx hPx
        _ = 0 := by
          rw [hDeriv x hx, (primitive_hasDerivAt x hx).deriv, sub_self]
    refine ⟨F 2 - primitive 2, ?_⟩
    intro x hx
    have hTwo : (2 : ℝ) ∈ domain := by
      norm_num [domain]
    have hEq :
        (fun y => F y - primitive y) x =
          (fun y => F y - primitive y) 2 :=
      hOpen.is_const_of_deriv_eq_zero hConnected
        hDifferenceDiff hDifferenceDeriv hx hTwo
    dsimp only at hEq
    linarith
  · rintro ⟨C, hC⟩
    have hOpen : IsOpen domain := isOpen_Ioi
    have hFDeriv : ∀ x ∈ domain, HasDerivAt F (partialFractions x) x := by
      intro x hx
      have hDomain : domain ∈ nhds x := hOpen.mem_nhds hx
      have hEq : F =ᶠ[nhds x] (fun y => primitive y + C) := by
        filter_upwards [hDomain] with y hy
        exact hC y hy
      exact ((primitive_hasDerivAt x hx).add_const C).congr_of_eventuallyEq hEq
    constructor
    · intro x hx
      exact (hFDeriv x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      exact (hFDeriv x hx).deriv

theorem gap4 : AntiderivativesOn original = PrimitiveFamily primitive := by
  exact gap2.trans gap3

end
end ProofGap.Exercise1733
