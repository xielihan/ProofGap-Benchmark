import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.IntermediateValue

namespace ProofGap.Exercise1722

noncomputable section

def branch : Set ℝ := Set.Iio 1
def integrand (x : ℝ) := (1 + x) / (1 - x)
def expandedIntegrand (x : ℝ) := -1 + 2 / (1 - x)
def primitive (x : ℝ) := -x - 2 * Real.log |1 - x|
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = p x + C}

private theorem integrand_eq_expanded_on_branch {x : ℝ} (hx : x ∈ branch) :
    integrand x = expandedIntegrand x := by
  have hxlt : x < 1 := hx
  have hne : 1 - x ≠ 0 := by linarith
  unfold integrand expandedIntegrand
  field_simp [hne] <;> ring

private theorem primitive_hasDerivAt {x : ℝ} (hx : x ∈ branch) :
    HasDerivAt primitive (expandedIntegrand x) x := by
  have hxlt : x < 1 := hx
  have hpos : 0 < 1 - x := by linarith
  have hinner : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
    simpa using
      (hasDerivAt_const (x := x) (c := (1 : ℝ))).sub (hasDerivAt_id x)
  have hlog : HasDerivAt (fun y : ℝ => Real.log (1 - y))
      ((1 - x)⁻¹ * (-1)) x :=
    (Real.hasDerivAt_log (ne_of_gt hpos)).comp x hinner
  have hbase : HasDerivAt
      (fun y : ℝ => -y - 2 * Real.log (1 - y))
      (-1 - 2 * ((1 - x)⁻¹ * (-1))) x := by
    simpa using
      (hasDerivAt_id x).neg.sub
        ((hasDerivAt_const (x := x) (c := (2 : ℝ))).mul hlog)
  have hopen : branch ∈ nhds x :=
    (show IsOpen branch from isOpen_Iio).mem_nhds hx
  have heq :
      (fun y : ℝ => -y - 2 * Real.log (1 - y)) =ᶠ[nhds x] primitive := by
    filter_upwards [hopen] with y hy
    change y < 1 at hy
    unfold primitive
    rw [abs_of_pos (by linarith)]
  have hd : HasDerivAt
      (fun y : ℝ => -y - 2 * Real.log (1 - y))
      (expandedIntegrand x) x := by
    simpa [expandedIntegrand, div_eq_mul_inv] using hbase
  exact hd.congr_of_eventuallyEq heq.symm

theorem gap1 :
    AntiderivativesOn integrand = AntiderivativesOn expandedIntegrand := by
  ext F
  constructor
  · intro h x hx
    simpa only [integrand_eq_expanded_on_branch hx] using h x hx
  · intro h x hx
    simpa only [integrand_eq_expanded_on_branch hx] using h x hx
theorem gap2 :
    AntiderivativesOn expandedIntegrand = PrimitiveFamily primitive := by
  ext F
  constructor
  · intro hF
    refine ⟨F 0 - primitive 0, ?_⟩
    have hzero : ∀ x ∈ branch,
        HasDerivAt (fun y => F y - primitive y) 0 x := by
      intro x hx
      simpa using (hF x hx).sub (primitive_hasDerivAt hx)
    have hdiff : DifferentiableOn ℝ (fun y => F y - primitive y)
        (Set.Iio (1 : ℝ)) := by
      intro y hy
      exact (hzero y hy).differentiableAt.differentiableWithinAt
    have hderiv : ∀ y ∈ Set.Iio (1 : ℝ),
        deriv (fun z => F z - primitive z) y = 0 := by
      intro y hy
      exact (hzero y hy).deriv
    intro x hx
    have h0 : (0 : ℝ) ∈ Set.Iio (1 : ℝ) := by norm_num
    have heq : F x - primitive x = F 0 - primitive 0 :=
      isOpen_Iio.is_const_of_deriv_eq_zero
        (isPreconnected_Iio : IsPreconnected (Set.Iio (1 : ℝ)))
        hdiff hderiv hx h0
    linarith
  · rintro ⟨C, hC⟩
    intro x hx
    have hopen : branch ∈ nhds x :=
      (show IsOpen branch from isOpen_Iio).mem_nhds hx
    have heq : F =ᶠ[nhds x] (fun y => primitive y + C) := by
      filter_upwards [hopen] with y hy
      exact hC y hy
    have hd : HasDerivAt (fun y : ℝ => primitive y + C)
        (expandedIntegrand x) x :=
      (primitive_hasDerivAt hx).add_const C
    exact hd.congr_of_eventuallyEq heq
theorem gap3 :
    AntiderivativesOn integrand = PrimitiveFamily primitive := by
  calc
    AntiderivativesOn integrand = AntiderivativesOn expandedIntegrand := gap1
    _ = PrimitiveFamily primitive := gap2

end
end ProofGap.Exercise1722
