import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1631

noncomputable section

def domain : Set ℝ := Set.Ioi 0
def factored (x : ℝ) : ℝ := ((1 - x) / x) ^ 2
def expanded (x : ℝ) : ℝ := 1 / x ^ 2 - 2 / x + 1
def primitive (x : ℝ) : ℝ := -(1 / x) - 2 * Real.log |x| + x
def AntiderivativesOn (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | DifferentiableOn ℝ F domain ∧ ∀ x ∈ domain, deriv F x = g x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ domain, F x = p x + C}

private theorem factored_eq_expanded {x : ℝ} (hx : x ∈ domain) :
    factored x = expanded x := by
  have hx0 : x ≠ 0 := ne_of_gt (by simpa [domain] using hx)
  unfold factored expanded
  field_simp [hx0]
  ring

private theorem primitive_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt primitive (expanded x) x := by
  have h :=
    (((hasDerivAt_id x).inv hx.ne').neg.sub
      ((hasDerivAt_const x (2 : ℝ)).mul (Real.hasDerivAt_log hx.ne'))).add
      (hasDerivAt_id x)
  have hcoef :
      -(-1 / x ^ 2) - (0 * Real.log x + 2 * x⁻¹) + 1 = expanded x := by
    simp [expanded, div_eq_mul_inv]
  rw [← hcoef]
  apply h.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
  simp [primitive, one_div, Real.log_abs]

theorem gap1 : AntiderivativesOn factored = AntiderivativesOn expanded := by
  apply Set.ext
  intro F
  simp only [AntiderivativesOn, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hF, hderiv⟩
    refine ⟨hF, fun x hx => ?_⟩
    exact (hderiv x hx).trans (factored_eq_expanded hx)
  · rintro ⟨hF, hderiv⟩
    refine ⟨hF, fun x hx => ?_⟩
    exact (hderiv x hx).trans (factored_eq_expanded hx).symm

theorem gap2 : AntiderivativesOn expanded = PrimitiveFamily primitive := by
  apply Set.ext
  intro F
  simp only [AntiderivativesOn, PrimitiveFamily, Set.mem_setOf_eq]
  have hopen : IsOpen domain := by
    simpa [domain] using (isOpen_Ioi : IsOpen (Set.Ioi (0 : ℝ)))
  have hpDiff : DifferentiableOn ℝ primitive domain := by
    intro x hx
    have hxpos : 0 < x := by simpa [domain] using hx
    exact (primitive_hasDerivAt hxpos).differentiableAt.differentiableWithinAt
  constructor
  · rintro ⟨hFdiff, hFderiv⟩
    have hqdiff : DifferentiableOn ℝ (fun x => F x - primitive x) domain :=
      hFdiff.sub hpDiff
    have hqderiv : ∀ x ∈ domain, deriv (fun y => F y - primitive y) x = 0 := by
      intro x hx
      have hxpos : 0 < x := by simpa [domain] using hx
      have hFAt : DifferentiableAt ℝ F x :=
        (hFdiff x hx).differentiableAt (hopen.mem_nhds hx)
      have hsub := hFAt.hasDerivAt.sub (primitive_hasDerivAt hxpos)
      simpa [hFderiv x hx] using hsub.deriv
    refine ⟨F 1 - primitive 1, ?_⟩
    intro x hx
    have hxpos : 0 < x := by simpa [domain] using hx
    have hqdiffI :
        DifferentiableOn ℝ (fun y => F y - primitive y) (Set.Ioo 0 (x + 2)) := by
      apply hqdiff.mono
      intro y hy
      simpa [domain] using hy.1
    have hqderivI :
        ∀ y ∈ Set.Ioo (0 : ℝ) (x + 2),
          deriv (fun z => F z - primitive z) y = 0 := by
      intro y hy
      apply hqderiv y
      simpa [domain] using hy.1
    have hxI : x ∈ Set.Ioo (0 : ℝ) (x + 2) := by
      constructor <;> linarith
    have honeI : (1 : ℝ) ∈ Set.Ioo (0 : ℝ) (x + 2) := by
      constructor <;> linarith
    have heq : F x - primitive x = F 1 - primitive 1 :=
      isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
        hqdiffI hqderivI hxI honeI
    linarith
  · rintro ⟨C, hFC⟩
    have hFhas : ∀ x ∈ domain, HasDerivAt F (expanded x) x := by
      intro x hx
      have hxpos : 0 < x := by simpa [domain] using hx
      have hG : HasDerivAt (fun y => primitive y + C) (expanded x) x :=
        (primitive_hasDerivAt hxpos).add_const C
      have hevent : F =ᶠ[nhds x] (fun y => primitive y + C) := by
        filter_upwards [hopen.mem_nhds hx] with y hy
        exact hFC y hy
      exact hG.congr_of_eventuallyEq hevent
    refine ⟨?_, ?_⟩
    · intro x hx
      exact (hFhas x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      exact (hFhas x hx).deriv

theorem gap3 : AntiderivativesOn factored = PrimitiveFamily primitive := by
  exact gap1.trans gap2

end
end ProofGap.Exercise1631
