import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1809

noncomputable section

def branch : Set ℝ := Set.Ioi 0
def integrand (x : ℝ) := Real.arctan (Real.sqrt x)
def residual (x : ℝ) := x / (Real.sqrt x * (1 + x))
def substitutedResidual (x : ℝ) :=
  (1 - 1 / (1 + x)) * deriv Real.sqrt x
def boundary (x : ℝ) := x * Real.arctan (Real.sqrt x)
def primitive (x : ℝ) :=
  (x + 1) * Real.arctan (Real.sqrt x) - Real.sqrt x
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def ByPartsFamily (c : ℝ) (r : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn r, ∀ x ∈ branch, F x = boundary x + c * G x}
def PrimitiveFamily : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = primitive x + C}

private theorem hasDerivAt_integrand_raw (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt integrand
      ((1 / (1 + (Real.sqrt x) ^ 2)) * (1 / (2 * Real.sqrt x))) x := by
  have hs := Real.hasDerivAt_sqrt (ne_of_gt hx)
  simpa only [integrand] using
    (Real.hasDerivAt_arctan (Real.sqrt x)).comp x hs

private theorem hasDerivAt_boundary (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt boundary (integrand x + residual x / 2) x := by
  have hxpos : 0 < x := hx
  have hspos : 0 < Real.sqrt x := Real.sqrt_pos.2 hxpos
  have hsne : Real.sqrt x ≠ 0 := ne_of_gt hspos
  have hx1 : 1 + x ≠ 0 := ne_of_gt (by linarith)
  have hcalc := (hasDerivAt_id x).mul (hasDerivAt_integrand_raw x hx)
  have hcalc' :
      HasDerivAt boundary
        (1 * integrand x +
          x * ((1 / (1 + (Real.sqrt x) ^ 2)) *
            (1 / (2 * Real.sqrt x)))) x := by
    simpa only [boundary, integrand, id_eq] using hcalc
  have hcoeff :
      1 * integrand x +
          x * ((1 / (1 + (Real.sqrt x) ^ 2)) *
            (1 / (2 * Real.sqrt x))) =
        integrand x + residual x / 2 := by
    simp only [one_mul]
    dsimp [residual]
    rw [Real.sq_sqrt (le_of_lt hxpos)]
    field_simp [hsne, hx1] <;> ring
  rw [hcoeff] at hcalc'
  exact hcalc'

private theorem substitutedResidual_eq (x : ℝ) (hx : x ∈ branch) :
    substitutedResidual x = residual x / 2 := by
  have hxpos : 0 < x := hx
  have hspos : 0 < Real.sqrt x := Real.sqrt_pos.2 hxpos
  have hsne : Real.sqrt x ≠ 0 := ne_of_gt hspos
  have hx1 : 1 + x ≠ 0 := ne_of_gt (by linarith)
  have hd : deriv Real.sqrt x = 1 / (2 * Real.sqrt x) :=
    (Real.hasDerivAt_sqrt (ne_of_gt hxpos)).deriv
  dsimp [substitutedResidual, residual]
  rw [hd]
  field_simp [hsne, hx1] <;> ring

private theorem hasDerivAt_primitive (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt primitive (integrand x) x := by
  have hxpos : 0 < x := hx
  have hs := Real.hasDerivAt_sqrt (ne_of_gt hxpos)
  have hspos : 0 < Real.sqrt x := Real.sqrt_pos.2 hxpos
  have hsne : Real.sqrt x ≠ 0 := ne_of_gt hspos
  have hx1 : 1 + x ≠ 0 := ne_of_gt (by linarith)
  have hcalc :=
    (((hasDerivAt_id x).add_const 1).mul
      (hasDerivAt_integrand_raw x hx)).sub hs
  have hcalc' :
      HasDerivAt primitive
        (1 * integrand x +
          (x + 1) * ((1 / (1 + (Real.sqrt x) ^ 2)) *
            (1 / (2 * Real.sqrt x))) -
          1 / (2 * Real.sqrt x)) x := by
    simpa only [primitive, integrand, id_eq] using hcalc
  have hcoeff :
      1 * integrand x +
          (x + 1) * ((1 / (1 + (Real.sqrt x) ^ 2)) *
            (1 / (2 * Real.sqrt x))) -
          1 / (2 * Real.sqrt x) = integrand x := by
    simp only [one_mul]
    rw [Real.sq_sqrt (le_of_lt hxpos)]
    field_simp [hsne, hx1] <;> ring
  rw [hcoeff] at hcalc'
  exact hcalc'

private theorem eq_at_one_of_hasDerivAt_zero
    (f : ℝ → ℝ)
    (hf : ∀ x ∈ branch, HasDerivAt f 0 x) :
    ∀ x ∈ branch, f x = f 1 := by
  intro x hx
  by_cases hxeq : x = 1
  · subst x
    rfl
  · have hopen : IsOpen branch := by
      simpa [branch] using (isOpen_Ioi : IsOpen (Set.Ioi (0 : ℝ)))
    have hconn : IsPreconnected branch := by
      simpa only [branch] using
        (isPreconnected_Ioi : IsPreconnected (Set.Ioi (0 : ℝ)))
    have hdiff : DifferentiableOn ℝ f branch := by
      intro y hy
      exact (hf y hy).differentiableAt.differentiableWithinAt
    have hderiv : ∀ y ∈ branch, deriv f y = 0 := by
      intro y hy
      exact (hf y hy).deriv
    have hone : (1 : ℝ) ∈ branch := by
      change (0 : ℝ) < 1
      exact zero_lt_one
    exact
      hopen.is_const_of_deriv_eq_zero hconn hdiff hderiv hx hone

theorem gap1 :
    AntiderivativesOn integrand =
      ByPartsFamily (-1 / 2) residual := by
  apply Set.ext
  intro F
  constructor
  · intro hF
    change ∀ x ∈ branch, HasDerivAt F (integrand x) x at hF
    change ∃ G ∈ AntiderivativesOn residual,
      ∀ x ∈ branch, F x = boundary x + (-1 / 2 : ℝ) * G x
    refine ⟨fun y => 2 * (boundary y - F y), ?_, ?_⟩
    · change ∀ x ∈ branch,
        HasDerivAt (fun y => 2 * (boundary y - F y)) (residual x) x
      intro x hx
      have hcalc :=
        ((hasDerivAt_boundary x hx).sub (hF x hx)).const_mul 2
      have hcoeff :
          2 * ((integrand x + residual x / 2) - integrand x) =
            residual x := by
        ring
      rw [hcoeff] at hcalc
      exact hcalc
    · intro x hx
      dsimp
      ring
  · rintro ⟨G, hG, hEq⟩
    change ∀ x ∈ branch, HasDerivAt G (residual x) x at hG
    change ∀ x ∈ branch, HasDerivAt F (integrand x) x
    intro x hx
    have hcalc :=
      (hasDerivAt_boundary x hx).add
        ((hG x hx).const_mul (-1 / 2 : ℝ))
    have hcoeff :
        integrand x + residual x / 2 + (-1 / 2 : ℝ) * residual x =
          integrand x := by
      ring
    rw [hcoeff] at hcalc
    apply hcalc.congr_of_eventuallyEq
    filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
    simpa only [Pi.add_apply] using hEq y hy
theorem gap2 :
    ByPartsFamily (-1 / 2) residual =
      ByPartsFamily (-1) substitutedResidual := by
  apply Set.ext
  intro F
  constructor
  · rintro ⟨G, hG, hEq⟩
    change ∀ x ∈ branch, HasDerivAt G (residual x) x at hG
    change ∃ H ∈ AntiderivativesOn substitutedResidual,
      ∀ x ∈ branch, F x = boundary x + (-1 : ℝ) * H x
    refine ⟨fun y => (1 / 2 : ℝ) * G y, ?_, ?_⟩
    · change ∀ x ∈ branch,
        HasDerivAt (fun y => (1 / 2 : ℝ) * G y)
          (substitutedResidual x) x
      intro x hx
      have hcalc := (hG x hx).const_mul (1 / 2 : ℝ)
      have hcoeff :
          (1 / 2 : ℝ) * residual x = substitutedResidual x := by
        rw [substitutedResidual_eq x hx]
        ring
      rw [hcoeff] at hcalc
      exact hcalc
    · intro x hx
      rw [hEq x hx]
      dsimp
      ring
  · rintro ⟨H, hH, hEq⟩
    change ∀ x ∈ branch,
      HasDerivAt H (substitutedResidual x) x at hH
    change ∃ G ∈ AntiderivativesOn residual,
      ∀ x ∈ branch, F x = boundary x + (-1 / 2 : ℝ) * G x
    refine ⟨fun y => 2 * H y, ?_, ?_⟩
    · change ∀ x ∈ branch,
        HasDerivAt (fun y => 2 * H y) (residual x) x
      intro x hx
      have hcalc := (hH x hx).const_mul 2
      have hcoeff : 2 * substitutedResidual x = residual x := by
        rw [substitutedResidual_eq x hx]
        ring
      rw [hcoeff] at hcalc
      exact hcalc
    · intro x hx
      rw [hEq x hx]
      dsimp
      ring
theorem gap3 :
    AntiderivativesOn integrand =
      ByPartsFamily (-1) substitutedResidual := by
  calc
    AntiderivativesOn integrand =
        ByPartsFamily (-1 / 2) residual := gap1
    _ = ByPartsFamily (-1) substitutedResidual := gap2
theorem gap4 :
    AntiderivativesOn integrand = PrimitiveFamily := by
  apply Set.ext
  intro F
  constructor
  · intro hF
    change ∀ x ∈ branch, HasDerivAt F (integrand x) x at hF
    change ∃ C : ℝ, ∀ x ∈ branch, F x = primitive x + C
    have hzero :
        ∀ x ∈ branch,
          HasDerivAt (fun y => F y - primitive y) 0 x := by
      intro x hx
      have hcalc := (hF x hx).sub (hasDerivAt_primitive x hx)
      have hcoeff : integrand x - integrand x = 0 := by ring
      rw [hcoeff] at hcalc
      exact hcalc
    refine ⟨F 1 - primitive 1, ?_⟩
    intro x hx
    have heq := eq_at_one_of_hasDerivAt_zero
      (fun y => F y - primitive y) hzero x hx
    dsimp at heq ⊢
    linarith
  · rintro ⟨C, hEq⟩
    change ∀ x ∈ branch, HasDerivAt F (integrand x) x
    intro x hx
    have hcalc := (hasDerivAt_primitive x hx).add_const C
    apply hcalc.congr_of_eventuallyEq
    filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
    exact hEq y hy

end
end ProofGap.Exercise1809
