import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1758

noncomputable section

def domain : Set ℝ := Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)
def sec (x : ℝ) : ℝ := 1 / Real.cos x
def original (x : ℝ) : ℝ := 1 / Real.cos x ^ 4
def factored (x : ℝ) : ℝ := sec x ^ 2 * (1 / Real.cos x ^ 2)
def substituted (x : ℝ) : ℝ := (1 + Real.tan x ^ 2) * sec x ^ 2
def primitive (x : ℝ) : ℝ := Real.tan x + (1 / 3) * Real.tan x ^ 3
def AntiderivativesOn (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | DifferentiableOn ℝ F domain ∧ ∀ x ∈ domain, deriv F x = g x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ domain, F x = p x + C}

private theorem primitive_hasDerivAt {x : ℝ} (hx : x ∈ domain) :
    HasDerivAt primitive (substituted x) x := by
  have hxIoo : x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    simpa [domain] using hx
  have hcos : Real.cos x ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo hxIoo)
  unfold primitive substituted sec
  convert (Real.hasDerivAt_tan hcos).add
    ((hasDerivAt_const x (1 / 3 : ℝ)).mul
      ((Real.hasDerivAt_tan hcos).pow 3)) using 1 <;>
    field_simp <;> ring

private theorem factored_eq_substituted {x : ℝ} (hx : x ∈ domain) :
    factored x = substituted x := by
  have hxIoo : x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    simpa [domain] using hx
  have hcos : Real.cos x ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo hxIoo)
  have htrig : 1 + Real.tan x ^ 2 = 1 / Real.cos x ^ 2 := by
    rw [Real.tan_eq_sin_div_cos]
    field_simp [hcos]
    nlinarith [Real.sin_sq_add_cos_sq x]
  unfold factored substituted sec
  rw [htrig]
  ring

theorem gap1 : AntiderivativesOn original = AntiderivativesOn factored := by
  ext F
  constructor
  · rintro ⟨hF, hderiv⟩
    refine ⟨hF, ?_⟩
    intro x hx
    calc
      deriv F x = original x := hderiv x hx
      _ = factored x := by
        unfold original factored sec
        ring
  · rintro ⟨hF, hderiv⟩
    refine ⟨hF, ?_⟩
    intro x hx
    calc
      deriv F x = factored x := hderiv x hx
      _ = original x := by
        unfold original factored sec
        ring

theorem gap2 : AntiderivativesOn factored = AntiderivativesOn substituted := by
  ext F
  constructor
  · rintro ⟨hF, hderiv⟩
    refine ⟨hF, ?_⟩
    intro x hx
    calc
      deriv F x = factored x := hderiv x hx
      _ = substituted x := factored_eq_substituted hx
  · rintro ⟨hF, hderiv⟩
    refine ⟨hF, ?_⟩
    intro x hx
    calc
      deriv F x = substituted x := hderiv x hx
      _ = factored x := (factored_eq_substituted hx).symm

theorem gap3 : AntiderivativesOn substituted = PrimitiveFamily primitive := by
  ext F
  constructor
  · rintro ⟨hF, hderiv⟩
    have hP : DifferentiableOn ℝ primitive domain := by
      intro x hx
      exact (primitive_hasDerivAt hx).differentiableAt.differentiableWithinAt
    have hG : DifferentiableOn ℝ (fun x => F x - primitive x) domain :=
      hF.sub hP
    have hzero : ∀ x ∈ domain, deriv (fun y => F y - primitive y) x = 0 := by
      intro x hx
      have hFa : DifferentiableAt ℝ F x :=
        (hF x hx).differentiableAt (isOpen_Ioo.mem_nhds hx)
      have hFx : HasDerivAt F (substituted x) x := by
        simpa [hderiv x hx] using hFa.hasDerivAt
      simpa using (hFx.sub (primitive_hasDerivAt hx)).deriv
    have h0 : (0 : ℝ) ∈ domain := by
      unfold domain
      constructor <;> linarith [Real.pi_pos]
    refine ⟨F 0 - primitive 0, ?_⟩
    intro x hx
    have hEq : F x - primitive x = F 0 - primitive 0 :=
      isOpen_Ioo.is_const_of_deriv_eq_zero
        isPreconnected_Ioo hG hzero hx h0
    linarith
  · rintro ⟨C, hFC⟩
    have hmodel : DifferentiableOn ℝ (fun x => primitive x + C) domain := by
      intro x hx
      exact (primitive_hasDerivAt hx).add_const C |>.differentiableAt.differentiableWithinAt
    have hF : DifferentiableOn ℝ F domain :=
      hmodel.congr (fun x hx => hFC x hx)
    refine ⟨hF, ?_⟩
    intro x hx
    have hm : HasDerivAt (fun y => primitive y + C) (substituted x) x :=
      (primitive_hasDerivAt hx).add_const C
    have hev : F =ᶠ[nhds x] fun y => primitive y + C :=
      (isOpen_Ioo.eventually_mem hx).mono (fun y hy => hFC y hy)
    exact (hm.congr_of_eventuallyEq hev).deriv

theorem gap4 : AntiderivativesOn original = PrimitiveFamily primitive := by
  rw [gap1, gap2, gap3]

end
end ProofGap.Exercise1758
