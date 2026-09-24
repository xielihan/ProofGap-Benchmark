import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Order.OrderClosed

namespace ProofGap.Exercise1649

noncomputable section

def domain : Set ℝ := Set.Ioo 0 Real.pi
def cot (x : ℝ) : ℝ := Real.cos x / Real.sin x
def csc (x : ℝ) : ℝ := 1 / Real.sin x
def primitive (x : ℝ) : ℝ := -cot x - x
def AntiderivativesOn (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | DifferentiableOn ℝ F domain ∧ ∀ x ∈ domain, deriv F x = g x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ domain, F x = p x + C}

private theorem primitive_hasDerivAt (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt primitive (csc x ^ 2 - 1) x := by
  have hsin : 0 < Real.sin x :=
    Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2
  have hsin_ne : Real.sin x ≠ 0 := ne_of_gt hsin
  have hcot : HasDerivAt cot
      (((-Real.sin x) * Real.sin x - Real.cos x * Real.cos x) /
        Real.sin x ^ 2) x := by
    simpa only [cot] using
      (Real.hasDerivAt_cos x).div (Real.hasDerivAt_sin x) hsin_ne
  have hp := hcot.neg.sub (hasDerivAt_id x)
  have hcoef :
      -(((-Real.sin x) * Real.sin x - Real.cos x * Real.cos x) /
          Real.sin x ^ 2) - 1 = csc x ^ 2 - 1 := by
    unfold csc
    field_simp [hsin_ne]
    nlinarith [Real.sin_sq_add_cos_sq x]
  rw [hcoef] at hp
  simpa only [primitive] using hp

private theorem deriv_zero_eqOn_Ioo
    (f : ℝ → ℝ) {a b : ℝ}
    (hf : DifferentiableOn ℝ f (Set.Ioo a b))
    (hzero : ∀ z ∈ Set.Ioo a b, deriv f z = 0)
    {x y : ℝ} (hx : x ∈ Set.Ioo a b) (hy : y ∈ Set.Ioo a b) :
    f x = f y := by
  have hordered :
      ∀ {u v : ℝ}, u ∈ Set.Ioo a b → v ∈ Set.Ioo a b →
        u < v → f u = f v := by
    intro u v hu hv huv
    have hIcc : Set.Icc u v ⊆ Set.Ioo a b := by
      intro z hz
      exact ⟨lt_of_lt_of_le hu.1 hz.1, lt_of_le_of_lt hz.2 hv.2⟩
    have hIoo : Set.Ioo u v ⊆ Set.Ioo a b := by
      intro z hz
      exact hIcc ⟨le_of_lt hz.1, le_of_lt hz.2⟩
    have hcont : ContinuousOn f (Set.Icc u v) := by
      intro z hz
      exact (hf z (hIcc hz)).continuousWithinAt.mono hIcc
    have hdiff : DifferentiableOn ℝ f (Set.Ioo u v) :=
      hf.mono hIoo
    obtain ⟨z, hz, hzslope⟩ :=
      exists_deriv_eq_slope f huv hcont hdiff
    have hzdom : z ∈ Set.Ioo a b :=
      hIoo hz
    have hslope : (f v - f u) / (v - u) = 0 := by
      rw [← hzslope, hzero z hzdom]
    have hden : v - u ≠ 0 :=
      sub_ne_zero.mpr (ne_of_gt huv)
    field_simp [hden] at hslope
    linarith
  rcases lt_trichotomy x y with hxy | hxy | hyx
  · exact hordered hx hy hxy
  · exact congrArg f hxy
  · exact (hordered hy hx hyx).symm

theorem gap1 (x : ℝ) (hx : x ∈ domain) : cot x ^ 2 = csc x ^ 2 - 1 := by
  have hsin : 0 < Real.sin x :=
    Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2
  unfold cot csc
  field_simp [ne_of_gt hsin]
  nlinarith [Real.sin_sq_add_cos_sq x]

theorem gap2 :
    AntiderivativesOn (fun x => cot x ^ 2) =
      AntiderivativesOn (fun x => csc x ^ 2 - 1) := by
  apply Set.ext
  intro F
  change
    (DifferentiableOn ℝ F domain ∧
        ∀ x ∈ domain, deriv F x = cot x ^ 2) ↔
      (DifferentiableOn ℝ F domain ∧
        ∀ x ∈ domain, deriv F x = csc x ^ 2 - 1)
  constructor
  · rintro ⟨hF, hderiv⟩
    exact ⟨hF, fun x hx => (hderiv x hx).trans (gap1 x hx)⟩
  · rintro ⟨hF, hderiv⟩
    exact ⟨hF, fun x hx => (hderiv x hx).trans (gap1 x hx).symm⟩

theorem gap3 :
    AntiderivativesOn (fun x => csc x ^ 2 - 1) =
      PrimitiveFamily primitive := by
  apply Set.ext
  intro F
  change
    (DifferentiableOn ℝ F domain ∧
        ∀ x ∈ domain, deriv F x = csc x ^ 2 - 1) ↔
      ∃ C : ℝ, ∀ x ∈ domain, F x = primitive x + C
  constructor
  · rintro ⟨hFdiff, hFderiv⟩
    let H : ℝ → ℝ := fun y => F y - primitive y
    have hHdiff : DifferentiableOn ℝ H domain := by
      intro x hx
      exact (hFdiff x hx).sub
        ((primitive_hasDerivAt x hx).differentiableAt.differentiableWithinAt)
    have hHzero : ∀ x ∈ domain, deriv H x = 0 := by
      intro x hx
      have hopen : domain ∈ nhds x := isOpen_Ioo.mem_nhds hx
      have hFAt : DifferentiableAt ℝ F x :=
        (hFdiff x hx).differentiableAt hopen
      have hsub :=
        (hFAt.hasDerivAt.sub (primitive_hasDerivAt x hx)).deriv
      simpa [H, hFderiv x hx] using hsub
    have hmid : Real.pi / 2 ∈ domain := by
      change 0 < Real.pi / 2 ∧ Real.pi / 2 < Real.pi
      constructor <;> nlinarith [Real.pi_pos]
    refine ⟨F (Real.pi / 2) - primitive (Real.pi / 2), ?_⟩
    intro x hx
    have heq : H x = H (Real.pi / 2) :=
      deriv_zero_eqOn_Ioo H hHdiff hHzero hx hmid
    dsimp [H] at heq
    linarith
  · rintro ⟨C, hFC⟩
    constructor
    · intro x hx
      have hopen : domain ∈ nhds x := isOpen_Ioo.mem_nhds hx
      have hevent :
          F =ᶠ[nhds x] (fun y => primitive y + C) :=
        Filter.mem_of_superset hopen (fun y hy => hFC y hy)
      have hFHas : HasDerivAt F (csc x ^ 2 - 1) x :=
        ((primitive_hasDerivAt x hx).add_const C).congr_of_eventuallyEq
          hevent
      exact hFHas.differentiableAt.differentiableWithinAt
    · intro x hx
      have hopen : domain ∈ nhds x := isOpen_Ioo.mem_nhds hx
      have hevent :
          F =ᶠ[nhds x] (fun y => primitive y + C) :=
        Filter.mem_of_superset hopen (fun y hy => hFC y hy)
      have hFHas : HasDerivAt F (csc x ^ 2 - 1) x :=
        ((primitive_hasDerivAt x hx).add_const C).congr_of_eventuallyEq
          hevent
      exact hFHas.deriv

theorem gap4 :
    AntiderivativesOn (fun x => cot x ^ 2) =
      PrimitiveFamily primitive := by
  exact gap2.trans gap3

end
end ProofGap.Exercise1649
