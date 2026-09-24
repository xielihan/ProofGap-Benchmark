import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2178
noncomputable section

def FamilyOn (U : Set ℝ) (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ U, HasDerivAt F (g x) x}

def TranslatesOn (U : Set ℝ) (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ U, F x = p x + C}

def sqrtPrimitive (x : ℝ) : ℝ := 2 * Real.sqrt x

theorem gap1 (f : ℝ → ℝ)
    (h : ∀ x : ℝ, 0 < x → HasDerivAt f (1 / x) (x ^ 2)) :
    ∀ y : ℝ, 0 < y → deriv f y = 1 / Real.sqrt y := by
  intro y hy
  have hd := h (Real.sqrt y) (Real.sqrt_pos.2 hy)
  rw [Real.sq_sqrt hy.le] at hd
  simpa using hd.deriv

theorem gap2 (f : ℝ → ℝ) (hf : DifferentiableOn ℝ f (Set.Ioi 0)) :
    FamilyOn (Set.Ioi 0) (deriv f) =
      TranslatesOn (Set.Ioi 0) f := by
  apply Set.ext
  intro F
  change
    (∀ x ∈ Set.Ioi (0 : ℝ), HasDerivAt F (deriv f x) x) ↔
      ∃ C : ℝ, ∀ x ∈ Set.Ioi (0 : ℝ), F x = f x + C
  have hf_at : ∀ x ∈ Set.Ioi (0 : ℝ), HasDerivAt f (deriv f x) x := by
    intro x hx
    exact ((hf x hx).differentiableAt (isOpen_Ioi.mem_nhds hx)).hasDerivAt
  constructor
  · intro hF
    refine ⟨F 1 - f 1, ?_⟩
    intro x hx
    have hdiff : DifferentiableOn ℝ (fun z => F z - f z) (Set.Ioi 0) := by
      intro z hz
      exact ((hF z hz).sub (hf_at z hz)).differentiableAt.differentiableWithinAt
    have hzero : ∀ z ∈ Set.Ioi (0 : ℝ), deriv (fun w => F w - f w) z = 0 := by
      intro z hz
      have hd := (hF z hz).sub (hf_at z hz)
      simpa using hd.deriv
    have h1 : (1 : ℝ) ∈ Set.Ioi 0 := by
      change (0 : ℝ) < 1
      exact zero_lt_one
    have hconst :
        (fun z => F z - f z) x = (fun z => F z - f z) 1 :=
      isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi hdiff hzero hx h1
    dsimp at hconst ⊢
    linarith
  · rintro ⟨C, hC⟩
    intro x hx
    have heq : F =ᶠ[nhds x] (fun z => f z + C) := by
      filter_upwards [isOpen_Ioi.mem_nhds hx] with z hz
      exact hC z hz
    exact ((hf_at x hx).add_const C).congr_of_eventuallyEq heq

theorem gap3 (f : ℝ → ℝ)
    (h : ∀ x : ℝ, 0 < x → deriv f x = 1 / Real.sqrt x) :
    FamilyOn (Set.Ioi 0) (deriv f) =
      FamilyOn (Set.Ioi 0) (fun x => 1 / Real.sqrt x) := by
  apply Set.ext
  intro F
  change
    (∀ x ∈ Set.Ioi (0 : ℝ), HasDerivAt F (deriv f x) x) ↔
      ∀ x ∈ Set.Ioi (0 : ℝ), HasDerivAt F (1 / Real.sqrt x) x
  constructor
  · intro hF x hx
    simpa [h x hx] using hF x hx
  · intro hF x hx
    simpa [h x hx] using hF x hx

theorem gap4 :
    FamilyOn (Set.Ioi 0) (fun x => 1 / Real.sqrt x) =
      TranslatesOn (Set.Ioi 0) sqrtPrimitive := by
  have hsder : ∀ x ∈ Set.Ioi (0 : ℝ),
      HasDerivAt sqrtPrimitive (1 / Real.sqrt x) x := by
    intro x hx
    have hsqrt_ne : Real.sqrt x ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hx)
    have hd : HasDerivAt (fun z : ℝ => 2 * Real.sqrt z)
        (2 * (1 / (2 * Real.sqrt x))) x :=
      (Real.hasDerivAt_sqrt (ne_of_gt hx)).const_mul 2
    have hcoef : 2 * (1 / (2 * Real.sqrt x)) = 1 / Real.sqrt x := by
      field_simp [hsqrt_ne]
    simpa only [sqrtPrimitive, hcoef] using hd
  have hsDiff : DifferentiableOn ℝ sqrtPrimitive (Set.Ioi 0) := by
    intro x hx
    exact (hsder x hx).differentiableAt.differentiableWithinAt
  have hsval : ∀ x : ℝ, 0 < x → deriv sqrtPrimitive x = 1 / Real.sqrt x := by
    intro x hx
    exact (hsder x hx).deriv
  exact (gap3 sqrtPrimitive hsval).symm.trans (gap2 sqrtPrimitive hsDiff)

theorem gap5 (f : ℝ → ℝ)
    (h : ∀ x : ℝ, 0 < x → HasDerivAt f (1 / Real.sqrt x) x) :
    TranslatesOn (Set.Ioi 0) f =
      TranslatesOn (Set.Ioi 0) sqrtPrimitive := by
  have hf : DifferentiableOn ℝ f (Set.Ioi 0) := by
    intro x hx
    exact (h x hx).differentiableAt.differentiableWithinAt
  have hval : ∀ x : ℝ, 0 < x → deriv f x = 1 / Real.sqrt x := by
    intro x hx
    exact (h x hx).deriv
  calc
    TranslatesOn (Set.Ioi 0) f = FamilyOn (Set.Ioi 0) (deriv f) :=
      (gap2 f hf).symm
    _ = FamilyOn (Set.Ioi 0) (fun x => 1 / Real.sqrt x) :=
      gap3 f hval
    _ = TranslatesOn (Set.Ioi 0) sqrtPrimitive := gap4

end
end ProofGap.Exercise2178
