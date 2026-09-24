import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace ProofGap.Exercise1734

noncomputable section

def domain : Set ℝ := Set.Ioi 1
def original (x : ℝ) : ℝ := 1 / (x ^ 2 + x - 2)
def partialFractions (x : ℝ) : ℝ :=
  (1 / 3) * (1 / (x - 1) - 1 / (x + 2))
def primitive (x : ℝ) : ℝ := (1 / 3) * Real.log |(x - 1) / (x + 2)|
def AntiderivativesOn (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | DifferentiableOn ℝ F domain ∧ ∀ x ∈ domain, deriv F x = g x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ domain, F x = p x + C}

private theorem primitive_hasDerivAt (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt primitive (partialFractions x) x := by
  change 1 < x at hx
  have hxdom : x ∈ Set.Ioi (1 : ℝ) := hx
  have hx1 : x - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hx)
  have hx2 : x + 2 ≠ 0 := ne_of_gt (by linarith)
  have hlog1 :
      HasDerivAt (fun y : ℝ => Real.log (y - 1)) ((x - 1)⁻¹) x := by
    simpa [one_div] using
      (Real.hasDerivAt_log hx1).comp x ((hasDerivAt_id x).sub_const 1)
  have hlog2 :
      HasDerivAt (fun y : ℝ => Real.log (y + 2)) ((x + 2)⁻¹) x := by
    simpa [one_div] using
      (Real.hasDerivAt_log hx2).comp x ((hasDerivAt_id x).add_const 2)
  have hsimple :
      HasDerivAt
        (fun y : ℝ =>
          (3 : ℝ)⁻¹ * (Real.log (y - 1) - Real.log (y + 2)))
        ((3 : ℝ)⁻¹ * ((x - 1)⁻¹ - (x + 2)⁻¹)) x := by
    exact (hlog1.sub hlog2).const_mul (3 : ℝ)⁻¹
  have heq :
      Filter.EventuallyEq (nhds x) primitive
        (fun y : ℝ =>
          (3 : ℝ)⁻¹ * (Real.log (y - 1) - Real.log (y + 2))) := by
    apply Filter.Eventually.mono (isOpen_Ioi.mem_nhds hxdom)
    intro y hy
    have hy1 : 0 < y - 1 := sub_pos.mpr hy
    have hy2 : 0 < y + 2 := by linarith
    unfold primitive
    rw [abs_of_pos (div_pos hy1 hy2)]
    rw [Real.log_div hy1.ne' hy2.ne']
    simp only [one_div]
  simpa [partialFractions, one_div] using
    hsimple.congr_of_eventuallyEq heq

theorem gap1 : AntiderivativesOn original = AntiderivativesOn partialFractions := by
  have hfunctions : ∀ x ∈ domain, original x = partialFractions x := by
    intro x hx
    change 1 < x at hx
    have hx1 : x - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hx)
    have hx2 : x + 2 ≠ 0 := ne_of_gt (by linarith)
    unfold original partialFractions
    rw [show x ^ 2 + x - 2 = (x - 1) * (x + 2) by ring]
    field_simp [hx1, hx2]
    <;> ring
  ext F
  change
    (DifferentiableOn ℝ F domain ∧ ∀ x ∈ domain, deriv F x = original x) ↔
      (DifferentiableOn ℝ F domain ∧
        ∀ x ∈ domain, deriv F x = partialFractions x)
  constructor
  · rintro ⟨hF, hderiv⟩
    refine ⟨hF, fun x hx => ?_⟩
    calc
      deriv F x = original x := hderiv x hx
      _ = partialFractions x := hfunctions x hx
  · rintro ⟨hF, hderiv⟩
    refine ⟨hF, fun x hx => ?_⟩
    calc
      deriv F x = partialFractions x := hderiv x hx
      _ = original x := (hfunctions x hx).symm

theorem gap2 : AntiderivativesOn partialFractions = PrimitiveFamily primitive := by
  ext F
  change
    (DifferentiableOn ℝ F domain ∧
        ∀ x ∈ domain, deriv F x = partialFractions x) ↔
      (∃ C : ℝ, ∀ x ∈ domain, F x = primitive x + C)
  constructor
  · rintro ⟨hFdiff, hFderiv⟩
    let D : ℝ → ℝ := fun x => F x - primitive x
    have hDhas : ∀ y ∈ domain, HasDerivAt D 0 y := by
      intro y hy
      have hFat : DifferentiableAt ℝ F y :=
        (hFdiff y hy).differentiableAt (isOpen_Ioi.mem_nhds hy)
      have h := hFat.hasDerivAt.sub (primitive_hasDerivAt y hy)
      rw [hFderiv y hy] at h
      simpa [D] using h
    have hlt : ∀ {a b : ℝ}, a ∈ domain → b ∈ domain → a < b → D a = D b := by
      intro a b ha hb hab
      have ha' : 1 < a := ha
      have hcont : ContinuousOn D (Set.Icc a b) := by
        intro y hy
        have hydomain : y ∈ domain := by
          change 1 < y
          exact lt_of_lt_of_le ha' hy.1
        exact (hDhas y hydomain).continuousAt.continuousWithinAt
      have hdiff : DifferentiableOn ℝ D (Set.Ioo a b) := by
        intro y hy
        have hydomain : y ∈ domain := by
          change 1 < y
          exact lt_trans ha' hy.1
        exact (hDhas y hydomain).differentiableAt.differentiableWithinAt
      obtain ⟨c, hc, hslope⟩ := exists_deriv_eq_slope D hab hcont hdiff
      have hcDomain : c ∈ domain := by
        change 1 < c
        exact lt_trans ha' hc.1
      rw [(hDhas c hcDomain).deriv] at hslope
      have hba : b - a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
      field_simp [hba] at hslope
      linarith
    have htwo : (2 : ℝ) ∈ domain := by
      norm_num [domain]
    have hconst : ∀ x ∈ domain, D x = D 2 := by
      intro x hx
      rcases lt_trichotomy x 2 with hx2 | hx2 | hx2
      · exact hlt hx htwo hx2
      · simpa [hx2]
      · exact (hlt htwo hx hx2).symm
    refine ⟨D 2, ?_⟩
    intro x hx
    have heq := hconst x hx
    dsimp [D] at heq ⊢
    linarith
  · rintro ⟨C, hC⟩
    have hFat : ∀ x ∈ domain, HasDerivAt F (partialFractions x) x := by
      intro x hx
      have hxdom : x ∈ Set.Ioi (1 : ℝ) := hx
      have heq :
          Filter.EventuallyEq (nhds x) (fun y : ℝ => primitive y + C) F := by
        apply Filter.Eventually.mono (isOpen_Ioi.mem_nhds hxdom)
        intro y hy
        exact (hC y hy).symm
      exact ((primitive_hasDerivAt x hx).add_const C).congr_of_eventuallyEq heq.symm
    refine ⟨?_, ?_⟩
    · intro x hx
      exact (hFat x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      exact (hFat x hx).deriv

theorem gap3 : AntiderivativesOn original = PrimitiveFamily primitive := by
  calc
    AntiderivativesOn original = AntiderivativesOn partialFractions := gap1
    _ = PrimitiveFamily primitive := gap2

end
end ProofGap.Exercise1734
