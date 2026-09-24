import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise1650

noncomputable section

def domain : Set ℝ := Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)
def sec (x : ℝ) : ℝ := 1 / Real.cos x
def primitive (x : ℝ) : ℝ := Real.tan x - x
def AntiderivativesOn (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | DifferentiableOn ℝ F domain ∧ ∀ x ∈ domain, deriv F x = g x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ domain, F x = p x + C}

private theorem domain_isOpen : IsOpen domain := by
  rw [domain]
  exact isOpen_Ioo

private theorem tan_sq_eq_sec_sq_sub_one {x : ℝ} (hx : x ∈ domain) :
    Real.tan x ^ 2 = sec x ^ 2 - 1 := by
  have hcos_pos : 0 < Real.cos x := by
    apply Real.cos_pos_of_mem_Ioo
    simpa [domain] using hx
  rw [Real.tan_eq_sin_div_cos]
  simp only [sec]
  field_simp [ne_of_gt hcos_pos]
  nlinarith [Real.sin_sq_add_cos_sq x]

private theorem hasDerivAt_primitive (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt primitive (sec x ^ 2 - 1) x := by
  have hcos_pos : 0 < Real.cos x := by
    apply Real.cos_pos_of_mem_Ioo
    simpa [domain] using hx
  have hcos : Real.cos x ≠ 0 := ne_of_gt hcos_pos
  simpa [primitive, sec, div_pow] using
    (Real.hasDerivAt_tan hcos).sub (hasDerivAt_id x)

private theorem primitive_differentiableOn :
    DifferentiableOn ℝ primitive domain := by
  intro x hx
  exact (hasDerivAt_primitive x hx).differentiableAt.differentiableWithinAt

private theorem exists_primitive_constant
    {F : ℝ → ℝ}
    (hF : DifferentiableOn ℝ F domain)
    (hderiv : ∀ x ∈ domain, deriv F x = sec x ^ 2 - 1) :
    ∃ C : ℝ, ∀ x ∈ domain, F x = primitive x + C := by
  let G : ℝ → ℝ := fun y => F y - primitive y
  have hGdiff : DifferentiableOn ℝ G domain := by
    dsimp [G]
    exact hF.sub primitive_differentiableOn
  have hGderiv : ∀ x ∈ domain, deriv G x = 0 := by
    intro x hx
    have hFat : DifferentiableAt ℝ F x :=
      (hF x hx).differentiableAt (domain_isOpen.mem_nhds hx)
    calc
      deriv G x = deriv F x - (sec x ^ 2 - 1) := by
        dsimp [G]
        exact (hFat.hasDerivAt.sub (hasDerivAt_primitive x hx)).deriv
      _ = 0 := by rw [hderiv x hx]; ring
  have hzero : (0 : ℝ) ∈ domain := by
    simp only [domain, Set.mem_Ioo]
    constructor <;> nlinarith [Real.pi_pos]
  refine ⟨F 0 - primitive 0, ?_⟩
  intro x hx
  have hconst : G x = G 0 := by
    rcases lt_trichotomy x 0 with hx0 | hx0 | hx0
    · have hIcc : Set.Icc x 0 ⊆ domain := by
        intro y hy
        have hxm : -(Real.pi / 2) < x ∧ x < Real.pi / 2 := by
          simpa only [domain, Set.mem_Ioo] using hx
        have h0m : -(Real.pi / 2) < (0 : ℝ) ∧ (0 : ℝ) < Real.pi / 2 := by
          simpa only [domain, Set.mem_Ioo] using hzero
        simpa only [domain, Set.mem_Ioo] using
          And.intro (lt_of_lt_of_le hxm.1 hy.1) (lt_of_le_of_lt hy.2 h0m.2)
      have hcont : ContinuousOn G (Set.Icc x 0) :=
        hGdiff.continuousOn.mono hIcc
      have hdiff : DifferentiableOn ℝ G (Set.Ioo x 0) :=
        hGdiff.mono (fun y hy => hIcc ⟨le_of_lt hy.1, le_of_lt hy.2⟩)
      obtain ⟨c, hc, hcslope⟩ :=
        exists_deriv_eq_slope (f := G) hx0 hcont hdiff
      have hcdom : c ∈ domain :=
        hIcc ⟨le_of_lt hc.1, le_of_lt hc.2⟩
      rw [hGderiv c hcdom] at hcslope
      have hden : (0 : ℝ) - x ≠ 0 := ne_of_gt (sub_pos.mpr hx0)
      field_simp [hden] at hcslope
      linarith
    · simpa [hx0]
    · have hIcc : Set.Icc 0 x ⊆ domain := by
        intro y hy
        have hxm : -(Real.pi / 2) < x ∧ x < Real.pi / 2 := by
          simpa only [domain, Set.mem_Ioo] using hx
        have h0m : -(Real.pi / 2) < (0 : ℝ) ∧ (0 : ℝ) < Real.pi / 2 := by
          simpa only [domain, Set.mem_Ioo] using hzero
        simpa only [domain, Set.mem_Ioo] using
          And.intro (lt_of_lt_of_le h0m.1 hy.1) (lt_of_le_of_lt hy.2 hxm.2)
      have hcont : ContinuousOn G (Set.Icc 0 x) :=
        hGdiff.continuousOn.mono hIcc
      have hdiff : DifferentiableOn ℝ G (Set.Ioo 0 x) :=
        hGdiff.mono (fun y hy => hIcc ⟨le_of_lt hy.1, le_of_lt hy.2⟩)
      obtain ⟨c, hc, hcslope⟩ :=
        exists_deriv_eq_slope (f := G) hx0 hcont hdiff
      have hcdom : c ∈ domain :=
        hIcc ⟨le_of_lt hc.1, le_of_lt hc.2⟩
      rw [hGderiv c hcdom] at hcslope
      have hden : x - (0 : ℝ) ≠ 0 := ne_of_gt (sub_pos.mpr hx0)
      field_simp [hden] at hcslope
      linarith
  dsimp [G] at hconst
  linarith

private theorem hasDerivAt_of_eq_primitive_add_const
    {F : ℝ → ℝ} {C : ℝ}
    (hF : ∀ x ∈ domain, F x = primitive x + C)
    (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt F (sec x ^ 2 - 1) x := by
  have hlocal : F =ᶠ[nhds x] (fun y => primitive y + C) := by
    filter_upwards [domain_isOpen.mem_nhds hx] with y hy
    exact hF y hy
  have hprimitive : HasDerivAt (fun y => primitive y + C) (sec x ^ 2 - 1) x := by
    simpa using (hasDerivAt_primitive x hx).add_const C
  exact hprimitive.congr_of_eventuallyEq hlocal

theorem gap1 :
    AntiderivativesOn (fun x => Real.tan x ^ 2) =
      AntiderivativesOn (fun x => sec x ^ 2 - 1) := by
  ext F
  simp only [AntiderivativesOn, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hF, hderiv⟩
    refine ⟨hF, ?_⟩
    intro x hx
    calc
      deriv F x = Real.tan x ^ 2 := hderiv x hx
      _ = sec x ^ 2 - 1 := tan_sq_eq_sec_sq_sub_one hx
  · rintro ⟨hF, hderiv⟩
    refine ⟨hF, ?_⟩
    intro x hx
    calc
      deriv F x = sec x ^ 2 - 1 := hderiv x hx
      _ = Real.tan x ^ 2 := (tan_sq_eq_sec_sq_sub_one hx).symm

theorem gap2 :
    AntiderivativesOn (fun x => sec x ^ 2 - 1) =
      PrimitiveFamily primitive := by
  ext F
  simp only [AntiderivativesOn, PrimitiveFamily, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hF, hderiv⟩
    exact exists_primitive_constant hF hderiv
  · rintro ⟨C, hC⟩
    refine ⟨?_, ?_⟩
    · intro x hx
      exact (hasDerivAt_of_eq_primitive_add_const hC x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      exact (hasDerivAt_of_eq_primitive_add_const hC x hx).deriv

theorem gap3 :
    AntiderivativesOn (fun x => Real.tan x ^ 2) =
      PrimitiveFamily primitive := by
  exact gap1.trans gap2

end
end ProofGap.Exercise1650
