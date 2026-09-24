import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1729

noncomputable section

def domain : Set ℝ := Set.Ioi 1
def original (x : ℝ) : ℝ := 1 / (Real.sqrt (x + 1) + Real.sqrt (x - 1))
def rationalized (x : ℝ) : ℝ :=
  (1 / 2) * (Real.sqrt (x + 1) - Real.sqrt (x - 1))
def primitive (x : ℝ) : ℝ :=
  (1 / 3) * (Real.rpow (x + 1) (3 / 2) - Real.rpow (x - 1) (3 / 2))
def AntiderivativesOn (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | DifferentiableOn ℝ F domain ∧ ∀ x ∈ domain, deriv F x = g x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ domain, F x = p x + C}

private theorem domain_isOpen : IsOpen domain := by
  simpa [domain] using (isOpen_Ioi : IsOpen (Set.Ioi (1 : ℝ)))

private theorem original_eq_rationalized {x : ℝ} (hx : x ∈ domain) :
    original x = rationalized x := by
  have hx' : 1 < x := hx
  have hp : 0 < x + 1 := by linarith
  have hm : 0 < x - 1 := by linarith
  have hsp : Real.sqrt (x + 1) ^ 2 = x + 1 :=
    Real.sq_sqrt hp.le
  have hsm : Real.sqrt (x - 1) ^ 2 = x - 1 :=
    Real.sq_sqrt hm.le
  have hden :
      Real.sqrt (x + 1) + Real.sqrt (x - 1) ≠ 0 := by
    positivity
  unfold original rationalized
  field_simp [hden]
  nlinarith

private theorem primitive_hasDerivAt {x : ℝ} (hx : x ∈ domain) :
    HasDerivAt primitive (rationalized x) x := by
  have hx' : 1 < x := hx
  have hp : 0 < x + 1 := by linarith
  have hm : 0 < x - 1 := by linarith
  have hplus : HasDerivAt (fun y : ℝ => y + 1) 1 x := by
    simpa using (hasDerivAt_id x).add_const 1
  have hminus : HasDerivAt (fun y : ℝ => y - 1) 1 x := by
    simpa using (hasDerivAt_id x).sub_const 1
  have hrp :
      HasDerivAt (fun y : ℝ => Real.rpow (y + 1) (3 / 2))
        ((3 / 2) * Real.rpow (x + 1) (1 / 2)) x := by
    change HasDerivAt (fun y : ℝ => (y + 1) ^ (3 / 2 : ℝ))
      ((3 / 2 : ℝ) * (x + 1) ^ (1 / 2 : ℝ)) x
    have he : (3 / 2 : ℝ) - 1 = 1 / 2 := by ring
    simpa only [he, mul_one, Function.comp_def] using
      (Real.hasDerivAt_rpow_const (p := (3 / 2 : ℝ))
        (Or.inl (ne_of_gt hp))).comp x hplus
  have hrm :
      HasDerivAt (fun y : ℝ => Real.rpow (y - 1) (3 / 2))
        ((3 / 2) * Real.rpow (x - 1) (1 / 2)) x := by
    change HasDerivAt (fun y : ℝ => (y - 1) ^ (3 / 2 : ℝ))
      ((3 / 2 : ℝ) * (x - 1) ^ (1 / 2 : ℝ)) x
    have he : (3 / 2 : ℝ) - 1 = 1 / 2 := by ring
    simpa only [he, mul_one, Function.comp_def] using
      (Real.hasDerivAt_rpow_const (p := (3 / 2 : ℝ))
        (Or.inl (ne_of_gt hm))).comp x hminus
  have hsp :
      Real.rpow (x + 1) (1 / 2) = Real.sqrt (x + 1) := by
    change (x + 1) ^ (1 / 2 : ℝ) = Real.sqrt (x + 1)
    exact (Real.sqrt_eq_rpow (x + 1)).symm
  have hsm :
      Real.rpow (x - 1) (1 / 2) = Real.sqrt (x - 1) := by
    change (x - 1) ^ (1 / 2 : ℝ) = Real.sqrt (x - 1)
    exact (Real.sqrt_eq_rpow (x - 1)).symm
  unfold primitive rationalized
  convert (hrp.sub hrm).const_mul (1 / 3 : ℝ) using 1
  rw [hsp, hsm]
  ring

theorem gap1 : AntiderivativesOn original = AntiderivativesOn rationalized := by
  ext F
  simp only [AntiderivativesOn, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hF, hderiv⟩
    exact ⟨hF, fun x hx => (hderiv x hx).trans (original_eq_rationalized hx)⟩
  · rintro ⟨hF, hderiv⟩
    exact ⟨hF, fun x hx => (hderiv x hx).trans (original_eq_rationalized hx).symm⟩

theorem gap2 : AntiderivativesOn rationalized = PrimitiveFamily primitive := by
  ext F
  simp only [AntiderivativesOn, PrimitiveFamily, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hFdiff, hFderiv⟩
    let H : ℝ → ℝ := fun x => F x - primitive x
    have hHzero : ∀ x ∈ domain, HasDerivAt H 0 x := by
      intro x hx
      have hFat : DifferentiableAt ℝ F x :=
        (hFdiff x hx).differentiableAt (domain_isOpen.mem_nhds hx)
      have hFder : HasDerivAt F (rationalized x) x := by
        simpa only [hFderiv x hx] using hFat.hasDerivAt
      simpa [H] using hFder.sub (primitive_hasDerivAt hx)
    have hHdiff : DifferentiableOn ℝ H domain := by
      intro x hx
      exact (hHzero x hx).differentiableAt.differentiableWithinAt
    have hHderiv : ∀ x ∈ domain, deriv H x = 0 := by
      intro x hx
      exact (hHzero x hx).deriv
    have hpre : IsPreconnected domain := by
      exact (convex_Ioi (1 : ℝ)).isPreconnected
    refine ⟨F 2 - primitive 2, ?_⟩
    intro x hx
    have htwo : (2 : ℝ) ∈ domain := by norm_num [domain]
    have hc : H x = H 2 :=
      domain_isOpen.is_const_of_deriv_eq_zero
        hpre hHdiff hHderiv hx htwo
    dsimp [H] at hc
    linarith
  · rintro ⟨C, hFC⟩
    have hFat : ∀ x ∈ domain, HasDerivAt F (rationalized x) x := by
      intro x hx
      have hsum :=
        (primitive_hasDerivAt hx).add_const C
      have hevent : F =ᶠ[nhds x] fun y => primitive y + C := by
        filter_upwards [domain_isOpen.mem_nhds hx] with y hy
        exact hFC y hy
      exact hsum.congr_of_eventuallyEq hevent
    constructor
    · intro x hx
      exact (hFat x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      exact (hFat x hx).deriv

theorem gap3 : AntiderivativesOn original = PrimitiveFamily primitive := by
  exact gap1.trans gap2

end
end ProofGap.Exercise1729
