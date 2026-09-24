import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1754

noncomputable section

def domain : Set ℝ := Set.Ioo 0 (Real.pi / 2)
def cot (x : ℝ) : ℝ := Real.cos x / Real.sin x
def original (x : ℝ) : ℝ := 1 / (Real.sin x ^ 2 * Real.cos x ^ 2)
def split (x : ℝ) : ℝ := 1 / Real.sin x ^ 2 + 1 / Real.cos x ^ 2
def primitive (x : ℝ) : ℝ := -cot x + Real.tan x
def AntiderivativesOn (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | DifferentiableOn ℝ F domain ∧ ∀ x ∈ domain, deriv F x = g x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ domain, F x = p x + C}

theorem gap1 : AntiderivativesOn original = AntiderivativesOn split := by
  apply Set.ext
  intro F
  simp only [AntiderivativesOn, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hF, hderiv⟩
    refine ⟨hF, ?_⟩
    intro x hx
    rw [hderiv x hx]
    rcases hx with ⟨hx0, hxpi⟩
    have hpi2 : Real.pi / 2 < Real.pi := by
      nlinarith [Real.pi_pos]
    have hsin : Real.sin x ≠ 0 :=
      ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hx0 (lt_trans hxpi hpi2))
    have hcos : Real.cos x ≠ 0 := by
      apply ne_of_gt
      apply Real.cos_pos_of_mem_Ioo
      constructor
      · nlinarith [Real.pi_pos]
      · exact hxpi
    simp only [original, split]
    field_simp [hsin, hcos]
    nlinarith [Real.sin_sq_add_cos_sq x]
  · rintro ⟨hF, hderiv⟩
    refine ⟨hF, ?_⟩
    intro x hx
    rw [hderiv x hx]
    rcases hx with ⟨hx0, hxpi⟩
    have hpi2 : Real.pi / 2 < Real.pi := by
      nlinarith [Real.pi_pos]
    have hsin : Real.sin x ≠ 0 :=
      ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hx0 (lt_trans hxpi hpi2))
    have hcos : Real.cos x ≠ 0 := by
      apply ne_of_gt
      apply Real.cos_pos_of_mem_Ioo
      constructor
      · nlinarith [Real.pi_pos]
      · exact hxpi
    simp only [original, split]
    field_simp [hsin, hcos]
    nlinarith [Real.sin_sq_add_cos_sq x]

theorem gap2 : AntiderivativesOn split = PrimitiveFamily primitive := by
  apply Set.ext
  intro F
  simp only [AntiderivativesOn, PrimitiveFamily, Set.mem_setOf_eq]
  have hprim : ∀ x ∈ domain, HasDerivAt primitive (split x) x := by
    intro x hx
    rcases hx with ⟨hx0, hxpi⟩
    have hpi2 : Real.pi / 2 < Real.pi := by
      nlinarith [Real.pi_pos]
    have hsin : Real.sin x ≠ 0 :=
      ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hx0 (lt_trans hxpi hpi2))
    have hcos : Real.cos x ≠ 0 := by
      apply ne_of_gt
      apply Real.cos_pos_of_mem_Ioo
      constructor
      · nlinarith [Real.pi_pos]
      · exact hxpi
    have hcoef :
        ((-Real.sin x) * Real.sin x - Real.cos x * Real.cos x) /
            Real.sin x ^ 2 =
          -1 / Real.sin x ^ 2 := by
      field_simp [hsin]
      nlinarith [Real.sin_sq_add_cos_sq x]
    have hcot : HasDerivAt cot (-1 / Real.sin x ^ 2) x := by
      rw [← hcoef]
      simpa only [cot] using
        (Real.hasDerivAt_cos x).div (Real.hasDerivAt_sin x) hsin
    have htan : HasDerivAt Real.tan (1 / Real.cos x ^ 2) x := by
      simpa using Real.hasDerivAt_tan hcos
    simpa only [primitive, split, one_div, neg_div, neg_neg] using
      hcot.neg.add htan
  constructor
  · rintro ⟨hFdiff, hFderiv⟩
    have hPdiff : DifferentiableOn ℝ primitive domain := by
      intro x hx
      exact (hprim x hx).differentiableAt.differentiableWithinAt
    have hdiff : ∀ x ∈ domain, deriv (fun y => F y - primitive y) x = 0 := by
      intro x hx
      have hxn : domain ∈ nhds x :=
        IsOpen.mem_nhds isOpen_Ioo hx
      have hFat : DifferentiableAt ℝ F x :=
        (hFdiff x hx).differentiableAt hxn
      have hsub := hFat.hasDerivAt.sub (hprim x hx)
      calc
        deriv (fun y => F y - primitive y) x = deriv F x - split x := hsub.deriv
        _ = 0 := by rw [hFderiv x hx]; simp
    have hxbase : Real.pi / 4 ∈ domain := by
      rw [domain]
      constructor <;> nlinarith [Real.pi_pos]
    refine ⟨F (Real.pi / 4) - primitive (Real.pi / 4), ?_⟩
    intro x hx
    have heq :
        (F - primitive) x =
          (F - primitive) (Real.pi / 4) := by
      exact
        isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
          (hFdiff.sub hPdiff) hdiff hx hxbase
    dsimp at heq
    linarith
  · rintro ⟨C, hFC⟩
    have hhas : ∀ x ∈ domain, HasDerivAt F (split x) x := by
      intro x hx
      have hxn : domain ∈ nhds x :=
        IsOpen.mem_nhds isOpen_Ioo hx
      have hlocal : F =ᶠ[nhds x] fun y => primitive y + C := by
        filter_upwards [hxn] with y hy
        exact hFC y hy
      exact ((hprim x hx).add_const C).congr_of_eventuallyEq hlocal
    constructor
    · intro x hx
      exact (hhas x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      exact (hhas x hx).deriv

theorem gap3 : AntiderivativesOn original = PrimitiveFamily primitive := by
  rw [gap1, gap2]

end
end ProofGap.Exercise1754
