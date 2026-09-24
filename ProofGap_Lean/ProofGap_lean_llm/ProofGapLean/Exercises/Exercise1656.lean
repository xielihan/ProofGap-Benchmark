import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1656

noncomputable section

def integrand (x : ℝ) : ℝ := (2 * x - 3) ^ 10
def primitive₁ (x : ℝ) : ℝ := (1 / 2) * (1 / 11) * (2 * x - 3) ^ 11
def primitive₂ (x : ℝ) : ℝ := (1 / 22) * (2 * x - 3) ^ 11
def Antiderivatives (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | Differentiable ℝ F ∧ ∀ x, deriv F x = g x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x, F x = p x + C}

private lemma primitive₁_hasDerivAt (x : ℝ) :
    HasDerivAt primitive₁ (integrand x) x := by
  unfold primitive₁ integrand
  convert
    (((((hasDerivAt_id x).const_mul 2).sub_const 3).pow 11).const_mul
      ((1 / 2 : ℝ) * (1 / 11 : ℝ))) using 1 <;> norm_num <;> ring

private lemma eq_at_zero_of_hasDerivAt_zero
    (f : ℝ → ℝ) (hf : ∀ x, HasDerivAt f 0 x) :
    ∀ x, f x = f 0 := by
  have hdiff : Differentiable ℝ f := fun x => (hf x).differentiableAt
  intro x
  rcases lt_trichotomy x 0 with hx | hx | hx
  · obtain ⟨c, hc, hsl⟩ :=
      exists_deriv_eq_slope f hx hdiff.continuous.continuousOn
        hdiff.differentiableOn
    have hquot : (f 0 - f x) / (0 - x) = 0 := by
      simpa only [(hf c).deriv] using hsl.symm
    have hden : 0 - x ≠ 0 := sub_ne_zero.mpr (ne_of_gt hx)
    have hnum : f 0 - f x = 0 :=
      (div_eq_zero_iff.mp hquot).resolve_right hden
    exact (sub_eq_zero.mp hnum).symm
  · simpa [hx]
  · obtain ⟨c, hc, hsl⟩ :=
      exists_deriv_eq_slope f hx hdiff.continuous.continuousOn
        hdiff.differentiableOn
    have hquot : (f x - f 0) / (x - 0) = 0 := by
      simpa only [(hf c).deriv] using hsl.symm
    have hden : x - 0 ≠ 0 := sub_ne_zero.mpr (ne_of_gt hx)
    have hnum : f x - f 0 = 0 :=
      (div_eq_zero_iff.mp hquot).resolve_right hden
    exact sub_eq_zero.mp hnum

theorem gap1 : Antiderivatives integrand = PrimitiveFamily primitive₁ := by
  ext F
  simp only [Antiderivatives, PrimitiveFamily, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hFd, hderiv⟩
    have hzero : ∀ x, HasDerivAt (fun y => F y - primitive₁ y) 0 x := by
      intro x
      have hFx : HasDerivAt F (integrand x) x := by
        simpa only [hderiv x] using (hFd x).hasDerivAt
      simpa using hFx.sub (primitive₁_hasDerivAt x)
    refine ⟨F 0 - primitive₁ 0, ?_⟩
    intro x
    have hc := eq_at_zero_of_hasDerivAt_zero
      (fun y => F y - primitive₁ y) hzero x
    linarith
  · rintro ⟨C, hC⟩
    have hEq : F = fun x => primitive₁ x + C := funext hC
    rw [hEq]
    constructor
    · intro x
      exact ((primitive₁_hasDerivAt x).add_const C).differentiableAt
    · intro x
      exact ((primitive₁_hasDerivAt x).add_const C).deriv

theorem gap2 : PrimitiveFamily primitive₁ = PrimitiveFamily primitive₂ := by
  have hp : primitive₁ = primitive₂ := by
    funext x
    unfold primitive₁ primitive₂
    ring
  rw [hp]

theorem gap3 : Antiderivatives integrand = PrimitiveFamily primitive₂ := by
  exact gap1.trans gap2

end
end ProofGap.Exercise1656
