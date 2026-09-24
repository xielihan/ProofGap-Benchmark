import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1677

noncomputable section

def inner (x : ℝ) : ℝ := 1 + x ^ 2
def integrand (x : ℝ) : ℝ := x / inner x ^ 2
def primitive (x : ℝ) : ℝ := -1 / (2 * inner x)

def IsAntiderivativeOn (F f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, HasDerivAt F (f x) x
def Family (f : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | IsAntiderivativeOn F f s}
def Translates (P : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C, ∀ x ∈ s, F x = P x + C}

private theorem hasDerivAt_inner (x : ℝ) : HasDerivAt inner (2 * x) x := by
  convert
    (hasDerivAt_const x (1 : ℝ)).add
      ((hasDerivAt_id x).mul (hasDerivAt_id x)) using 1
  · ext y
    simp [inner, pow_two]
  · simp [id]
    ring

private theorem eq_const_of_deriv_eq_zero {f : ℝ → ℝ}
    (hf : Differentiable ℝ f) (hderiv : ∀ x, deriv f x = 0) (x : ℝ) :
    f x = f 0 := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · obtain ⟨c, hc, hcderiv⟩ :=
      exists_deriv_eq_slope f hx hf.continuous.continuousOn hf.differentiableOn
    rw [hderiv c] at hcderiv
    have hden : (0 : ℝ) - x ≠ 0 := by linarith
    have hslope : (f 0 - f x) / (0 - x) = 0 := hcderiv.symm
    have hnum : f 0 - f x = 0 :=
      (div_eq_zero_iff.mp hslope).resolve_right hden
    linarith
  · subst x
    rfl
  · obtain ⟨c, hc, hcderiv⟩ :=
      exists_deriv_eq_slope f hx hf.continuous.continuousOn hf.differentiableOn
    rw [hderiv c] at hcderiv
    have hden : x - (0 : ℝ) ≠ 0 := by linarith
    have hslope : (f x - f 0) / (x - 0) = 0 := hcderiv.symm
    have hnum : f x - f 0 = 0 :=
      (div_eq_zero_iff.mp hslope).resolve_right hden
    linarith

theorem gap1 (x : ℝ) :
    integrand x = (1 / 2 : ℝ) * deriv inner x / inner x ^ 2 := by
  rw [(hasDerivAt_inner x).deriv]
  unfold integrand
  ring

theorem gap2 (x : ℝ) :
    HasDerivAt primitive (integrand x) x := by
  have hi_pos : 0 < inner x := by
    unfold inner
    nlinarith [sq_nonneg x]
  have hden : HasDerivAt (fun y => 2 * inner y) (2 * (2 * x)) x := by
    simpa using (hasDerivAt_const x (2 : ℝ)).mul (hasDerivAt_inner x)
  have hden_ne : 2 * inner x ≠ 0 :=
    mul_ne_zero (by norm_num) (ne_of_gt hi_pos)
  have hquot := (hasDerivAt_const x (-1 : ℝ)).div hden hden_ne
  unfold primitive
  convert hquot using 1
  · unfold integrand
    field_simp [hden_ne, ne_of_gt hi_pos]
    ring

theorem gap3 :
    Family integrand Set.univ = Translates primitive Set.univ := by
  ext F
  constructor
  · intro hF
    change IsAntiderivativeOn F integrand Set.univ at hF
    change ∃ C, ∀ x ∈ Set.univ, F x = primitive x + C
    have hzero : ∀ x, HasDerivAt (fun y => F y - primitive y) 0 x := by
      intro x
      simpa using (hF x (Set.mem_univ x)).sub (gap2 x)
    have hdiff : Differentiable ℝ (fun y => F y - primitive y) :=
      fun x => (hzero x).differentiableAt
    have hderiv : ∀ x, deriv (fun y => F y - primitive y) x = 0 :=
      fun x => (hzero x).deriv
    refine ⟨F 0 - primitive 0, ?_⟩
    intro x hx
    have hc := eq_const_of_deriv_eq_zero hdiff hderiv x
    linarith
  · intro hF
    change ∃ C, ∀ x ∈ Set.univ, F x = primitive x + C at hF
    change IsAntiderivativeOn F integrand Set.univ
    obtain ⟨C, hC⟩ := hF
    have hEq : F = fun y => primitive y + C := by
      funext y
      exact hC y (Set.mem_univ y)
    intro x hx
    rw [hEq]
    exact (gap2 x).add_const C

end

end ProofGap.Exercise1677
