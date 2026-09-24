import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1661

noncomputable section

def integrand (x : ℝ) : ℝ := 1 / (2 + 3 * x ^ 2)
def primitive (x : ℝ) : ℝ :=
  1 / Real.sqrt 6 * Real.arctan (x * Real.sqrt (3 / 2))

def IsAntiderivativeOn (F f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, HasDerivAt F (f x) x
def Family (f : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | IsAntiderivativeOn F f s}
def Translates (P : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C, ∀ x ∈ s, F x = P x + C}

theorem gap1 (x : ℝ) :
    2 + 3 * x ^ 2 = (Real.sqrt 2) ^ 2 + (Real.sqrt 3 * x) ^ 2 := by
  have h2 : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have h3 : (Real.sqrt 3) ^ 2 = (3 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  nlinarith

theorem gap2 (x : ℝ) :
    HasDerivAt primitive (integrand x) x := by
  have ha2 : (Real.sqrt (3 / 2 : ℝ)) ^ 2 = (3 / 2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hb2 : (Real.sqrt 6) ^ 2 = (6 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have ha_nonneg : 0 ≤ Real.sqrt (3 / 2 : ℝ) := Real.sqrt_nonneg _
  have hb_nonneg : 0 ≤ Real.sqrt 6 := Real.sqrt_nonneg _
  have ha : Real.sqrt (3 / 2 : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hrel : Real.sqrt 6 = 2 * Real.sqrt (3 / 2 : ℝ) := by
    nlinarith [sq_nonneg (Real.sqrt 6 - 2 * Real.sqrt (3 / 2 : ℝ))]
  have hd1 : 1 + (x * Real.sqrt (3 / 2 : ℝ)) ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg (x * Real.sqrt (3 / 2 : ℝ))]
  have hd2 : 2 + 3 * x ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg x]
  have hinner :
      HasDerivAt (fun y : ℝ => y * Real.sqrt (3 / 2 : ℝ))
        (Real.sqrt (3 / 2 : ℝ)) x := by
    simpa using (hasDerivAt_id x).mul_const (Real.sqrt (3 / 2 : ℝ))
  have harctan :
      HasDerivAt
        (fun y : ℝ => Real.arctan (y * Real.sqrt (3 / 2 : ℝ)))
        (1 / (1 + (x * Real.sqrt (3 / 2 : ℝ)) ^ 2) *
          Real.sqrt (3 / 2 : ℝ)) x := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_arctan (x * Real.sqrt (3 / 2 : ℝ))).comp x hinner
  have hcoeff :
      1 / Real.sqrt 6 *
          (1 / (1 + (x * Real.sqrt (3 / 2 : ℝ)) ^ 2) *
            Real.sqrt (3 / 2 : ℝ)) =
        1 / (2 + 3 * x ^ 2) := by
    rw [hrel]
    field_simp [ha, hd1, hd2]
    nlinarith
  unfold primitive integrand
  rw [← hcoeff]
  exact harctan.const_mul (1 / Real.sqrt 6)

theorem gap3 :
    Family integrand Set.univ = Translates primitive Set.univ := by
  ext F
  constructor
  · intro hF
    change IsAntiderivativeOn F integrand Set.univ at hF
    change ∃ C, ∀ x ∈ Set.univ, F x = primitive x + C
    have hzero : ∀ x : ℝ,
        HasDerivAt (fun y : ℝ => F y - primitive y) 0 x := by
      intro x
      simpa using (hF x (by simp)).sub (gap2 x)
    have hdiff : Differentiable ℝ (fun y : ℝ => F y - primitive y) :=
      fun x => (hzero x).differentiableAt
    have hderiv : ∀ x : ℝ, deriv (fun y : ℝ => F y - primitive y) x = 0 :=
      fun x => (hzero x).deriv
    refine ⟨F 0 - primitive 0, ?_⟩
    intro x hx
    have heq : F x - primitive x = F 0 - primitive 0 :=
      is_const_of_deriv_eq_zero hdiff hderiv x 0
    linarith
  · intro hF
    change ∃ C, ∀ x ∈ Set.univ, F x = primitive x + C at hF
    change IsAntiderivativeOn F integrand Set.univ
    rcases hF with ⟨C, hC⟩
    have hEq : F = fun y : ℝ => primitive y + C := by
      funext y
      exact hC y (by simp)
    intro x hx
    rw [hEq]
    simpa using (gap2 x).add_const C

end

end ProofGap.Exercise1661
