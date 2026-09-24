import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2037
noncomputable section

def integrand (x : ℝ) :=
  (Real.sin x ^ 2 - Real.cos x ^ 2) / (Real.sin x ^ 4 + Real.cos x ^ 4)
def firstReduced (x : ℝ) :=
  -Real.cos (2 * x) / (1 - (1 / 2 : ℝ) * Real.sin (2 * x) ^ 2)
def secondReduced (x : ℝ) :=
  -(1 / (2 * Real.sqrt 2)) *
    (2 * Real.cos (2 * x) / (Real.sqrt 2 - Real.sin (2 * x)) +
      2 * Real.cos (2 * x) / (Real.sqrt 2 + Real.sin (2 * x)))
def primitive (x : ℝ) :=
  1 / (2 * Real.sqrt 2) *
    Real.log ((Real.sqrt 2 - Real.sin (2 * x)) /
      (Real.sqrt 2 + Real.sin (2 * x)))
def Family (f : ℝ → ℝ) := {F : ℝ → ℝ | ∀ x, HasDerivAt F (f x) x}
def Translates (p : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ C, ∀ x, F x = p x + C}

private theorem sqrtTwo_sin_denominators_pos (x : ℝ) :
    0 < Real.sqrt 2 - Real.sin x ∧ 0 < Real.sqrt 2 + Real.sin x := by
  constructor
  · exact sub_pos.mpr
      (lt_of_le_of_lt (Real.sin_le_one x) Real.one_lt_sqrt_two)
  · nlinarith [Real.neg_one_le_sin x, Real.one_lt_sqrt_two]

private theorem integrand_eq_firstReduced : integrand = firstReduced := by
  funext x
  have hsc := Real.sin_sq_add_cos_sq x
  have hnum : Real.sin x ^ 2 - Real.cos x ^ 2 = -Real.cos (2 * x) := by
    rw [Real.cos_two_mul]
    nlinarith
  have hden : Real.sin x ^ 4 + Real.cos x ^ 4 =
      1 - (1 / 2 : ℝ) * Real.sin (2 * x) ^ 2 := by
    rw [Real.sin_two_mul]
    calc
      Real.sin x ^ 4 + Real.cos x ^ 4 =
          (Real.sin x ^ 2 + Real.cos x ^ 2) ^ 2 -
            2 * (Real.sin x * Real.cos x) ^ 2 := by ring
      _ = 1 - 2 * (Real.sin x * Real.cos x) ^ 2 := by
        rw [hsc]
        ring
      _ = 1 - (1 / 2 : ℝ) * (2 * Real.sin x * Real.cos x) ^ 2 := by
        ring
  unfold integrand firstReduced
  rw [hnum, hden]

private theorem firstReduced_eq_secondReduced : firstReduced = secondReduced := by
  funext x
  rcases sqrtTwo_sin_denominators_pos (2 * x) with ⟨hminus, hplus⟩
  have hsqrt : Real.sqrt 2 ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hsqrt_pos : 0 < Real.sqrt 2 := by
    nlinarith [Real.one_lt_sqrt_two]
  have hden :
      1 - (1 / 2 : ℝ) * Real.sin (2 * x) ^ 2 =
        (Real.sqrt 2 - Real.sin (2 * x)) *
          (Real.sqrt 2 + Real.sin (2 * x)) / 2 := by
    nlinarith
  unfold firstReduced secondReduced
  rw [hden]
  field_simp [ne_of_gt hminus, ne_of_gt hplus, ne_of_gt hsqrt_pos] <;> ring

private theorem hasDerivAt_primitive (x : ℝ) :
    HasDerivAt primitive (integrand x) x := by
  rw [integrand_eq_firstReduced, firstReduced_eq_secondReduced]
  rcases sqrtTwo_sin_denominators_pos (2 * x) with ⟨hminus, hplus⟩
  have hsin : HasDerivAt (fun y : ℝ => Real.sin (2 * y))
      (2 * Real.cos (2 * x)) x := by
    simpa [Function.comp_def, mul_comm] using
      (Real.hasDerivAt_sin (2 * x)).comp x
        ((hasDerivAt_id x).const_mul 2)
  have hsub : HasDerivAt
      (fun y : ℝ => Real.sqrt 2 - Real.sin (2 * y))
      (-2 * Real.cos (2 * x)) x := by
    simpa using (hasDerivAt_const x (Real.sqrt 2)).sub hsin
  have hadd : HasDerivAt
      (fun y : ℝ => Real.sqrt 2 + Real.sin (2 * y))
      (2 * Real.cos (2 * x)) x := by
    exact hsin.const_add (Real.sqrt 2)
  have hlogSub :=
    (Real.hasDerivAt_log (ne_of_gt hminus)).comp x hsub
  have hlogAdd :=
    (Real.hasDerivAt_log (ne_of_gt hplus)).comp x hadd
  have hlog : HasDerivAt
      (fun y : ℝ =>
        Real.log (Real.sqrt 2 - Real.sin (2 * y)) -
          Real.log (Real.sqrt 2 + Real.sin (2 * y)))
      ((-2 * Real.cos (2 * x)) /
          (Real.sqrt 2 - Real.sin (2 * x)) -
        (2 * Real.cos (2 * x)) /
          (Real.sqrt 2 + Real.sin (2 * x))) x := by
    simpa [div_eq_mul_inv, mul_comm] using hlogSub.sub hlogAdd
  have hder := hlog.const_mul (1 / (2 * Real.sqrt 2))
  convert hder using 1
  · funext y
    unfold primitive
    rcases sqrtTwo_sin_denominators_pos (2 * y) with ⟨hyminus, hyplus⟩
    rw [Real.log_div (ne_of_gt hyminus) (ne_of_gt hyplus)]
  · unfold secondReduced
    ring

theorem gap1 : Family integrand = Family firstReduced := by
  rw [integrand_eq_firstReduced]
theorem gap2 : Family integrand = Family secondReduced := by
  rw [integrand_eq_firstReduced, firstReduced_eq_secondReduced]
theorem gap3 : Family integrand = Translates primitive := by
  ext F
  change (∀ x, HasDerivAt F (integrand x) x) ↔
    ∃ C : ℝ, ∀ x, F x = primitive x + C
  constructor
  · intro hF
    have hzero : ∀ x, HasDerivAt (fun y => F y - primitive y) 0 x := by
      intro x
      simpa using (hF x).sub (hasDerivAt_primitive x)
    have hdiff : Differentiable ℝ (fun y => F y - primitive y) :=
      fun x => (hzero x).differentiableAt
    have hderiv : ∀ x, deriv (fun y => F y - primitive y) x = 0 :=
      fun x => (hzero x).deriv
    refine ⟨F 0 - primitive 0, ?_⟩
    intro x
    have hc := is_const_of_deriv_eq_zero hdiff hderiv x 0
    linarith
  · rintro ⟨C, hC⟩
    have hFC : F = fun x => primitive x + C := funext hC
    rw [hFC]
    intro x
    exact (hasDerivAt_primitive x).add_const C

end
end ProofGap.Exercise2037
