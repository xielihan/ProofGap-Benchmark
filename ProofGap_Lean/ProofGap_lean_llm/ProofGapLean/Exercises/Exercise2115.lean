import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2115
noncomputable section

def asinhForm (x : ℝ) := Real.log (x + Real.sqrt (1 + x ^ 2))
def integrand (x : ℝ) := asinhForm x / (Real.sqrt (1 + x ^ 2)) ^ 3
def differentialForm (x : ℝ) :=
  asinhForm x * deriv (fun y : ℝ => y / Real.sqrt (1 + y ^ 2)) x
def residual (x : ℝ) := x / (1 + x ^ 2)
def primitive (x : ℝ) :=
  x * asinhForm x / Real.sqrt (1 + x ^ 2) -
    Real.log (Real.sqrt (1 + x ^ 2))

def Family (f : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∀ x, HasDerivAt F (f x) x}
def ByPartsFamily :=
  {F : ℝ → ℝ | ∃ A ∈ Family residual, ∀ x,
    F x = x * asinhForm x / Real.sqrt (1 + x ^ 2) - A x}
def Translates (p : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ C : ℝ, ∀ x, F x = p x + C}

private lemma one_add_sq_pos (x : ℝ) : 0 < 1 + x ^ 2 := by
  positivity

private lemma sqrt_one_add_sq_ne (x : ℝ) : Real.sqrt (1 + x ^ 2) ≠ 0 := by
  positivity

private lemma asinh_arg_pos (x : ℝ) : 0 < x + Real.sqrt (1 + x ^ 2) := by
  have hs := Real.sq_sqrt (le_of_lt (one_add_sq_pos x))
  have hn := Real.sqrt_nonneg (1 + x ^ 2)
  nlinarith [sq_nonneg x]

private lemma hasDerivAt_sqrt_one_add_sq (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.sqrt (1 + y ^ 2))
      (x / Real.sqrt (1 + x ^ 2)) x := by
  convert Real.hasDerivAt_sqrt (ne_of_gt (one_add_sq_pos x))
      |>.comp x ((hasDerivAt_const x 1).add ((hasDerivAt_id x).pow 2)) using 1 <;>
    simp only [id_eq] <;>
    field_simp [sqrt_one_add_sq_ne x] <;>
    ring

private lemma hasDerivAt_asinhForm (x : ℝ) :
    HasDerivAt asinhForm (1 / Real.sqrt (1 + x ^ 2)) x := by
  have hinner : HasDerivAt (fun y : ℝ => y + Real.sqrt (1 + y ^ 2))
      (1 + x / Real.sqrt (1 + x ^ 2)) x := by
    simpa only [id_eq] using
      (hasDerivAt_id x).add (hasDerivAt_sqrt_one_add_sq x)
  have hlog := (Real.hasDerivAt_log (ne_of_gt (asinh_arg_pos x))).comp x hinner
  unfold asinhForm
  convert hlog using 1
  field_simp [sqrt_one_add_sq_ne x, ne_of_gt (asinh_arg_pos x)]
  have hs := Real.sq_sqrt (le_of_lt (one_add_sq_pos x))
  nlinarith

private lemma sqrt_fraction (x : ℝ) :
    x / Real.sqrt (1 + x ^ 2) * (1 / Real.sqrt (1 + x ^ 2)) =
      x / (1 + x ^ 2) := by
  calc
    x / Real.sqrt (1 + x ^ 2) * (1 / Real.sqrt (1 + x ^ 2)) =
        x / (Real.sqrt (1 + x ^ 2)) ^ 2 := by
          field_simp [sqrt_one_add_sq_ne x]
    _ = x / (1 + x ^ 2) := by
      rw [Real.sq_sqrt (le_of_lt (one_add_sq_pos x))]

private lemma hasDerivAt_g (x : ℝ) :
    HasDerivAt (fun y : ℝ => y / Real.sqrt (1 + y ^ 2))
      (1 / Real.sqrt (1 + x ^ 2) ^ 3) x := by
  have hquot : HasDerivAt (fun y : ℝ => y / Real.sqrt (1 + y ^ 2))
      ((1 * Real.sqrt (1 + x ^ 2) -
          x * (x / Real.sqrt (1 + x ^ 2))) /
        Real.sqrt (1 + x ^ 2) ^ 2) x := by
    simpa only [id_eq] using
      (hasDerivAt_id x).div (hasDerivAt_sqrt_one_add_sq x)
        (sqrt_one_add_sq_ne x)
  convert hquot using 1
  field_simp [sqrt_one_add_sq_ne x]
  have hs := Real.sq_sqrt (le_of_lt (one_add_sq_pos x))
  nlinarith

private lemma deriv_g (x : ℝ) :
    deriv (fun y : ℝ => y / Real.sqrt (1 + y ^ 2)) x =
      1 / (Real.sqrt (1 + x ^ 2)) ^ 3 := by
  exact (hasDerivAt_g x).deriv

private lemma hasDerivAt_mul_asinh (x : ℝ) :
    HasDerivAt (fun y : ℝ => y * asinhForm y / Real.sqrt (1 + y ^ 2))
      (asinhForm x / Real.sqrt (1 + x ^ 2) ^ 3 + x / (1 + x ^ 2)) x := by
  have hmul := (hasDerivAt_g x).mul (hasDerivAt_asinhForm x)
  rw [sqrt_fraction x] at hmul
  convert hmul using 1
  · funext y
    change y * asinhForm y / Real.sqrt (1 + y ^ 2) =
      (y / Real.sqrt (1 + y ^ 2)) * asinhForm y
    ring
  · ring

private lemma hasDerivAt_log_sqrt (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.log (Real.sqrt (1 + y ^ 2)))
      (x / (1 + x ^ 2)) x := by
  have hlog :=
    (Real.hasDerivAt_log (sqrt_one_add_sq_ne x)).comp x
      (hasDerivAt_sqrt_one_add_sq x)
  have hcoef :
      (Real.sqrt (1 + x ^ 2))⁻¹ *
          (x / Real.sqrt (1 + x ^ 2)) = x / (1 + x ^ 2) := by
    calc
      (Real.sqrt (1 + x ^ 2))⁻¹ *
          (x / Real.sqrt (1 + x ^ 2)) =
          x / Real.sqrt (1 + x ^ 2) *
            (1 / Real.sqrt (1 + x ^ 2)) := by ring
      _ = x / (1 + x ^ 2) := sqrt_fraction x
  rw [hcoef] at hlog
  simpa only [Function.comp_apply] using hlog

private lemma hasDerivAt_primitive (x : ℝ) :
    HasDerivAt primitive (integrand x) x := by
  have h := (hasDerivAt_mul_asinh x).sub (hasDerivAt_log_sqrt x)
  unfold primitive integrand
  convert h using 1
  ring

theorem gap1 : Family integrand = Family differentialForm := by
  ext F
  constructor <;> intro hF x
  · convert hF x using 1
    unfold integrand differentialForm
    rw [deriv_g]
    ring
  · convert hF x using 1
    unfold integrand differentialForm
    rw [deriv_g]
    ring
theorem gap2 : Family differentialForm = ByPartsFamily := by
  ext F
  constructor
  · intro hF
    refine ⟨fun x => x * asinhForm x / Real.sqrt (1 + x ^ 2) - F x, ?_, ?_⟩
    · intro x
      have hprod := (hasDerivAt_mul_asinh x).sub (hF x)
      have hcoef :
          asinhForm x / Real.sqrt (1 + x ^ 2) ^ 3 + x / (1 + x ^ 2) -
              differentialForm x = residual x := by
        unfold differentialForm residual
        rw [deriv_g]
        ring
      rw [hcoef] at hprod
      simpa only using hprod
    · intro x
      ring
  · rintro ⟨A, hA, hF⟩
    intro x
    have hprod := (hasDerivAt_mul_asinh x).sub (hA x)
    have hcoef :
        asinhForm x / Real.sqrt (1 + x ^ 2) ^ 3 + x / (1 + x ^ 2) -
            residual x = differentialForm x := by
      unfold differentialForm residual
      rw [deriv_g]
      ring
    rw [hcoef] at hprod
    have hEq : F = fun y => y * asinhForm y / Real.sqrt (1 + y ^ 2) - A y := by
      funext y
      exact hF y
    rw [hEq]
    simpa only using hprod
theorem gap3 : Family integrand = ByPartsFamily := by
  rw [gap1, gap2]
theorem gap4 : Family integrand = Translates primitive := by
  ext F
  constructor
  · intro hF
    have hp : ∀ x, HasDerivAt primitive (integrand x) x := by
      intro x
      exact hasDerivAt_primitive x
    refine ⟨F 0 - primitive 0, ?_⟩
    intro x
    have hconst : F x - primitive x = F 0 - primitive 0 :=
      is_const_of_deriv_eq_zero
        (fun y => (hF y).differentiableAt.sub (hp y).differentiableAt)
        (fun y => by
          simpa using ((hF y).sub (hp y)).deriv) x 0
    linarith
  · rintro ⟨C, hF⟩
    intro x
    have hp : HasDerivAt primitive (integrand x) x := hasDerivAt_primitive x
    have hEq : F = fun y => primitive y + C := by
      funext y
      exact hF y
    rw [hEq]
    simpa using hp.add_const C

end
end ProofGap.Exercise2115
