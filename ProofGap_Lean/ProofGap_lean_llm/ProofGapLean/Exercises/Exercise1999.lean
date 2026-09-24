import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1999

noncomputable section

def branch : Set ℝ := {x | Real.sin x ≠ 0}
def cot (x : ℝ) := Real.cos x / Real.sin x
def originalIntegrand (x : ℝ) := 1 / Real.sin x ^ 3
def cotSubstitutionIntegrand (x : ℝ) :=
  1 / Real.sin x * deriv cot x
def firstResidual (x : ℝ) :=
  cot x * (Real.cos x / Real.sin x ^ 2)
def secondResidual (x : ℝ) :=
  (1 - Real.sin x ^ 2) / Real.sin x ^ 3
def primitive (x : ℝ) :=
  -Real.cos x / (2 * Real.sin x ^ 2) +
    1 / 2 * Real.log |Real.tan (x / 2)|
def Antiderivatives (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def NegatedFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ Antiderivatives cotSubstitutionIntegrand,
    ∀ x ∈ branch, F x = -G x}
def FirstByPartsFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ Antiderivatives firstResidual,
    ∀ x ∈ branch, F x = -cot x / Real.sin x - G x}
def SecondByPartsFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ Antiderivatives secondResidual,
    ∀ x ∈ branch, F x = -Real.cos x / Real.sin x ^ 2 - G x}
def RecurrenceFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ Antiderivatives originalIntegrand,
    ∀ x ∈ branch,
      F x =
        -Real.cos x / Real.sin x ^ 2 - G x +
          Real.log |Real.tan (x / 2)|}
def ComponentwisePrimitiveFamily : Set (ℝ → ℝ) :=
  {F | ∃ K : ℝ → ℝ,
    (∀ x ∈ branch, F x = primitive x + K x) ∧
    (∀ x ∈ branch, HasDerivAt K 0 x)}

private lemma hasDerivAt_of_eq_on_branch
    {f g : ℝ → ℝ} {f' x : ℝ} (hx : x ∈ branch)
    (hfg : ∀ y ∈ branch, f y = g y)
    (hg : HasDerivAt g f' x) : HasDerivAt f f' x := by
  apply hg.congr_of_eventuallyEq
  filter_upwards [Real.continuous_sin.continuousAt.eventually_ne hx] with y hy
  exact hfg y hy

private lemma hasDerivAt_cot (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt cot (-1 / Real.sin x ^ 2) x := by
  have hs : Real.sin x ≠ 0 := hx
  unfold cot
  apply ((Real.hasDerivAt_cos x).div (Real.hasDerivAt_sin x) hs).congr_deriv
  field_simp [hs]
  nlinarith [Real.sin_sq_add_cos_sq x]

private lemma cotSubstitutionIntegrand_eq_neg_original
    (x : ℝ) (hx : x ∈ branch) :
    cotSubstitutionIntegrand x = -originalIntegrand x := by
  have hs : Real.sin x ≠ 0 := hx
  unfold cotSubstitutionIntegrand originalIntegrand
  rw [(hasDerivAt_cot x hx).deriv]
  field_simp [hs]

private lemma firstResidual_eq_secondResidual
    (x : ℝ) (hx : x ∈ branch) :
    firstResidual x = secondResidual x := by
  have hs : Real.sin x ≠ 0 := hx
  have hcos : Real.cos x ^ 2 = 1 - Real.sin x ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq x]
  unfold firstResidual secondResidual cot
  calc
    (Real.cos x / Real.sin x) *
        (Real.cos x / Real.sin x ^ 2) =
        Real.cos x ^ 2 / Real.sin x ^ 3 := by
          field_simp [hs]
    _ = (1 - Real.sin x ^ 2) / Real.sin x ^ 3 := by rw [hcos]

private lemma firstBoundary_eq_secondBoundary
    (x : ℝ) (hx : x ∈ branch) :
    -cot x / Real.sin x = -Real.cos x / Real.sin x ^ 2 := by
  have hs : Real.sin x ≠ 0 := hx
  simp only [cot, Pi.neg_apply]
  field_simp [hs]

private lemma hasDerivAt_firstBoundary (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt (fun y => -cot y / Real.sin y)
      (originalIntegrand x + firstResidual x) x := by
  have hs : Real.sin x ≠ 0 := hx
  apply ((hasDerivAt_cot x hx).neg.div (Real.hasDerivAt_sin x) hs).congr_deriv
  simp only [originalIntegrand, firstResidual, cot, Pi.neg_apply]
  field_simp [hs]
  nlinarith [Real.sin_sq_add_cos_sq x]

private lemma hasDerivAt_secondBoundary (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt (fun y => -Real.cos y / Real.sin y ^ 2)
      (originalIntegrand x + secondResidual x) x := by
  have h := hasDerivAt_firstBoundary x hx
  rw [firstResidual_eq_secondResidual x hx] at h
  apply hasDerivAt_of_eq_on_branch
    (f := fun y => -Real.cos y / Real.sin y ^ 2)
    (g := fun y => -cot y / Real.sin y) hx
  · intro y hy
    exact (firstBoundary_eq_secondBoundary y hy).symm
  · exact h

private lemma mem_firstByParts_iff_original (F : ℝ → ℝ) :
    F ∈ FirstByPartsFamily ↔ F ∈ Antiderivatives originalIntegrand := by
  constructor
  · rintro ⟨G, hG, hFG⟩
    intro x hx
    have hExpr := (hasDerivAt_firstBoundary x hx).sub (hG x hx)
    apply hasDerivAt_of_eq_on_branch
      (f := F) (g := fun y => -cot y / Real.sin y - G y) hx hFG
    exact hExpr.congr_deriv (by ring)
  · intro hF
    refine ⟨fun y => -cot y / Real.sin y - F y, ?_, ?_⟩
    · intro x hx
      exact ((hasDerivAt_firstBoundary x hx).sub (hF x hx)).congr_deriv
        (by ring)
    · intro x hx
      ring

private lemma sin_half_ne_zero (x : ℝ) (hx : x ∈ branch) :
    Real.sin (x / 2) ≠ 0 := by
  have hdouble : Real.sin x =
      2 * Real.sin (x / 2) * Real.cos (x / 2) := by
    convert Real.sin_two_mul (x / 2) using 1 <;> ring
  intro h
  apply hx
  rw [hdouble, h]
  ring

private lemma cos_half_ne_zero (x : ℝ) (hx : x ∈ branch) :
    Real.cos (x / 2) ≠ 0 := by
  have hdouble : Real.sin x =
      2 * Real.sin (x / 2) * Real.cos (x / 2) := by
    convert Real.sin_two_mul (x / 2) using 1 <;> ring
  intro h
  apply hx
  rw [hdouble, h]
  ring

private lemma tan_half_ne_zero (x : ℝ) (hx : x ∈ branch) :
    Real.tan (x / 2) ≠ 0 := by
  rw [Real.tan_eq_sin_div_cos]
  exact div_ne_zero (sin_half_ne_zero x hx) (cos_half_ne_zero x hx)

private lemma hasDerivAt_logTanHalf (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt (fun y => Real.log |Real.tan (y / 2)|)
      (1 / Real.sin x) x := by
  have hs := sin_half_ne_zero x hx
  have hc := cos_half_ne_zero x hx
  have ht0 := (Real.hasDerivAt_tan hc).comp x
    ((hasDerivAt_id x).div_const 2)
  have ht : HasDerivAt (fun y : ℝ => Real.tan (y / 2))
      ((1 / Real.cos (x / 2) ^ 2) * (1 / 2)) x := by
    simpa only [Function.comp_apply] using ht0.congr_deriv (by ring)
  have hlog := (Real.hasDerivAt_log (tan_half_ne_zero x hx)).comp x ht
  have hlogabs : HasDerivAt (fun y => Real.log |Real.tan (y / 2)|)
      ((Real.tan (x / 2))⁻¹ *
        ((1 / Real.cos (x / 2) ^ 2) * (1 / 2))) x := by
    simpa only [Function.comp_apply, Real.log_abs] using hlog
  have hdouble : Real.sin x =
      2 * Real.sin (x / 2) * Real.cos (x / 2) := by
    convert Real.sin_two_mul (x / 2) using 1 <;> ring
  apply hlogabs.congr_deriv
  rw [Real.tan_eq_sin_div_cos, hdouble]
  field_simp [hs, hc]

private lemma hasDerivAt_recurrenceTerm (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt
      (fun y => -Real.cos y / Real.sin y ^ 2 +
        Real.log |Real.tan (y / 2)|)
      (2 * originalIntegrand x) x := by
  have hs : Real.sin x ≠ 0 := hx
  apply ((hasDerivAt_secondBoundary x hx).add
    (hasDerivAt_logTanHalf x hx)).congr_deriv
  unfold originalIntegrand secondResidual
  field_simp [hs]
  ring

private lemma mem_recurrence_iff_original (F : ℝ → ℝ) :
    F ∈ RecurrenceFamily ↔ F ∈ Antiderivatives originalIntegrand := by
  constructor
  · rintro ⟨G, hG, hFG⟩
    intro x hx
    have hExpr := (hasDerivAt_recurrenceTerm x hx).sub (hG x hx)
    apply hasDerivAt_of_eq_on_branch
      (f := F)
      (g := fun y =>
        (-Real.cos y / Real.sin y ^ 2 +
          Real.log |Real.tan (y / 2)|) - G y) hx
    · intro y hy
      calc
        F y = -Real.cos y / Real.sin y ^ 2 - G y +
            Real.log |Real.tan (y / 2)| := hFG y hy
        _ = (-Real.cos y / Real.sin y ^ 2 +
            Real.log |Real.tan (y / 2)|) - G y := by ring
    · exact hExpr.congr_deriv (by ring)
  · intro hF
    refine ⟨fun y =>
      (-Real.cos y / Real.sin y ^ 2 +
        Real.log |Real.tan (y / 2)|) - F y, ?_, ?_⟩
    · intro x hx
      exact ((hasDerivAt_recurrenceTerm x hx).sub (hF x hx)).congr_deriv
        (by ring)
    · intro x hx
      ring

private lemma hasDerivAt_primitive (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt primitive (originalIntegrand x) x := by
  have hscaled : HasDerivAt
      (fun y => (1 / 2 : ℝ) *
        (-Real.cos y / Real.sin y ^ 2 +
          Real.log |Real.tan (y / 2)|))
      (originalIntegrand x) x := by
    apply ((hasDerivAt_recurrenceTerm x hx).const_mul (1 / 2 : ℝ)).congr_deriv
    ring
  apply hasDerivAt_of_eq_on_branch
    (f := primitive)
    (g := fun y => (1 / 2 : ℝ) *
      (-Real.cos y / Real.sin y ^ 2 +
        Real.log |Real.tan (y / 2)|)) hx
  · intro y hy
    have hsy : Real.sin y ≠ 0 := hy
    unfold primitive
    field_simp [hsy]
  · exact hscaled

private lemma mem_componentwise_iff_original (F : ℝ → ℝ) :
    F ∈ ComponentwisePrimitiveFamily ↔
      F ∈ Antiderivatives originalIntegrand := by
  constructor
  · rintro ⟨K, hFK, hK⟩
    intro x hx
    apply hasDerivAt_of_eq_on_branch
      (f := F) (g := fun y => primitive y + K y) hx hFK
    exact ((hasDerivAt_primitive x hx).add (hK x hx)).congr_deriv
      (by ring)
  · intro hF
    refine ⟨fun y => F y - primitive y, ?_, ?_⟩
    · intro x hx
      ring
    · intro x hx
      exact ((hF x hx).sub (hasDerivAt_primitive x hx)).congr_deriv
        (by ring)

theorem gap1 :
    Antiderivatives originalIntegrand = NegatedFamily := by
  ext F
  constructor
  · intro hF
    refine ⟨fun y => -F y, ?_, ?_⟩
    · intro x hx
      rw [cotSubstitutionIntegrand_eq_neg_original x hx]
      exact (hF x hx).neg
    · intro x hx
      ring
  · rintro ⟨G, hG, hFG⟩
    intro x hx
    apply hasDerivAt_of_eq_on_branch (f := F) (g := fun y => -G y) hx hFG
    have h := (hG x hx).neg
    rw [cotSubstitutionIntegrand_eq_neg_original x hx] at h
    simpa using h
theorem gap2 :
    NegatedFamily = FirstByPartsFamily := by
  calc
    NegatedFamily = Antiderivatives originalIntegrand := gap1.symm
    _ = FirstByPartsFamily :=
      Set.ext fun F => (mem_firstByParts_iff_original F).symm
theorem gap3 :
    FirstByPartsFamily = SecondByPartsFamily := by
  ext F
  constructor
  · rintro ⟨G, hG, hFG⟩
    refine ⟨G, ?_, ?_⟩
    · intro x hx
      simpa only [firstResidual_eq_secondResidual x hx] using hG x hx
    · intro x hx
      calc
        F x = -cot x / Real.sin x - G x := hFG x hx
        _ = -Real.cos x / Real.sin x ^ 2 - G x := by
          rw [firstBoundary_eq_secondBoundary x hx]
  · rintro ⟨G, hG, hFG⟩
    refine ⟨G, ?_, ?_⟩
    · intro x hx
      simpa only [firstResidual_eq_secondResidual x hx] using hG x hx
    · intro x hx
      calc
        F x = -Real.cos x / Real.sin x ^ 2 - G x := hFG x hx
        _ = -cot x / Real.sin x - G x := by
          rw [firstBoundary_eq_secondBoundary x hx]
theorem gap4 :
    Antiderivatives originalIntegrand = SecondByPartsFamily := by
  calc
    Antiderivatives originalIntegrand = NegatedFamily := gap1
    _ = FirstByPartsFamily := gap2
    _ = SecondByPartsFamily := gap3
theorem gap5 :
    Antiderivatives originalIntegrand = RecurrenceFamily := by
  exact Set.ext fun F => (mem_recurrence_iff_original F).symm
theorem gap6 :
    Antiderivatives originalIntegrand =
      ComponentwisePrimitiveFamily := by
  exact Set.ext fun F => (mem_componentwise_iff_original F).symm

end
end ProofGap.Exercise1999
