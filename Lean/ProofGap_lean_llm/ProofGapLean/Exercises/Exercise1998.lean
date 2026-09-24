import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace ProofGap.Exercise1998

noncomputable section

def branch : Set ℝ := {x | Real.sin x ≠ 0}
def originalIntegrand (x : ℝ) := Real.cos x ^ 4 / Real.sin x ^ 3
def sineSubstitutionIntegrand (x : ℝ) :=
  Real.cos x ^ 3 / Real.sin x ^ 3 * deriv Real.sin x
def reciprocalSquareIntegrand (x : ℝ) :=
  Real.cos x ^ 3 * deriv (fun y : ℝ => 1 / Real.sin y ^ 2) x
def firstResidual (x : ℝ) :=
  Real.cos x ^ 2 * Real.sin x / Real.sin x ^ 2
def secondResidual (x : ℝ) :=
  (1 - Real.sin x ^ 2) / Real.sin x
def primitive (x : ℝ) :=
  -Real.cos x ^ 3 / (2 * Real.sin x ^ 2) -
    3 / 2 * Real.log |Real.tan (x / 2)| -
    3 / 2 * Real.cos x
def Antiderivatives (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def ScaledReciprocalFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ Antiderivatives reciprocalSquareIntegrand,
    ∀ x ∈ branch, F x = -1 / 2 * G x}
def FirstByPartsFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ Antiderivatives firstResidual,
    ∀ x ∈ branch,
      F x = -Real.cos x ^ 3 / (2 * Real.sin x ^ 2) - 3 / 2 * G x}
def SecondByPartsFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ Antiderivatives secondResidual,
    ∀ x ∈ branch,
      F x = -Real.cos x ^ 3 / (2 * Real.sin x ^ 2) - 3 / 2 * G x}
def ComponentwisePrimitiveFamily : Set (ℝ → ℝ) :=
  {F | ∃ K : ℝ → ℝ,
    (∀ x ∈ branch, F x = primitive x + K x) ∧
    (∀ x ∈ branch, HasDerivAt K 0 x)}

private lemma branch_isOpen : IsOpen branch := by
  unfold branch
  exact (isOpen_ne : IsOpen {y : ℝ | y ≠ 0}).preimage Real.continuous_sin

private lemma hasDerivAt_congr_on_branch
    {F G : ℝ → ℝ} {a x : ℝ} (hx : x ∈ branch)
    (hFG : ∀ y ∈ branch, F y = G y) (hG : HasDerivAt G a x) :
    HasDerivAt F a x := by
  apply hG.congr_of_eventuallyEq
  filter_upwards [branch_isOpen.mem_nhds hx] with y hy
  exact hFG y hy

private lemma deriv_sin_eq_cos (x : ℝ) : deriv Real.sin x = Real.cos x := by
  exact (Real.hasDerivAt_sin x).deriv

private lemma sineSubstitution_eq_original (x : ℝ) :
    sineSubstitutionIntegrand x = originalIntegrand x := by
  unfold sineSubstitutionIntegrand originalIntegrand
  rw [deriv_sin_eq_cos]
  ring

private lemma deriv_reciprocal_sine_square (x : ℝ) (hx : x ∈ branch) :
    deriv (fun y : ℝ => 1 / Real.sin y ^ 2) x =
      -2 * Real.cos x / Real.sin x ^ 3 := by
  have hs : Real.sin x ≠ 0 := hx
  have h := ((Real.hasDerivAt_sin x).pow 2).inv (pow_ne_zero 2 hs)
  have hd : deriv (fun y : ℝ => (Real.sin y ^ 2)⁻¹) x =
      -(2 * Real.sin x ^ (2 - 1) * Real.cos x) /
        (Real.sin x ^ 2) ^ 2 := by
    simpa only [Pi.inv_apply, Pi.pow_apply] using h.deriv
  simp only [one_div]
  rw [hd]
  field_simp [hs]
  ring_nf

private lemma reciprocal_eq_sineSubstitution (x : ℝ) (hx : x ∈ branch) :
    reciprocalSquareIntegrand x = -2 * sineSubstitutionIntegrand x := by
  unfold reciprocalSquareIntegrand
  rw [deriv_reciprocal_sine_square x hx]
  rw [sineSubstitution_eq_original]
  unfold originalIntegrand
  ring

private def boundaryTerm (x : ℝ) : ℝ :=
  -Real.cos x ^ 3 / (2 * Real.sin x ^ 2)

private lemma hasDerivAt_boundaryTerm (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt boundaryTerm
      (originalIntegrand x + (3 / 2 : ℝ) * firstResidual x) x := by
  have hs : Real.sin x ≠ 0 := hx
  have hn : HasDerivAt (fun y : ℝ => -Real.cos y ^ 3)
      (3 * Real.cos x ^ 2 * Real.sin x) x := by
    convert ((Real.hasDerivAt_cos x).pow 3).neg using 1 <;> ring
  have hd : HasDerivAt (fun y : ℝ => 2 * Real.sin y ^ 2)
      (4 * Real.sin x * Real.cos x) x := by
    convert ((Real.hasDerivAt_sin x).pow 2).const_mul (2 : ℝ) using 1 <;> ring
  have hq := hn.div hd (mul_ne_zero (by norm_num) (pow_ne_zero 2 hs))
  change HasDerivAt
    (fun y : ℝ => -Real.cos y ^ 3 / (2 * Real.sin y ^ 2))
    (originalIntegrand x + (3 / 2 : ℝ) * firstResidual x) x
  convert hq using 1
  unfold originalIntegrand firstResidual
  field_simp [hs]
  ring_nf

private lemma firstResidual_eq_secondResidual (x : ℝ) (hx : x ∈ branch) :
    firstResidual x = secondResidual x := by
  have hs : Real.sin x ≠ 0 := hx
  unfold firstResidual secondResidual
  field_simp [hs]
  nlinarith [Real.sin_sq_add_cos_sq x]

private lemma hasDerivAt_log_abs_tan_half (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt (fun y : ℝ => Real.log |Real.tan (y / 2)|)
      (1 / Real.sin x) x := by
  have hsx : Real.sin x ≠ 0 := hx
  have hdouble : Real.sin x =
      2 * Real.sin (x / 2) * Real.cos (x / 2) := by
    convert Real.sin_two_mul (x / 2) using 1 <;> ring
  have hs : Real.sin (x / 2) ≠ 0 := by
    intro h
    apply hsx
    rw [hdouble, h]
    ring
  have hc : Real.cos (x / 2) ≠ 0 := by
    intro h
    apply hsx
    rw [hdouble, h]
    ring
  have ht : Real.tan (x / 2) ≠ 0 := by
    rw [Real.tan_eq_sin_div_cos]
    exact div_ne_zero hs hc
  have hhalf : HasDerivAt (fun y : ℝ => y / 2) (1 / 2 : ℝ) x :=
    (hasDerivAt_id x).div_const 2
  have htan0 := (Real.hasDerivAt_tan hc).comp x hhalf
  have htan : HasDerivAt (fun y : ℝ => Real.tan (y / 2))
      (1 / (2 * Real.cos (x / 2) ^ 2)) x := by
    convert htan0 using 1 <;> ring
  have hlog0 := (Real.hasDerivAt_log ht).comp x htan
  have hlog : HasDerivAt (fun y : ℝ => Real.log (Real.tan (y / 2)))
      (1 / Real.sin x) x := by
    convert hlog0 using 1
    rw [hdouble, Real.tan_eq_sin_div_cos]
    field_simp [hs, hc]
  simpa only [Real.log_abs] using hlog

private lemma hasDerivAt_primitive (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt primitive (originalIntegrand x) x := by
  have hs : Real.sin x ≠ 0 := hx
  have hres0 := (hasDerivAt_log_abs_tan_half x hx).add
    (Real.hasDerivAt_cos x)
  have hres : HasDerivAt
      (fun y : ℝ => Real.log |Real.tan (y / 2)| + Real.cos y)
      (secondResidual x) x := by
    convert hres0 using 1
    unfold secondResidual
    field_simp [hs]
    ring
  have h := (hasDerivAt_boundaryTerm x hx).sub
    (hres.const_mul (3 / 2 : ℝ))
  convert h using 1
  · funext y
    simp only [Pi.sub_apply]
    unfold primitive boundaryTerm
    ring
  · rw [firstResidual_eq_secondResidual x hx]
    ring

theorem gap1 :
    Antiderivatives originalIntegrand =
      Antiderivatives sineSubstitutionIntegrand := by
  ext F
  simp only [Antiderivatives, Set.mem_setOf_eq]
  constructor
  · intro h x hx
    simpa only [sineSubstitution_eq_original x] using h x hx
  · intro h x hx
    simpa only [sineSubstitution_eq_original x] using h x hx
theorem gap2 :
    Antiderivatives sineSubstitutionIntegrand =
      ScaledReciprocalFamily := by
  ext F
  simp only [Antiderivatives, ScaledReciprocalFamily, Set.mem_setOf_eq]
  constructor
  · intro hF
    refine ⟨fun y => (-2 : ℝ) * F y, ?_, ?_⟩
    · intro x hx
      have h := (hF x hx).const_mul (-2 : ℝ)
      simpa only [reciprocal_eq_sineSubstitution x hx] using h
    · intro x hx
      ring
  · rintro ⟨G, hG, hFG⟩ x hx
    have hs : HasDerivAt (fun y => (-1 / 2 : ℝ) * G y)
        (sineSubstitutionIntegrand x) x := by
      have h := (hG x hx).const_mul (-1 / 2 : ℝ)
      convert h using 1
      rw [reciprocal_eq_sineSubstitution x hx]
      ring
    exact hasDerivAt_congr_on_branch hx hFG hs
theorem gap3 :
    Antiderivatives originalIntegrand =
      ScaledReciprocalFamily := by
  rw [gap1, gap2]
theorem gap4 :
    Antiderivatives originalIntegrand =
      FirstByPartsFamily := by
  ext F
  simp only [Antiderivatives, FirstByPartsFamily, Set.mem_setOf_eq]
  constructor
  · intro hF
    refine ⟨fun y => (2 / 3 : ℝ) * (boundaryTerm y - F y), ?_, ?_⟩
    · intro x hx
      have h := ((hasDerivAt_boundaryTerm x hx).sub (hF x hx)).const_mul (2 / 3 : ℝ)
      convert h using 1
      ring
    · intro x hx
      unfold boundaryTerm
      ring
  · rintro ⟨G, hG, hFG⟩ x hx
    have hs : HasDerivAt
        (fun y => boundaryTerm y - (3 / 2 : ℝ) * G y)
        (originalIntegrand x) x := by
      have h := (hasDerivAt_boundaryTerm x hx).sub
        ((hG x hx).const_mul (3 / 2 : ℝ))
      convert h using 1
      ring
    apply hasDerivAt_congr_on_branch hx ?_ hs
    intro y hy
    simpa only [boundaryTerm] using hFG y hy
theorem gap5 :
    FirstByPartsFamily = SecondByPartsFamily := by
  have hanti : Antiderivatives firstResidual = Antiderivatives secondResidual := by
    ext G
    simp only [Antiderivatives, Set.mem_setOf_eq]
    constructor
    · intro h x hx
      simpa only [firstResidual_eq_secondResidual x hx] using h x hx
    · intro h x hx
      simpa only [firstResidual_eq_secondResidual x hx] using h x hx
  unfold FirstByPartsFamily SecondByPartsFamily
  rw [hanti]
theorem gap6 :
    Antiderivatives originalIntegrand =
      SecondByPartsFamily := by
  rw [gap4, gap5]
theorem gap7 :
    Antiderivatives originalIntegrand =
      ComponentwisePrimitiveFamily := by
  ext F
  simp only [Antiderivatives, ComponentwisePrimitiveFamily, Set.mem_setOf_eq]
  constructor
  · intro hF
    refine ⟨fun y => F y - primitive y, ?_, ?_⟩
    · intro x hx
      ring
    · intro x hx
      have h := (hF x hx).sub (hasDerivAt_primitive x hx)
      convert h using 1
      ring
  · rintro ⟨K, hFK, hK⟩ x hx
    have hs : HasDerivAt (fun y => primitive y + K y)
        (originalIntegrand x) x := by
      have h := (hasDerivAt_primitive x hx).add (hK x hx)
      convert h using 1
      ring
    exact hasDerivAt_congr_on_branch hx hFK hs

end
end ProofGap.Exercise1998
