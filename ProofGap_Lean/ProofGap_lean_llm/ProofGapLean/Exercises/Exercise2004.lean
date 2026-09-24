import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise2004

noncomputable section

def branch : Set ℝ := {x | Real.cos x ≠ 0}
def sec (x : ℝ) := 1 / Real.cos x
def originalIntegrand (x : ℝ) := Real.tan x ^ 5
def rewrittenIntegrand (x : ℝ) :=
  Real.tan x * (sec x ^ 2 - 1) ^ 2
def firstPart (x : ℝ) := sec x ^ 4 * Real.tan x
def secondPart (x : ℝ) := sec x ^ 2 * Real.tan x
def thirdPart (x : ℝ) := Real.tan x
def substitution₁ (x : ℝ) := sec x ^ 3 * deriv sec x
def substitution₂ (x : ℝ) := sec x * deriv sec x
def logarithmicPart (x : ℝ) := deriv Real.cos x / Real.cos x
def primitiveSec (x : ℝ) :=
  1 / 4 * sec x ^ 4 - sec x ^ 2 - Real.log |Real.cos x|
def primitiveTan (x : ℝ) :=
  1 / 4 * Real.tan x ^ 4 - 1 / 2 * Real.tan x ^ 2 -
    Real.log |Real.cos x|
def Antiderivatives (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def ThreeTermFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ Antiderivatives firstPart,
    ∃ H ∈ Antiderivatives secondPart,
    ∃ K ∈ Antiderivatives thirdPart,
      ∀ x ∈ branch, F x = G x - 2 * H x + K x}
def SubstitutionFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ Antiderivatives substitution₁,
    ∃ H ∈ Antiderivatives substitution₂,
    ∃ K ∈ Antiderivatives logarithmicPart,
      ∀ x ∈ branch, F x = G x - 2 * H x - K x}
def ComponentwisePrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ K : ℝ → ℝ,
    (∀ x ∈ branch, F x = p x + K x) ∧
    (∀ x ∈ branch, HasDerivAt K 0 x)}

private lemma branch_isOpen : IsOpen branch := by
  have h : branch = Real.cos ⁻¹' ({0} : Set ℝ)ᶜ := by
    ext x
    simp [branch]
  rw [h]
  exact
    (isClosed_singleton : IsClosed ({0} : Set ℝ)).isOpen_compl.preimage
      Real.continuous_cos

private lemma hasDerivAt_of_eqOn_branch
    {F G : ℝ → ℝ} {d x : ℝ} (hx : x ∈ branch)
    (hG : HasDerivAt G d x)
    (hEq : ∀ y ∈ branch, F y = G y) : HasDerivAt F d x := by
  apply hG.congr_of_eventuallyEq
  exact Filter.Eventually.mono (branch_isOpen.mem_nhds hx) fun y hy =>
    hEq y hy

private lemma sec_sq_sub_one_eq_tan_sq (x : ℝ) (hx : x ∈ branch) :
    sec x ^ 2 - 1 = Real.tan x ^ 2 := by
  have hcos : Real.cos x ≠ 0 := hx
  rw [sec, Real.tan_eq_sin_div_cos]
  field_simp [hcos]
  nlinarith [Real.sin_sq_add_cos_sq x]

private lemma original_eq_rewritten_at (x : ℝ) (hx : x ∈ branch) :
    originalIntegrand x = rewrittenIntegrand x := by
  simp only [originalIntegrand, rewrittenIntegrand]
  rw [sec_sq_sub_one_eq_tan_sq x hx]
  ring

private lemma rewritten_as_three_at (x : ℝ) :
    rewrittenIntegrand x =
      firstPart x - 2 * secondPart x + thirdPart x := by
  simp only [rewrittenIntegrand, firstPart, secondPart, thirdPart]
  ring

private lemma antiderivatives_congr_on_branch {f g : ℝ → ℝ}
    (hfg : ∀ x ∈ branch, f x = g x) :
    Antiderivatives f = Antiderivatives g := by
  apply Set.ext
  intro F
  change
    (∀ x ∈ branch, HasDerivAt F (f x) x) ↔
      ∀ x ∈ branch, HasDerivAt F (g x) x
  constructor
  · intro h x hx
    simpa only [hfg x hx] using h x hx
  · intro h x hx
    simpa only [hfg x hx] using h x hx

private lemma sec_hasDerivAt (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt sec (sec x * Real.tan x) x := by
  have hcos : Real.cos x ≠ 0 := hx
  have h :
      HasDerivAt (fun y => (Real.cos y)⁻¹)
        (Real.sin x / Real.cos x ^ 2) x := by
    simpa only [neg_neg] using (Real.hasDerivAt_cos x).inv hcos
  have heq :
      sec x * Real.tan x = Real.sin x / Real.cos x ^ 2 := by
    simp only [sec, Real.tan_eq_sin_div_cos]
    field_simp [hcos] <;> ring
  have hsec : sec = (fun y : ℝ => (Real.cos y)⁻¹) := by
    funext y
    simp only [sec, one_div]
  rw [heq, hsec]
  exact h

private lemma first_primitive_hasDerivAt (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt (fun y => (1 / 4 : ℝ) * sec y ^ 4) (firstPart x) x := by
  have hs := sec_hasDerivAt x hx
  convert (hs.pow 4).const_mul (1 / 4 : ℝ) using 1 <;>
    simp [firstPart] <;> ring

private lemma second_primitive_hasDerivAt (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt (fun y => (1 / 2 : ℝ) * sec y ^ 2) (secondPart x) x := by
  have hs := sec_hasDerivAt x hx
  convert (hs.pow 2).const_mul (1 / 2 : ℝ) using 1 <;>
    simp [secondPart] <;> ring

private lemma log_abs_cos_hasDerivAt (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt (fun y => Real.log |Real.cos y|) (-Real.tan x) x := by
  have hcos : Real.cos x ≠ 0 := hx
  have h := (Real.hasDerivAt_log hcos).comp x (Real.hasDerivAt_cos x)
  convert h using 1
  · funext y
    simp only [Real.log_abs, Function.comp_apply]
  · rw [Real.tan_eq_sin_div_cos]
    field_simp [hcos]

private lemma substitution_one_eq_first_at (x : ℝ) (hx : x ∈ branch) :
    substitution₁ x = firstPart x := by
  have hd := (sec_hasDerivAt x hx).deriv
  simp only [substitution₁, firstPart]
  rw [hd]
  ring

private lemma substitution_two_eq_second_at (x : ℝ) (hx : x ∈ branch) :
    substitution₂ x = secondPart x := by
  have hd := (sec_hasDerivAt x hx).deriv
  simp only [substitution₂, secondPart]
  rw [hd]
  ring

private lemma logarithmic_eq_neg_third_at (x : ℝ) (hx : x ∈ branch) :
    logarithmicPart x = -thirdPart x := by
  have hcos : Real.cos x ≠ 0 := hx
  have hd := (Real.hasDerivAt_cos x).deriv
  simp only [logarithmicPart, thirdPart]
  rw [hd, Real.tan_eq_sin_div_cos]
  field_simp [hcos]

private lemma primitiveSec_hasDerivAt (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt primitiveSec (originalIntegrand x) x := by
  have h1 := first_primitive_hasDerivAt x hx
  have h2 := second_primitive_hasDerivAt x hx
  have h3 := (log_abs_cos_hasDerivAt x hx).neg
  have h := (h1.sub (h2.const_mul 2)).add h3
  convert h using 1
  · funext y
    change
      (1 / 4 * sec y ^ 4 - sec y ^ 2 - Real.log |Real.cos y|) =
        (1 / 4 * sec y ^ 4 - 2 * (1 / 2 * sec y ^ 2)) +
          -Real.log |Real.cos y|
    ring
  · rw [original_eq_rewritten_at x hx, rewritten_as_three_at x]
    simp only [thirdPart, neg_neg]

private lemma primitiveTan_eq_primitiveSec_add_const (x : ℝ) (hx : x ∈ branch) :
    primitiveTan x = primitiveSec x + (3 / 4 : ℝ) := by
  have h2 : sec x ^ 2 = Real.tan x ^ 2 + 1 := by
    nlinarith [sec_sq_sub_one_eq_tan_sq x hx]
  have h4 : sec x ^ 4 = (Real.tan x ^ 2 + 1) ^ 2 := by
    calc
      sec x ^ 4 = (sec x ^ 2) ^ 2 := by ring
      _ = (Real.tan x ^ 2 + 1) ^ 2 := by rw [h2]
  simp only [primitiveTan, primitiveSec]
  rw [h2, h4]
  ring

private lemma primitiveTan_hasDerivAt (x : ℝ) (hx : x ∈ branch) :
    HasDerivAt primitiveTan (originalIntegrand x) x := by
  have h := (primitiveSec_hasDerivAt x hx).add_const (3 / 4 : ℝ)
  exact hasDerivAt_of_eqOn_branch hx h primitiveTan_eq_primitiveSec_add_const

private lemma antiderivatives_eq_componentwise {f p : ℝ → ℝ}
    (hp : ∀ x ∈ branch, HasDerivAt p (f x) x) :
    Antiderivatives f = ComponentwisePrimitiveFamily p := by
  apply Set.ext
  intro F
  change
    (∀ x ∈ branch, HasDerivAt F (f x) x) ↔
      ∃ K : ℝ → ℝ,
        (∀ x ∈ branch, F x = p x + K x) ∧
          ∀ x ∈ branch, HasDerivAt K 0 x
  constructor
  · intro hF
    refine ⟨fun y => F y - p y, ?_, ?_⟩
    · intro x hx
      ring
    · intro x hx
      convert (hF x hx).sub (hp x hx) using 1
      ring
  · rintro ⟨K, hEq, hK⟩
    intro x hx
    have h := (hp x hx).add (hK x hx)
    have h' : HasDerivAt (fun y => p y + K y) (f x) x := by
      convert h using 1
      ring
    exact hasDerivAt_of_eqOn_branch hx h' hEq

theorem gap1 :
    Antiderivatives originalIntegrand =
      Antiderivatives rewrittenIntegrand := by
  exact antiderivatives_congr_on_branch original_eq_rewritten_at
theorem gap2 :
    Antiderivatives rewrittenIntegrand = ThreeTermFamily := by
  apply Set.ext
  intro F
  change
    (∀ x ∈ branch, HasDerivAt F (rewrittenIntegrand x) x) ↔
      ∃ G, (∀ x ∈ branch, HasDerivAt G (firstPart x) x) ∧
        ∃ H, (∀ x ∈ branch, HasDerivAt H (secondPart x) x) ∧
          ∃ K, (∀ x ∈ branch, HasDerivAt K (thirdPart x) x) ∧
            ∀ x ∈ branch, F x = G x - 2 * H x + K x
  constructor
  · intro hF
    let G : ℝ → ℝ := fun y => (1 / 4 : ℝ) * sec y ^ 4
    let H : ℝ → ℝ := fun y => (1 / 2 : ℝ) * sec y ^ 2
    let K : ℝ → ℝ := fun y => F y - G y + 2 * H y
    have hG : ∀ x ∈ branch, HasDerivAt G (firstPart x) x := by
      intro x hx
      exact first_primitive_hasDerivAt x hx
    have hH : ∀ x ∈ branch, HasDerivAt H (secondPart x) x := by
      intro x hx
      exact second_primitive_hasDerivAt x hx
    have hK : ∀ x ∈ branch, HasDerivAt K (thirdPart x) x := by
      intro x hx
      dsimp only [K]
      have h := ((hF x hx).sub (hG x hx)).add ((hH x hx).const_mul 2)
      convert h using 1
      rw [rewritten_as_three_at x]
      ring
    refine ⟨G, hG, H, hH, K, hK, ?_⟩
    intro x hx
    dsimp only [K]
    ring
  · rintro ⟨G, hG, H, hH, K, hK, hEq⟩
    intro x hx
    have h := ((hG x hx).sub ((hH x hx).const_mul 2)).add (hK x hx)
    have h' :
        HasDerivAt (fun y => G y - 2 * H y + K y)
          (firstPart x - 2 * secondPart x + thirdPart x) x := by
      convert h using 1 <;> ring
    rw [rewritten_as_three_at x]
    exact hasDerivAt_of_eqOn_branch hx h' hEq
theorem gap3 :
    Antiderivatives originalIntegrand = ThreeTermFamily := by
  calc
    Antiderivatives originalIntegrand = Antiderivatives rewrittenIntegrand := gap1
    _ = ThreeTermFamily := gap2
theorem gap4 :
    Antiderivatives originalIntegrand = SubstitutionFamily := by
  rw [gap3]
  apply Set.ext
  intro F
  change
    (∃ G, G ∈ Antiderivatives firstPart ∧
      ∃ H, H ∈ Antiderivatives secondPart ∧
        ∃ K, K ∈ Antiderivatives thirdPart ∧
          ∀ x ∈ branch, F x = G x - 2 * H x + K x) ↔
    (∃ G, G ∈ Antiderivatives substitution₁ ∧
      ∃ H, H ∈ Antiderivatives substitution₂ ∧
        ∃ K, K ∈ Antiderivatives logarithmicPart ∧
          ∀ x ∈ branch, F x = G x - 2 * H x - K x)
  constructor
  · rintro ⟨G, hG, H, hH, K, hK, hEq⟩
    have hG' : G ∈ Antiderivatives substitution₁ := by
      intro x hx
      simpa only [substitution_one_eq_first_at x hx] using hG x hx
    have hH' : H ∈ Antiderivatives substitution₂ := by
      intro x hx
      simpa only [substitution_two_eq_second_at x hx] using hH x hx
    have hK' : (fun y => -K y) ∈ Antiderivatives logarithmicPart := by
      intro x hx
      have h := (hK x hx).neg
      convert h using 1
      rw [logarithmic_eq_neg_third_at x hx]
    refine ⟨G, hG', H, hH', fun y => -K y, hK', ?_⟩
    intro x hx
    rw [hEq x hx]
    ring
  · rintro ⟨G, hG, H, hH, K, hK, hEq⟩
    have hG' : G ∈ Antiderivatives firstPart := by
      intro x hx
      simpa only [substitution_one_eq_first_at x hx] using hG x hx
    have hH' : H ∈ Antiderivatives secondPart := by
      intro x hx
      simpa only [substitution_two_eq_second_at x hx] using hH x hx
    have hK' : (fun y => -K y) ∈ Antiderivatives thirdPart := by
      intro x hx
      have h := (hK x hx).neg
      convert h using 1
      rw [logarithmic_eq_neg_third_at x hx]
      ring
    refine ⟨G, hG', H, hH', fun y => -K y, hK', ?_⟩
    intro x hx
    rw [hEq x hx]
    ring
theorem gap5 :
    SubstitutionFamily =
      ComponentwisePrimitiveFamily primitiveSec := by
  rw [← gap4]
  exact antiderivatives_eq_componentwise primitiveSec_hasDerivAt
theorem gap6 :
    Antiderivatives originalIntegrand =
      ComponentwisePrimitiveFamily primitiveSec := by
  exact antiderivatives_eq_componentwise primitiveSec_hasDerivAt
theorem gap7 :
    Antiderivatives originalIntegrand =
      ComponentwisePrimitiveFamily primitiveTan := by
  exact antiderivatives_eq_componentwise primitiveTan_hasDerivAt

end
end ProofGap.Exercise2004
