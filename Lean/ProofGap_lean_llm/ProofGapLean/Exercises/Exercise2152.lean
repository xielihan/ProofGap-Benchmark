import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2152

noncomputable section

def Antiderivatives (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x, HasDerivAt F (f x) x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x, F x = p x + C}
def s (x : ℝ) := Real.sqrt (1 + x ^ 2)
def integrand (x : ℝ) := x * Real.arctan x / s x
def substitutionIntegrand (x : ℝ) :=
  Real.arctan x * deriv s x
def ByPartsFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ Antiderivatives (fun x => 1 / s x),
    ∀ x, F x = s x * Real.arctan x - G x}
def primitive (x : ℝ) :=
  s x * Real.arctan x - Real.log (x + s x)

private lemma s_pos (x : ℝ) : 0 < s x := by
  unfold s
  positivity

private lemma s_ne (x : ℝ) : s x ≠ 0 :=
  ne_of_gt (s_pos x)

private lemma s_sq (x : ℝ) : s x ^ 2 = 1 + x ^ 2 := by
  unfold s
  apply Real.sq_sqrt
  positivity

private lemma hasDerivAt_s (x : ℝ) : HasDerivAt s (x / s x) x := by
  have hinner :
      HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * x) x := by
    convert
      (hasDerivAt_const x (1 : ℝ)).add ((hasDerivAt_id x).pow 2) using 1 <;>
      norm_num <;> ring
  have harg : 1 + x ^ 2 ≠ 0 := by positivity
  have hsqrt : Real.sqrt (1 + x ^ 2) ≠ 0 := by positivity
  unfold s
  convert (Real.hasDerivAt_sqrt harg).comp x hinner using 1
  field_simp [hsqrt]

private lemma integrand_eq_substitution (x : ℝ) :
    integrand x = substitutionIntegrand x := by
  unfold integrand substitutionIntegrand
  rw [(hasDerivAt_s x).deriv]
  ring

private lemma s_div_one_add_sq (x : ℝ) :
    s x * (1 / (1 + x ^ 2)) = 1 / s x := by
  rw [← s_sq x]
  field_simp [s_ne x]

private lemma hasDerivAt_s_mul_arctan (x : ℝ) :
    HasDerivAt (fun y => s y * Real.arctan y)
      (substitutionIntegrand x + 1 / s x) x := by
  convert (hasDerivAt_s x).mul (Real.hasDerivAt_arctan x) using 1
  unfold substitutionIntegrand
  rw [(hasDerivAt_s x).deriv, s_div_one_add_sq]
  ring

private lemma add_s_pos (x : ℝ) : 0 < x + s x := by
  by_cases hx : 0 ≤ x
  · nlinarith [s_pos x]
  · have hxle : x ≤ 0 := le_of_not_ge hx
    have hxn : 0 ≤ -x := neg_nonneg.mpr hxle
    have hsnonneg : 0 ≤ s x := le_of_lt (s_pos x)
    have hlt : -x < s x := by
      by_contra h
      have hle : s x ≤ -x := le_of_not_gt h
      have hp : 0 ≤ (-x - s x) * (-x + s x) :=
        mul_nonneg (sub_nonneg.mpr hle) (add_nonneg hxn hsnonneg)
      nlinarith [s_sq x]
    nlinarith

private lemma hasDerivAt_log_add_s (x : ℝ) :
    HasDerivAt (fun y => Real.log (y + s y)) (1 / s x) x := by
  have hsum :
      HasDerivAt (fun y => y + s y) (1 + x / s x) x :=
    (hasDerivAt_id x).add (hasDerivAt_s x)
  have hsum_ne : x + s x ≠ 0 := ne_of_gt (add_s_pos x)
  convert (Real.hasDerivAt_log hsum_ne).comp x hsum using 1
  field_simp [s_ne x, hsum_ne] <;> ring

private lemma hasDerivAt_primitive (x : ℝ) :
    HasDerivAt primitive (integrand x) x := by
  unfold primitive
  convert (hasDerivAt_s_mul_arctan x).sub (hasDerivAt_log_add_s x) using 1
  rw [integrand_eq_substitution]
  ring

private lemma antiderivatives_eq_primitive
    {f p : ℝ → ℝ} (hp : ∀ x, HasDerivAt p (f x) x) :
    Antiderivatives f = PrimitiveFamily p := by
  ext F
  change
    (∀ x, HasDerivAt F (f x) x) ↔
      ∃ C : ℝ, ∀ x, F x = p x + C
  constructor
  · intro hF
    have hzero : ∀ x, HasDerivAt (fun y => F y - p y) 0 x := by
      intro x
      convert (hF x).sub (hp x) using 1
      ring
    have hdiff : Differentiable ℝ (fun y => F y - p y) :=
      fun x => (hzero x).differentiableAt
    have hderiv : ∀ x, deriv (fun y => F y - p y) x = 0 :=
      fun x => (hzero x).deriv
    refine ⟨F 0 - p 0, ?_⟩
    intro x
    have hc := is_const_of_deriv_eq_zero hdiff hderiv x 0
    linarith
  · rintro ⟨C, hFC⟩
    intro x
    have hEq : F = fun y => p y + C := funext hFC
    rw [hEq]
    exact (hp x).add_const C

theorem gap1 :
    Antiderivatives integrand =
      Antiderivatives substitutionIntegrand := by
  ext F
  change
    (∀ x, HasDerivAt F (integrand x) x) ↔
      ∀ x, HasDerivAt F (substitutionIntegrand x) x
  constructor
  · intro hF x
    rw [← integrand_eq_substitution x]
    exact hF x
  · intro hF x
    rw [integrand_eq_substitution x]
    exact hF x
theorem gap2 :
    Antiderivatives substitutionIntegrand = ByPartsFamily := by
  ext F
  change
    (∀ x, HasDerivAt F (substitutionIntegrand x) x) ↔
      ∃ G, (∀ x, HasDerivAt G (1 / s x) x) ∧
        ∀ x, F x = s x * Real.arctan x - G x
  constructor
  · intro hF
    refine ⟨fun x => s x * Real.arctan x - F x, ?_, ?_⟩
    · intro x
      convert (hasDerivAt_s_mul_arctan x).sub (hF x) using 1 <;> ring
    · intro x
      ring
  · rintro ⟨G, hG, hFG⟩
    intro x
    have hEq : F = fun y => s y * Real.arctan y - G y := funext hFG
    rw [hEq]
    convert (hasDerivAt_s_mul_arctan x).sub (hG x) using 1 <;> ring
theorem gap3 :
    Antiderivatives integrand = ByPartsFamily := by
  exact gap1.trans gap2
theorem gap4 :
    Antiderivatives integrand = PrimitiveFamily primitive := by
  exact antiderivatives_eq_primitive hasDerivAt_primitive

end
end ProofGap.Exercise2152
