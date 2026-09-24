import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2054
noncomputable section

def denom (x : ℝ) := 3 * Real.sin x ^ 2 + 4 * Real.cos x ^ 2
def integrand (x : ℝ) := (2 * Real.sin x - Real.cos x) / denom x
def sinPart (x : ℝ) := 2 * Real.sin x / denom x
def cosPart (x : ℝ) := Real.cos x / denom x
def cosineSub (x : ℝ) := deriv Real.cos x / (3 + Real.cos x ^ 2)
def sineSub (x : ℝ) := deriv Real.sin x / (4 - Real.sin x ^ 2)
def primitive (x : ℝ) :=
  -(2 / Real.sqrt 3) * Real.arctan (Real.cos x / Real.sqrt 3) -
    (1 / 4 : ℝ) * Real.log ((2 + Real.sin x) / (2 - Real.sin x))
def Family (f : ℝ → ℝ) := {F : ℝ → ℝ | ∀ x, HasDerivAt F (f x) x}
def SplitFamily :=
  {F : ℝ → ℝ | ∃ P ∈ Family sinPart, ∃ Q ∈ Family cosPart,
    ∀ x, F x = P x - Q x}
def SubstitutionFamily :=
  {F : ℝ → ℝ | ∃ P ∈ Family cosineSub, ∃ Q ∈ Family sineSub,
    ∀ x, F x = -2 * P x - Q x}
def Translates (p : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ C, ∀ x, F x = p x + C}

private def cosinePrimitive (x : ℝ) :=
  (1 / Real.sqrt 3) * Real.arctan (Real.cos x / Real.sqrt 3)

private def sinePrimitive (x : ℝ) :=
  (1 / 4 : ℝ) * Real.log ((2 + Real.sin x) / (2 - Real.sin x))

private theorem integrand_identities (x : ℝ) :
    integrand x = sinPart x - cosPart x ∧
      sinPart x = -2 * cosineSub x ∧
      cosPart x = sineSub x := by
  have htrig := Real.sin_sq_add_cos_sq x
  have hdc : denom x = 3 + Real.cos x ^ 2 := by
    unfold denom
    nlinarith
  have hds : denom x = 4 - Real.sin x ^ 2 := by
    unfold denom
    nlinarith
  constructor
  · unfold integrand sinPart cosPart
    ring
  constructor
  · unfold sinPart cosineSub
    rw [(Real.hasDerivAt_cos x).deriv, hdc]
    ring
  · unfold cosPart sineSub
    rw [(Real.hasDerivAt_sin x).deriv, hds]

private theorem canonical_derivatives (x : ℝ) :
    HasDerivAt cosinePrimitive (cosineSub x) x ∧
      HasDerivAt sinePrimitive (sineSub x) x := by
  have hsqrt : Real.sqrt (3 : ℝ) ≠ 0 := by positivity
  have hsqrt_sq : Real.sqrt (3 : ℝ) ^ 2 = 3 :=
    Real.sq_sqrt (by norm_num)
  have hplus : 2 + Real.sin x ≠ 0 := by
    have h := Real.neg_one_le_sin x
    linarith
  have hminus : 2 - Real.sin x ≠ 0 := by
    have h := Real.sin_le_one x
    linarith
  have hquot : (2 + Real.sin x) / (2 - Real.sin x) ≠ 0 :=
    div_ne_zero hplus hminus
  have hfour : 4 - Real.sin x ^ 2 ≠ 0 := by
    intro h
    apply (mul_ne_zero hplus hminus)
    calc
      (2 + Real.sin x) * (2 - Real.sin x) = 4 - Real.sin x ^ 2 := by ring
      _ = 0 := h
  constructor
  · change HasDerivAt
      (fun y => (1 / Real.sqrt 3) *
        Real.arctan (Real.cos y / Real.sqrt 3))
      (cosineSub x) x
    have h :=
      (Real.hasDerivAt_arctan (Real.cos x / Real.sqrt 3)).comp x
        ((Real.hasDerivAt_cos x).div_const (Real.sqrt 3))
    have hatanDen : 1 + (Real.cos x / Real.sqrt 3) ^ 2 ≠ 0 := by positivity
    have hcosDen : 3 + Real.cos x ^ 2 ≠ 0 := by positivity
    convert h.const_mul (1 / Real.sqrt 3) using 1
    unfold cosineSub
    rw [(Real.hasDerivAt_cos x).deriv]
    field_simp [hsqrt, hatanDen, hcosDen]
    rw [hsqrt_sq]
  · change HasDerivAt
      (fun y => (1 / 4 : ℝ) *
        Real.log ((2 + Real.sin y) / (2 - Real.sin y)))
      (sineSub x) x
    have hnum : HasDerivAt (fun y : ℝ => 2 + Real.sin y) (Real.cos x) x := by
      exact (Real.hasDerivAt_sin x).const_add 2
    have hden : HasDerivAt (fun y : ℝ => 2 - Real.sin y) (-Real.cos x) x := by
      exact (Real.hasDerivAt_sin x).const_sub 2
    have hdiv := hnum.div hden hminus
    have hlog := (Real.hasDerivAt_log hquot).comp x hdiv
    convert hlog.const_mul (1 / 4 : ℝ) using 1
    unfold sineSub
    rw [(Real.hasDerivAt_sin x).deriv]
    field_simp [hplus, hminus, hquot, hfour] <;> ring

theorem gap1 : Family integrand = SplitFamily := by
  apply Set.ext
  intro F
  constructor
  · intro hF
    change ∀ x, HasDerivAt F (integrand x) x at hF
    refine ⟨fun y => F y + sinePrimitive y, ?_, sinePrimitive, ?_, ?_⟩
    · intro x
      have h := (hF x).add (canonical_derivatives x).2
      have hi := integrand_identities x
      have heq : integrand x + sineSub x = sinPart x := by
        calc
          integrand x + sineSub x = (sinPart x - cosPart x) + sineSub x := by rw [hi.1]
          _ = sinPart x := by rw [hi.2.2]; ring
      simpa only [heq] using h
    · intro x
      have hi := integrand_identities x
      simpa only [hi.2.2] using (canonical_derivatives x).2
    · intro x
      ring
  · rintro ⟨P, hP, Q, hQ, hF⟩
    change ∀ x, HasDerivAt F (integrand x) x
    have hfun : F = fun y => P y - Q y := funext hF
    rw [hfun]
    intro x
    have hi := integrand_identities x
    have h := (hP x).sub (hQ x)
    simpa only [hi.1] using h
theorem gap2 : Family integrand = SubstitutionFamily := by
  apply Set.ext
  intro F
  constructor
  · intro hF
    change ∀ x, HasDerivAt F (integrand x) x at hF
    refine ⟨cosinePrimitive, ?_, fun y => -2 * cosinePrimitive y - F y, ?_, ?_⟩
    · intro x
      exact (canonical_derivatives x).1
    · intro x
      have h := ((canonical_derivatives x).1.const_mul (-2)).sub (hF x)
      have hi := integrand_identities x
      have heq : -2 * cosineSub x - integrand x = sineSub x := by
        calc
          -2 * cosineSub x - integrand x =
              -2 * cosineSub x - (sinPart x - cosPart x) := by rw [hi.1]
          _ = sineSub x := by rw [hi.2.1, hi.2.2]; ring
      simpa only [heq] using h
    · intro x
      ring
  · rintro ⟨P, hP, Q, hQ, hF⟩
    change ∀ x, HasDerivAt F (integrand x) x
    have hfun : F = fun y => -2 * P y - Q y := funext hF
    rw [hfun]
    intro x
    have h := ((hP x).const_mul (-2)).sub (hQ x)
    have hi := integrand_identities x
    have heq : -2 * cosineSub x - sineSub x = integrand x := by
      calc
        -2 * cosineSub x - sineSub x = sinPart x - cosPart x := by
          rw [hi.2.1, hi.2.2]
        _ = integrand x := hi.1.symm
    simpa only [heq] using h
theorem gap3 : SubstitutionFamily = Translates primitive := by
  rw [← gap2]
  have hshape : primitive = fun y => -2 * cosinePrimitive y - sinePrimitive y := by
    funext y
    unfold primitive cosinePrimitive sinePrimitive
    ring
  have hprimitive : ∀ x, HasDerivAt primitive (integrand x) x := by
    intro x
    rw [hshape]
    have h := ((canonical_derivatives x).1.const_mul (-2)).sub
      (canonical_derivatives x).2
    have hi := integrand_identities x
    have heq : -2 * cosineSub x - sineSub x = integrand x := by
      calc
        -2 * cosineSub x - sineSub x = sinPart x - cosPart x := by
          rw [hi.2.1, hi.2.2]
        _ = integrand x := hi.1.symm
    simpa only [heq] using h
  apply Set.ext
  intro F
  constructor
  · intro hF
    change ∀ x, HasDerivAt F (integrand x) x at hF
    change ∃ C : ℝ, ∀ x, F x = primitive x + C
    refine ⟨F 0 - primitive 0, ?_⟩
    have hdiff : Differentiable ℝ (fun y : ℝ => F y - primitive y) := by
      intro y
      exact ((hF y).sub (hprimitive y)).differentiableAt
    have hzero : ∀ y, deriv (fun z : ℝ => F z - primitive z) y = 0 := by
      intro y
      simpa using (((hF y).sub (hprimitive y)).deriv)
    intro x
    have hc := is_const_of_deriv_eq_zero hdiff hzero x 0
    linarith [hc]
  · rintro ⟨C, hF⟩
    change ∀ x, HasDerivAt F (integrand x) x
    have hfun : F = fun y => primitive y + C := funext hF
    rw [hfun]
    intro x
    exact (hprimitive x).add_const C
theorem gap4 : Family integrand = Translates primitive := by
  exact gap2.trans gap3

end
end ProofGap.Exercise2054
