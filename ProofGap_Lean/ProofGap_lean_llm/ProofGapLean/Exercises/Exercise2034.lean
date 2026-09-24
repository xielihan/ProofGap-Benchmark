import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Defs.Filter
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2034
noncomputable section

def integrand (x : ℝ) := Real.sin x / (Real.sin x ^ 3 + Real.cos x ^ 3)
def factored (x : ℝ) :=
  Real.sin x / ((Real.sin x + Real.cos x) * (1 - Real.sin x * Real.cos x))
def oddPart (x : ℝ) :=
  (Real.sin x - Real.cos x) /
    ((Real.sin x + Real.cos x) * (1 - Real.sin x * Real.cos x))
def evenPart (x : ℝ) := 1 / (1 - Real.sin x * Real.cos x)
def logPart (x : ℝ) :=
  -(Real.cos x - Real.sin x) / (Real.sin x + Real.cos x)
def productPart (x : ℝ) :=
  (Real.sin x ^ 2 - Real.cos x ^ 2) / (1 - Real.sin x * Real.cos x)
def cotPart (x : ℝ) :=
  1 / ((Real.cos x / Real.sin x - 1 / 2) ^ 2 + 3 / 4) *
    deriv (fun y : ℝ => Real.cos y / Real.sin y) x
def primitive (x : ℝ) :=
  -(1 / 6 : ℝ) *
      Real.log ((Real.sin x + Real.cos x) ^ 2 /
        (1 - Real.sin x * Real.cos x)) -
    1 / Real.sqrt 3 *
      Real.arctan ((2 * Real.cos x - Real.sin x) / (Real.sqrt 3 * Real.sin x))
def Family (U : Set ℝ) (f : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∀ x ∈ U, HasDerivAt F (f x) x}
def PairFamily (U : Set ℝ) :=
  {F : ℝ → ℝ | ∃ P ∈ Family U oddPart, ∃ Q ∈ Family U evenPart,
    ∀ x ∈ U, F x = (1 / 2 : ℝ) * P x + (1 / 2 : ℝ) * Q x}
def TripleFamily (U : Set ℝ) :=
  {F : ℝ → ℝ | ∃ P ∈ Family U logPart, ∃ Q ∈ Family U productPart,
    ∃ R ∈ Family U evenPart, ∀ x ∈ U,
      F x = (1 / 3 : ℝ) * P x + (1 / 6 : ℝ) * Q x + (1 / 2 : ℝ) * R x}
def Translates (U : Set ℝ) (p : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ C, ∀ x ∈ U, F x = p x + C}
def Regular (U : Set ℝ) : Prop :=
  IsOpen U ∧ IsPreconnected U ∧
    (∀ x ∈ U, Real.sin x + Real.cos x ≠ 0 ∧ Real.sin x ≠ 0)

private lemma denom_pos (x : ℝ) :
    0 < 1 - Real.sin x * Real.cos x := by
  have ht := Real.sin_sq_add_cos_sq x
  nlinarith [sq_nonneg (Real.sin x - Real.cos x)]

private lemma integrand_eq_factored (x : ℝ)
    (hsum : Real.sin x + Real.cos x ≠ 0) :
    integrand x = factored x := by
  have hfac : Real.sin x ^ 3 + Real.cos x ^ 3 =
      (Real.sin x + Real.cos x) *
        (1 - Real.sin x * Real.cos x) := by
    have ht : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 :=
      Real.sin_sq_add_cos_sq x
    calc
      Real.sin x ^ 3 + Real.cos x ^ 3 =
          (Real.sin x + Real.cos x) *
            (Real.sin x ^ 2 - Real.sin x * Real.cos x + Real.cos x ^ 2) := by
              ring
      _ = (Real.sin x + Real.cos x) *
            ((Real.sin x ^ 2 + Real.cos x ^ 2) - Real.sin x * Real.cos x) := by
              ring
      _ = (Real.sin x + Real.cos x) *
            (1 - Real.sin x * Real.cos x) := by rw [ht]
  unfold integrand factored
  rw [hfac]

private lemma pair_identity (x : ℝ)
    (hsum : Real.sin x + Real.cos x ≠ 0) :
    integrand x =
      (1 / 2 : ℝ) * oddPart x + (1 / 2 : ℝ) * evenPart x := by
  rw [integrand_eq_factored x hsum]
  unfold factored oddPart evenPart
  have hdne : 1 - Real.sin x * Real.cos x ≠ 0 :=
    ne_of_gt (denom_pos x)
  field_simp [hsum, hdne]
  ring

private lemma triple_identity (x : ℝ)
    (hsum : Real.sin x + Real.cos x ≠ 0) :
    integrand x =
      (1 / 3 : ℝ) * logPart x + (1 / 6 : ℝ) * productPart x +
        (1 / 2 : ℝ) * evenPart x := by
  rw [integrand_eq_factored x hsum]
  unfold factored logPart productPart evenPart
  have hdne : 1 - Real.sin x * Real.cos x ≠ 0 :=
    ne_of_gt (denom_pos x)
  have ht := Real.sin_sq_add_cos_sq x
  have htm := congrArg
    (fun z : ℝ => z * (Real.sin x - Real.cos x)) ht
  field_simp [hsum, hdne]
  ring_nf at htm ⊢
  nlinarith

private def evenPrimitive (x : ℝ) :=
  -(2 / Real.sqrt 3) *
    Real.arctan ((2 * Real.cos x - Real.sin x) /
      (Real.sqrt 3 * Real.sin x))

private lemma hasDerivAt_evenPrimitive (x : ℝ)
    (hsin : Real.sin x ≠ 0) :
    HasDerivAt evenPrimitive (evenPart x) x := by
  have hsqrtpos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt : Real.sqrt 3 ≠ 0 := ne_of_gt hsqrtpos
  have hden : Real.sqrt 3 * Real.sin x ≠ 0 := mul_ne_zero hsqrt hsin
  have hn := ((Real.hasDerivAt_cos x).const_mul 2).sub
    (Real.hasDerivAt_sin x)
  have hm := (Real.hasDerivAt_sin x).const_mul (Real.sqrt 3)
  have hq : HasDerivAt
      (fun y : ℝ => (2 * Real.cos y - Real.sin y) /
        (Real.sqrt 3 * Real.sin y))
      (((2 * -Real.sin x - Real.cos x) *
          (Real.sqrt 3 * Real.sin x) -
        (2 * Real.cos x - Real.sin x) *
          (Real.sqrt 3 * Real.cos x)) /
        (Real.sqrt 3 * Real.sin x) ^ 2) x := by
    simpa only [Pi.div_apply, Pi.sub_apply] using hn.div hm hden
  have hraw := ((Real.hasDerivAt_arctan _).comp x hq).const_mul
    (-(2 / Real.sqrt 3))
  have h : HasDerivAt evenPrimitive
      (-(2 / Real.sqrt 3) *
        (1 / (1 + ((2 * Real.cos x - Real.sin x) /
          (Real.sqrt 3 * Real.sin x)) ^ 2) *
          (((2 * -Real.sin x - Real.cos x) *
              (Real.sqrt 3 * Real.sin x) -
            (2 * Real.cos x - Real.sin x) *
              (Real.sqrt 3 * Real.cos x)) /
            (Real.sqrt 3 * Real.sin x) ^ 2))) x := by
    simpa only [evenPrimitive, Function.comp_apply] using hraw
  have ht : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq x
  have hsqrt_sq : (Real.sqrt 3) ^ 2 = (3 : ℝ) := by
    norm_num
  have hnum :
      (2 * -Real.sin x - Real.cos x) *
          (Real.sqrt 3 * Real.sin x) -
        (2 * Real.cos x - Real.sin x) *
          (Real.sqrt 3 * Real.cos x) =
      -(2 * Real.sqrt 3) := by
    calc
      _ = -(2 * Real.sqrt 3) *
          (Real.sin x ^ 2 + Real.cos x ^ 2) := by ring
      _ = -(2 * Real.sqrt 3) := by rw [ht]; ring
  have hden_sq :
      (Real.sqrt 3 * Real.sin x) ^ 2 = 3 * Real.sin x ^ 2 := by
    rw [mul_pow, hsqrt_sq]
  have huDen :
      1 + ((2 * Real.cos x - Real.sin x) /
        (Real.sqrt 3 * Real.sin x)) ^ 2 =
      4 * (1 - Real.sin x * Real.cos x) / (3 * Real.sin x ^ 2) := by
    field_simp [hsin, hsqrt]
    ring_nf at ht ⊢
    rw [hsqrt_sq]
    nlinarith
  have hval :
      -(2 / Real.sqrt 3) *
        (1 / (1 + ((2 * Real.cos x - Real.sin x) /
          (Real.sqrt 3 * Real.sin x)) ^ 2) *
          (((2 * -Real.sin x - Real.cos x) *
              (Real.sqrt 3 * Real.sin x) -
            (2 * Real.cos x - Real.sin x) *
              (Real.sqrt 3 * Real.cos x)) /
            (Real.sqrt 3 * Real.sin x) ^ 2)) = evenPart x := by
    rw [hnum, hden_sq, huDen]
    unfold evenPart
    have hdne : 1 - Real.sin x * Real.cos x ≠ 0 :=
      ne_of_gt (denom_pos x)
    field_simp [hsin, hsqrt, hdne] <;> ring
  rw [← hval]
  exact h

private def simpleLogPrimitive (x : ℝ) :=
  -(1 / 2 : ℝ) * Real.log ((Real.sin x + Real.cos x) ^ 2)

private lemma hasDerivAt_simpleLogPrimitive (x : ℝ)
    (hsum : Real.sin x + Real.cos x ≠ 0) :
    HasDerivAt simpleLogPrimitive (logPart x) x := by
  have ha : HasDerivAt (fun y : ℝ => Real.sin y + Real.cos y)
      (Real.cos x - Real.sin x) x :=
    (Real.hasDerivAt_sin x).add (Real.hasDerivAt_cos x)
  have ha2 := ha.pow 2
  have hlog := (Real.hasDerivAt_log (pow_ne_zero 2 hsum)).comp x ha2
  have h := hlog.const_mul (-(1 / 2 : ℝ))
  unfold simpleLogPrimitive
  convert h using 1
  unfold logPart
  field_simp [hsum]
  ring

private lemma hasDerivAt_denom (x : ℝ) :
    HasDerivAt (fun y : ℝ => 1 - Real.sin y * Real.cos y)
      (Real.sin x ^ 2 - Real.cos x ^ 2) x := by
  have h := (hasDerivAt_const x (1 : ℝ)).sub
    ((Real.hasDerivAt_sin x).mul (Real.hasDerivAt_cos x))
  convert h using 1 <;> ring

private lemma hasDerivAt_logAbsSum (x : ℝ)
    (hsum : Real.sin x + Real.cos x ≠ 0) :
    HasDerivAt (fun y : ℝ => Real.log |Real.sin y + Real.cos y|)
      ((Real.cos x - Real.sin x) / (Real.sin x + Real.cos x)) x := by
  have ha : HasDerivAt (fun y : ℝ => Real.sin y + Real.cos y)
      (Real.cos x - Real.sin x) x :=
    (Real.hasDerivAt_sin x).add (Real.hasDerivAt_cos x)
  simpa only [Function.comp_apply, Real.log_abs, div_eq_mul_inv, mul_comm] using
    (Real.hasDerivAt_log hsum).comp x ha

private def oddHalfPrimitive (x : ℝ) :=
  -(1 / 6 : ℝ) *
    Real.log ((Real.sin x + Real.cos x) ^ 2 /
      (1 - Real.sin x * Real.cos x))

private lemma hasDerivAt_oddHalfPrimitive (x : ℝ)
    (hsum : Real.sin x + Real.cos x ≠ 0) :
    HasDerivAt oddHalfPrimitive ((1 / 2 : ℝ) * oddPart x) x := by
  have ha : HasDerivAt (fun y : ℝ => Real.sin y + Real.cos y)
      (Real.cos x - Real.sin x) x :=
    (Real.hasDerivAt_sin x).add (Real.hasDerivAt_cos x)
  have ha2 := ha.pow 2
  have hd := hasDerivAt_denom x
  have hdne : 1 - Real.sin x * Real.cos x ≠ 0 :=
    ne_of_gt (denom_pos x)
  have hq := ha2.div hd hdne
  have hqne :
      (Real.sin x + Real.cos x) ^ 2 /
        (1 - Real.sin x * Real.cos x) ≠ 0 :=
    div_ne_zero (pow_ne_zero 2 hsum) hdne
  have hlog := (Real.hasDerivAt_log hqne).comp x hq
  have h := hlog.const_mul (-(1 / 6 : ℝ))
  unfold oddHalfPrimitive
  convert h using 1
  unfold oddPart
  simp only [Function.comp_apply, Pi.pow_apply, Pi.div_apply]
  have ht := Real.sin_sq_add_cos_sq x
  have htm := congrArg
    (fun z : ℝ => z * (Real.sin x - Real.cos x)) ht
  field_simp [hsum, hdne]
  ring_nf at htm ⊢
  nlinarith

private lemma hasDerivAt_primitive (x : ℝ)
    (hsin : Real.sin x ≠ 0) (hsum : Real.sin x + Real.cos x ≠ 0) :
    HasDerivAt primitive (integrand x) x := by
  have hsqrt : Real.sqrt 3 ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hfun : primitive =
      (fun y => oddHalfPrimitive y + (1 / 2 : ℝ) * evenPrimitive y) := by
    funext y
    unfold primitive oddHalfPrimitive evenPrimitive
    field_simp [hsqrt]
    ring
  rw [hfun]
  have h := (hasDerivAt_oddHalfPrimitive x hsum).add
    ((hasDerivAt_evenPrimitive x hsin).const_mul (1 / 2 : ℝ))
  have hval :
      (1 / 2 : ℝ) * oddPart x + (1 / 2 : ℝ) * evenPart x = integrand x :=
    (pair_identity x hsum).symm
  rw [hval] at h
  simpa only [Pi.add_apply] using h

theorem gap1 (U : Set ℝ) (hU : Regular U) :
    Family U integrand = Family U factored := by
  rcases hU with ⟨_, _, hreg⟩
  apply Set.ext
  intro F
  simp only [Family, Set.mem_setOf_eq]
  constructor
  · intro hF x hx
    simpa only [integrand_eq_factored x (hreg x hx).1] using hF x hx
  · intro hF x hx
    simpa only [integrand_eq_factored x (hreg x hx).1] using hF x hx
theorem gap2 (U : Set ℝ) (hU : Regular U) :
    Family U integrand = PairFamily U := by
  rcases hU with ⟨hopen, _, hreg⟩
  apply Set.ext
  intro F
  simp only [Family, PairFamily, Set.mem_setOf_eq]
  constructor
  · intro hF
    refine ⟨(fun y => 2 * F y - evenPrimitive y), ?_, evenPrimitive, ?_, ?_⟩
    · intro x hx
      have h := ((hF x hx).const_mul 2).sub
        (hasDerivAt_evenPrimitive x (hreg x hx).2)
      convert h using 1
      linarith [pair_identity x (hreg x hx).1]
    · intro x hx
      exact hasDerivAt_evenPrimitive x (hreg x hx).2
    · intro x _
      ring
  · rintro ⟨P, hP, Q, hQ, hEq⟩
    intro x hx
    have hcomb := ((hP x hx).const_mul (1 / 2 : ℝ)).add
      ((hQ x hx).const_mul (1 / 2 : ℝ))
    have hval :
        (1 / 2 : ℝ) * oddPart x + (1 / 2 : ℝ) * evenPart x = integrand x :=
      (pair_identity x (hreg x hx).1).symm
    rw [hval] at hcomb
    have hc : HasDerivAt
        (fun y => (1 / 2 : ℝ) * P y + (1 / 2 : ℝ) * Q y)
        (integrand x) x := by
      simpa only [Pi.add_apply] using hcomb
    have heq : F =ᶠ[nhds x]
        (fun y => (1 / 2 : ℝ) * P y + (1 / 2 : ℝ) * Q y) := by
      filter_upwards [hopen.mem_nhds hx] with y hy
      exact hEq y hy
    exact hc.congr_of_eventuallyEq heq
theorem gap3 (U : Set ℝ) (hU : Regular U) :
    Family U integrand = TripleFamily U := by
  rcases hU with ⟨hopen, _, hreg⟩
  apply Set.ext
  intro F
  simp only [Family, TripleFamily, Set.mem_setOf_eq]
  constructor
  · intro hF
    refine ⟨simpleLogPrimitive, ?_,
      (fun y => 6 * F y - 2 * simpleLogPrimitive y - 3 * evenPrimitive y), ?_,
      evenPrimitive, ?_, ?_⟩
    · intro x hx
      exact hasDerivAt_simpleLogPrimitive x (hreg x hx).1
    · intro x hx
      have h := (((hF x hx).const_mul 6).sub
        ((hasDerivAt_simpleLogPrimitive x (hreg x hx).1).const_mul 2)).sub
        ((hasDerivAt_evenPrimitive x (hreg x hx).2).const_mul 3)
      convert h using 1
      linarith [triple_identity x (hreg x hx).1]
    · intro x hx
      exact hasDerivAt_evenPrimitive x (hreg x hx).2
    · intro x _
      ring
  · rintro ⟨P, hP, Q, hQ, R, hR, hEq⟩
    intro x hx
    have hcomb := (((hP x hx).const_mul (1 / 3 : ℝ)).add
      ((hQ x hx).const_mul (1 / 6 : ℝ))).add
      ((hR x hx).const_mul (1 / 2 : ℝ))
    have hval :
        (1 / 3 : ℝ) * logPart x + (1 / 6 : ℝ) * productPart x +
          (1 / 2 : ℝ) * evenPart x = integrand x :=
      (triple_identity x (hreg x hx).1).symm
    rw [hval] at hcomb
    have hc : HasDerivAt
        (fun y => (1 / 3 : ℝ) * P y + (1 / 6 : ℝ) * Q y +
          (1 / 2 : ℝ) * R y) (integrand x) x := by
      simpa only [Pi.add_apply] using hcomb
    have heq : F =ᶠ[nhds x]
        (fun y => (1 / 3 : ℝ) * P y + (1 / 6 : ℝ) * Q y +
          (1 / 2 : ℝ) * R y) := by
      filter_upwards [hopen.mem_nhds hx] with y hy
      exact hEq y hy
    exact hc.congr_of_eventuallyEq heq
theorem gap4 (x : ℝ) (hxsin : Real.sin x ≠ 0)
    (hxsum : Real.sin x + Real.cos x ≠ 0) :
    integrand x =
      -(1 / 3 : ℝ) * deriv (fun y => Real.log |Real.sin y + Real.cos y|) x +
      (1 / 6 : ℝ) * deriv (fun y => Real.log (1 - Real.sin y * Real.cos y)) x -
      (1 / 2 : ℝ) * cotPart x := by
  have hdne : 1 - Real.sin x * Real.cos x ≠ 0 :=
    ne_of_gt (denom_pos x)
  have hlogabs := hasDerivAt_logAbsSum x hxsum
  have hlogden := (Real.hasDerivAt_log hdne).comp x (hasDerivAt_denom x)
  have hcot := (Real.hasDerivAt_cos x).div (Real.hasDerivAt_sin x) hxsin
  have hlogabsval :
      deriv (fun y => Real.log |Real.sin y + Real.cos y|) x =
        -logPart x := by
    rw [hlogabs.deriv]
    unfold logPart
    ring
  have hlogdenderiv :
      deriv (fun y => Real.log (1 - Real.sin y * Real.cos y)) x =
        (1 - Real.sin x * Real.cos x)⁻¹ *
          (Real.sin x ^ 2 - Real.cos x ^ 2) := by
    simpa only [Function.comp_apply] using hlogden.deriv
  have hlogdenval :
      deriv (fun y => Real.log (1 - Real.sin y * Real.cos y)) x =
        productPart x := by
    rw [hlogdenderiv]
    unfold productPart
    field_simp [hdne]
  have hcotderiv :
      deriv (fun y : ℝ => Real.cos y / Real.sin y) x =
        (-Real.sin x * Real.sin x - Real.cos x * Real.cos x) /
          Real.sin x ^ 2 := by
    simpa only [Pi.div_apply] using hcot.deriv
  have ht : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq x
  have hD :
      (Real.cos x / Real.sin x - 1 / 2) ^ 2 + 3 / 4 =
        (1 - Real.sin x * Real.cos x) / Real.sin x ^ 2 := by
    field_simp [hxsin]
    ring_nf at ht ⊢
    nlinarith
  have hnum :
      -Real.sin x * Real.sin x - Real.cos x * Real.cos x = -1 := by
    nlinarith [ht]
  have hcotpart : cotPart x = -evenPart x := by
    unfold cotPart
    rw [hcotderiv, hD, hnum]
    unfold evenPart
    field_simp [hxsin, hdne] <;> ring
  rw [hlogabsval, hlogdenval, hcotpart, triple_identity x hxsum]
  ring
theorem gap5 (U : Set ℝ) (hU : Regular U) :
    Family U integrand = Translates U primitive := by
  rcases hU with ⟨hopen, hconn, hreg⟩
  apply Set.ext
  intro F
  simp only [Family, Translates, Set.mem_setOf_eq]
  constructor
  · intro hF
    by_cases hne : U.Nonempty
    · rcases hne with ⟨x₀, hx₀⟩
      let g : ℝ → ℝ := fun x => F x - primitive x
      have hgdiff : DifferentiableOn ℝ g U := by
        intro x hx
        exact ((hF x hx).sub
          (hasDerivAt_primitive x (hreg x hx).2 (hreg x hx).1)).differentiableAt.differentiableWithinAt
      have hgzero : ∀ x ∈ U, deriv g x = 0 := by
        intro x hx
        have hg := (hF x hx).sub
          (hasDerivAt_primitive x (hreg x hx).2 (hreg x hx).1)
        simpa [g] using hg.deriv
      refine ⟨F x₀ - primitive x₀, ?_⟩
      intro x hx
      have heq : g x = g x₀ :=
        hopen.is_const_of_deriv_eq_zero hconn hgdiff hgzero hx hx₀
      change F x - primitive x = F x₀ - primitive x₀ at heq
      linarith
    · refine ⟨0, ?_⟩
      intro x hx
      exact False.elim (hne ⟨x, hx⟩)
  · rintro ⟨C, hEq⟩
    intro x hx
    have hp := (hasDerivAt_primitive x (hreg x hx).2 (hreg x hx).1).add_const C
    have heq : F =ᶠ[nhds x] (fun y => primitive y + C) := by
      filter_upwards [hopen.mem_nhds hx] with y hy
      exact hEq y hy
    exact hp.congr_of_eventuallyEq heq

end
end ProofGap.Exercise2034
