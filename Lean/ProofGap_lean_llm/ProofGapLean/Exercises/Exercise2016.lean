import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2016
noncomputable section

def integrand (a b x : ℝ) := Real.sin x * Real.sin (x + a) * Real.sin (x + b)
def firstReduced (a b x : ℝ) :=
  Real.sin x * (Real.cos (a - b) - Real.cos (2 * x + a + b))
def secondReduced (a b x : ℝ) :=
  Real.sin (3 * x + a + b) - Real.sin (x + a + b)
def primitive (a b x : ℝ) :=
  -(1 / 2 : ℝ) * Real.cos x * Real.cos (a - b) +
    (1 / 12 : ℝ) * Real.cos (3 * x + a + b) -
    (1 / 4 : ℝ) * Real.cos (x + a + b)
def Family (f : ℝ → ℝ) := {F : ℝ → ℝ | ∀ x, HasDerivAt F (f x) x}
def ScaledFamily (f : ℝ → ℝ) (c : ℝ) :=
  {F : ℝ → ℝ | ∃ G ∈ Family f, ∀ x, F x = c * G x}
def SecondFamily (a b : ℝ) :=
  {F : ℝ → ℝ | ∃ G ∈ Family (secondReduced a b), ∀ x,
    F x = -(1 / 2 : ℝ) * Real.cos x * Real.cos (a - b) - (1 / 4 : ℝ) * G x}
def Translates (p : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ C, ∀ x, F x = p x + C}

private lemma two_mul_sin_mul_sin (u v : ℝ) :
    2 * Real.sin u * Real.sin v =
      Real.cos (u - v) - Real.cos (u + v) := by
  rw [Real.cos_sub, Real.cos_add]
  ring

private lemma integrand_eq_half_first (a b x : ℝ) :
    integrand a b x = (1 / 2 : ℝ) * firstReduced a b x := by
  unfold integrand firstReduced
  have h := two_mul_sin_mul_sin (x + a) (x + b)
  have hsub : (x + a) - (x + b) = a - b := by ring
  have hadd : (x + a) + (x + b) = 2 * x + a + b := by ring
  rw [hsub, hadd] at h
  rw [← h]
  ring

private lemma sin_add_sub_identity (u v : ℝ) :
    Real.sin (u + v) - Real.sin (u - v) =
      2 * Real.cos u * Real.sin v := by
  rw [Real.sin_add, Real.sin_sub]
  ring

private lemma secondReduced_eq_product (a b x : ℝ) :
    secondReduced a b x =
      2 * Real.sin x * Real.cos (2 * x + a + b) := by
  unfold secondReduced
  have h := sin_add_sub_identity (2 * x + a + b) x
  have hadd : (2 * x + a + b) + x = 3 * x + a + b := by ring
  have hsub : (2 * x + a + b) - x = x + a + b := by ring
  rw [hadd, hsub] at h
  calc
    Real.sin (3 * x + a + b) - Real.sin (x + a + b) =
        2 * Real.cos (2 * x + a + b) * Real.sin x := h
    _ = 2 * Real.sin x * Real.cos (2 * x + a + b) := by ring

private def basePrimitive (a b x : ℝ) :=
  -(1 / 2 : ℝ) * Real.cos x * Real.cos (a - b)

private def secondPrimitive (a b x : ℝ) :=
  -(1 / 3 : ℝ) * Real.cos (3 * x + a + b) +
    Real.cos (x + a + b)

private lemma primitive_decomposition (a b : ℝ) :
    primitive a b = fun x =>
      basePrimitive a b x - (1 / 4 : ℝ) * secondPrimitive a b x := by
  funext x
  unfold primitive basePrimitive secondPrimitive
  ring

private lemma hasDerivAt_basePrimitive (a b x : ℝ) :
    HasDerivAt (basePrimitive a b)
      ((1 / 2 : ℝ) * Real.sin x * Real.cos (a - b)) x := by
  unfold basePrimitive
  convert ((Real.hasDerivAt_cos x).const_mul (-(1 / 2 : ℝ))).mul_const
    (Real.cos (a - b)) using 1 <;> ring

private lemma hasDerivAt_secondPrimitive (a b x : ℝ) :
    HasDerivAt (secondPrimitive a b) (secondReduced a b x) x := by
  unfold secondPrimitive secondReduced
  have h3 : HasDerivAt (fun y : ℝ => 3 * y + a + b) 3 x := by
    convert (((hasDerivAt_id x).const_mul 3).add_const a).add_const b using 1 <;> ring
  have h1 : HasDerivAt (fun y : ℝ => y + a + b) 1 x := by
    convert ((hasDerivAt_id x).add_const a).add_const b using 1 <;> ring
  have hc3 := (Real.hasDerivAt_cos (3 * x + a + b)).comp x h3
  have hc1 := (Real.hasDerivAt_cos (x + a + b)).comp x h1
  convert (hc3.const_mul (-(1 / 3 : ℝ))).add hc1 using 1 <;> ring

private lemma hasDerivAt_primitive (a b x : ℝ) :
    HasDerivAt (primitive a b) (integrand a b x) x := by
  rw [primitive_decomposition]
  have h := (hasDerivAt_basePrimitive a b x).sub
    ((hasDerivAt_secondPrimitive a b x).const_mul (1 / 4 : ℝ))
  convert h using 1
  rw [integrand_eq_half_first, secondReduced_eq_product]
  unfold firstReduced
  ring

private theorem antiderivatives_eq_translates {f p : ℝ → ℝ}
    (hp : ∀ x, HasDerivAt p (f x) x) :
    Family f = Translates p := by
  apply Set.ext
  intro F
  change (∀ x, HasDerivAt F (f x) x) ↔ ∃ C, ∀ x, F x = p x + C
  constructor
  · intro hF
    have hd : ∀ x, HasDerivAt (fun y => F y - p y) 0 x := by
      intro x
      convert (hF x).sub (hp x) using 1 <;> ring
    refine ⟨F 0 - p 0, ?_⟩
    intro x
    have hc : F x - p x = F 0 - p 0 :=
      is_const_of_deriv_eq_zero
        (fun y => (hd y).differentiableAt)
        (fun y => (hd y).deriv) x 0
    calc
      F x = p x + (F x - p x) := by ring
      _ = p x + (F 0 - p 0) := by rw [hc]
  · rintro ⟨C, hF⟩
    intro x
    have hfun : F = fun y => p y + C := funext hF
    rw [hfun]
    exact (hp x).add_const C

theorem gap1 (a b : ℝ) :
    Family (integrand a b) = ScaledFamily (firstReduced a b) (1 / 2) := by
  have hp : ∀ x, HasDerivAt (primitive a b) (integrand a b x) x :=
    fun x => hasDerivAt_primitive a b x
  have hfirst : ∀ x, HasDerivAt (fun y => 2 * primitive a b y)
      (firstReduced a b x) x := by
    intro x
    have h := (hp x).const_mul 2
    convert h using 1
    rw [integrand_eq_half_first]
    ring
  rw [antiderivatives_eq_translates hp]
  apply Set.ext
  intro F
  change (∃ C, ∀ x, F x = primitive a b x + C) ↔
    ∃ G, (∀ x, HasDerivAt G (firstReduced a b x) x) ∧
      ∀ x, F x = (1 / 2 : ℝ) * G x
  constructor
  · rintro ⟨C, hF⟩
    refine ⟨fun x => 2 * primitive a b x + 2 * C, ?_, ?_⟩
    · intro x
      exact (hfirst x).add_const (2 * C)
    · intro x
      rw [hF x]
      ring
  · rintro ⟨G, hG, hFG⟩
    have hGt : G ∈ Translates (fun x => 2 * primitive a b x) := by
      rw [← antiderivatives_eq_translates hfirst]
      exact hG
    rcases hGt with ⟨C, hGC⟩
    refine ⟨(1 / 2 : ℝ) * C, ?_⟩
    intro x
    rw [hFG x, hGC x]
    ring
theorem gap2 (a b : ℝ) :
    Family (integrand a b) = SecondFamily a b := by
  have hp : ∀ x, HasDerivAt (primitive a b) (integrand a b x) x :=
    fun x => hasDerivAt_primitive a b x
  have hq : ∀ x, HasDerivAt (secondPrimitive a b)
      (secondReduced a b x) x :=
    fun x => hasDerivAt_secondPrimitive a b x
  rw [antiderivatives_eq_translates hp]
  apply Set.ext
  intro F
  change (∃ C, ∀ x, F x = primitive a b x + C) ↔
    ∃ G, (∀ x, HasDerivAt G (secondReduced a b x) x) ∧
      ∀ x, F x = basePrimitive a b x - (1 / 4 : ℝ) * G x
  constructor
  · rintro ⟨C, hF⟩
    refine ⟨fun x => secondPrimitive a b x - 4 * C, ?_, ?_⟩
    · intro x
      exact (hq x).sub_const (4 * C)
    · intro x
      rw [hF x]
      unfold primitive basePrimitive secondPrimitive
      ring
  · rintro ⟨G, hG, hFG⟩
    have hGt : G ∈ Translates (secondPrimitive a b) := by
      rw [← antiderivatives_eq_translates hq]
      exact hG
    rcases hGt with ⟨C, hGC⟩
    refine ⟨-(1 / 4 : ℝ) * C, ?_⟩
    intro x
    rw [hFG x, hGC x]
    unfold primitive basePrimitive secondPrimitive
    ring
theorem gap3 (a b : ℝ) :
    Family (integrand a b) = Translates (primitive a b) := by
  exact antiderivatives_eq_translates (fun x => hasDerivAt_primitive a b x)

end
end ProofGap.Exercise2016
