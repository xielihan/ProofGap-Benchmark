import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2015
noncomputable section

def integrand (x : ℝ) :=
  Real.sin x * Real.sin (x / 2) * Real.sin (x / 3)
def firstReduced (x : ℝ) :=
  (Real.cos ((2 / 3 : ℝ) * x) - Real.cos ((4 / 3 : ℝ) * x)) * Real.sin (x / 2)
def leftReduced (x : ℝ) :=
  Real.sin ((7 / 6 : ℝ) * x) - Real.sin ((1 / 6 : ℝ) * x)
def rightReduced (x : ℝ) :=
  Real.sin ((11 / 6 : ℝ) * x) - Real.sin ((5 / 6 : ℝ) * x)
def primitive (x : ℝ) :=
  -(3 / 14 : ℝ) * Real.cos ((7 / 6 : ℝ) * x) +
    (3 / 2 : ℝ) * Real.cos (x / 6) +
    (3 / 22 : ℝ) * Real.cos ((11 / 6 : ℝ) * x) -
    (3 / 10 : ℝ) * Real.cos ((5 / 6 : ℝ) * x)
def Family (f : ℝ → ℝ) := {F : ℝ → ℝ | ∀ x, HasDerivAt F (f x) x}
def ScaledFamily (f : ℝ → ℝ) (c : ℝ) :=
  {F : ℝ → ℝ | ∃ G ∈ Family f, ∀ x, F x = c * G x}
def PairFamily (f g : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ P ∈ Family f, ∃ Q ∈ Family g,
    ∀ x, F x = (1 / 4 : ℝ) * P x - (1 / 4 : ℝ) * Q x}
def Translates (p : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ C, ∀ x, F x = p x + C}

private theorem integrand_eq_half_first (x : ℝ) :
    integrand x = (1 / 2 : ℝ) * firstReduced x := by
  unfold integrand firstReduced
  have h23 : (2 / 3 : ℝ) * x = x - x / 3 := by ring
  have h43 : (4 / 3 : ℝ) * x = x + x / 3 := by ring
  rw [h23, h43, Real.cos_sub, Real.cos_add]
  ring

private theorem first_eq_half_pair (x : ℝ) :
    firstReduced x =
      (1 / 2 : ℝ) * leftReduced x - (1 / 2 : ℝ) * rightReduced x := by
  have hleft :
      leftReduced x =
        2 * Real.cos ((2 / 3 : ℝ) * x) * Real.sin (x / 2) := by
    unfold leftReduced
    have h7 : (7 / 6 : ℝ) * x = (2 / 3 : ℝ) * x + x / 2 := by ring
    have h1 : (1 / 6 : ℝ) * x = (2 / 3 : ℝ) * x - x / 2 := by ring
    rw [h7, h1, Real.sin_add, Real.sin_sub]
    ring
  have hright :
      rightReduced x =
        2 * Real.cos ((4 / 3 : ℝ) * x) * Real.sin (x / 2) := by
    unfold rightReduced
    have h11 : (11 / 6 : ℝ) * x = (4 / 3 : ℝ) * x + x / 2 := by ring
    have h5 : (5 / 6 : ℝ) * x = (4 / 3 : ℝ) * x - x / 2 := by ring
    rw [h11, h5, Real.sin_add, Real.sin_sub]
    ring
  rw [hleft, hright]
  unfold firstReduced
  ring

private theorem integrand_eq_quarter_pair (x : ℝ) :
    integrand x =
      (1 / 4 : ℝ) * leftReduced x - (1 / 4 : ℝ) * rightReduced x := by
  rw [integrand_eq_half_first, first_eq_half_pair]
  ring

private def rightPrimitive (x : ℝ) :=
  -(6 / 11 : ℝ) * Real.cos ((11 / 6 : ℝ) * x) +
    (6 / 5 : ℝ) * Real.cos ((5 / 6 : ℝ) * x)

private theorem hasDerivAt_rightPrimitive (x : ℝ) :
    HasDerivAt rightPrimitive (rightReduced x) x := by
  have h11 :=
    (Real.hasDerivAt_cos ((11 / 6 : ℝ) * x)).comp x
      ((hasDerivAt_id x).const_mul (11 / 6 : ℝ))
  have h5 :=
    (Real.hasDerivAt_cos ((5 / 6 : ℝ) * x)).comp x
      ((hasDerivAt_id x).const_mul (5 / 6 : ℝ))
  unfold rightPrimitive rightReduced
  convert (h11.const_mul (-(6 / 11 : ℝ))).add
    (h5.const_mul (6 / 5 : ℝ)) using 1 <;> ring

private theorem hasDerivAt_primitive (x : ℝ) :
    HasDerivAt primitive (integrand x) x := by
  have h7 :=
    (Real.hasDerivAt_cos ((7 / 6 : ℝ) * x)).comp x
      ((hasDerivAt_id x).const_mul (7 / 6 : ℝ))
  have h1 :=
    (Real.hasDerivAt_cos (x / 6)).comp x
      ((hasDerivAt_id x).div_const 6)
  have h11 :=
    (Real.hasDerivAt_cos ((11 / 6 : ℝ) * x)).comp x
      ((hasDerivAt_id x).const_mul (11 / 6 : ℝ))
  have h5 :=
    (Real.hasDerivAt_cos ((5 / 6 : ℝ) * x)).comp x
      ((hasDerivAt_id x).const_mul (5 / 6 : ℝ))
  unfold primitive
  convert
    ((((h7.const_mul (-(3 / 14 : ℝ))).add
      (h1.const_mul (3 / 2 : ℝ))).add
      (h11.const_mul (3 / 22 : ℝ))).sub
      (h5.const_mul (3 / 10 : ℝ))) using 1
  rw [integrand_eq_quarter_pair]
  unfold leftReduced rightReduced
  ring

theorem gap1 : Family integrand = ScaledFamily firstReduced (1 / 2) := by
  apply Set.ext
  intro F
  simp only [Family, ScaledFamily, Set.mem_setOf_eq]
  constructor
  · intro hF
    refine ⟨fun x => 2 * F x, ?_, ?_⟩
    · intro x
      convert (hF x).const_mul 2 using 1
      rw [integrand_eq_half_first]
      ring
    · intro x
      ring
  · rintro ⟨G, hG, hEq⟩
    intro x
    have hfun : F = fun y => (1 / 2 : ℝ) * G y := funext hEq
    rw [hfun]
    convert (hG x).const_mul (1 / 2 : ℝ) using 1
    exact integrand_eq_half_first x
theorem gap2 : Family integrand = PairFamily leftReduced rightReduced := by
  apply Set.ext
  intro F
  simp only [Family, PairFamily, Set.mem_setOf_eq]
  constructor
  · intro hF
    refine ⟨fun x => 4 * F x + rightPrimitive x, ?_, rightPrimitive, ?_, ?_⟩
    · intro x
      convert ((hF x).const_mul 4).add (hasDerivAt_rightPrimitive x) using 1
      rw [integrand_eq_quarter_pair]
      ring
    · exact hasDerivAt_rightPrimitive
    · intro x
      ring
  · rintro ⟨P, hP, Q, hQ, hEq⟩
    intro x
    have hfun : F = fun y => (1 / 4 : ℝ) * P y - (1 / 4 : ℝ) * Q y :=
      funext hEq
    rw [hfun]
    convert ((hP x).const_mul (1 / 4 : ℝ)).sub
      ((hQ x).const_mul (1 / 4 : ℝ)) using 1
    exact integrand_eq_quarter_pair x
theorem gap3 : Family integrand = Translates primitive := by
  apply Set.ext
  intro F
  simp only [Family, Translates, Set.mem_setOf_eq]
  constructor
  · intro hF
    have hzero : ∀ x, HasDerivAt (fun y => F y - primitive y) 0 x := by
      intro x
      convert (hF x).sub (hasDerivAt_primitive x) using 1 <;> ring
    have hdiff : Differentiable ℝ (fun y => F y - primitive y) :=
      fun x => (hzero x).differentiableAt
    have hderiv : ∀ x, deriv (fun y => F y - primitive y) x = 0 :=
      fun x => (hzero x).deriv
    refine ⟨F 0 - primitive 0, ?_⟩
    intro x
    have hc := is_const_of_deriv_eq_zero hdiff hderiv x 0
    calc
      F x = primitive x + (F x - primitive x) := by ring
      _ = primitive x + (F 0 - primitive 0) := by rw [hc]
  · rintro ⟨C, hEq⟩
    intro x
    have hfun : F = fun y => primitive y + C := funext hEq
    rw [hfun]
    simpa using (hasDerivAt_primitive x).add_const C

end
end ProofGap.Exercise2015
