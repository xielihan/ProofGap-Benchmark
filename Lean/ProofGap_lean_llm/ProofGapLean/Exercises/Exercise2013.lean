import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2013
noncomputable section

def integrand (x : ℝ) := Real.sin (5 * x) * Real.cos x
def reduced (x : ℝ) := Real.sin (4 * x) + Real.sin (6 * x)
def primitive (x : ℝ) := -(1 / 8 : ℝ) * Real.cos (4 * x) -
  (1 / 12 : ℝ) * Real.cos (6 * x)
def Family (f : ℝ → ℝ) := {F : ℝ → ℝ | ∀ x, HasDerivAt F (f x) x}
def ScaledFamily (f : ℝ → ℝ) (c : ℝ) :=
  {F : ℝ → ℝ | ∃ G ∈ Family f, ∀ x, F x = c * G x}
def Translates (p : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ C, ∀ x, F x = p x + C}

private lemma reduced_eq_two_integrand (x : ℝ) :
    reduced x = 2 * integrand x := by
  unfold reduced integrand
  rw [show 4 * x = 5 * x - x by ring,
      show 6 * x = 5 * x + x by ring,
      Real.sin_sub, Real.sin_add]
  ring

private lemma hasDerivAt_primitive (x : ℝ) :
    HasDerivAt primitive (integrand x) x := by
  have h4 : HasDerivAt (fun y : ℝ => Real.cos (4 * y))
      (-4 * Real.sin (4 * x)) x := by
    convert (Real.hasDerivAt_cos (4 * x)).comp x
      ((hasDerivAt_id x).const_mul (4 : ℝ)) using 1 <;>
      simp <;> ring
  have h6 : HasDerivAt (fun y : ℝ => Real.cos (6 * y))
      (-6 * Real.sin (6 * x)) x := by
    convert (Real.hasDerivAt_cos (6 * x)).comp x
      ((hasDerivAt_id x).const_mul (6 : ℝ)) using 1 <;>
      simp <;> ring
  have hval :
      (-(1 / 8 : ℝ)) * (-4 * Real.sin (4 * x)) -
          (1 / 12 : ℝ) * (-6 * Real.sin (6 * x)) = integrand x := by
    calc
      (-(1 / 8 : ℝ)) * (-4 * Real.sin (4 * x)) -
          (1 / 12 : ℝ) * (-6 * Real.sin (6 * x)) =
          (1 / 2 : ℝ) * reduced x := by
            unfold reduced
            ring
      _ = integrand x := by
        rw [reduced_eq_two_integrand]
        ring
  have h := (h4.const_mul (-(1 / 8 : ℝ))).sub
    (h6.const_mul (1 / 12 : ℝ))
  rw [hval] at h
  change HasDerivAt
    (fun y : ℝ =>
      -(1 / 8 : ℝ) * Real.cos (4 * y) -
        (1 / 12 : ℝ) * Real.cos (6 * y))
    (integrand x) x
  exact h

theorem gap1 : Family integrand = ScaledFamily reduced (1 / 2) := by
  apply Set.ext
  intro F
  constructor
  · intro hF
    refine ⟨fun x => 2 * F x, ?_, ?_⟩
    · intro x
      simpa only [reduced_eq_two_integrand] using
        (hF x).const_mul (2 : ℝ)
    · intro x
      ring
  · rintro ⟨G, hG, hFG⟩
    intro x
    have hfun : F = fun y => (1 / 2 : ℝ) * G y := funext hFG
    rw [hfun]
    convert (hG x).const_mul (1 / 2 : ℝ) using 1
    rw [reduced_eq_two_integrand]
    ring
theorem gap2 : Family integrand = Translates primitive := by
  apply Set.ext
  intro F
  constructor
  · intro hF
    let H : ℝ → ℝ := fun x => F x - primitive x
    have hH : ∀ x, HasDerivAt H 0 x := by
      intro x
      dsimp [H]
      convert (hF x).sub (hasDerivAt_primitive x) using 1 <;> ring
    have hdiff : Differentiable ℝ H :=
      fun x => (hH x).differentiableAt
    have hderiv : ∀ x, deriv H x = 0 :=
      fun x => (hH x).deriv
    refine ⟨H 0, ?_⟩
    intro x
    have hc : H x = H 0 :=
      is_const_of_deriv_eq_zero hdiff hderiv x 0
    dsimp [H] at hc ⊢
    linarith
  · rintro ⟨C, hFC⟩
    intro x
    have hfun : F = fun y => primitive y + C := funext hFC
    have hp : HasDerivAt (fun y : ℝ => primitive y + C) (integrand x) x :=
      (hasDerivAt_primitive x).add_const C
    exact hfun.symm ▸ hp

end
end ProofGap.Exercise2013
