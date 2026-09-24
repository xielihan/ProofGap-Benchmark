import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1797

noncomputable section

def integrand (x : ℝ) : ℝ := x ^ 3 * Real.exp (-x ^ 2)
def primitive (x : ℝ) : ℝ :=
  -(x ^ 2 + 1) / 2 * Real.exp (-x ^ 2)
def IsAntiderivative (F f : ℝ → ℝ) : Prop := ∀ x, HasDerivAt F (f x) x
def Family (f : ℝ → ℝ) : Set (ℝ → ℝ) := {F | IsAntiderivative F f}
def Translates (P : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C, ∀ x, F x = P x + C}

theorem gap1 (x : ℝ) :
    HasDerivAt (fun y => Real.exp (-y ^ 2))
      (-2 * x * Real.exp (-x ^ 2)) x := by
  have hsq : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    convert (hasDerivAt_id x).pow 2 using 1 <;> simp [id_eq] <;> ring
  convert (Real.hasDerivAt_exp (-x ^ 2)).comp x hsq.neg using 1 <;> ring

theorem gap2 (x : ℝ) :
    HasDerivAt
      (fun y => -(1 / 2 : ℝ) * y ^ 2 * Real.exp (-y ^ 2))
      (integrand x - x * Real.exp (-x ^ 2)) x := by
  convert (((hasDerivAt_id x).pow 2).const_mul (-(1 / 2 : ℝ))).mul
      (gap1 x) using 1 <;> simp [integrand] <;> ring

theorem gap3 (x : ℝ) :
    HasDerivAt
      (fun y => -(1 / 2 : ℝ) * Real.exp (-y ^ 2))
      (x * Real.exp (-x ^ 2)) x := by
  convert (gap1 x).const_mul (-(1 / 2 : ℝ)) using 1 <;> ring

theorem gap4 (x : ℝ) :
    -(1 / 2 : ℝ) * x ^ 2 * Real.exp (-x ^ 2) -
        (1 / 2 : ℝ) * Real.exp (-x ^ 2) =
      primitive x := by
  unfold primitive
  ring

theorem gap5 :
    Family integrand = Translates primitive := by
  have hprim : IsAntiderivative primitive integrand := by
    intro x
    have hfun :
        (fun y : ℝ =>
          -(1 / 2 : ℝ) * y ^ 2 * Real.exp (-y ^ 2) +
            -(1 / 2 : ℝ) * Real.exp (-y ^ 2)) = primitive := by
      funext y
      rw [← gap4 y]
      ring
    rw [← hfun]
    simpa using (gap2 x).add (gap3 x)
  ext F
  constructor
  · intro hF
    change IsAntiderivative F integrand at hF
    change ∃ C, ∀ x, F x = primitive x + C
    let g : ℝ → ℝ := fun y => F y - primitive y
    have hzero : ∀ x, HasDerivAt g 0 x := by
      intro x
      simpa [g] using (hF x).sub (hprim x)
    have hgdiff : Differentiable ℝ g := fun x => (hzero x).differentiableAt
    have hgderiv : ∀ x, deriv g x = 0 := fun x => (hzero x).deriv
    have hconst : ∀ a b : ℝ, g a = g b :=
      is_const_of_deriv_eq_zero hgdiff hgderiv
    refine ⟨F 0 - primitive 0, ?_⟩
    intro x
    have hx := hconst x 0
    dsimp [g] at hx
    calc
      F x = primitive x + (F x - primitive x) := by ring
      _ = primitive x + (F 0 - primitive 0) := by rw [hx]
  · intro hF
    change ∃ C, ∀ x, F x = primitive x + C at hF
    rcases hF with ⟨C, hC⟩
    change IsAntiderivative F integrand
    intro x
    convert (hprim x).add (hasDerivAt_const x C) using 1
    · funext y
      simpa using hC y
    · ring

end

end ProofGap.Exercise1797
