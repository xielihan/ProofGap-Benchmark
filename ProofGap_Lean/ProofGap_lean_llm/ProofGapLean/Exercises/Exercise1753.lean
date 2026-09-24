import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1753

noncomputable section

def original (x : ℝ) : ℝ := Real.sin (3 * x) ^ 2 * Real.sin (2 * x) ^ 3
def firstExpansion (x : ℝ) : ℝ :=
  (1 / 2) * (1 - Real.cos (6 * x)) *
    (1 / 4) * (3 * Real.sin (2 * x) - Real.sin (6 * x))
def secondExpansion (x : ℝ) : ℝ :=
  (1 / 8) * (3 * Real.sin (2 * x) -
    3 * Real.cos (6 * x) * Real.sin (2 * x) -
    Real.sin (6 * x) + Real.sin (6 * x) * Real.cos (6 * x))
def reduced (x : ℝ) : ℝ :=
  (3 / 8) * Real.sin (2 * x) + (3 / 16) * Real.sin (4 * x) -
    (1 / 8) * Real.sin (6 * x) - (3 / 16) * Real.sin (8 * x) +
    (1 / 16) * Real.sin (12 * x)
def primitive (x : ℝ) : ℝ :=
  -(3 / 16) * Real.cos (2 * x) - (3 / 64) * Real.cos (4 * x) +
    (1 / 48) * Real.cos (6 * x) + (3 / 128) * Real.cos (8 * x) -
    (1 / 192) * Real.cos (12 * x)
def Antiderivatives (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | Differentiable ℝ F ∧ ∀ x, deriv F x = g x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x, F x = p x + C}

private theorem primitive_hasDerivAt (x : ℝ) :
    HasDerivAt primitive (reduced x) x := by
  have h₂ :
      HasDerivAt (fun y : ℝ => -(3 / 16 : ℝ) * Real.cos (2 * y))
        ((3 / 8 : ℝ) * Real.sin (2 * x)) x := by
    convert
      ((Real.hasDerivAt_cos (2 * x)).comp x
        ((hasDerivAt_id x).const_mul 2)).const_mul (-(3 / 16 : ℝ)) using 1 <;>
      ring
  have h₄ :
      HasDerivAt (fun y : ℝ => (3 / 64 : ℝ) * Real.cos (4 * y))
        (-(3 / 16 : ℝ) * Real.sin (4 * x)) x := by
    convert
      ((Real.hasDerivAt_cos (4 * x)).comp x
        ((hasDerivAt_id x).const_mul 4)).const_mul (3 / 64 : ℝ) using 1 <;>
      ring
  have h₆ :
      HasDerivAt (fun y : ℝ => (1 / 48 : ℝ) * Real.cos (6 * y))
        (-(1 / 8 : ℝ) * Real.sin (6 * x)) x := by
    convert
      ((Real.hasDerivAt_cos (6 * x)).comp x
        ((hasDerivAt_id x).const_mul 6)).const_mul (1 / 48 : ℝ) using 1 <;>
      ring
  have h₈ :
      HasDerivAt (fun y : ℝ => (3 / 128 : ℝ) * Real.cos (8 * y))
        (-(3 / 16 : ℝ) * Real.sin (8 * x)) x := by
    convert
      ((Real.hasDerivAt_cos (8 * x)).comp x
        ((hasDerivAt_id x).const_mul 8)).const_mul (3 / 128 : ℝ) using 1 <;>
      ring
  have h₁₂ :
      HasDerivAt (fun y : ℝ => (1 / 192 : ℝ) * Real.cos (12 * y))
        (-(1 / 16 : ℝ) * Real.sin (12 * x)) x := by
    convert
      ((Real.hasDerivAt_cos (12 * x)).comp x
        ((hasDerivAt_id x).const_mul 12)).const_mul (1 / 192 : ℝ) using 1 <;>
      ring
  unfold primitive reduced
  convert ((((h₂.sub h₄).add h₆).add h₈).sub h₁₂) using 1 <;> ring

private theorem eq_of_deriv_eq_zero {f : ℝ → ℝ}
    (hf : Differentiable ℝ f) (hzero : ∀ x, deriv f x = 0)
    (x y : ℝ) : f x = f y := by
  exact is_const_of_deriv_eq_zero hf hzero x y

theorem gap1 (x : ℝ) : original x = firstExpansion x := by
  have hc : Real.cos (6 * x) = 1 - 2 * Real.sin (3 * x) ^ 2 := by
    rw [show 6 * x = 2 * (3 * x) by ring, Real.cos_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq (3 * x)]
  have hs : Real.sin (6 * x) = 3 * Real.sin (2 * x) - 4 * Real.sin (2 * x) ^ 3 := by
    rw [show 6 * x = 3 * (2 * x) by ring, Real.sin_three_mul]
  unfold original firstExpansion
  rw [hc, hs]
  ring

theorem gap2 (x : ℝ) : original x = secondExpansion x := by
  calc
    original x = firstExpansion x := gap1 x
    _ = secondExpansion x := by
      unfold firstExpansion secondExpansion
      ring

theorem gap3 (x : ℝ) : secondExpansion x = reduced x := by
  have hprod₁ :
      Real.cos (6 * x) * Real.sin (2 * x) =
        (Real.sin (8 * x) - Real.sin (4 * x)) / 2 := by
    rw [show 8 * x = 6 * x + 2 * x by ring, Real.sin_add,
      show 4 * x = 6 * x - 2 * x by ring, Real.sin_sub]
    ring
  have hscaled₁ :
      3 * Real.cos (6 * x) * Real.sin (2 * x) =
        3 * ((Real.sin (8 * x) - Real.sin (4 * x)) / 2) := by
    calc
      3 * Real.cos (6 * x) * Real.sin (2 * x) =
          3 * (Real.cos (6 * x) * Real.sin (2 * x)) := by ring
      _ = 3 * ((Real.sin (8 * x) - Real.sin (4 * x)) / 2) := by
        rw [hprod₁]
  have hprod₂ :
      Real.sin (6 * x) * Real.cos (6 * x) = Real.sin (12 * x) / 2 := by
    rw [show 12 * x = 2 * (6 * x) by ring, Real.sin_two_mul]
    ring
  unfold secondExpansion reduced
  rw [hscaled₁, hprod₂]
  ring

theorem gap4 (x : ℝ) : original x = reduced x := by
  calc
    original x = secondExpansion x := gap2 x
    _ = reduced x := gap3 x

theorem gap5 : Antiderivatives original = PrimitiveFamily primitive := by
  ext F
  change
    (Differentiable ℝ F ∧ ∀ x, deriv F x = original x) ↔
      ∃ C : ℝ, ∀ x, F x = primitive x + C
  have hp : Differentiable ℝ primitive :=
    fun x => (primitive_hasDerivAt x).differentiableAt
  constructor
  · rintro ⟨hF, hderiv⟩
    have hdiff : Differentiable ℝ (fun x => F x - primitive x) := hF.sub hp
    have hzero : ∀ x, deriv (fun y => F y - primitive y) x = 0 := by
      intro x
      have hz : HasDerivAt (fun y => F y - primitive y) 0 x := by
        convert (hF x).hasDerivAt.sub (primitive_hasDerivAt x) using 1 <;>
          simp [hderiv x, gap4 x]
      exact hz.deriv
    refine ⟨F 0 - primitive 0, ?_⟩
    intro x
    have hc := eq_of_deriv_eq_zero hdiff hzero x 0
    exact (sub_eq_iff_eq_add.mp hc).trans (by ring)
  · rintro ⟨C, hC⟩
    have hFC : F = fun x => primitive x + C := funext hC
    constructor
    · rw [hFC]
      exact hp.add (differentiable_const C)
    · intro x
      rw [hFC]
      calc
        deriv (fun y => primitive y + C) x = reduced x :=
          ((primitive_hasDerivAt x).add_const C).deriv
        _ = original x := (gap4 x).symm

end
end ProofGap.Exercise1753
