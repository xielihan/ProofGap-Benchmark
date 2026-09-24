import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1745

noncomputable section

def original (x : ℝ) : ℝ := Real.cos (x / 2) * Real.cos (x / 3)
def reduced (x : ℝ) : ℝ :=
  (1 / 2) * (Real.cos (5 * x / 6) + Real.cos (x / 6))
def primitive (x : ℝ) : ℝ :=
  (3 / 5) * Real.sin (5 * x / 6) + 3 * Real.sin (x / 6)
def Antiderivatives (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | Differentiable ℝ F ∧ ∀ x, deriv F x = g x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x, F x = p x + C}

private theorem original_eq_reduced : original = reduced := by
  funext x
  unfold original reduced
  rw [show 5 * x / 6 = x / 2 + x / 3 by ring]
  rw [show x / 6 = x / 2 - x / 3 by ring]
  rw [Real.cos_add, Real.cos_sub]
  ring

private theorem primitive_hasDerivAt (x : ℝ) :
    HasDerivAt primitive (reduced x) x := by
  unfold primitive reduced
  convert
    ((((Real.hasDerivAt_sin (5 * x / 6)).comp x
          (((hasDerivAt_id x).const_mul 5).div_const 6)).const_mul (3 / 5)).add
      (((Real.hasDerivAt_sin (x / 6)).comp x
          ((hasDerivAt_id x).div_const 6)).const_mul 3)) using 1 <;> ring

private theorem differentiable_eq_add_const
    (f p : ℝ → ℝ) (hf : Differentiable ℝ f) (hp : Differentiable ℝ p)
    (hderiv : ∀ x, deriv f x = deriv p x) :
    ∃ C : ℝ, ∀ x, f x = p x + C := by
  let q : ℝ → ℝ := fun x => f x - p x
  have hqdiff : Differentiable ℝ q := hf.sub hp
  have hqzero : ∀ x, deriv q x = 0 := by
    intro x
    have h := ((hf x).hasDerivAt.sub (hp x).hasDerivAt).deriv
    simpa [q, hderiv x] using h
  refine ⟨f 0 - p 0, ?_⟩
  intro x
  have hx : q x = q 0 :=
    is_const_of_deriv_eq_zero hqdiff hqzero x 0
  dsimp [q] at hx
  linarith

theorem gap1 : Antiderivatives original = Antiderivatives reduced := by
  rw [original_eq_reduced]

theorem gap2 : Antiderivatives reduced = PrimitiveFamily primitive := by
  ext F
  constructor
  · rintro ⟨hFdiff, hFderiv⟩
    exact differentiable_eq_add_const F primitive hFdiff
      (fun x => (primitive_hasDerivAt x).differentiableAt)
      (fun x => by rw [hFderiv x, (primitive_hasDerivAt x).deriv])
  · rintro ⟨C, hC⟩
    have hEq : F = fun x => primitive x + C := funext hC
    subst F
    constructor
    · exact fun x => ((primitive_hasDerivAt x).add_const C).differentiableAt
    · intro x
      exact ((primitive_hasDerivAt x).add_const C).deriv

theorem gap3 : Antiderivatives original = PrimitiveFamily primitive := by
  calc
    Antiderivatives original = Antiderivatives reduced := gap1
    _ = PrimitiveFamily primitive := gap2

end
end ProofGap.Exercise1745
