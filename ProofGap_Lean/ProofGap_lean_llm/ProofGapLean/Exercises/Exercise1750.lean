import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1750

noncomputable section

def original (x : ℝ) : ℝ := Real.cos x ^ 4
def squared (x : ℝ) : ℝ := ((1 + Real.cos (2 * x)) / 2) ^ 2
def expanded (x : ℝ) : ℝ :=
  (1 / 4) * (1 + 2 * Real.cos (2 * x) +
    (1 + Real.cos (4 * x)) / 2)
def reduced (x : ℝ) : ℝ :=
  (1 / 8) * (3 + 4 * Real.cos (2 * x) + Real.cos (4 * x))
def primitive (x : ℝ) : ℝ :=
  (3 / 8) * x + (1 / 4) * Real.sin (2 * x) +
    (1 / 32) * Real.sin (4 * x)
def Antiderivatives (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | Differentiable ℝ F ∧ ∀ x, deriv F x = g x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x, F x = p x + C}

private theorem primitive_hasDerivAt (x : ℝ) :
    HasDerivAt primitive (reduced x) x := by
  have h1 := (hasDerivAt_id x).const_mul (3 / 8 : ℝ)
  have h2 :=
    ((Real.hasDerivAt_sin (2 * x)).comp x
      ((hasDerivAt_id x).const_mul (2 : ℝ))).const_mul (1 / 4 : ℝ)
  have h3 :=
    ((Real.hasDerivAt_sin (4 * x)).comp x
      ((hasDerivAt_id x).const_mul (4 : ℝ))).const_mul (1 / 32 : ℝ)
  have h := (h1.add h2).add h3
  convert h using 1 <;> simp [primitive, reduced] <;> ring

theorem gap1 : Antiderivatives original = Antiderivatives squared := by
  apply congrArg Antiderivatives
  funext x
  unfold original squared
  rw [Real.cos_two_mul]
  ring

theorem gap2 : Antiderivatives squared = Antiderivatives expanded := by
  apply congrArg Antiderivatives
  funext x
  unfold squared expanded
  have hcos :
      Real.cos (4 * x) = 2 * Real.cos (2 * x) ^ 2 - 1 := by
    rw [show (4 : ℝ) * x = 2 * (2 * x) by ring]
    exact Real.cos_two_mul (2 * x)
  rw [hcos]
  ring

theorem gap3 : Antiderivatives original = Antiderivatives expanded := by
  exact gap1.trans gap2

theorem gap4 : Antiderivatives original = Antiderivatives reduced := by
  calc
    Antiderivatives original = Antiderivatives expanded := gap3
    _ = Antiderivatives reduced := by
      apply congrArg Antiderivatives
      funext x
      unfold expanded reduced
      ring

theorem gap5 : Antiderivatives reduced = PrimitiveFamily primitive := by
  ext F
  change
    (Differentiable ℝ F ∧ ∀ x, deriv F x = reduced x) ↔
      ∃ C : ℝ, ∀ x, F x = primitive x + C
  constructor
  · rintro ⟨hFdiff, hFderiv⟩
    let H : ℝ → ℝ := fun x => F x - primitive x
    have hHzero : ∀ x, HasDerivAt H 0 x := by
      intro x
      simpa [H, hFderiv x] using
        ((hFdiff x).hasDerivAt.sub (primitive_hasDerivAt x))
    have hHdiff : Differentiable ℝ H :=
      fun x => (hHzero x).differentiableAt
    have hHderiv : ∀ x, deriv H x = 0 :=
      fun x => (hHzero x).deriv
    have hmono : Monotone H :=
      monotone_of_deriv_nonneg hHdiff (fun x => by simp [hHderiv x])
    have hanti : Antitone H :=
      antitone_of_deriv_nonpos hHdiff (fun x => by simp [hHderiv x])
    refine ⟨H 0, ?_⟩
    intro x
    have hx0 : H x = H 0 := by
      rcases le_total x 0 with hx | hx
      · exact le_antisymm (hmono hx) (hanti hx)
      · exact le_antisymm (hanti hx) (hmono hx)
    dsimp [H] at hx0 ⊢
    linarith
  · rintro ⟨C, hC⟩
    have hEq : F = fun x => primitive x + C := funext hC
    subst F
    constructor
    · intro x
      exact ((primitive_hasDerivAt x).add_const C).differentiableAt
    · intro x
      exact ((primitive_hasDerivAt x).add_const C).deriv

theorem gap6 : Antiderivatives original = PrimitiveFamily primitive := by
  exact gap4.trans gap5

end
end ProofGap.Exercise1750
