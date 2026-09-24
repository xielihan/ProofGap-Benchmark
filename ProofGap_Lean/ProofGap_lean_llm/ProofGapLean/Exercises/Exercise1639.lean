import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace ProofGap.Exercise1639

noncomputable section

def original (x : ℝ) : ℝ := x ^ 2 / (1 + x ^ 2)
def simple (x : ℝ) : ℝ := 1 - 1 / (x ^ 2 + 1)
def primitive (x : ℝ) : ℝ := x - Real.arctan x
def Antiderivatives (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | Differentiable ℝ F ∧ ∀ x, deriv F x = g x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x, F x = p x + C}

theorem gap1 : Antiderivatives original = Antiderivatives simple := by
  have h : original = simple := by
    funext x
    unfold original simple
    have hx : x ^ 2 + 1 ≠ 0 := by positivity
    rw [show 1 + x ^ 2 = x ^ 2 + 1 by ring]
    field_simp [hx]
    ring
  rw [h]

theorem gap2 : Antiderivatives simple = PrimitiveFamily primitive := by
  have hp_at : ∀ x, HasDerivAt primitive (simple x) x := by
    intro x
    simpa [primitive, simple, div_eq_mul_inv, add_comm] using
      (hasDerivAt_id x).sub (Real.hasDerivAt_arctan x)
  have hp : Differentiable ℝ primitive := by
    intro x
    exact (hp_at x).differentiableAt
  apply Set.ext
  intro F
  simp only [Antiderivatives, PrimitiveFamily, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hF, hderiv⟩
    let H : ℝ → ℝ := fun x => F x - primitive x
    have hH : Differentiable ℝ H := hF.sub hp
    have hHderiv : ∀ x, deriv H x = 0 := by
      intro x
      simpa [H, hderiv x] using
        (hF.differentiableAt.hasDerivAt.sub (hp_at x)).deriv
    have hmono : Monotone H := by
      apply monotone_of_deriv_nonneg hH
      intro x
      rw [hHderiv x]
    have hanti : Antitone H := by
      apply antitone_of_deriv_nonpos hH
      intro x
      rw [hHderiv x]
    refine ⟨H 0, ?_⟩
    intro x
    have hx : H x = H 0 := by
      rcases le_total x 0 with hx0 | h0x
      · exact le_antisymm (hmono hx0) (hanti hx0)
      · exact le_antisymm (hanti h0x) (hmono h0x)
    dsimp [H] at hx ⊢
    linarith
  · rintro ⟨C, hFC⟩
    have heq : F = fun x => primitive x + C := by
      funext x
      exact hFC x
    rw [heq]
    constructor
    · exact hp.add (differentiable_const C)
    · intro x
      exact ((hp_at x).add_const C).deriv

theorem gap3 : Antiderivatives original = PrimitiveFamily primitive := by
  rw [gap1, gap2]

end
end ProofGap.Exercise1639
