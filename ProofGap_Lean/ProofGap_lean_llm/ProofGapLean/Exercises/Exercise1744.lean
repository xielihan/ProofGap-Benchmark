import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1744

noncomputable section

def original (x : ℝ) : ℝ := Real.sin (3 * x) * Real.sin (5 * x)
def reduced (x : ℝ) : ℝ := (1 / 2) * (Real.cos (2 * x) - Real.cos (8 * x))
def primitive (x : ℝ) : ℝ :=
  (1 / 4) * Real.sin (2 * x) - (1 / 16) * Real.sin (8 * x)
def Antiderivatives (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | Differentiable ℝ F ∧ ∀ x, deriv F x = g x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x, F x = p x + C}

private theorem primitive_hasDerivAt (x : ℝ) :
    HasDerivAt primitive (reduced x) x := by
  unfold primitive reduced
  convert
    (((((hasDerivAt_id x).const_mul 2).sin).const_mul (1 / 4)).sub
      ((((hasDerivAt_id x).const_mul 8).sin).const_mul (1 / 16))) using 1 <;>
    simp only [id_eq] <;> ring

theorem gap1 : Antiderivatives original = Antiderivatives reduced := by
  have h : original = reduced := by
    funext x
    unfold original reduced
    rw [show 2 * x = -(3 * x - 5 * x) by ring, Real.cos_neg,
      Real.cos_sub, show 8 * x = 3 * x + 5 * x by ring, Real.cos_add]
    ring
  rw [h]

theorem gap2 : Antiderivatives reduced = PrimitiveFamily primitive := by
  ext F
  change (Differentiable ℝ F ∧ ∀ x, deriv F x = reduced x) ↔
    ∃ C : ℝ, ∀ x, F x = primitive x + C
  constructor
  · rintro ⟨hFdiff, hFderiv⟩
    have hZero : ∀ x, HasDerivAt (fun y => F y - primitive y) 0 x := by
      intro x
      have hx := (hFdiff x).hasDerivAt.sub (primitive_hasDerivAt x)
      convert hx using 1
      rw [hFderiv x]
      ring
    have hDiff : Differentiable ℝ (fun y => F y - primitive y) :=
      fun x => (hZero x).differentiableAt
    have hDeriv : ∀ x, deriv (fun y => F y - primitive y) x = 0 :=
      fun x => (hZero x).deriv
    refine ⟨F 0 - primitive 0, ?_⟩
    intro x
    have heq : F x - primitive x = F 0 - primitive 0 :=
      (is_const_of_deriv_eq_zero hDiff hDeriv) x 0
    linarith
  · rintro ⟨C, hF⟩
    have hfun : F = fun x => primitive x + C := funext hF
    have hAt : ∀ x, HasDerivAt F (reduced x) x := by
      intro x
      rw [hfun]
      exact (primitive_hasDerivAt x).add_const C
    exact ⟨fun x => (hAt x).differentiableAt, fun x => (hAt x).deriv⟩

theorem gap3 : Antiderivatives original = PrimitiveFamily primitive := by
  exact gap1.trans gap2

end
end ProofGap.Exercise1744
