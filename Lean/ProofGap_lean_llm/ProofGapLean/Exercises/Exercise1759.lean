import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1759

noncomputable section

def original (x : ℝ) : ℝ := 1 / (1 + Real.exp x)
def reduced (x : ℝ) : ℝ := 1 - Real.exp x / (1 + Real.exp x)
def primitive (x : ℝ) : ℝ := x - Real.log (1 + Real.exp x)
def Antiderivatives (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | Differentiable ℝ F ∧ ∀ x, deriv F x = g x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x, F x = p x + C}

private theorem primitive_hasDerivAt (x : ℝ) :
    HasDerivAt primitive (reduced x) x := by
  have hne : 1 + Real.exp x ≠ 0 := by positivity
  simpa [primitive, reduced, div_eq_mul_inv, mul_comm] using
    (hasDerivAt_id x).sub
      ((Real.hasDerivAt_log hne).comp x
        ((Real.hasDerivAt_exp x).const_add 1))

theorem gap1 : Antiderivatives original = Antiderivatives reduced := by
  have hfun : original = reduced := by
    funext x
    unfold original reduced
    have hne : 1 + Real.exp x ≠ 0 := by positivity
    field_simp [hne] <;> ring
  rw [hfun]

theorem gap2 : Antiderivatives reduced = PrimitiveFamily primitive := by
  ext F
  change
    (Differentiable ℝ F ∧ ∀ x, deriv F x = reduced x) ↔
      ∃ C : ℝ, ∀ x, F x = primitive x + C
  constructor
  · rintro ⟨hFd, hDer⟩
    have hzero (x : ℝ) :
        HasDerivAt (fun y => F y - primitive y) 0 x := by
      simpa [hDer x] using
        (hFd x).hasDerivAt.sub (primitive_hasDerivAt x)
    have hdiff : Differentiable ℝ (fun x => F x - primitive x) :=
      fun x => (hzero x).differentiableAt
    have hmono : Monotone (fun x => F x - primitive x) :=
      monotone_of_deriv_nonneg hdiff (fun x => (hzero x).deriv.ge)
    have hanti : Antitone (fun x => F x - primitive x) :=
      antitone_of_deriv_nonpos hdiff (fun x => (hzero x).deriv.le)
    have hconst : ∀ x, F x - primitive x = F 0 - primitive 0 := by
      intro x
      rcases le_total x 0 with hx | hx
      · exact le_antisymm (hmono hx) (hanti hx)
      · exact le_antisymm (hanti hx) (hmono hx)
    refine ⟨F 0 - primitive 0, ?_⟩
    intro x
    simpa [add_comm] using (sub_eq_iff_eq_add.mp (hconst x))
  · rintro ⟨C, hC⟩
    have hEq : F = fun x => primitive x + C := funext hC
    rw [hEq]
    constructor
    · exact fun x => ((primitive_hasDerivAt x).add_const C).differentiableAt
    · intro x
      exact ((primitive_hasDerivAt x).add_const C).deriv

theorem gap3 : Antiderivatives original = PrimitiveFamily primitive := by
  exact gap1.trans gap2

end
end ProofGap.Exercise1759
