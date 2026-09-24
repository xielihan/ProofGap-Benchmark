import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1646

noncomputable section

def original (x : ℝ) : ℝ :=
  (Real.exp (3 * x) + 1) / (Real.exp x + 1)
def simple (x : ℝ) : ℝ := Real.exp (2 * x) - Real.exp x + 1
def primitive (x : ℝ) : ℝ :=
  (1 / 2) * Real.exp (2 * x) - Real.exp x + x
def Antiderivatives (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | Differentiable ℝ F ∧ ∀ x, deriv F x = g x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x, F x = p x + C}

private theorem primitive_hasDerivAt (x : ℝ) :
    HasDerivAt primitive (simple x) x := by
  have he2 : HasDerivAt (fun y : ℝ => Real.exp (2 * y))
      (Real.exp (2 * x) * 2) x := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_exp (2 * x)).comp x
        ((hasDerivAt_id x).const_mul 2)
  unfold primitive simple
  convert (((he2.const_mul (1 / 2)).sub
    (Real.hasDerivAt_exp x)).add (hasDerivAt_id x)) using 1 <;> ring

theorem gap1 : Antiderivatives original = Antiderivatives simple := by
  apply congrArg Antiderivatives
  funext x
  unfold original simple
  have hne : Real.exp x + 1 ≠ 0 := by positivity
  rw [show 3 * x = (x + x) + x by ring,
    show 2 * x = x + x by ring]
  simp only [Real.exp_add]
  field_simp [hne]
  ring

theorem gap2 : Antiderivatives simple = PrimitiveFamily primitive := by
  ext F
  constructor
  · rintro ⟨hF, hderiv⟩
    have hzero : ∀ x, HasDerivAt (fun y => F y - primitive y) 0 x := by
      intro x
      simpa [hderiv x] using
        (hF x).hasDerivAt.sub (primitive_hasDerivAt x)
    have hdiff : Differentiable ℝ (fun x => F x - primitive x) := by
      intro x
      exact (hzero x).differentiableAt
    refine ⟨F 0 - primitive 0, ?_⟩
    intro x
    have hc : F x - primitive x = F 0 - primitive 0 :=
      is_const_of_deriv_eq_zero hdiff (fun y => (hzero y).deriv) x 0
    linarith
  · rintro ⟨C, hC⟩
    have hEq : F = fun x => primitive x + C := by
      funext x
      exact hC x
    subst F
    constructor
    · intro x
      exact ((primitive_hasDerivAt x).add_const C).differentiableAt
    · intro x
      exact ((primitive_hasDerivAt x).add_const C).deriv

theorem gap3 : Antiderivatives original = PrimitiveFamily primitive := by
  rw [gap1, gap2]

end
end ProofGap.Exercise1646
