import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2118
noncomputable section

def integrand (x : ℝ) := Real.sinh x ^ 3
def factored (x : ℝ) := Real.sinh x ^ 2 * Real.sinh x
def coshDifferential (x : ℝ) :=
  (Real.cosh x ^ 2 - 1) * deriv Real.cosh x
def primitive (x : ℝ) := (1 / 3 : ℝ) * Real.cosh x ^ 3 - Real.cosh x

def Family (f : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∀ x, HasDerivAt F (f x) x}
def Translates (p : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ C : ℝ, ∀ x, F x = p x + C}

private theorem primitive_hasDerivAt (x : ℝ) :
    HasDerivAt primitive (coshDifferential x) x := by
  unfold primitive coshDifferential
  rw [(Real.hasDerivAt_cosh x).deriv]
  convert
    ((((Real.hasDerivAt_cosh x).pow 3).const_mul (1 / 3 : ℝ)).sub
      (Real.hasDerivAt_cosh x)) using 1 <;> ring

theorem gap1 : Family integrand = Family factored := by
  apply congrArg Family
  funext x
  unfold integrand factored
  ring
theorem gap2 : Family factored = Family coshDifferential := by
  apply congrArg Family
  funext x
  unfold factored coshDifferential
  rw [(Real.hasDerivAt_cosh x).deriv]
  have h : Real.cosh x ^ 2 - 1 = Real.sinh x ^ 2 := by
    linarith [Real.cosh_sq_sub_sinh_sq x]
  rw [h]
theorem gap3 : Family coshDifferential = Translates primitive := by
  apply Set.ext
  intro F
  simp only [Family, Translates, Set.mem_setOf_eq]
  constructor
  · intro hF
    let G : ℝ → ℝ := fun x => F x - primitive x
    have hG (x : ℝ) : HasDerivAt G 0 x := by
      dsimp [G]
      simpa using (hF x).sub (primitive_hasDerivAt x)
    have hGdiff : Differentiable ℝ G := fun x => (hG x).differentiableAt
    have hGzero : ∀ x, deriv G x = 0 := fun x => (hG x).deriv
    refine ⟨G 0, ?_⟩
    intro x
    have hc : G x = G 0 :=
      is_const_of_deriv_eq_zero hGdiff hGzero x 0
    dsimp [G] at hc ⊢
    linarith
  · rintro ⟨C, hC⟩
    have hEq : F = fun x => primitive x + C := funext hC
    intro x
    have hp : HasDerivAt (fun y => primitive y + C)
        (coshDifferential x) x :=
      (primitive_hasDerivAt x).add_const C
    exact hEq.symm ▸ hp
theorem gap4 : Family integrand = Translates primitive := by
  calc
    Family integrand = Family factored := gap1
    _ = Family coshDifferential := gap2
    _ = Translates primitive := gap3

end
end ProofGap.Exercise2118
