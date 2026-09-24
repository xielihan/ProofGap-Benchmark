import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace ProofGap.Exercise1762

noncomputable section

def integrand (x : ℝ) : ℝ := Real.cosh x ^ 2
def primitive (x : ℝ) : ℝ := (1 / 4 : ℝ) * Real.sinh (2 * x) + x / 2
def IsAntiderivative (F f : ℝ → ℝ) : Prop := ∀ x, HasDerivAt F (f x) x
def Family (f : ℝ → ℝ) : Set (ℝ → ℝ) := {F | IsAntiderivative F f}
def Translates (P : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C, ∀ x, F x = P x + C}

private theorem zeroDerivativeConstant1762 {g : ℝ → ℝ}
    (hg : ∀ x, HasDerivAt g 0 x) : ∀ x, g x = g 0 := by
  intro x
  exact is_const_of_deriv_eq_zero
    (fun y => (hg y).differentiableAt)
    (fun y => (hg y).deriv) x 0

theorem gap1 (x : ℝ) :
    integrand x = (Real.cosh (2 * x) + 1) / 2 := by
  unfold integrand
  rw [Real.cosh_two_mul]
  nlinarith [Real.cosh_sq_sub_sinh_sq x]

theorem gap2 (x : ℝ) :
    HasDerivAt primitive ((Real.cosh (2 * x) + 1) / 2) x := by
  have hlin : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
    simpa using (hasDerivAt_id x).const_mul 2
  have hs :
      HasDerivAt (fun y : ℝ => Real.sinh (2 * y))
        (Real.cosh (2 * x) * 2) x := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_sinh (2 * x)).comp x hlin
  have hsum :=
    (hs.const_mul (1 / 4 : ℝ)).add ((hasDerivAt_id x).div_const 2)
  convert hsum using 1 <;> simp <;> ring

theorem gap3 :
    Family integrand = Translates primitive := by
  have hP : IsAntiderivative primitive integrand := by
    intro x
    rw [gap1 x]
    exact gap2 x
  ext F
  change IsAntiderivative F integrand ↔
    ∃ C, ∀ x, F x = primitive x + C
  constructor
  · intro hF
    have hzero :
        ∀ x, HasDerivAt (fun y => F y - primitive y) 0 x := by
      intro x
      simpa using (hF x).sub (hP x)
    refine ⟨F 0 - primitive 0, ?_⟩
    intro x
    have hc := zeroDerivativeConstant1762 hzero x
    linarith
  · rintro ⟨C, hC⟩
    have hFC : F = fun y => primitive y + C := funext hC
    intro x
    rw [hFC]
    simpa using (hP x).add_const C

end

end ProofGap.Exercise1762
