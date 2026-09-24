import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1764

noncomputable section

def integrand (x : ℝ) : ℝ := Real.cosh x * Real.cosh (3 * x)
def primitive (x : ℝ) : ℝ :=
  (1 / 8 : ℝ) * Real.sinh (4 * x) + (1 / 4 : ℝ) * Real.sinh (2 * x)
def IsAntiderivative (F f : ℝ → ℝ) : Prop := ∀ x, HasDerivAt F (f x) x
def Family (f : ℝ → ℝ) : Set (ℝ → ℝ) := {F | IsAntiderivative F f}
def Translates (P : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C, ∀ x, F x = P x + C}

theorem gap1 (x : ℝ) :
    integrand x = (Real.cosh (4 * x) + Real.cosh (2 * x)) / 2 := by
  unfold integrand
  rw [show 4 * x = x + 3 * x by ring,
      show 2 * x = 3 * x - x by ring,
      Real.cosh_add, Real.cosh_sub]
  ring

theorem gap2 (x : ℝ) :
    HasDerivAt primitive (integrand x) x := by
  have h4 :
      HasDerivAt (fun y : ℝ => Real.sinh (4 * y))
        (4 * Real.cosh (4 * x)) x := by
    convert (Real.hasDerivAt_sinh (4 * x)).comp x
      ((hasDerivAt_id x).const_mul 4) using 1 <;> ring
  have h2 :
      HasDerivAt (fun y : ℝ => Real.sinh (2 * y))
        (2 * Real.cosh (2 * x)) x := by
    convert (Real.hasDerivAt_sinh (2 * x)).comp x
      ((hasDerivAt_id x).const_mul 2) using 1 <;> ring
  unfold primitive
  rw [gap1]
  convert (h4.const_mul (1 / 8 : ℝ)).add
    (h2.const_mul (1 / 4 : ℝ)) using 1 <;> ring

theorem gap3 :
    Family integrand = Translates primitive := by
  ext F
  constructor
  · intro hF
    change ∀ x, HasDerivAt F (integrand x) x at hF
    change ∃ C, ∀ x, F x = primitive x + C
    have hzero : ∀ x, HasDerivAt (fun y => F y - primitive y) 0 x := by
      intro x
      simpa only [sub_self] using (hF x).sub (gap2 x)
    have hdiff : Differentiable ℝ (fun y => F y - primitive y) :=
      fun x => (hzero x).differentiableAt
    have hderiv : ∀ x, deriv (fun y => F y - primitive y) x = 0 :=
      fun x => (hzero x).deriv
    have hconst_all := is_const_of_deriv_eq_zero hdiff hderiv
    have hconst (x : ℝ) :
        F x - primitive x = F 0 - primitive 0 := by
      exact @hconst_all x 0
    refine ⟨F 0 - primitive 0, ?_⟩
    intro x
    calc
      F x = primitive x + (F x - primitive x) := by ring
      _ = primitive x + (F 0 - primitive 0) := by rw [hconst x]
  · intro hF
    change ∃ C, ∀ x, F x = primitive x + C at hF
    rcases hF with ⟨C, hC⟩
    have hFeq : F = fun y => primitive y + C := funext hC
    rw [hFeq]
    change ∀ x, HasDerivAt (fun y => primitive y + C) (integrand x) x
    intro x
    exact (gap2 x).add_const C

end

end ProofGap.Exercise1764
