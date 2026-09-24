import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise2094
noncomputable section

def f (x : ℝ) := (1 - 1 / x) * Real.exp (-x)
def Family (U : Set ℝ) (g : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∀ x ∈ U, HasDerivAt F (g x) x}
def LiForm (U : Set ℝ) := {F : ℝ → ℝ |
  ∃ L ∈ Family U (fun x => Real.exp (-x) / x), ∃ C, ∀ x ∈ U,
    F x = -Real.exp (-x) - L x + C}
def Regular (U : Set ℝ) :=
  IsOpen U ∧ IsPreconnected U ∧ ∀ x ∈ U, x ≠ 0

private theorem hasDerivAt_neg_exp_neg (x : ℝ) :
    HasDerivAt (fun y : ℝ => -Real.exp (-y)) (Real.exp (-x)) x := by
  simpa using
    ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_id x).neg).neg

theorem gap1 (U : Set ℝ) (hU : Regular U) :
    Family U f = LiForm U := by
  rcases hU with ⟨hUopen, _hUconn, _hUnz⟩
  apply Set.ext
  intro F
  constructor
  · intro hF
    change ∀ x ∈ U, HasDerivAt F (f x) x at hF
    change ∃ L ∈ Family U (fun x => Real.exp (-x) / x),
      ∃ C, ∀ x ∈ U, F x = -Real.exp (-x) - L x + C
    let L : ℝ → ℝ := fun y => -Real.exp (-y) - F y
    refine ⟨L, ?_, 0, ?_⟩
    · change ∀ x ∈ U, HasDerivAt L (Real.exp (-x) / x) x
      intro x hx
      have hf_eq : f x = Real.exp (-x) - Real.exp (-x) / x := by
        unfold f
        simp only [div_eq_mul_inv]
        ring
      have hcoef : Real.exp (-x) - f x = Real.exp (-x) / x := by
        rw [hf_eq]
        ring
      simpa only [L, hcoef] using
        (hasDerivAt_neg_exp_neg x).sub (hF x hx)
    · intro x _hx
      dsimp [L]
      ring
  · intro hLi
    change ∃ L ∈ Family U (fun x => Real.exp (-x) / x),
      ∃ C, ∀ x ∈ U, F x = -Real.exp (-x) - L x + C at hLi
    rcases hLi with ⟨L, hL, C, hform⟩
    change ∀ x ∈ U, HasDerivAt L (Real.exp (-x) / x) x at hL
    change ∀ x ∈ U, HasDerivAt F (f x) x
    intro x hx
    have hf_eq : f x = Real.exp (-x) - Real.exp (-x) / x := by
      unfold f
      simp only [div_eq_mul_inv]
      ring
    have hderG :
        HasDerivAt (fun y : ℝ => -Real.exp (-y) - L y + C)
          (Real.exp (-x) - Real.exp (-x) / x) x := by
      simpa using ((hasDerivAt_neg_exp_neg x).sub (hL x hx)).add_const C
    have hEq :
        F =ᶠ[nhds x] (fun y : ℝ => -Real.exp (-y) - L y + C) :=
      Filter.Eventually.mono (hUopen.mem_nhds hx) (fun y hy => hform y hy)
    have hderF :
        HasDerivAt F (Real.exp (-x) - Real.exp (-x) / x) x :=
      hderG.congr_of_eventuallyEq hEq
    simpa only [hf_eq] using hderF

end
end ProofGap.Exercise2094
