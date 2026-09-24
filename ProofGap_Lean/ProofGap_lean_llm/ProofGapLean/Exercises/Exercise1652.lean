import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

namespace ProofGap.Exercise1652

noncomputable section

def primitive (x : ℝ) : ℝ := x - Real.tanh x
def Antiderivatives (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | Differentiable ℝ F ∧ ∀ x, deriv F x = g x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x, F x = p x + C}

theorem gap1 (x : ℝ) :
    Real.tanh x ^ 2 = 1 - 1 / Real.cosh x ^ 2 := by
  rw [Real.tanh_eq_sinh_div_cosh]
  have hc : Real.cosh x ≠ 0 := ne_of_gt (Real.cosh_pos x)
  field_simp [hc]
  nlinarith [Real.cosh_sq_sub_sinh_sq x]

theorem gap2 :
    Antiderivatives (fun x => Real.tanh x ^ 2) =
      Antiderivatives (fun x => 1 - 1 / Real.cosh x ^ 2) := by
  apply congrArg Antiderivatives
  funext x
  exact gap1 x

theorem gap3 :
    Antiderivatives (fun x => 1 - 1 / Real.cosh x ^ 2) =
      PrimitiveFamily primitive := by
  have hp (x : ℝ) :
      HasDerivAt primitive (1 - 1 / Real.cosh x ^ 2) x := by
    have hc : Real.cosh x ≠ 0 := ne_of_gt (Real.cosh_pos x)
    have htq : HasDerivAt (fun y => Real.sinh y / Real.cosh y)
        (1 / Real.cosh x ^ 2) x := by
      have hq := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) hc
      convert hq using 1
      field_simp [hc]
      nlinarith [Real.cosh_sq_sub_sinh_sq x]
    have hfun : Real.tanh = fun y => Real.sinh y / Real.cosh y := by
      funext y
      exact Real.tanh_eq_sinh_div_cosh y
    have ht : HasDerivAt Real.tanh (1 / Real.cosh x ^ 2) x := by
      rw [hfun]
      exact htq
    simpa only [primitive] using (hasDerivAt_id x).sub ht
  ext F
  simp only [Antiderivatives, PrimitiveFamily, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hF, hF'⟩
    let H : ℝ → ℝ := fun x => F x - primitive x
    have hH (x : ℝ) : HasDerivAt H 0 x := by
      simpa [H, hF' x] using ((hF x).hasDerivAt.sub (hp x))
    have hHdiff : Differentiable ℝ H :=
      fun x => (hH x).differentiableAt
    have hmono : Monotone H := by
      apply monotone_of_deriv_nonneg hHdiff
      intro x
      rw [(hH x).deriv]
    have hanti : Antitone H := by
      apply antitone_of_deriv_nonpos hHdiff
      intro x
      rw [(hH x).deriv]
    have hconst (x : ℝ) : H x = H 0 := by
      rcases le_total x 0 with hx | hx
      · exact le_antisymm (hmono hx) (hanti hx)
      · exact le_antisymm (hanti hx) (hmono hx)
    refine ⟨H 0, ?_⟩
    intro x
    have hx := hconst x
    dsimp [H] at hx ⊢
    linarith
  · rintro ⟨C, hC⟩
    have hFC : F = fun x => primitive x + C := funext hC
    have hHas (x : ℝ) :
        HasDerivAt F (1 - 1 / Real.cosh x ^ 2) x := by
      rw [hFC]
      simpa only [Pi.add_apply, add_zero] using
        (hp x).add (hasDerivAt_const x C)
    exact ⟨fun x => (hHas x).differentiableAt, fun x => (hHas x).deriv⟩

theorem gap4 :
    Antiderivatives (fun x => Real.tanh x ^ 2) =
      PrimitiveFamily primitive := by
  exact gap2.trans gap3

end
end ProofGap.Exercise1652
