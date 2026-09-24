import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1763

noncomputable section

def integrand (x : ℝ) : ℝ := Real.sinh x * Real.sinh (2 * x)
def primitive (x : ℝ) : ℝ := (2 / 3 : ℝ) * Real.sinh x ^ 3
def IsAntiderivative (F f : ℝ → ℝ) : Prop := ∀ x, HasDerivAt F (f x) x
def Family (f : ℝ → ℝ) : Set (ℝ → ℝ) := {F | IsAntiderivative F f}
def Translates (P : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C, ∀ x, F x = P x + C}

private def Function.IsConstant (G : ℝ → ℝ) : Prop := ∀ x y, G x = G y

private theorem isConst_of_deriv_eq_zero {G : ℝ → ℝ}
    (hGdiff : Differentiable ℝ G) (hGderiv : ∀ x, deriv G x = 0) :
    Function.IsConstant G := by
  have hmono : Monotone G :=
    monotone_of_deriv_nonneg hGdiff (fun x => by rw [hGderiv x])
  have hanti : Antitone G :=
    antitone_of_deriv_nonpos hGdiff (fun x => by rw [hGderiv x])
  intro x y
  rcases le_total x y with hxy | hyx
  · exact le_antisymm (hmono hxy) (hanti hxy)
  · exact le_antisymm (hanti hyx) (hmono hyx)

theorem gap1 (x : ℝ) :
    integrand x = 2 * Real.sinh x ^ 2 * Real.cosh x := by
  unfold integrand
  rw [show (2 : ℝ) * x = x + x by ring, Real.sinh_add]
  ring

theorem gap2 (x : ℝ) :
    2 * Real.sinh x ^ 2 * Real.cosh x =
      2 * Real.sinh x ^ 2 * deriv Real.sinh x := by
  have hs : deriv Real.sinh x = Real.cosh x :=
    (Real.hasDerivAt_sinh x).deriv
  rw [hs]

theorem gap3 (x : ℝ) :
    HasDerivAt primitive (integrand x) x := by
  rw [gap1]
  unfold primitive
  convert ((Real.hasDerivAt_sinh x).pow 3).const_mul (2 / 3 : ℝ) using 1 <;> ring

theorem gap4 :
    Family integrand = Translates primitive := by
  ext F
  change IsAntiderivative F integrand ↔ ∃ C, ∀ x, F x = primitive x + C
  constructor
  · intro hF
    let G : ℝ → ℝ := fun x => F x - primitive x
    have hG : ∀ x, HasDerivAt G 0 x := by
      intro x
      simpa [G] using (hF x).sub (gap3 x)
    have hGdiff : Differentiable ℝ G := fun x => (hG x).differentiableAt
    have hGderiv : ∀ x, deriv G x = 0 := fun x => (hG x).deriv
    have hconst : Function.IsConstant G :=
      isConst_of_deriv_eq_zero hGdiff hGderiv
    refine ⟨G 0, ?_⟩
    intro x
    have hx : G x = G 0 := hconst x 0
    dsimp [G] at hx ⊢
    linarith
  · rintro ⟨C, hC⟩
    change IsAntiderivative F integrand
    have hEq : F = fun x => primitive x + C := funext hC
    rw [hEq]
    intro x
    exact (gap3 x).add_const C

end

end ProofGap.Exercise1763
