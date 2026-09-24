import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

namespace ProofGap.Exercise1654

noncomputable section

def Antiderivatives (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {G | Differentiable ℝ G ∧ ∀ x, deriv G x = g x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {G | ∃ C : ℝ, ∀ x, G x = p x + C}
def scaledPrimitive (F : ℝ → ℝ) (a b x : ℝ) : ℝ :=
  (1 / a) * F (a * x + b)

private theorem hasDerivAt_scaledPrimitive_aux
    (F : ℝ → ℝ) (hF : Differentiable ℝ F)
    (a : ℝ) (ha : a ≠ 0) (b x : ℝ) :
    HasDerivAt (scaledPrimitive F a b) (deriv F (a * x + b)) x := by
  have hinner : HasDerivAt (fun y : ℝ => a * y + b) a x := by
    simpa using ((hasDerivAt_id x).const_mul a).add_const b
  have hcomp :
      HasDerivAt (fun y : ℝ => F (a * y + b))
        (deriv F (a * x + b) * a) x :=
    ((hF (a * x + b)).hasDerivAt).comp x hinner
  have hcoef :
      (1 / a) * (deriv F (a * x + b) * a) = deriv F (a * x + b) := by
    field_simp [ha]
  simpa only [scaledPrimitive, hcoef] using hcomp.const_mul (1 / a)

theorem gap1 (f F : ℝ → ℝ) (hF : Differentiable ℝ F)
    (hderiv : ∀ x, deriv F x = f x) (x : ℝ) :
    deriv F x = f x := by
  exact hderiv x

theorem gap2 (f F : ℝ → ℝ) (hF : Differentiable ℝ F)
    (hderiv : ∀ x, deriv F x = f x) (a x b : ℝ) :
    deriv F (a * x + b) = f (a * x + b) := by
  exact hderiv (a * x + b)

theorem gap3 (F : ℝ → ℝ) (hF : Differentiable ℝ F)
    (a : ℝ) (ha : a ≠ 0) (b x : ℝ) :
    deriv (scaledPrimitive F a b) x = deriv F (a * x + b) := by
  exact (hasDerivAt_scaledPrimitive_aux F hF a ha b x).deriv

theorem gap4 (f F : ℝ → ℝ) (hF : Differentiable ℝ F)
    (hderiv : ∀ x, deriv F x = f x)
    (a : ℝ) (ha : a ≠ 0) (b x : ℝ) :
    deriv (scaledPrimitive F a b) x = f (a * x + b) := by
  rw [gap3 F hF a ha b x]
  exact hderiv (a * x + b)

theorem gap5 (f F : ℝ → ℝ) (hF : Differentiable ℝ F)
    (hderiv : ∀ x, deriv F x = f x)
    (a : ℝ) (ha : a ≠ 0) (b : ℝ) :
    Antiderivatives (fun x => f (a * x + b)) =
      PrimitiveFamily (scaledPrimitive F a b) := by
  let P := scaledPrimitive F a b
  have hP : Differentiable ℝ P := by
    intro x
    exact (hasDerivAt_scaledPrimitive_aux F hF a ha b x).differentiableAt
  ext G
  change
    (Differentiable ℝ G ∧ ∀ x, deriv G x = f (a * x + b)) ↔
      ∃ C : ℝ, ∀ x, G x = P x + C
  constructor
  · rintro ⟨hG, hGderiv⟩
    let H : ℝ → ℝ := fun x => G x - P x
    have hH : Differentiable ℝ H := hG.sub hP
    have hHderiv : ∀ x, deriv H x = 0 := by
      intro x
      have hsub := ((hG x).hasDerivAt.sub (hP x).hasDerivAt).deriv
      have heq : deriv G x = deriv P x :=
        (hGderiv x).trans (gap4 f F hF hderiv a ha b x).symm
      simpa [H, heq] using hsub
    have hmono : Monotone H := by
      apply monotone_of_deriv_nonneg hH
      intro x
      rw [hHderiv x]
    have hanti : Antitone H := by
      apply antitone_of_deriv_nonpos hH
      intro x
      rw [hHderiv x]
    refine ⟨G 0 - P 0, ?_⟩
    intro x
    have hc : H x = H 0 := by
      rcases le_total x 0 with hx | hx
      · exact le_antisymm (hmono hx) (hanti hx)
      · exact le_antisymm (hanti hx) (hmono hx)
    dsimp [H] at hc
    linarith
  · rintro ⟨C, hGC⟩
    have hGeq : G = fun x => P x + C := funext hGC
    constructor
    · rw [hGeq]
      exact hP.add (differentiable_const C)
    · intro x
      calc
        deriv G x = deriv P x := by
          rw [hGeq]
          exact ((hP x).hasDerivAt.add_const C).deriv
        _ = f (a * x + b) := gap4 f F hF hderiv a ha b x

theorem gap6 (f F : ℝ → ℝ) (hF : Differentiable ℝ F)
    (hderiv : ∀ x, deriv F x = f x)
    (a : ℝ) (ha : a ≠ 0) (b : ℝ) :
    Antiderivatives (fun x => f (a * x + b)) =
      PrimitiveFamily (scaledPrimitive F a b) := by
  exact gap5 f F hF hderiv a ha b

end
end ProofGap.Exercise1654
