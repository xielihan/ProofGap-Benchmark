import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2177
noncomputable section

def Family (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x, HasDerivAt F (g x) x}

def scaledFamily (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ G : ℝ → ℝ,
    G ∈ Family (fun x => 2 * deriv f (2 * x)) ∧
    ∀ x, F x = (1 / 2 : ℝ) * G x}

def primitive (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (1 / 2 : ℝ) * f (2 * x)

def Translates (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x, F x = p x + C}

private theorem hasDerivAt_primitive (f : ℝ → ℝ) (hf : Differentiable ℝ f) (x : ℝ) :
    HasDerivAt (primitive f) (deriv f (2 * x)) x := by
  have hinner : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
    convert (hasDerivAt_id x).const_mul 2 using 1 <;> ring
  have hcomp : HasDerivAt (fun y : ℝ => f (2 * y))
      (deriv f (2 * x) * 2) x := by
    simpa [Function.comp_def] using
      (hf (2 * x)).hasDerivAt.comp x hinner
  convert hcomp.const_mul (1 / 2 : ℝ) using 1 <;>
    simp [primitive] <;> ring

theorem gap1 (f : ℝ → ℝ) (hf : Differentiable ℝ f) :
    Family (fun x => deriv f (2 * x)) = scaledFamily f := by
  ext F
  constructor
  · intro hF
    change ∀ x, HasDerivAt F (deriv f (2 * x)) x at hF
    change ∃ G : ℝ → ℝ,
      (∀ x, HasDerivAt G (2 * deriv f (2 * x)) x) ∧
      ∀ x, F x = (1 / 2 : ℝ) * G x
    refine ⟨fun x => 2 * F x, ?_, ?_⟩
    · intro x
      convert (hF x).const_mul 2 using 1 <;> ring
    · intro x
      ring
  · rintro ⟨G, hG, hFG⟩
    change ∀ x, HasDerivAt G (2 * deriv f (2 * x)) x at hG
    change ∀ x, HasDerivAt F (deriv f (2 * x)) x
    have hEq : F = fun y => (1 / 2 : ℝ) * G y := funext hFG
    intro x
    rw [hEq]
    convert (hG x).const_mul (1 / 2 : ℝ) using 1 <;> ring

theorem gap2 (f : ℝ → ℝ) (hf : Differentiable ℝ f) :
    scaledFamily f = Translates (primitive f) := by
  have hp : ∀ x, HasDerivAt (primitive f) (deriv f (2 * x)) x :=
    hasDerivAt_primitive f hf
  ext F
  constructor
  · intro hscaled
    have hF : F ∈ Family (fun x => deriv f (2 * x)) := by
      rw [gap1 f hf]
      exact hscaled
    change ∀ x, HasDerivAt F (deriv f (2 * x)) x at hF
    change ∃ C : ℝ, ∀ x, F x = primitive f x + C
    let H : ℝ → ℝ := fun x => F x - primitive f x
    have hH : ∀ x, HasDerivAt H 0 x := by
      intro x
      dsimp [H]
      convert (hF x).sub (hp x) using 1 <;> ring
    have hdiff : Differentiable ℝ H := fun x => (hH x).differentiableAt
    have hzero : ∀ x, deriv H x = 0 := fun x => (hH x).deriv
    refine ⟨F 0 - primitive f 0, ?_⟩
    intro x
    have hc : H x = H 0 :=
      is_const_of_deriv_eq_zero hdiff hzero x 0
    dsimp [H] at hc
    linarith
  · intro htranslate
    change ∃ C : ℝ, ∀ x, F x = primitive f x + C at htranslate
    rcases htranslate with ⟨C, hC⟩
    have hEq : F = fun y => primitive f y + C := funext hC
    have hF : F ∈ Family (fun x => deriv f (2 * x)) := by
      change ∀ x, HasDerivAt F (deriv f (2 * x)) x
      intro x
      rw [hEq]
      exact (hp x).add_const C
    rw [gap1 f hf] at hF
    exact hF

theorem gap3 (f : ℝ → ℝ) (hf : Differentiable ℝ f) :
    Family (fun x => deriv f (2 * x)) = Translates (primitive f) := by
  exact (gap1 f hf).trans (gap2 f hf)

end
end ProofGap.Exercise2177
