import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1738

noncomputable section

def original (x : ℝ) : ℝ := x / (x ^ 4 + 3 * x ^ 2 + 2)
def substituted (x : ℝ) : ℝ :=
  (1 / 2) * (1 / ((x ^ 2 + 1) * (x ^ 2 + 2))) * (2 * x)
def partialFractions (x : ℝ) : ℝ :=
  (1 / 2) * (1 / (x ^ 2 + 1) - 1 / (x ^ 2 + 2)) * (2 * x)
def primitive (x : ℝ) : ℝ :=
  (1 / 2) * Real.log ((x ^ 2 + 1) / (x ^ 2 + 2))
def Antiderivatives (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | Differentiable ℝ F ∧ ∀ x, deriv F x = g x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x, F x = p x + C}

private theorem original_eq_substituted : original = substituted := by
  funext x
  unfold original substituted
  have hfac : x ^ 4 + 3 * x ^ 2 + 2 = (x ^ 2 + 1) * (x ^ 2 + 2) := by
    ring
  rw [hfac]
  have h1 : x ^ 2 + 1 ≠ 0 := by positivity
  have h2 : x ^ 2 + 2 ≠ 0 := by positivity
  field_simp [h1, h2]

private theorem substituted_eq_partialFractions : substituted = partialFractions := by
  funext x
  unfold substituted partialFractions
  have h1 : x ^ 2 + 1 ≠ 0 := by positivity
  have h2 : x ^ 2 + 2 ≠ 0 := by positivity
  field_simp [h1, h2]
  ring

private theorem primitive_hasDerivAt (x : ℝ) :
    HasDerivAt primitive (partialFractions x) x := by
  have h1 : HasDerivAt (fun y : ℝ => y ^ 2 + 1) (2 * x) x := by
    convert ((hasDerivAt_id x).pow 2).add_const 1 using 1 <;>
      simp [mul_comm]
  have h2 : HasDerivAt (fun y : ℝ => y ^ 2 + 2) (2 * x) x := by
    convert ((hasDerivAt_id x).pow 2).add_const 2 using 1 <;>
      simp [mul_comm]
  have hn1 : x ^ 2 + 1 ≠ 0 := by positivity
  have hn2 : x ^ 2 + 2 ≠ 0 := by positivity
  have hl1 : HasDerivAt (fun y : ℝ => Real.log (y ^ 2 + 1))
      ((x ^ 2 + 1)⁻¹ * (2 * x)) x := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_log hn1).comp x h1
  have hl2 : HasDerivAt (fun y : ℝ => Real.log (y ^ 2 + 2))
      ((x ^ 2 + 2)⁻¹ * (2 * x)) x := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_log hn2).comp x h2
  have heq : primitive = fun y : ℝ =>
      (1 / 2) * (Real.log (y ^ 2 + 1) - Real.log (y ^ 2 + 2)) := by
    funext y
    unfold primitive
    rw [Real.log_div (by positivity) (by positivity)]
  rw [heq]
  convert (hl1.sub hl2).const_mul (1 / 2) using 1
  unfold partialFractions
  ring

private theorem primitive_differentiable : Differentiable ℝ primitive := by
  intro x
  exact (primitive_hasDerivAt x).differentiableAt

theorem gap1 : Antiderivatives original = Antiderivatives substituted := by
  unfold Antiderivatives
  rw [original_eq_substituted]

theorem gap2 : Antiderivatives substituted = Antiderivatives partialFractions := by
  unfold Antiderivatives
  rw [substituted_eq_partialFractions]

theorem gap3 : Antiderivatives partialFractions = PrimitiveFamily primitive := by
  ext F
  constructor
  · rintro ⟨hFdiff, hFderiv⟩
    let q : ℝ → ℝ := fun x => F x - primitive x
    have hqdiff : Differentiable ℝ q :=
      hFdiff.sub primitive_differentiable
    have hqderiv : ∀ x, deriv q x = 0 := by
      intro x
      have hx := ((hFdiff x).hasDerivAt.sub (primitive_hasDerivAt x)).deriv
      simpa [q, hFderiv x] using hx
    have hqconst := is_const_of_deriv_eq_zero hqdiff hqderiv
    refine ⟨F 0 - primitive 0, ?_⟩
    intro x
    have hx := hqconst x 0
    dsimp [q] at hx
    linarith
  · rintro ⟨C, hC⟩
    have hFeq : F = fun x => primitive x + C := by
      funext x
      exact hC x
    rw [hFeq]
    refine ⟨primitive_differentiable.add (differentiable_const C), ?_⟩
    intro x
    exact ((primitive_hasDerivAt x).add_const C).deriv

theorem gap4 : Antiderivatives original = PrimitiveFamily primitive := by
  calc
    Antiderivatives original = Antiderivatives substituted := gap1
    _ = Antiderivatives partialFractions := gap2
    _ = PrimitiveFamily primitive := gap3

end
end ProofGap.Exercise1738
