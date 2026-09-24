import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1760

noncomputable section

def original (x : ℝ) : ℝ := (1 + Real.exp x) ^ 2 / (1 + Real.exp (2 * x))
def reduced (x : ℝ) : ℝ := 1 + 2 * Real.exp x / (1 + Real.exp (2 * x))
def primitive (x : ℝ) : ℝ := x + 2 * Real.arctan (Real.exp x)
def Antiderivatives (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | Differentiable ℝ F ∧ ∀ x, deriv F x = g x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x, F x = p x + C}

private theorem primitive_hasDerivAt (x : ℝ) :
    HasDerivAt primitive (reduced x) x := by
  unfold primitive
  convert (hasDerivAt_id x).add
    (((Real.hasDerivAt_arctan (Real.exp x)).comp x
      (Real.hasDerivAt_exp x)).const_mul 2) using 1
  unfold reduced
  have hexp : Real.exp (2 * x) = Real.exp x * Real.exp x := by
    rw [show 2 * x = x + x by ring, Real.exp_add]
  rw [hexp]
  have hsq : 0 ≤ Real.exp x * Real.exp x := mul_self_nonneg _
  have hden : 1 + Real.exp x * Real.exp x ≠ 0 := by
    apply ne_of_gt
    linarith
  field_simp [hden, pow_two]
  <;> ring

private theorem constant_of_zero_derivative (f : ℝ → ℝ)
    (hf : Differentiable ℝ f) (hzero : ∀ x, deriv f x = 0) :
    ∀ x y, f x = f y := by
  exact is_const_of_deriv_eq_zero hf hzero

theorem gap1 : Antiderivatives original = Antiderivatives reduced := by
  have hfun : original = reduced := by
    funext x
    unfold original reduced
    have hexp : Real.exp (2 * x) = Real.exp x * Real.exp x := by
      rw [show 2 * x = x + x by ring, Real.exp_add]
    rw [hexp]
    have hsq : 0 ≤ Real.exp x * Real.exp x := mul_self_nonneg _
    have hden : 1 + Real.exp x * Real.exp x ≠ 0 := by
      apply ne_of_gt
      linarith
    field_simp [hden]
    <;> ring
  rw [hfun]

theorem gap2 : Antiderivatives reduced = PrimitiveFamily primitive := by
  ext F
  change (Differentiable ℝ F ∧ ∀ x, deriv F x = reduced x) ↔
    ∃ C : ℝ, ∀ x, F x = primitive x + C
  constructor
  · rintro ⟨hFd, hFder⟩
    have hpDiff : Differentiable ℝ primitive := fun x =>
      (primitive_hasDerivAt x).differentiableAt
    have hd : Differentiable ℝ (fun x => F x - primitive x) :=
      hFd.sub hpDiff
    have hd0 : ∀ x, deriv (fun x => F x - primitive x) x = 0 := by
      intro x
      calc
        deriv (fun x => F x - primitive x) x = deriv F x - reduced x :=
          ((hFd x).hasDerivAt.sub (primitive_hasDerivAt x)).deriv
        _ = 0 := by rw [hFder x]; ring
    refine ⟨F 0 - primitive 0, ?_⟩
    intro x
    have hc := constant_of_zero_derivative
      (fun t => F t - primitive t) hd hd0 x 0
    linarith
  · rintro ⟨C, hC⟩
    have hEq : F = fun x => primitive x + C := funext hC
    rw [hEq]
    constructor
    · intro x
      exact ((primitive_hasDerivAt x).add_const C).differentiableAt
    · intro x
      exact ((primitive_hasDerivAt x).add_const C).deriv

theorem gap3 : Antiderivatives original = PrimitiveFamily primitive := by
  calc
    Antiderivatives original = Antiderivatives reduced := gap1
    _ = PrimitiveFamily primitive := gap2

end
end ProofGap.Exercise1760
