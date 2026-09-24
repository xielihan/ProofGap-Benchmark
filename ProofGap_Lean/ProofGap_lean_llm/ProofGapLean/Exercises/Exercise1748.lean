import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1748

noncomputable section

def original (x : ℝ) : ℝ := Real.cos x ^ 3
def substituted (x : ℝ) : ℝ :=
  (1 - Real.sin x ^ 2) * Real.cos x
def primitive (x : ℝ) : ℝ := Real.sin x - (1 / 3) * Real.sin x ^ 3
def Antiderivatives (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | Differentiable ℝ F ∧ ∀ x, deriv F x = g x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x, F x = p x + C}

private theorem original_eq_substituted : original = substituted := by
  funext x
  rw [original, substituted]
  calc
    Real.cos x ^ 3 = Real.cos x ^ 2 * Real.cos x := by ring
    _ = (1 - Real.sin x ^ 2) * Real.cos x := by
      rw [eq_sub_of_add_eq (Real.sin_sq_add_cos_sq x)]
      ring

private theorem primitive_hasDerivAt (x : ℝ) :
    HasDerivAt primitive (substituted x) x := by
  have h := (Real.hasDerivAt_sin x).sub
    (((Real.hasDerivAt_sin x).pow 3).const_mul (1 / 3))
  convert h using 1 <;> simp [primitive, substituted] <;> ring

private theorem primitive_differentiable : Differentiable ℝ primitive := by
  intro x
  exact (primitive_hasDerivAt x).differentiableAt

private theorem eq_of_everywhere_hasDerivAt_zero
    (f : ℝ → ℝ) (h : ∀ x, HasDerivAt f 0 x) (x y : ℝ) : f x = f y := by
  have hfd : Differentiable ℝ f := fun z => (h z).differentiableAt
  apply is_const_of_deriv_eq_zero hfd
  intro z
  exact (h z).deriv

theorem gap1 : Antiderivatives original = Antiderivatives substituted := by
  rw [original_eq_substituted]

theorem gap2 : Antiderivatives substituted = PrimitiveFamily primitive := by
  ext F
  change
    (Differentiable ℝ F ∧ ∀ x, deriv F x = substituted x) ↔
      ∃ C : ℝ, ∀ x, F x = primitive x + C
  constructor
  · rintro ⟨hFdiff, hFderiv⟩
    have hzero : ∀ x, HasDerivAt (fun y => F y - primitive y) 0 x := by
      intro x
      have hFx : HasDerivAt F (substituted x) x := by
        simpa [hFderiv x] using (hFdiff x).hasDerivAt
      simpa using hFx.sub (primitive_hasDerivAt x)
    refine ⟨F 0 - primitive 0, fun x => ?_⟩
    have hx : F x - primitive x = F 0 - primitive 0 :=
      eq_of_everywhere_hasDerivAt_zero
        (fun y => F y - primitive y) hzero x 0
    calc
      F x = (F x - primitive x) + primitive x := by ring
      _ = (F 0 - primitive 0) + primitive x := by rw [hx]
      _ = primitive x + (F 0 - primitive 0) := by ring
  · rintro ⟨C, hC⟩
    have hFeq : F = fun x => primitive x + C := funext hC
    constructor
    · rw [hFeq]
      exact primitive_differentiable.add (differentiable_const (c := C))
    · intro x
      rw [hFeq]
      simpa using ((primitive_hasDerivAt x).add_const C).deriv

theorem gap3 : Antiderivatives original = PrimitiveFamily primitive := by
  exact gap1.trans gap2

end
end ProofGap.Exercise1748
