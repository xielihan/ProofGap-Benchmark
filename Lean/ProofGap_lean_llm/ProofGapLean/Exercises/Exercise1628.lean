import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1628

noncomputable section

def factored (x : ℝ) : ℝ := (3 - x ^ 2) ^ 3
def expanded (x : ℝ) : ℝ := 27 - 27 * x ^ 2 + 9 * x ^ 4 - x ^ 6
def primitive (x : ℝ) : ℝ :=
  27 * x - 9 * x ^ 3 + (9 / 5) * x ^ 5 - (1 / 7) * x ^ 7
def Antiderivatives (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | Differentiable ℝ F ∧ ∀ x, deriv F x = g x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x, F x = p x + C}

private theorem primitive_hasDerivAt (x : ℝ) :
    HasDerivAt primitive (expanded x) x := by
  have h1 : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
  have h2 := h1.mul h1
  have h3 := h2.mul h1
  have h4 := h3.mul h1
  have h5 := h4.mul h1
  have h6 := h5.mul h1
  have h7 := h6.mul h1
  unfold primitive expanded
  convert
    ((((hasDerivAt_const x (27 : ℝ)).mul h1).sub
      ((hasDerivAt_const x (9 : ℝ)).mul h3)).add
      ((hasDerivAt_const x ((9 : ℝ) / 5)).mul h5)).sub
      ((hasDerivAt_const x ((1 : ℝ) / 7)).mul h7)
    using 1 <;> norm_num <;> ring_nf
  funext y
  dsimp
  ring

private theorem eq_at_zero_of_deriv_eq_zero
    (f : ℝ → ℝ) (hf : Differentiable ℝ f)
    (hderiv : ∀ x, deriv f x = 0) (x : ℝ) : f x = f 0 := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · obtain ⟨c, hc, hceq⟩ :=
      exists_deriv_eq_slope (f := f) hx
        hf.continuous.continuousOn hf.differentiableOn
    have hslope : (f 0 - f x) / (0 - x) = 0 := by
      rw [← hceq, hderiv c]
    have hden : 0 - x ≠ 0 := by linarith
    have hnum : f 0 - f x = 0 :=
      (div_eq_zero_iff.mp hslope).resolve_right hden
    linarith
  · simpa [hx]
  · obtain ⟨c, hc, hceq⟩ :=
      exists_deriv_eq_slope (f := f) hx
        hf.continuous.continuousOn hf.differentiableOn
    have hslope : (f x - f 0) / (x - 0) = 0 := by
      rw [← hceq, hderiv c]
    have hden : x - 0 ≠ 0 := by linarith
    have hnum : f x - f 0 = 0 :=
      (div_eq_zero_iff.mp hslope).resolve_right hden
    linarith

theorem gap1 : Antiderivatives factored = Antiderivatives expanded := by
  have h : factored = expanded := by
    funext x
    unfold factored expanded
    ring
  rw [h]

theorem gap2 : Antiderivatives expanded = PrimitiveFamily primitive := by
  ext F
  constructor
  · rintro ⟨hFdiff, hFderiv⟩
    have hpDiff : Differentiable ℝ primitive :=
      fun x => (primitive_hasDerivAt x).differentiableAt
    have hDdiff : Differentiable ℝ (fun x => F x - primitive x) :=
      hFdiff.sub hpDiff
    have hDderiv : ∀ x, deriv (fun y => F y - primitive y) x = 0 := by
      intro x
      have hd := ((hFdiff x).hasDerivAt.sub (primitive_hasDerivAt x)).deriv
      simpa [hFderiv x] using hd
    refine ⟨F 0 - primitive 0, ?_⟩
    intro x
    have hx := eq_at_zero_of_deriv_eq_zero
      (fun y => F y - primitive y) hDdiff hDderiv x
    linarith
  · rintro ⟨C, hC⟩
    have hF : F = fun x => primitive x + C := funext hC
    subst F
    constructor
    · exact fun x =>
        ((primitive_hasDerivAt x).add (hasDerivAt_const x C)).differentiableAt
    · intro x
      simpa using (primitive_hasDerivAt x).deriv

theorem gap3 : Antiderivatives factored = PrimitiveFamily primitive := by
  calc
    Antiderivatives factored = Antiderivatives expanded := gap1
    _ = PrimitiveFamily primitive := gap2

end
end ProofGap.Exercise1628
