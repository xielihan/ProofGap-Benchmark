import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1800

noncomputable section

def branch : Set ℝ := Set.univ
def integrand (x : ℝ) := x * Real.sinh x
def rewrittenIntegrand (x : ℝ) := x * deriv Real.cosh x
def residual (x : ℝ) := Real.cosh x
def boundary (x : ℝ) := x * Real.cosh x
def primitive (x : ℝ) := x * Real.cosh x - Real.sinh x
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def ByPartsFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn residual, ∀ x ∈ branch, F x = boundary x - G x}
def PrimitiveFamily : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = primitive x + C}

private theorem hasDerivAt_zero_eq_at_zero
    (f : ℝ → ℝ) (h : ∀ x, HasDerivAt f 0 x) :
    ∀ x, f x = f 0 := by
  have hf : Differentiable ℝ f := fun x => (h x).differentiableAt
  have hd : ∀ x, deriv f x = 0 := fun x => (h x).deriv
  exact fun x => is_const_of_deriv_eq_zero hf hd x 0

theorem gap1 :
    AntiderivativesOn integrand = AntiderivativesOn rewrittenIntegrand := by
  ext F
  simp only [AntiderivativesOn, Set.mem_setOf_eq]
  constructor
  · intro hF x hx
    have hdc : deriv Real.cosh x = Real.sinh x :=
      (Real.hasDerivAt_cosh x).deriv
    simpa [integrand, rewrittenIntegrand, hdc] using hF x hx
  · intro hF x hx
    have hdc : deriv Real.cosh x = Real.sinh x :=
      (Real.hasDerivAt_cosh x).deriv
    simpa [integrand, rewrittenIntegrand, hdc] using hF x hx
theorem gap2 :
    AntiderivativesOn rewrittenIntegrand = ByPartsFamily := by
  ext F
  simp only [AntiderivativesOn, ByPartsFamily, Set.mem_setOf_eq]
  constructor
  · intro hF
    refine ⟨fun y => boundary y - F y, ?_, ?_⟩
    · intro x hx
      have hb : HasDerivAt boundary (Real.cosh x + x * Real.sinh x) x := by
        simpa [boundary] using
          (hasDerivAt_id x).mul (Real.hasDerivAt_cosh x)
      have hdc : deriv Real.cosh x = Real.sinh x :=
        (Real.hasDerivAt_cosh x).deriv
      have hf : HasDerivAt F (x * Real.sinh x) x := by
        simpa [rewrittenIntegrand, hdc] using hF x hx
      simpa [residual] using hb.sub hf
    · intro x hx
      ring
  · rintro ⟨G, hG, hrel⟩
    intro x hx
    have hb : HasDerivAt boundary (Real.cosh x + x * Real.sinh x) x := by
      simpa [boundary] using
        (hasDerivAt_id x).mul (Real.hasDerivAt_cosh x)
    have hg : HasDerivAt G (Real.cosh x) x := by
      simpa [residual] using hG x hx
    have hdc : deriv Real.cosh x = Real.sinh x :=
      (Real.hasDerivAt_cosh x).deriv
    have heq : F = fun y => boundary y - G y := by
      funext y
      exact hrel y (by simp [branch])
    rw [heq]
    simpa [rewrittenIntegrand, hdc] using hb.sub hg
theorem gap3 : ByPartsFamily = PrimitiveFamily := by
  ext F
  simp only [ByPartsFamily, PrimitiveFamily, AntiderivativesOn,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨G, hG, hrel⟩
    have hzero : ∀ x, HasDerivAt (fun y => G y - Real.sinh y) 0 x := by
      intro x
      have hg : HasDerivAt G (Real.cosh x) x := by
        simpa [residual] using hG x (by simp [branch])
      simpa using hg.sub (Real.hasDerivAt_sinh x)
    have hc := hasDerivAt_zero_eq_at_zero
      (fun y => G y - Real.sinh y) hzero
    refine ⟨-(G 0 - Real.sinh 0), ?_⟩
    intro x hx
    have hc_x := hc x
    dsimp at hc_x
    simp only [Real.sinh_zero, sub_zero] at hc_x
    rw [hrel x hx]
    dsimp [boundary, primitive]
    simp only [Real.sinh_zero, sub_zero]
    linarith
  · rintro ⟨C, hrel⟩
    refine ⟨fun y => Real.sinh y - C, ?_, ?_⟩
    · intro x hx
      simpa [residual] using (Real.hasDerivAt_sinh x).sub_const C
    · intro x hx
      rw [hrel x hx]
      dsimp [boundary, primitive]
      ring
theorem gap4 : AntiderivativesOn integrand = PrimitiveFamily := by
  exact gap1.trans (gap2.trans gap3)

end
end ProofGap.Exercise1800
