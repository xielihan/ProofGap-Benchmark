import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1802

noncomputable section

def branch : Set ℝ := Set.univ
def integrand (x : ℝ) := Real.arctan x
def residual (x : ℝ) := x / (1 + x ^ 2)
def boundary (x : ℝ) := x * Real.arctan x
def primitive (x : ℝ) :=
  x * Real.arctan x - (1 / 2 : ℝ) * Real.log (1 + x ^ 2)
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def ByPartsFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn residual, ∀ x ∈ branch, F x = boundary x - G x}
def PrimitiveFamily : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = primitive x + C}

private theorem hasDerivAtBoundary1802 (x : ℝ) :
    HasDerivAt boundary (integrand x + residual x) x := by
  simpa [boundary, integrand, residual, div_eq_mul_inv] using
    (hasDerivAt_id x).mul (Real.hasDerivAt_arctan x)

private theorem hasDerivAtLogHalf1802 (x : ℝ) :
    HasDerivAt (fun y : ℝ => (1 / 2 : ℝ) * Real.log (1 + y ^ 2))
      (residual x) x := by
  have hxpos : 0 < 1 + x ^ 2 := by
    nlinarith [sq_nonneg x]
  have hinner : HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * x) x := by
    convert (hasDerivAt_const x (1 : ℝ)).add ((hasDerivAt_id x).pow 2) using 1 <;>
      simp [id] <;> ring
  have hlog :
      HasDerivAt (fun y : ℝ => Real.log (1 + y ^ 2))
        ((1 + x ^ 2)⁻¹ * (2 * x)) x := by
    simpa only [Function.comp_apply] using
      (Real.hasDerivAt_log (ne_of_gt hxpos)).comp x hinner
  convert hlog.const_mul (1 / 2 : ℝ) using 1 <;>
    simp [residual, div_eq_mul_inv] <;> ring

private theorem hasDerivAtPrimitive1802 (x : ℝ) :
    HasDerivAt primitive (integrand x) x := by
  have h := (hasDerivAtBoundary1802 x).sub (hasDerivAtLogHalf1802 x)
  have hfun :
      boundary - (fun y : ℝ => (1 / 2 : ℝ) * Real.log (1 + y ^ 2)) = primitive := by
    funext y
    rfl
  rw [hfun] at h
  simpa using h

private theorem antiderivativeEqAddConst1802
    {f P F : ℝ → ℝ}
    (hP : ∀ x, HasDerivAt P (f x) x)
    (hF : ∀ x, HasDerivAt F (f x) x) :
    ∃ C : ℝ, ∀ x, F x = P x + C := by
  have hD : ∀ x, HasDerivAt (fun y => F y - P y) 0 x := by
    intro x
    simpa using (hF x).sub (hP x)
  have hdiff : Differentiable ℝ (fun y => F y - P y) :=
    fun x => (hD x).differentiableAt
  have hderiv : ∀ x, deriv (fun y => F y - P y) x = 0 :=
    fun x => (hD x).deriv
  refine ⟨F 0 - P 0, ?_⟩
  intro x
  have hx := is_const_of_deriv_eq_zero hdiff hderiv x 0
  linarith [hx]

theorem gap1 : AntiderivativesOn integrand = ByPartsFamily := by
  ext F
  simp only [AntiderivativesOn, ByPartsFamily, Set.mem_setOf_eq]
  constructor
  · intro hF
    refine ⟨fun y => boundary y - F y, ?_, ?_⟩
    · intro x hx
      simpa using (hasDerivAtBoundary1802 x).sub (hF x hx)
    · intro x hx
      ring
  · rintro ⟨G, hG, hFG⟩
    have heq : F = fun y => boundary y - G y := by
      funext y
      exact hFG y (by simp [branch])
    rw [heq]
    intro x hx
    simpa using (hasDerivAtBoundary1802 x).sub (hG x hx)
theorem gap2 : ByPartsFamily = PrimitiveFamily := by
  ext F
  constructor
  · intro hF
    have hA : F ∈ AntiderivativesOn integrand := by
      rw [gap1]
      exact hF
    obtain ⟨C, hC⟩ :=
      antiderivativeEqAddConst1802
        (f := integrand) (P := primitive) (F := F)
        hasDerivAtPrimitive1802
        (fun x => hA x (by simp [branch]))
    refine ⟨C, ?_⟩
    intro x hx
    exact hC x
  · rintro ⟨C, hC⟩
    have heq : F = fun y => primitive y + C := by
      funext y
      exact hC y (by simp [branch])
    have hA : F ∈ AntiderivativesOn integrand := by
      intro x hx
      rw [heq]
      simpa using (hasDerivAtPrimitive1802 x).add_const C
    rw [← gap1]
    exact hA
theorem gap3 : AntiderivativesOn integrand = PrimitiveFamily := by
  calc
    AntiderivativesOn integrand = ByPartsFamily := gap1
    _ = PrimitiveFamily := gap2

end
end ProofGap.Exercise1802
