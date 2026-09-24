import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1807

noncomputable section

def branch : Set ℝ := Set.univ
def asinhLog (x : ℝ) := Real.log (x + Real.sqrt (1 + x ^ 2))
def integrand (x : ℝ) := asinhLog x
def residual (x : ℝ) := x / Real.sqrt (1 + x ^ 2)
def boundary (x : ℝ) := x * asinhLog x
def primitive (x : ℝ) := boundary x - Real.sqrt (1 + x ^ 2)
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def ByPartsFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn residual, ∀ x ∈ branch, F x = boundary x - G x}
def PrimitiveFamily : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = primitive x + C}

private lemma hasDerivAt_sqrtOneAddSq (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.sqrt (1 + y ^ 2))
      (x / Real.sqrt (1 + x ^ 2)) x := by
  have hpos : 0 < 1 + x ^ 2 := by positivity
  convert ((Real.hasDerivAt_sqrt hpos.ne').comp x
    ((hasDerivAt_const x (1 : ℝ)).add
      ((hasDerivAt_id x).pow 2))) using 1 <;>
    simp only [id_eq] <;> field_simp <;> ring

private lemma hasDerivAt_asinhLog (x : ℝ) :
    HasDerivAt asinhLog (1 / Real.sqrt (1 + x ^ 2)) x := by
  have hpos : 0 < 1 + x ^ 2 := by positivity
  have hsqrt := hasDerivAt_sqrtOneAddSq x
  have hsqrtpos : 0 < Real.sqrt (1 + x ^ 2) := Real.sqrt_pos.2 hpos
  have hargpos : 0 < x + Real.sqrt (1 + x ^ 2) := by
    have hsqsqrt : (Real.sqrt (1 + x ^ 2)) ^ 2 = 1 + x ^ 2 :=
      Real.sq_sqrt hpos.le
    nlinarith [Real.sqrt_nonneg (1 + x ^ 2)]
  unfold asinhLog
  have h := (Real.hasDerivAt_log hargpos.ne').comp x
    ((hasDerivAt_id x).add hsqrt)
  convert h using 1
  field_simp [hargpos.ne', hsqrtpos.ne']
  ring

private lemma hasDerivAt_boundary (x : ℝ) :
    HasDerivAt boundary (integrand x + residual x) x := by
  simpa [boundary, integrand, residual, div_eq_mul_inv] using
    (hasDerivAt_id x).mul (hasDerivAt_asinhLog x)

theorem gap1 :
    AntiderivativesOn integrand = ByPartsFamily := by
  ext F
  constructor
  · intro hF
    refine ⟨fun x => boundary x - F x, ?_, ?_⟩
    · intro x hx
      simpa [sub_eq_add_neg] using
        (hasDerivAt_boundary x).sub (hF x hx)
    · intro x hx
      ring
  · rintro ⟨G, hG, hFG⟩
    have heq : F = fun y => boundary y - G y := by
      funext y
      exact hFG y (Set.mem_univ y)
    intro x hx
    rw [heq]
    simpa [sub_eq_add_neg] using
      (hasDerivAt_boundary x).sub (hG x hx)
theorem gap2 :
    ByPartsFamily = PrimitiveFamily := by
  ext F
  constructor
  · rintro ⟨G, hG, hFG⟩
    have hzero : ∀ x : ℝ, HasDerivAt
        (fun y => G y - Real.sqrt (1 + y ^ 2)) 0 x := by
      intro x
      simpa [residual] using
        (hG x (Set.mem_univ x)).sub (hasDerivAt_sqrtOneAddSq x)
    have hconst : ∃ C : ℝ, ∀ x : ℝ,
        G x - Real.sqrt (1 + x ^ 2) = C := by
      let H : ℝ → ℝ := fun y => G y - Real.sqrt (1 + y ^ 2)
      have hdiff : Differentiable ℝ H := by
        intro y
        exact (hzero y).differentiableAt
      have hderiv : ∀ y : ℝ, deriv H y = 0 := by
        intro y
        exact (hzero y).deriv
      refine ⟨H 0, ?_⟩
      intro x
      exact is_const_of_deriv_eq_zero hdiff hderiv x 0
    rcases hconst with ⟨C, hC⟩
    refine ⟨-C, ?_⟩
    intro x hx
    have hGx := hC x
    have hFx := hFG x hx
    unfold primitive
    linarith
  · rintro ⟨C, hFC⟩
    refine ⟨fun x => Real.sqrt (1 + x ^ 2) - C, ?_, ?_⟩
    · intro x hx
      simpa [residual] using (hasDerivAt_sqrtOneAddSq x).sub_const C
    · intro x hx
      have h := hFC x hx
      unfold primitive at h
      linarith
theorem gap3 :
    AntiderivativesOn integrand = PrimitiveFamily := by
  rw [gap1, gap2]

end
end ProofGap.Exercise1807
