import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise1815

noncomputable section

def branch : Set ℝ := Set.univ
def asinhLog (x : ℝ) := Real.log (x + Real.sqrt (1 + x ^ 2))
def integrand (x : ℝ) :=
  x * asinhLog x / Real.sqrt (1 + x ^ 2)
def substitutedIntegrand (x : ℝ) :=
  asinhLog x * deriv (fun t : ℝ => Real.sqrt (1 + t ^ 2)) x
def residual (x : ℝ) :=
  Real.sqrt (1 + x ^ 2) * (1 / Real.sqrt (1 + x ^ 2))
def boundary (x : ℝ) := Real.sqrt (1 + x ^ 2) * asinhLog x
def primitive (x : ℝ) := boundary x - x
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def ByPartsFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn residual, ∀ x ∈ branch, F x = boundary x - G x}
def PrimitiveFamily : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = primitive x + C}

private lemma base_pos (x : ℝ) : 0 < 1 + x ^ 2 := by
  nlinarith [sq_nonneg x]

private lemma sqrt_base_ne (x : ℝ) : Real.sqrt (1 + x ^ 2) ≠ 0 := by
  exact ne_of_gt (Real.sqrt_pos.2 (base_pos x))

private lemma hasDerivAt_root (x : ℝ) :
    HasDerivAt (fun t : ℝ => Real.sqrt (1 + t ^ 2))
      (x / Real.sqrt (1 + x ^ 2)) x := by
  have hp : HasDerivAt (fun t : ℝ => 1 + t ^ 2) (2 * x) x := by
    convert (hasDerivAt_const x 1).add ((hasDerivAt_id x).pow 2) using 1 <;>
      simp [id] <;> ring
  have hs := (Real.hasDerivAt_sqrt (ne_of_gt (base_pos x))).comp x hp
  convert hs using 1 <;> field_simp [sqrt_base_ne x] <;> ring

private lemma log_argument_pos (x : ℝ) :
    0 < x + Real.sqrt (1 + x ^ 2) := by
  have hs := Real.sqrt_nonneg (1 + x ^ 2)
  have hs2 := Real.sq_sqrt (le_of_lt (base_pos x))
  nlinarith [sq_nonneg x]

private lemma hasDerivAt_asinhLog (x : ℝ) :
    HasDerivAt asinhLog (1 / Real.sqrt (1 + x ^ 2)) x := by
  have hi : HasDerivAt
      (fun t : ℝ => t + Real.sqrt (1 + t ^ 2))
      (1 + x / Real.sqrt (1 + x ^ 2)) x :=
    (hasDerivAt_id x).add (hasDerivAt_root x)
  have hl := hi.log (ne_of_gt (log_argument_pos x))
  have hc :
      (1 + x / Real.sqrt (1 + x ^ 2)) /
          (x + Real.sqrt (1 + x ^ 2)) =
        1 / Real.sqrt (1 + x ^ 2) := by
    field_simp [sqrt_base_ne x, ne_of_gt (log_argument_pos x)]
    ring
  simpa [asinhLog, hc] using hl

private lemma integrand_eq_substituted (x : ℝ) :
    integrand x = substitutedIntegrand x := by
  have hd := (hasDerivAt_root x).deriv
  unfold integrand substitutedIntegrand
  rw [hd]
  field_simp [sqrt_base_ne x]

private lemma residual_eq_one (x : ℝ) : residual x = 1 := by
  unfold residual
  field_simp [sqrt_base_ne x]

private lemma hasDerivAt_boundary (x : ℝ) :
    HasDerivAt boundary (integrand x + residual x) x := by
  have hd := (hasDerivAt_root x).mul (hasDerivAt_asinhLog x)
  have hc :
      integrand x + residual x =
        x / Real.sqrt (1 + x ^ 2) * asinhLog x +
          Real.sqrt (1 + x ^ 2) *
            (1 / Real.sqrt (1 + x ^ 2)) := by
    unfold integrand residual
    field_simp [sqrt_base_ne x]
  rw [hc]
  simpa only [boundary] using hd

private lemma antiderivative_residual_affine
    (G : ℝ → ℝ) (hG : G ∈ AntiderivativesOn residual) (x : ℝ) :
    G x = x + G 0 := by
  have hz : ∀ y : ℝ, HasDerivAt (fun t : ℝ => G t - t) 0 y := by
    intro y
    have hGy := hG y (by simp [branch])
    rw [residual_eq_one] at hGy
    convert hGy.sub (hasDerivAt_id y) using 1 <;> ring
  have hdiff : Differentiable ℝ (fun t : ℝ => G t - t) := by
    intro y
    exact (hz y).differentiableAt
  have hzero : ∀ y : ℝ, deriv (fun t : ℝ => G t - t) y = 0 := by
    intro y
    exact (hz y).deriv
  have heq := is_const_of_deriv_eq_zero hdiff hzero x 0
  linarith

theorem gap1 :
    AntiderivativesOn integrand =
      AntiderivativesOn substitutedIntegrand := by
  apply Set.ext
  intro F
  change
    (∀ x ∈ branch, HasDerivAt F (integrand x) x) ↔
      (∀ x ∈ branch, HasDerivAt F (substitutedIntegrand x) x)
  constructor
  · intro hF x hx
    rw [← integrand_eq_substituted x]
    exact hF x hx
  · intro hF x hx
    rw [integrand_eq_substituted x]
    exact hF x hx
theorem gap2 :
    AntiderivativesOn integrand = ByPartsFamily := by
  apply Set.ext
  intro F
  change
    (∀ x ∈ branch, HasDerivAt F (integrand x) x) ↔
      (∃ G ∈ AntiderivativesOn residual,
        ∀ x ∈ branch, F x = boundary x - G x)
  constructor
  · intro hF
    refine ⟨fun x => boundary x - F x, ?_, ?_⟩
    · intro x hx
      have hd := (hasDerivAt_boundary x).sub (hF x hx)
      convert hd using 1 <;> ring
    · intro x hx
      ring
  · rintro ⟨G, hG, hrep⟩
    have hEq : F = fun x => boundary x - G x := by
      funext x
      exact hrep x (by simp [branch])
    intro x hx
    rw [hEq]
    have hd := (hasDerivAt_boundary x).sub (hG x hx)
    convert hd using 1 <;> ring
theorem gap3 :
    ByPartsFamily = PrimitiveFamily := by
  apply Set.ext
  intro F
  change
    (∃ G ∈ AntiderivativesOn residual,
      ∀ x ∈ branch, F x = boundary x - G x) ↔
      (∃ C : ℝ, ∀ x ∈ branch, F x = primitive x + C)
  constructor
  · rintro ⟨G, hG, hrep⟩
    refine ⟨-G 0, ?_⟩
    intro x hx
    rw [hrep x hx, antiderivative_residual_affine G hG x]
    unfold primitive
    ring
  · rintro ⟨C, hrep⟩
    refine ⟨fun x => x - C, ?_, ?_⟩
    · intro x hx
      rw [residual_eq_one]
      simpa using (hasDerivAt_id x).sub_const C
    · intro x hx
      rw [hrep x hx]
      unfold primitive
      ring
theorem gap4 :
    AntiderivativesOn integrand = PrimitiveFamily := by
  exact gap2.trans gap3

end
end ProofGap.Exercise1815
