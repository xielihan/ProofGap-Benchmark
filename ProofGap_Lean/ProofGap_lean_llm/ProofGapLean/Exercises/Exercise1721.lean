import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1721

noncomputable section

def branch : Set ℝ := Set.univ
def integrand (x : ℝ) := x ^ 2 * (2 - 3 * x ^ 2) ^ 2
def expandedIntegrand (x : ℝ) := 4 * x ^ 2 - 12 * x ^ 4 + 9 * x ^ 6
def primitive (x : ℝ) :=
  (4 / 3 : ℝ) * x ^ 3 - (12 / 5 : ℝ) * x ^ 5 + (9 / 7 : ℝ) * x ^ 7
def AntiderivativesOn (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ branch, F x = p x + C}

private theorem primitive_hasDerivAt (x : ℝ) :
    HasDerivAt primitive (expandedIntegrand x) x := by
  have h1 := hasDerivAt_id x
  have h2 := h1.mul h1
  have h3 := h2.mul h1
  have h4 := h3.mul h1
  have h5 := h4.mul h1
  have h6 := h5.mul h1
  have h7 := h6.mul h1
  have hp3 : HasDerivAt (fun y : ℝ => y ^ 3) (3 * x ^ 2) x := by
    convert h3 using 1 <;>
      first
      | (funext y; simp [id]; ring)
      | (simp [id]; ring)
  have hp5 : HasDerivAt (fun y : ℝ => y ^ 5) (5 * x ^ 4) x := by
    convert h5 using 1 <;>
      first
      | (funext y; simp [id]; ring)
      | (simp [id]; ring)
  have hp7 : HasDerivAt (fun y : ℝ => y ^ 7) (7 * x ^ 6) x := by
    convert h7 using 1 <;>
      first
      | (funext y; simp [id]; ring)
      | (simp [id]; ring)
  unfold primitive expandedIntegrand
  convert
    (((hasDerivAt_const x (4 / 3 : ℝ)).mul hp3).sub
      ((hasDerivAt_const x (12 / 5 : ℝ)).mul hp5)).add
      ((hasDerivAt_const x (9 / 7 : ℝ)).mul hp7) using 1 <;>
    first
    | (funext y; simp; norm_num; ring)
    | (simp; norm_num; ring)

private theorem everywhere_zero_derivative_is_constant
    {f : ℝ → ℝ} (h : ∀ x : ℝ, HasDerivAt f 0 x) (x y : ℝ) :
    f x = f y := by
  have hd : Differentiable ℝ f := by
    intro z
    exact (h z).differentiableAt
  have hz : ∀ z : ℝ, deriv f z = 0 := by
    intro z
    exact (h z).deriv
  exact is_const_of_deriv_eq_zero hd hz x y

theorem gap1 :
    AntiderivativesOn integrand = AntiderivativesOn expandedIntegrand := by
  ext F
  change
    (∀ x ∈ branch, HasDerivAt F (integrand x) x) ↔
      ∀ x ∈ branch, HasDerivAt F (expandedIntegrand x) x
  constructor
  · intro h x hx
    convert h x hx using 1 <;>
      simp [integrand, expandedIntegrand] <;> ring
  · intro h x hx
    convert h x hx using 1 <;>
      simp [integrand, expandedIntegrand] <;> ring
theorem gap2 :
    AntiderivativesOn expandedIntegrand = PrimitiveFamily primitive := by
  ext F
  change
    (∀ x ∈ branch, HasDerivAt F (expandedIntegrand x) x) ↔
      ∃ C : ℝ, ∀ x ∈ branch, F x = primitive x + C
  constructor
  · intro h
    refine ⟨F 0 - primitive 0, ?_⟩
    have hzero : ∀ y : ℝ,
        HasDerivAt (fun z => F z - primitive z) 0 y := by
      intro y
      convert
        (h y (by simp [branch])).sub (primitive_hasDerivAt y) using 1 <;>
        ring
    intro x hx
    have hc : F x - primitive x = F 0 - primitive 0 :=
      everywhere_zero_derivative_is_constant hzero x 0
    calc
      F x = primitive x + (F x - primitive x) := by ring
      _ = primitive x + (F 0 - primitive 0) := by rw [hc]
  · rintro ⟨C, hC⟩ x hx
    have hF : F = fun y => primitive y + C := by
      funext y
      exact hC y (by simp [branch])
    rw [hF]
    exact (primitive_hasDerivAt x).add_const C
theorem gap3 :
    AntiderivativesOn integrand = PrimitiveFamily primitive := by
  exact gap1.trans gap2

end
end ProofGap.Exercise1721
