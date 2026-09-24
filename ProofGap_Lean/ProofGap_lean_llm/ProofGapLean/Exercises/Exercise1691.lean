import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1691

noncomputable section

def inner (x : ℝ) : ℝ := Real.exp x
def integrand (x : ℝ) : ℝ := 1 / (Real.exp x + Real.exp (-x))
def primitive (x : ℝ) : ℝ := Real.arctan (inner x)

def IsAntiderivativeOn (F f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, HasDerivAt F (f x) x
def Family (f : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | IsAntiderivativeOn F f s}
def Translates (P : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C, ∀ x ∈ s, F x = P x + C}

theorem gap1 (x : ℝ) :
    integrand x = deriv inner x / (1 + inner x ^ 2) := by
  have hinner : HasDerivAt inner (Real.exp x) x := by
    simpa [inner] using Real.hasDerivAt_exp x
  rw [hinner.deriv]
  unfold integrand inner
  rw [Real.exp_neg]
  have he : 0 < Real.exp x := Real.exp_pos x
  have hsum : Real.exp x + (Real.exp x)⁻¹ ≠ 0 := by positivity
  have hquad : 1 + Real.exp x ^ 2 ≠ 0 := by positivity
  field_simp [Real.exp_ne_zero, hsum, hquad]
  <;> ring

theorem gap2 (x : ℝ) :
    HasDerivAt primitive (integrand x) x := by
  have hinner : HasDerivAt inner (Real.exp x) x := by
    simpa [inner] using Real.hasDerivAt_exp x
  have hcomp := (Real.hasDerivAt_arctan (inner x)).comp x hinner
  rw [gap1 x, hinner.deriv]
  simpa [primitive, div_eq_mul_inv, mul_comm] using hcomp

theorem gap3 :
    Family integrand Set.univ = Translates primitive Set.univ := by
  ext F
  constructor
  · intro hF
    change IsAntiderivativeOn F integrand Set.univ at hF
    change ∃ C, ∀ x ∈ Set.univ, F x = primitive x + C
    let G : ℝ → ℝ := fun x => F x - primitive x
    have hG : ∀ x, HasDerivAt G 0 x := by
      intro x
      simpa [G] using (hF x (Set.mem_univ x)).sub (gap2 x)
    have hGdiff : Differentiable ℝ G := fun x => (hG x).differentiableAt
    have hGderiv : ∀ x, deriv G x = 0 := fun x => (hG x).deriv
    refine ⟨G 0, ?_⟩
    intro x hx
    have hconst : G x = G 0 :=
      is_const_of_deriv_eq_zero hGdiff hGderiv x 0
    have heq : F x - primitive x = G 0 := by
      simpa [G] using hconst
    simpa [add_comm] using (sub_eq_iff_eq_add).mp heq
  · intro hF
    change ∃ C, ∀ x ∈ Set.univ, F x = primitive x + C at hF
    change IsAntiderivativeOn F integrand Set.univ
    rcases hF with ⟨C, hC⟩
    have hfun : F = fun x => primitive x + C := by
      funext x
      exact hC x (Set.mem_univ x)
    intro x hx
    rw [hfun]
    exact (gap2 x).add_const C

end

end ProofGap.Exercise1691
