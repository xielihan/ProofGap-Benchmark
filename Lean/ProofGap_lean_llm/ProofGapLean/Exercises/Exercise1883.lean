import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1883

noncomputable section

def integrand (x : ℝ) : ℝ := 1 / (x ^ 4 - 1)
def domain : Set ℝ := {x | x ≠ -1 ∧ x ≠ 1}
def primitive (x : ℝ) : ℝ :=
  (1 / 4 : ℝ) * Real.log |(x - 1) / (x + 1)| -
    (1 / 2 : ℝ) * Real.arctan x
def IsAntiderivativeOn (F f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, HasDerivAt F (f x) x
def Family (f : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | IsAntiderivativeOn F f s}
def Translates (P : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C, ∀ x ∈ s, F x = P x + C}

theorem gap1 (x : ℝ) (hx : x ∈ domain) :
    integrand x =
      (1 / 2 : ℝ) * (1 / (x ^ 2 - 1) - 1 / (x ^ 2 + 1)) := by
  change x ≠ -1 ∧ x ≠ 1 at hx
  rcases hx with ⟨hx_neg, hx_pos⟩
  have hx_sub : x - 1 ≠ 0 := sub_ne_zero.mpr hx_pos
  have hx_add : x + 1 ≠ 0 := by
    intro h
    apply hx_neg
    linarith
  have hsq_sub : x ^ 2 - 1 ≠ 0 := by
    rw [show x ^ 2 - 1 = (x - 1) * (x + 1) by ring]
    exact mul_ne_zero hx_sub hx_add
  have hsq_add : x ^ 2 + 1 ≠ 0 := by
    nlinarith [sq_nonneg x]
  have hfour : x ^ 4 - 1 ≠ 0 := by
    rw [show x ^ 4 - 1 = (x ^ 2 - 1) * (x ^ 2 + 1) by ring]
    exact mul_ne_zero hsq_sub hsq_add
  unfold integrand
  field_simp [hfour, hsq_sub, hsq_add]
  ring

theorem gap2 (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt primitive (integrand x) x := by
  have hx' := hx
  change x ≠ -1 ∧ x ≠ 1 at hx'
  rcases hx' with ⟨hx_neg, hx_pos⟩
  have hx_sub : x - 1 ≠ 0 := sub_ne_zero.mpr hx_pos
  have hx_add : x + 1 ≠ 0 := by
    intro h
    apply hx_neg
    linarith
  have hsq_sub : x ^ 2 - 1 ≠ 0 := by
    rw [show x ^ 2 - 1 = (x - 1) * (x + 1) by ring]
    exact mul_ne_zero hx_sub hx_add
  have hsq_add : x ^ 2 + 1 ≠ 0 := by
    nlinarith [sq_nonneg x]
  have hquot :
      HasDerivAt (fun y : ℝ => (y - 1) / (y + 1))
        (2 / (x + 1) ^ 2) x := by
    convert
      ((hasDerivAt_id x).sub_const 1).div
        ((hasDerivAt_id x).add_const 1) hx_add using 1 <;>
      simp only [id_eq] <;> ring
  have hlogquot :
      HasDerivAt (fun y : ℝ => Real.log ((y - 1) / (y + 1)))
        (((x - 1) / (x + 1))⁻¹ * (2 / (x + 1) ^ 2)) x := by
    simpa only [Function.comp_apply] using
      (Real.hasDerivAt_log (div_ne_zero hx_sub hx_add)).comp x hquot
  have hderiv :=
    (hlogquot.const_mul (1 / 4 : ℝ)).sub
      ((Real.hasDerivAt_arctan x).const_mul (1 / 2 : ℝ))
  have hcoeff :
      (1 / 4 : ℝ) *
          (((x - 1) / (x + 1))⁻¹ * (2 / (x + 1) ^ 2)) -
        (1 / 2 : ℝ) * (1 / (1 + x ^ 2)) =
      integrand x := by
    rw [gap1 x hx]
    field_simp [hx_sub, hx_add, hsq_sub, hsq_add]
    ring
  have hfun :
      primitive =
        ((fun y : ℝ => (1 / 4 : ℝ) * Real.log ((y - 1) / (y + 1))) -
          (fun y : ℝ => (1 / 2 : ℝ) * Real.arctan y)) := by
    funext y
    simp only [primitive, Pi.sub_apply, Real.log_abs]
  rw [← hcoeff, hfun]
  exact hderiv

theorem gap3 (s : Set ℝ) (hopen : IsOpen s) (hs : IsPreconnected s)
    (hdom : s ⊆ domain) :
    Family integrand s = Translates primitive s := by
  ext F
  change IsAntiderivativeOn F integrand s ↔
    ∃ C, ∀ x ∈ s, F x = primitive x + C
  constructor
  · intro hF
    have hzero :
        ∀ x ∈ s, HasDerivAt (fun y : ℝ => F y - primitive y) 0 x := by
      intro x hx
      simpa using (hF x hx).sub (gap2 x (hdom hx))
    have hdiff :
        DifferentiableOn ℝ (fun y : ℝ => F y - primitive y) s := by
      intro x hx
      exact (hzero x hx).differentiableAt.differentiableWithinAt
    have hderiv :
        ∀ x ∈ s, deriv (fun y : ℝ => F y - primitive y) x = 0 := by
      intro x hx
      exact (hzero x hx).deriv
    by_cases hne : s.Nonempty
    · rcases hne with ⟨x₀, hx₀⟩
      refine ⟨F x₀ - primitive x₀, ?_⟩
      intro x hx
      have heq :
          F x - primitive x = F x₀ - primitive x₀ :=
        hopen.is_const_of_deriv_eq_zero hs hdiff hderiv hx hx₀
      linarith
    · refine ⟨0, ?_⟩
      intro x hx
      exact (hne ⟨x, hx⟩).elim
  · rintro ⟨C, hC⟩
    intro x hx
    have hevent :
        F =ᶠ[nhds x] (fun y : ℝ => primitive y + C) := by
      filter_upwards [hopen.mem_nhds hx] with y hy
      exact hC y hy
    exact
      ((gap2 x (hdom hx)).add_const C).congr_of_eventuallyEq hevent

end

end ProofGap.Exercise1883
