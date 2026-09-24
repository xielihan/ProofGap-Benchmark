import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise1913

noncomputable section

def domain : Set ℝ := {x | x ≠ 0}
def integrand (x : ℝ) : ℝ := 1 / (x * (x ^ 10 + 2))
def partialFractionIntegrand (x : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (1 / x - x ^ 9 / (x ^ 10 + 2))
def substitutedIntegrand (x : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (1 / x) -
    (1 / 20 : ℝ) * (1 / (x ^ 10 + 2)) *
      deriv (fun y : ℝ => y ^ 10 + 2) x
def primitiveRaw (x : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.log |x| -
    (1 / 20 : ℝ) * Real.log (x ^ 10 + 2)
def primitive (x : ℝ) : ℝ :=
  (1 / 20 : ℝ) * Real.log (x ^ 10 / (x ^ 10 + 2))
def Family (f : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ s, HasDerivAt F (f x) x}
def Translates (p : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ s, F x = p x + C}

private theorem integrand_eq_partial (x : ℝ) (hx : x ≠ 0) :
    integrand x = partialFractionIntegrand x := by
  have hden : x ^ 10 + 2 ≠ 0 := by positivity
  unfold integrand partialFractionIntegrand
  field_simp [hx, hden] <;> ring

private theorem polynomial_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y : ℝ => y ^ 10 + 2) (10 * x ^ 9) x := by
  convert ((hasDerivAt_id x).pow 10).add_const 2 using 1 <;> norm_num

private theorem partial_eq_substituted (x : ℝ) :
    partialFractionIntegrand x = substitutedIntegrand x := by
  have hd : deriv (fun y : ℝ => y ^ 10 + 2) x = 10 * x ^ 9 :=
    (polynomial_hasDerivAt x).deriv
  unfold partialFractionIntegrand substitutedIntegrand
  rw [hd]
  ring

private theorem primitiveRaw_hasDerivAt (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt primitiveRaw (integrand x) x := by
  have hden : x ^ 10 + 2 ≠ 0 := by positivity
  have hlogabs : HasDerivAt (fun y : ℝ => Real.log |y|) x⁻¹ x := by
    simpa only [Real.log_abs] using Real.hasDerivAt_log hx
  have hlog_at_poly :
      HasDerivAt Real.log (x ^ 10 + 2)⁻¹ (x ^ 10 + 2) :=
    Real.hasDerivAt_log hden
  have hlogpoly :
      HasDerivAt (fun y : ℝ => Real.log (y ^ 10 + 2))
        ((x ^ 10 + 2)⁻¹ * (10 * x ^ 9)) x := by
    simpa only [Function.comp_apply] using
      hlog_at_poly.comp x (polynomial_hasDerivAt x)
  have hraw :
      HasDerivAt primitiveRaw
        ((1 / 2 : ℝ) * x⁻¹ -
          (1 / 20 : ℝ) * ((x ^ 10 + 2)⁻¹ * (10 * x ^ 9))) x := by
    change HasDerivAt
      (fun y : ℝ =>
        (1 / 2 : ℝ) * Real.log |y| -
          (1 / 20 : ℝ) * Real.log (y ^ 10 + 2)) _ x
    exact (hlogabs.const_mul (1 / 2 : ℝ)).sub
      (hlogpoly.const_mul (1 / 20 : ℝ))
  have hcoef :
      (1 / 2 : ℝ) * x⁻¹ -
          (1 / 20 : ℝ) * ((x ^ 10 + 2)⁻¹ * (10 * x ^ 9)) =
        partialFractionIntegrand x := by
    unfold partialFractionIntegrand
    ring
  rw [hcoef, ← integrand_eq_partial x hx] at hraw
  exact hraw

private theorem primitiveRaw_eq_primitive (x : ℝ) (hx : x ≠ 0) :
    primitiveRaw x = primitive x := by
  have hden : x ^ 10 + 2 ≠ 0 := by positivity
  unfold primitiveRaw primitive
  rw [Real.log_div (pow_ne_zero 10 hx) hden, Real.log_pow, Real.log_abs]
  ring

private theorem family_eq_translates_of_primitive
    (s : Set ℝ) (hopen : IsOpen s) (hs : IsPreconnected s)
    (hdom : s ⊆ domain) (p : ℝ → ℝ)
    (hp : ∀ x ∈ s, HasDerivAt p (integrand x) x) :
    Family integrand s = Translates p s := by
  apply Set.ext
  intro F
  constructor
  · intro hF
    change ∀ x ∈ s, HasDerivAt F (integrand x) x at hF
    change ∃ C, ∀ x ∈ s, F x = p x + C
    by_cases hne : s.Nonempty
    · rcases hne with ⟨x₀, hx₀⟩
      have hzero : ∀ y ∈ s, HasDerivAt (fun z => F z - p z) 0 y := by
        intro y hy
        simpa using (hF y hy).sub (hp y hy)
      have hdiff : DifferentiableOn ℝ (fun z => F z - p z) s := by
        intro y hy
        exact (hzero y hy).differentiableAt.differentiableWithinAt
      have hderiv : ∀ y ∈ s, deriv (fun z => F z - p z) y = 0 := by
        intro y hy
        exact (hzero y hy).deriv
      refine ⟨F x₀ - p x₀, ?_⟩
      intro x hx
      have heq : F x - p x = F x₀ - p x₀ := by
        exact hopen.is_const_of_deriv_eq_zero hs hdiff hderiv hx hx₀
      calc
        F x = p x + (F x - p x) := by ring
        _ = p x + (F x₀ - p x₀) := by rw [heq]
    · refine ⟨0, ?_⟩
      intro x hx
      exact (hne ⟨x, hx⟩).elim
  · intro hF
    change ∃ C, ∀ x ∈ s, F x = p x + C at hF
    change ∀ x ∈ s, HasDerivAt F (integrand x) x
    rcases hF with ⟨C, hC⟩
    intro x hx
    have hevent : F =ᶠ[nhds x] (fun y => p y + C) := by
      filter_upwards [hopen.mem_nhds hx] with y hy
      exact hC y hy
    exact ((hp x hx).add_const C).congr_of_eventuallyEq hevent

theorem gap1 (s : Set ℝ) (hdom : s ⊆ domain) :
    Family integrand s = Family partialFractionIntegrand s := by
  apply Set.ext
  intro F
  constructor
  · intro hF
    change ∀ x ∈ s, HasDerivAt F (integrand x) x at hF
    change ∀ x ∈ s, HasDerivAt F (partialFractionIntegrand x) x
    intro x hx
    rw [← integrand_eq_partial x (hdom hx)]
    exact hF x hx
  · intro hF
    change ∀ x ∈ s, HasDerivAt F (partialFractionIntegrand x) x at hF
    change ∀ x ∈ s, HasDerivAt F (integrand x) x
    intro x hx
    rw [integrand_eq_partial x (hdom hx)]
    exact hF x hx

theorem gap2 (s : Set ℝ) (hdom : s ⊆ domain) :
    Family partialFractionIntegrand s = Family substitutedIntegrand s := by
  apply Set.ext
  intro F
  constructor
  · intro hF
    change ∀ x ∈ s, HasDerivAt F (partialFractionIntegrand x) x at hF
    change ∀ x ∈ s, HasDerivAt F (substitutedIntegrand x) x
    intro x hx
    rw [← partial_eq_substituted x]
    exact hF x hx
  · intro hF
    change ∀ x ∈ s, HasDerivAt F (substitutedIntegrand x) x at hF
    change ∀ x ∈ s, HasDerivAt F (partialFractionIntegrand x) x
    intro x hx
    rw [partial_eq_substituted x]
    exact hF x hx

theorem gap3 (s : Set ℝ) (hdom : s ⊆ domain) :
    Family integrand s = Family substitutedIntegrand s := by
  exact (gap1 s hdom).trans (gap2 s hdom)

theorem gap4 (s : Set ℝ) (hopen : IsOpen s) (hs : IsPreconnected s)
    (hdom : s ⊆ domain) :
    Family integrand s = Translates primitiveRaw s := by
  apply family_eq_translates_of_primitive s hopen hs hdom
  intro x hx
  exact primitiveRaw_hasDerivAt x (hdom hx)

theorem gap5 (s : Set ℝ) (hdom : s ⊆ domain) :
    Translates primitiveRaw s = Translates primitive s := by
  apply Set.ext
  intro F
  constructor
  · intro hF
    change ∃ C, ∀ x ∈ s, F x = primitiveRaw x + C at hF
    change ∃ C, ∀ x ∈ s, F x = primitive x + C
    rcases hF with ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro x hx
    rw [← primitiveRaw_eq_primitive x (hdom hx)]
    exact hC x hx
  · intro hF
    change ∃ C, ∀ x ∈ s, F x = primitive x + C at hF
    change ∃ C, ∀ x ∈ s, F x = primitiveRaw x + C
    rcases hF with ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro x hx
    rw [primitiveRaw_eq_primitive x (hdom hx)]
    exact hC x hx

theorem gap6 (s : Set ℝ) (hopen : IsOpen s) (hs : IsPreconnected s)
    (hdom : s ⊆ domain) :
    Family integrand s = Translates primitive s := by
  calc
    Family integrand s = Translates primitiveRaw s := gap4 s hopen hs hdom
    _ = Translates primitive s := gap5 s hdom

end

end ProofGap.Exercise1913
