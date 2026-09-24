import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1915

noncomputable section

def domain : Set ℝ := {x | x ≠ 0 ∧ 1 + x ^ 7 ≠ 0}
def integrand (x : ℝ) : ℝ := (1 - x ^ 7) / (x * (1 + x ^ 7))
def partialFractionIntegrand (x : ℝ) : ℝ :=
  1 / x - 2 * x ^ 6 / (1 + x ^ 7)
def substitutedIntegrand (x : ℝ) : ℝ :=
  1 / x -
    (2 / 7 : ℝ) * (1 / (1 + x ^ 7)) *
      deriv (fun y : ℝ => 1 + y ^ 7) x
def primitiveRaw (x : ℝ) : ℝ :=
  Real.log |x| - (2 / 7 : ℝ) * Real.log |1 + x ^ 7|
def primitive (x : ℝ) : ℝ :=
  (1 / 7 : ℝ) * Real.log (|x| ^ 7 / (1 + x ^ 7) ^ 2)
def Family (f : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ s, HasDerivAt F (f x) x}
def Translates (p : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ s, F x = p x + C}

private theorem integrand_eq_partial {x : ℝ} (hx : x ∈ domain) :
    integrand x = partialFractionIntegrand x := by
  have hx0 : x ≠ 0 := hx.1
  have hq : 1 + x ^ 7 ≠ 0 := hx.2
  unfold integrand partialFractionIntegrand
  field_simp [hx0, hq]
  ring

private theorem polynomial_deriv (x : ℝ) :
    deriv (fun y : ℝ => 1 + y ^ 7) x = 7 * x ^ 6 := by
  have h :=
    ((hasDerivAt_id x).pow 7).const_add 1
  convert h.deriv using 1 <;> norm_num

private theorem partial_eq_substituted {x : ℝ} (hx : x ∈ domain) :
    partialFractionIntegrand x = substitutedIntegrand x := by
  unfold partialFractionIntegrand substitutedIntegrand
  rw [polynomial_deriv]
  ring

private theorem primitiveRaw_hasDerivAt {x : ℝ} (hx : x ∈ domain) :
    HasDerivAt primitiveRaw (integrand x) x := by
  have hx0 : x ≠ 0 := hx.1
  have hq : 1 + x ^ 7 ≠ 0 := hx.2
  have hlx : HasDerivAt (fun y : ℝ => Real.log |y|) (1 / x) x := by
    simpa only [Real.log_abs, one_div] using Real.hasDerivAt_log hx0
  have hpoly :
      HasDerivAt (fun y : ℝ => 1 + y ^ 7) (7 * x ^ 6) x := by
    convert ((hasDerivAt_id x).pow 7).const_add 1 using 1 <;> norm_num
  have hlq :
      HasDerivAt (fun y : ℝ => Real.log |1 + y ^ 7|)
        ((7 * x ^ 6) / (1 + x ^ 7)) x := by
    have hraw := (Real.hasDerivAt_log hq).comp x hpoly
    convert hraw using 1
    · funext y
      simp only [Function.comp_apply, Real.log_abs]
    · field_simp [hq]
  have hraw := hlx.sub (hlq.const_mul (2 / 7 : ℝ))
  unfold primitiveRaw integrand
  convert hraw using 1
  field_simp [hx0, hq]
  ring

private theorem primitiveRaw_eq_primitive {x : ℝ} (hx : x ∈ domain) :
    primitiveRaw x = primitive x := by
  have hx0 : x ≠ 0 := hx.1
  have hq : 1 + x ^ 7 ≠ 0 := hx.2
  have habs : |x| ≠ 0 := abs_ne_zero.mpr hx0
  have hlog :
      Real.log (|x| ^ 7 / (1 + x ^ 7) ^ 2) =
        7 * Real.log |x| - 2 * Real.log |1 + x ^ 7| := by
    rw [Real.log_div (pow_ne_zero 7 habs) (pow_ne_zero 2 hq),
      Real.log_pow, Real.log_pow]
    norm_num
  unfold primitiveRaw primitive
  rw [hlog]
  ring

private theorem family_eq_translates_raw
    (s : Set ℝ) (hopen : IsOpen s) (hs : IsPreconnected s)
    (hdom : s ⊆ domain) :
    Family integrand s = Translates primitiveRaw s := by
  ext F
  change (∀ x ∈ s, HasDerivAt F (integrand x) x) ↔
    ∃ C, ∀ x ∈ s, F x = primitiveRaw x + C
  constructor
  · intro hF
    by_cases hne : s.Nonempty
    · rcases hne with ⟨x0, hx0⟩
      have hz : ∀ x ∈ s, HasDerivAt (fun y => F y - primitiveRaw y) 0 x := by
        intro x hx
        simpa using (hF x hx).sub (primitiveRaw_hasDerivAt (hdom hx))
      have hdiff : DifferentiableOn ℝ (fun y => F y - primitiveRaw y) s := by
        intro x hx
        exact (hz x hx).differentiableAt.differentiableWithinAt
      have hderiv : ∀ x ∈ s, deriv (fun y => F y - primitiveRaw y) x = 0 := by
        intro x hx
        exact (hz x hx).deriv
      refine ⟨F x0 - primitiveRaw x0, ?_⟩
      intro x hx
      have heq : F x - primitiveRaw x = F x0 - primitiveRaw x0 :=
        hopen.is_const_of_deriv_eq_zero hs hdiff hderiv
          (x := x) (y := x0) hx hx0
      linarith
    · refine ⟨0, ?_⟩
      intro x hx
      exact (hne ⟨x, hx⟩).elim
  · rintro ⟨C, hC⟩
    intro x hx
    have heq : F =ᶠ[nhds x] fun y => primitiveRaw y + C := by
      filter_upwards [hopen.mem_nhds hx] with y hy
      exact hC y hy
    exact ((primitiveRaw_hasDerivAt (hdom hx)).add_const C).congr_of_eventuallyEq heq

theorem gap1 (s : Set ℝ) (hdom : s ⊆ domain) :
    Family integrand s = Family partialFractionIntegrand s := by
  ext F
  constructor <;> intro h <;> intro x hx
  · simpa [integrand_eq_partial (hdom hx)] using h x hx
  · simpa [integrand_eq_partial (hdom hx)] using h x hx

theorem gap2 (s : Set ℝ) (hdom : s ⊆ domain) :
    Family partialFractionIntegrand s = Family substitutedIntegrand s := by
  ext F
  constructor <;> intro h <;> intro x hx
  · simpa [partial_eq_substituted (hdom hx)] using h x hx
  · simpa [partial_eq_substituted (hdom hx)] using h x hx

theorem gap3 (s : Set ℝ) (hdom : s ⊆ domain) :
    Family integrand s = Family substitutedIntegrand s := by
  rw [gap1 s hdom, gap2 s hdom]

theorem gap4 (s : Set ℝ) (hopen : IsOpen s) (hs : IsPreconnected s)
    (hdom : s ⊆ domain) :
    Family integrand s = Translates primitiveRaw s := by
  exact family_eq_translates_raw s hopen hs hdom

theorem gap5 (s : Set ℝ) (hdom : s ⊆ domain) :
    Translates primitiveRaw s = Translates primitive s := by
  ext F
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro x hx
    rw [← primitiveRaw_eq_primitive (hdom hx)]
    exact hC x hx
  · rintro ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro x hx
    rw [primitiveRaw_eq_primitive (hdom hx)]
    exact hC x hx

theorem gap6 (s : Set ℝ) (hopen : IsOpen s) (hs : IsPreconnected s)
    (hdom : s ⊆ domain) :
    Family integrand s = Translates primitive s := by
  rw [gap4 s hopen hs hdom, gap5 s hdom]

end

end ProofGap.Exercise1915
