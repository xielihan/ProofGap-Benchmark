import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1914

noncomputable section

def domain : Set ℝ := {x | x ≠ 0}
def integrand (x : ℝ) : ℝ := 1 / (x * (x ^ 10 + 1) ^ 2)
def numeratorRewrite (x : ℝ) : ℝ :=
  (x ^ 10 + 1 - x ^ 10) / (x * (x ^ 10 + 1) ^ 2)
def firstSplit (x : ℝ) : ℝ :=
  1 / (x * (x ^ 10 + 1)) - x ^ 9 / (x ^ 10 + 1) ^ 2
def partialFractionIntegrand (x : ℝ) : ℝ :=
  1 / x - x ^ 9 / (x ^ 10 + 1) - x ^ 9 / (x ^ 10 + 1) ^ 2
def substitutedIntegrand (x : ℝ) : ℝ :=
  1 / x -
    (1 / 10 : ℝ) * (1 / (x ^ 10 + 1)) *
      deriv (fun y : ℝ => y ^ 10 + 1) x -
    (1 / 10 : ℝ) * (1 / (x ^ 10 + 1) ^ 2) *
      deriv (fun y : ℝ => y ^ 10 + 1) x
def primitiveRaw (x : ℝ) : ℝ :=
  Real.log |x| -
    (1 / 10 : ℝ) * Real.log (x ^ 10 + 1) +
    1 / (10 * (x ^ 10 + 1))
def primitive (x : ℝ) : ℝ :=
  (1 / 10 : ℝ) * Real.log (x ^ 10 / (x ^ 10 + 1)) +
    1 / (10 * (x ^ 10 + 1))
def Family (f : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ s, HasDerivAt F (f x) x}
def Translates (p : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ s, F x = p x + C}

private theorem primitiveRaw_hasDerivAt_partialFraction (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt primitiveRaw (partialFractionIntegrand x) x := by
  have hden : x ^ 10 + 1 ≠ 0 := by positivity
  have hpoly :
      HasDerivAt (fun y : ℝ => y ^ 10 + 1) (10 * x ^ 9) x := by
    convert ((hasDerivAt_id x).pow 10).add_const 1 using 1 <;> norm_num
  have hlogabs :
      HasDerivAt (fun y : ℝ => Real.log |y|) (1 / x) x := by
    simpa only [Real.log_abs, one_div] using Real.hasDerivAt_log hx
  have hlogpoly :
      HasDerivAt (fun y : ℝ => Real.log (y ^ 10 + 1))
        ((10 * x ^ 9) / (x ^ 10 + 1)) x := by
    convert (Real.hasDerivAt_log hden).comp x hpoly using 1 <;> ring
  have hscaled :
      HasDerivAt (fun y : ℝ => 10 * (y ^ 10 + 1)) (100 * x ^ 9) x := by
    convert hpoly.const_mul 10 using 1 <;> ring
  have hscaled_ne : 10 * (x ^ 10 + 1) ≠ 0 :=
    mul_ne_zero (by norm_num) hden
  have hrecip :
      HasDerivAt (fun y : ℝ => 1 / (10 * (y ^ 10 + 1)))
        (-x ^ 9 / (x ^ 10 + 1) ^ 2) x := by
    convert hscaled.inv hscaled_ne using 1
    · ext y
      simp only [one_div]
      change (10 * (y ^ 10 + 1))⁻¹ = (10 * (y ^ 10 + 1))⁻¹
      rfl
    · field_simp [hden]
      ring
  unfold primitiveRaw partialFractionIntegrand
  convert (hlogabs.sub (hlogpoly.const_mul (1 / 10))).add hrecip using 1 <;> ring

theorem gap1 (x : ℝ) :
    integrand x = numeratorRewrite x := by
  unfold integrand numeratorRewrite
  ring

theorem gap2 (x : ℝ) :
    numeratorRewrite x = firstSplit x := by
  unfold numeratorRewrite firstSplit
  by_cases hx : x = 0
  · subst x
    norm_num
  · have hpos : 0 < x ^ 10 + 1 := by positivity
    field_simp [hx, ne_of_gt hpos] <;> ring

theorem gap3 (x : ℝ) :
    firstSplit x = partialFractionIntegrand x := by
  unfold firstSplit partialFractionIntegrand
  by_cases hx : x = 0
  · subst x
    norm_num
  · have hpos : 0 < x ^ 10 + 1 := by positivity
    field_simp [hx, ne_of_gt hpos] <;> ring

theorem gap4 (x : ℝ) :
    integrand x = partialFractionIntegrand x := by
  calc
    integrand x = numeratorRewrite x := gap1 x
    _ = firstSplit x := gap2 x
    _ = partialFractionIntegrand x := gap3 x

theorem gap5 (s : Set ℝ) (hdom : s ⊆ domain) :
    Family integrand s = Family partialFractionIntegrand s := by
  ext F
  simp only [Family, Set.mem_setOf_eq]
  constructor
  · intro hF x hx
    simpa only [gap4] using hF x hx
  · intro hF x hx
    simpa only [gap4] using hF x hx

theorem gap6 (s : Set ℝ) (hdom : s ⊆ domain) :
    Family partialFractionIntegrand s = Family substitutedIntegrand s := by
  have heq : ∀ x : ℝ, substitutedIntegrand x = partialFractionIntegrand x := by
    intro x
    have hd : deriv (fun y : ℝ => y ^ 10 + 1) x = 10 * x ^ 9 := by
      convert (((hasDerivAt_id x).pow 10).add_const 1).deriv using 1 <;> norm_num
    unfold substitutedIntegrand partialFractionIntegrand
    rw [hd]
    ring
  ext F
  simp only [Family, Set.mem_setOf_eq]
  constructor
  · intro hF x hx
    simpa only [heq x] using hF x hx
  · intro hF x hx
    simpa only [heq x] using hF x hx

theorem gap7 (s : Set ℝ) (hdom : s ⊆ domain) :
    Family integrand s = Family substitutedIntegrand s := by
  exact (gap5 s hdom).trans (gap6 s hdom)

theorem gap8 (s : Set ℝ) (hopen : IsOpen s) (hs : IsPreconnected s)
    (hdom : s ⊆ domain) :
    Family integrand s = Translates primitiveRaw s := by
  have hp : ∀ x ∈ s, HasDerivAt primitiveRaw (integrand x) x := by
    intro x hx
    have hx0 : x ≠ 0 := by
      simpa [domain] using hdom hx
    simpa only [gap4] using primitiveRaw_hasDerivAt_partialFraction x hx0
  apply Set.ext
  intro F
  simp only [Family, Translates, Set.mem_setOf_eq]
  constructor
  · intro hF
    have hzero : ∀ x ∈ s,
        HasDerivAt (fun y : ℝ => F y - primitiveRaw y) 0 x := by
      intro x hx
      convert (hF x hx).sub (hp x hx) using 1 <;> ring
    have hdiff : DifferentiableOn ℝ (fun y : ℝ => F y - primitiveRaw y) s := by
      intro x hx
      exact (hzero x hx).differentiableAt.differentiableWithinAt
    have hderiv : ∀ x ∈ s, deriv (fun y : ℝ => F y - primitiveRaw y) x = 0 := by
      intro x hx
      exact (hzero x hx).deriv
    rcases s.eq_empty_or_nonempty with rfl | hsne
    · exact ⟨0, by simp⟩
    · rcases hsne with ⟨x₀, hx₀⟩
      refine ⟨F x₀ - primitiveRaw x₀, ?_⟩
      intro x hx
      have hc : F x - primitiveRaw x = F x₀ - primitiveRaw x₀ := by
        exact hopen.is_const_of_deriv_eq_zero hs hdiff hderiv
          (x := x) (y := x₀) hx hx₀
      linarith
  · rintro ⟨C, hFC⟩
    intro x hx
    have heq : F =ᶠ[nhds x] (fun y : ℝ => primitiveRaw y + C) := by
      filter_upwards [hopen.mem_nhds hx] with y hy
      exact hFC y hy
    exact ((hp x hx).add_const C).congr_of_eventuallyEq heq

theorem gap9 (s : Set ℝ) (hdom : s ⊆ domain) :
    Translates primitiveRaw s = Translates primitive s := by
  have hprim : ∀ x ∈ s, primitiveRaw x = primitive x := by
    intro x hx
    have hx0 : x ≠ 0 := by
      simpa [domain] using hdom hx
    have hdenpos : 0 < x ^ 10 + 1 := by positivity
    have hlog :
        Real.log (x ^ 10 / (x ^ 10 + 1)) =
          10 * Real.log |x| - Real.log (x ^ 10 + 1) := by
      rw [Real.log_div (pow_ne_zero 10 hx0) (ne_of_gt hdenpos),
        Real.log_pow, Real.log_abs] <;> norm_num
    unfold primitiveRaw primitive
    rw [hlog]
    ring
  apply Set.ext
  intro F
  simp only [Translates, Set.mem_setOf_eq]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro x hx
    calc
      F x = primitiveRaw x + C := hC x hx
      _ = primitive x + C := by rw [hprim x hx]
  · rintro ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro x hx
    calc
      F x = primitive x + C := hC x hx
      _ = primitiveRaw x + C := by rw [hprim x hx]

theorem gap10 (s : Set ℝ) (hopen : IsOpen s) (hs : IsPreconnected s)
    (hdom : s ⊆ domain) :
    Family integrand s = Translates primitive s := by
  exact (gap8 s hopen hs hdom).trans (gap9 s hdom)

end

end ProofGap.Exercise1914
