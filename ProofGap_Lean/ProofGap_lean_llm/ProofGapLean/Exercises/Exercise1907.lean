import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1907

noncomputable section

def domain : Set ℝ := {x | x ≠ 0}
def u (x : ℝ) : ℝ := 1 / x ^ 4
def integrand (x : ℝ) : ℝ :=
  (x ^ 4 - 3) / (x * (x ^ 8 + 3 * x ^ 4 + 2))
def reciprocalRewrite (x : ℝ) : ℝ :=
  (1 - 3 / x ^ 4) /
    (x ^ 5 * (1 + 3 / x ^ 4 + 2 / x ^ 8))
def substitutedIntegrand (x : ℝ) : ℝ :=
  (-(1 / 4 : ℝ) * (1 - 3 / x ^ 4)) /
      (2 / x ^ 8 + 3 / x ^ 4 + 1) *
    deriv u x
def partialFractionIntegrand (x : ℝ) : ℝ :=
  -(1 / 4 : ℝ) *
      (5 / (2 / x ^ 4 + 1) - 4 / (1 / x ^ 4 + 1)) *
    deriv u x
def primitiveRaw (x : ℝ) : ℝ :=
  -(5 / 8 : ℝ) * Real.log (2 / x ^ 4 + 1) +
    Real.log (1 / x ^ 4 + 1)
def primitive (x : ℝ) : ℝ :=
  (5 / 8 : ℝ) * Real.log (x ^ 4 / (x ^ 4 + 2)) -
    Real.log (x ^ 4 / (x ^ 4 + 1))
def Family (f : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ s, HasDerivAt F (f x) x}
def Translates (p : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ s, F x = p x + C}

private theorem hasDerivAt_u_aux {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt u (-4 / x ^ 5) x := by
  have hpow : HasDerivAt (fun y : ℝ => y ^ 4) (4 * x ^ 3) x := by
    simpa using (hasDerivAt_id x).pow 4
  unfold u
  convert (hasDerivAt_const x (1 : ℝ)).div hpow (pow_ne_zero 4 hx) using 1
  field_simp [hx]
  ring_nf

private theorem deriv_u_aux {x : ℝ} (hx : x ≠ 0) :
    deriv u x = -4 / x ^ 5 :=
  (hasDerivAt_u_aux hx).deriv

private theorem integrand_eq_reciprocal_aux {x : ℝ} (hx : x ≠ 0) :
    integrand x = reciprocalRewrite x := by
  have hp : x ^ 8 + 3 * x ^ 4 + 2 ≠ 0 := by positivity
  have hr : 1 + 3 / x ^ 4 + 2 / x ^ 8 ≠ 0 := by positivity
  simp only [integrand, reciprocalRewrite]
  field_simp [hx, hp, hr]

private theorem reciprocal_eq_substituted_aux {x : ℝ} (hx : x ≠ 0) :
    reciprocalRewrite x = substitutedIntegrand x := by
  have hr : 1 + 3 / x ^ 4 + 2 / x ^ 8 ≠ 0 := by positivity
  have hs : 2 / x ^ 8 + 3 / x ^ 4 + 1 ≠ 0 := by positivity
  simp only [reciprocalRewrite, substitutedIntegrand]
  rw [deriv_u_aux hx]
  field_simp [hx, hr, hs]
  ring

private theorem substituted_eq_partial_aux {x : ℝ} (hx : x ≠ 0) :
    substitutedIntegrand x = partialFractionIntegrand x := by
  have hs : 2 / x ^ 8 + 3 / x ^ 4 + 1 ≠ 0 := by positivity
  have h₂ : 2 / x ^ 4 + 1 ≠ 0 := by positivity
  have h₁ : 1 / x ^ 4 + 1 ≠ 0 := by positivity
  simp only [substitutedIntegrand, partialFractionIntegrand]
  field_simp [hx, hs, h₂, h₁]
  ring

private theorem hasDerivAt_primitiveRaw_aux {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt primitiveRaw (partialFractionIntegrand x) x := by
  have hu := hasDerivAt_u_aux hx
  have h₂ : 2 / x ^ 4 + 1 ≠ 0 := by positivity
  have h₁ : 1 / x ^ 4 + 1 ≠ 0 := by positivity
  have h₂u : 2 * u x + 1 ≠ 0 := by
    simpa [u, div_eq_mul_inv] using h₂
  have h₁u : u x + 1 ≠ 0 := by
    simpa [u] using h₁
  have hlog₂ :
      HasDerivAt (fun y : ℝ => Real.log (2 / y ^ 4 + 1))
        ((2 * (-4 / x ^ 5)) / (2 / x ^ 4 + 1)) x := by
    simpa [u, div_eq_mul_inv] using
      (((hu.const_mul 2).add_const 1).log h₂u)
  have hlog₁ :
      HasDerivAt (fun y : ℝ => Real.log (1 / y ^ 4 + 1))
        ((-4 / x ^ 5) / (1 / x ^ 4 + 1)) x := by
    simpa [u] using ((hu.add_const 1).log h₁u)
  have hp : HasDerivAt primitiveRaw
      (-(5 / 8 : ℝ) * ((2 * (-4 / x ^ 5)) / (2 / x ^ 4 + 1)) +
        (-4 / x ^ 5) / (1 / x ^ 4 + 1)) x := by
    change HasDerivAt
      (fun y : ℝ => -(5 / 8 : ℝ) * Real.log (2 / y ^ 4 + 1) +
        Real.log (1 / y ^ 4 + 1))
      (-(5 / 8 : ℝ) * ((2 * (-4 / x ^ 5)) / (2 / x ^ 4 + 1)) +
        (-4 / x ^ 5) / (1 / x ^ 4 + 1)) x
    simpa only [neg_mul] using
      (hlog₂.const_mul (-(5 / 8 : ℝ))).add hlog₁
  convert hp using 1
  simp only [partialFractionIntegrand]
  rw [deriv_u_aux hx]
  field_simp [hx, h₂, h₁]
  ring

private theorem family_eq_translates_aux
    (f p : ℝ → ℝ) (s : Set ℝ) (hopen : IsOpen s) (hs : IsPreconnected s)
    (hp : ∀ x ∈ s, HasDerivAt p (f x) x) :
    Family f s = Translates p s := by
  ext F
  simp only [Family, Translates, Set.mem_setOf_eq]
  constructor
  · intro hF
    by_cases hne : s.Nonempty
    · rcases hne with ⟨x₀, hx₀⟩
      refine ⟨F x₀ - p x₀, ?_⟩
      have hd : ∀ x ∈ s, HasDerivAt (fun y => F y - p y) 0 x := by
        intro x hx
        convert (hF x hx).sub (hp x hx) using 1 <;> ring
      have hdiff : DifferentiableOn ℝ (fun y => F y - p y) s := by
        intro x hx
        exact (hd x hx).differentiableAt.differentiableWithinAt
      have hderiv : ∀ x ∈ s, deriv (fun y => F y - p y) x = 0 := by
        intro x hx
        exact (hd x hx).deriv
      intro x hx
      have hcx : F x - p x = F x₀ - p x₀ :=
        hopen.is_const_of_deriv_eq_zero hs hdiff hderiv hx hx₀
      calc
        F x = (F x - p x) + p x := by ring
        _ = (F x₀ - p x₀) + p x := by rw [hcx]
        _ = p x + (F x₀ - p x₀) := by ring
    · refine ⟨0, ?_⟩
      intro x hx
      exact (hne ⟨x, hx⟩).elim
  · rintro ⟨C, hC⟩ x hx
    apply ((hp x hx).add_const C).congr_of_eventuallyEq
    filter_upwards [hopen.mem_nhds hx] with y hy
    exact hC y hy

private theorem primitive_eq_primitiveRaw_aux {x : ℝ} (hx : x ≠ 0) :
    primitive x = primitiveRaw x := by
  have hx4 : 0 < x ^ 4 := by positivity
  have hfrac₂ : 2 / x ^ 4 + 1 = (x ^ 4 + 2) / x ^ 4 := by
    field_simp [ne_of_gt hx4]
    ring
  have hfrac₁ : 1 / x ^ 4 + 1 = (x ^ 4 + 1) / x ^ 4 := by
    field_simp [ne_of_gt hx4]
    ring
  have hlog02 :
      Real.log (x ^ 4 / (x ^ 4 + 2)) =
        Real.log (x ^ 4) - Real.log (x ^ 4 + 2) :=
    Real.log_div (ne_of_gt hx4) (by positivity)
  have hlog01 :
      Real.log (x ^ 4 / (x ^ 4 + 1)) =
        Real.log (x ^ 4) - Real.log (x ^ 4 + 1) :=
    Real.log_div (ne_of_gt hx4) (by positivity)
  have hlog20 :
      Real.log (2 / x ^ 4 + 1) =
        Real.log (x ^ 4 + 2) - Real.log (x ^ 4) := by
    rw [hfrac₂]
    exact Real.log_div (by positivity) (ne_of_gt hx4)
  have hlog10 :
      Real.log (1 / x ^ 4 + 1) =
        Real.log (x ^ 4 + 1) - Real.log (x ^ 4) := by
    rw [hfrac₁]
    exact Real.log_div (by positivity) (ne_of_gt hx4)
  unfold primitive primitiveRaw
  rw [hlog02, hlog01, hlog20, hlog10]
  ring

theorem gap1 (s : Set ℝ) (hdom : s ⊆ domain) :
    Family integrand s = Family reciprocalRewrite s := by
  ext F
  simp only [Family, Set.mem_setOf_eq]
  constructor
  · intro hF x hx
    have hx0 : x ≠ 0 := by simpa [domain] using hdom hx
    simpa only [integrand_eq_reciprocal_aux hx0] using hF x hx
  · intro hF x hx
    have hx0 : x ≠ 0 := by simpa [domain] using hdom hx
    simpa only [integrand_eq_reciprocal_aux hx0] using hF x hx

theorem gap2 (s : Set ℝ) (hdom : s ⊆ domain) :
    Family reciprocalRewrite s = Family substitutedIntegrand s := by
  ext F
  simp only [Family, Set.mem_setOf_eq]
  constructor
  · intro hF x hx
    have hx0 : x ≠ 0 := by simpa [domain] using hdom hx
    simpa only [reciprocal_eq_substituted_aux hx0] using hF x hx
  · intro hF x hx
    have hx0 : x ≠ 0 := by simpa [domain] using hdom hx
    simpa only [reciprocal_eq_substituted_aux hx0] using hF x hx

theorem gap3 (s : Set ℝ) (hdom : s ⊆ domain) :
    Family integrand s = Family substitutedIntegrand s := by
  calc
    Family integrand s = Family reciprocalRewrite s := gap1 s hdom
    _ = Family substitutedIntegrand s := gap2 s hdom

theorem gap4 (s : Set ℝ) (hdom : s ⊆ domain) :
    Family integrand s = Family partialFractionIntegrand s := by
  calc
    Family integrand s = Family substitutedIntegrand s := gap3 s hdom
    _ = Family partialFractionIntegrand s := by
      ext F
      simp only [Family, Set.mem_setOf_eq]
      constructor
      · intro hF x hx
        have hx0 : x ≠ 0 := by simpa [domain] using hdom hx
        simpa only [substituted_eq_partial_aux hx0] using hF x hx
      · intro hF x hx
        have hx0 : x ≠ 0 := by simpa [domain] using hdom hx
        simpa only [substituted_eq_partial_aux hx0] using hF x hx

theorem gap5 (s : Set ℝ) (hopen : IsOpen s) (hs : IsPreconnected s)
    (hdom : s ⊆ domain) :
    Family partialFractionIntegrand s = Translates primitiveRaw s := by
  apply family_eq_translates_aux partialFractionIntegrand primitiveRaw s hopen hs
  intro x hx
  have hx0 : x ≠ 0 := by simpa [domain] using hdom hx
  exact hasDerivAt_primitiveRaw_aux hx0

theorem gap6 (s : Set ℝ) (hopen : IsOpen s) (hs : IsPreconnected s)
    (hdom : s ⊆ domain) :
    Family integrand s = Translates primitiveRaw s := by
  calc
    Family integrand s = Family partialFractionIntegrand s := gap4 s hdom
    _ = Translates primitiveRaw s := gap5 s hopen hs hdom

theorem gap7 (s : Set ℝ) (hopen : IsOpen s) (hs : IsPreconnected s)
    (hdom : s ⊆ domain) :
    Family integrand s = Translates primitive s := by
  rw [gap6 s hopen hs hdom]
  ext F
  simp only [Translates, Set.mem_setOf_eq]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro x hx
    have hx0 : x ≠ 0 := by simpa [domain] using hdom hx
    rw [primitive_eq_primitiveRaw_aux hx0]
    exact hC x hx
  · rintro ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro x hx
    have hx0 : x ≠ 0 := by simpa [domain] using hdom hx
    rw [← primitive_eq_primitiveRaw_aux hx0]
    exact hC x hx

end

end ProofGap.Exercise1907
