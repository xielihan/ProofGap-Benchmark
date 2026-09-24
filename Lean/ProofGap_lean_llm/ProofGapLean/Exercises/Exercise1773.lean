import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1773

noncomputable section

def subst (x : ℝ) : ℝ := Real.tan x
def integrand (x : ℝ) : ℝ := Real.sin x ^ 2 / Real.cos x ^ 6
def primitive (x : ℝ) : ℝ :=
  (1 / 5 : ℝ) * Real.tan x ^ 5 + (1 / 3 : ℝ) * Real.tan x ^ 3
def domain : Set ℝ := {x | Real.cos x ≠ 0}
def IsAntiderivativeOn (F f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, HasDerivAt F (f x) x
def Family (f : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | IsAntiderivativeOn F f s}
def Translates (P : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C, ∀ x ∈ s, F x = P x + C}

theorem gap1 (x : ℝ) (hx : x ∈ domain) :
    1 / Real.cos x ^ 4 =
      (1 + subst x ^ 2) * deriv subst x := by
  have hc : Real.cos x ≠ 0 := by
    simpa [domain] using hx
  have ht : HasDerivAt subst (1 / Real.cos x ^ 2) x := by
    simpa only [subst] using Real.hasDerivAt_tan hc
  rw [ht.deriv]
  rw [subst, Real.tan_eq_sin_div_cos]
  field_simp [hc] <;> nlinarith [Real.sin_sq_add_cos_sq x]

theorem gap2 (x : ℝ) (hx : x ∈ domain) :
    integrand x = (subst x ^ 4 + subst x ^ 2) * deriv subst x := by
  have hc : Real.cos x ≠ 0 := by
    simpa [domain] using hx
  calc
    integrand x = subst x ^ 2 * (1 / Real.cos x ^ 4) := by
      rw [integrand, subst, Real.tan_eq_sin_div_cos]
      field_simp [hc]
    _ = subst x ^ 2 * ((1 + subst x ^ 2) * deriv subst x) := by
      rw [gap1 x hx]
    _ = (subst x ^ 4 + subst x ^ 2) * deriv subst x := by
      ring

theorem gap3 (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt primitive (integrand x) x := by
  have hc : Real.cos x ≠ 0 := by
    simpa [domain] using hx
  have ht0 : HasDerivAt subst (1 / Real.cos x ^ 2) x := by
    simpa only [subst] using Real.hasDerivAt_tan hc
  have hd : deriv subst x = 1 / Real.cos x ^ 2 := ht0.deriv
  have ht : HasDerivAt subst (deriv subst x) x := by
    rw [hd]
    exact ht0
  have hpoly : HasDerivAt primitive
      ((subst x ^ 4 + subst x ^ 2) * deriv subst x) x := by
    convert ((ht.pow 5).const_mul (1 / 5 : ℝ)).add
      ((ht.pow 3).const_mul (1 / 3 : ℝ)) using 1 <;>
      simp [primitive, subst] <;> ring
  rw [gap2 x hx]
  exact hpoly

theorem gap4 (x : ℝ) :
    (1 / 5 : ℝ) * subst x ^ 5 + (1 / 3 : ℝ) * subst x ^ 3 =
      primitive x := by
  rfl

theorem gap5 (s : Set ℝ) (hopen : IsOpen s) (hs : IsPreconnected s)
    (hdom : s ⊆ domain) :
    Family integrand s = Translates primitive s := by
  ext F
  change IsAntiderivativeOn F integrand s ↔
    ∃ C, ∀ x ∈ s, F x = primitive x + C
  constructor
  · intro hF
    have hzero : ∀ x ∈ s,
        HasDerivAt (fun y => F y - primitive y) 0 x := by
      intro x hx
      convert (hF x hx).sub (gap3 x (hdom hx)) using 1 <;> ring
    have hdiff : DifferentiableOn ℝ (fun y => F y - primitive y) s := by
      intro x hx
      exact (hzero x hx).differentiableAt.differentiableWithinAt
    have hderiv : ∀ x ∈ s, deriv (fun y => F y - primitive y) x = 0 := by
      intro x hx
      exact (hzero x hx).deriv
    have hconst : ∀ x ∈ s, ∀ y ∈ s,
        F x - primitive x = F y - primitive y := by
      intro x hx y hy
      exact hopen.is_const_of_deriv_eq_zero hs hdiff hderiv hx hy
    by_cases hsne : s.Nonempty
    · rcases hsne with ⟨x0, hx0⟩
      refine ⟨F x0 - primitive x0, ?_⟩
      intro x hx
      have hsame := hconst x0 hx0 x hx
      linarith
    · refine ⟨0, ?_⟩
      intro x hx
      exact (hsne ⟨x, hx⟩).elim
  · rintro ⟨C, hC⟩
    intro x hx
    have hbase : HasDerivAt (fun y => primitive y + C) (integrand x) x :=
      (gap3 x (hdom hx)).add_const C
    have heq : F =ᶠ[nhds x] (fun y => primitive y + C) := by
      filter_upwards [hopen.mem_nhds hx] with y hy
      exact hC y hy
    exact hbase.congr_of_eventuallyEq heq

end

end ProofGap.Exercise1773
