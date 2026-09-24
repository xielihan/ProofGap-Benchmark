import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1681

noncomputable section

def integrand (x : ℝ) : ℝ := Real.sin (1 / x) / x ^ 2
def primitive (x : ℝ) : ℝ := Real.cos (1 / x)
def domain : Set ℝ := {x | x ≠ 0}

def IsAntiderivativeOn (F f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, HasDerivAt F (f x) x
def Family (f : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | IsAntiderivativeOn F f s}
def Translates (P : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C, ∀ x ∈ s, F x = P x + C}

private theorem hasDerivAt_reciprocal (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ => 1 / y) (-1 / x ^ 2) x := by
  convert (hasDerivAt_const x (1 : ℝ)).div (hasDerivAt_id x) hx using 1 <;>
    simp [id, div_eq_mul_inv] <;> ring

theorem gap1 (x : ℝ) (hx : x ∈ domain) :
    integrand x = -Real.sin (1 / x) * deriv (fun y : ℝ => 1 / y) x := by
  have hx0 : x ≠ 0 := by
    simpa [domain] using hx
  rw [(hasDerivAt_reciprocal x hx0).deriv]
  unfold integrand
  ring

theorem gap2 (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt primitive (integrand x) x := by
  have hx0 : x ≠ 0 := by
    simpa [domain] using hx
  unfold primitive integrand
  convert (hasDerivAt_reciprocal x hx0).cos using 1 <;> ring

theorem gap3 (s : Set ℝ) (hopen : IsOpen s) (hs : IsPreconnected s)
    (hdom : s ⊆ domain) :
    Family integrand s = Translates primitive s := by
  ext F
  constructor
  · intro hF
    change IsAntiderivativeOn F integrand s at hF
    change ∃ C, ∀ x ∈ s, F x = primitive x + C
    have hzero : ∀ x ∈ s,
        HasDerivAt (fun y : ℝ => F y - primitive y) 0 x := by
      intro x hx
      convert (hF x hx).sub (gap2 x (hdom hx)) using 1 <;> ring
    have hdiff : DifferentiableOn ℝ (fun y : ℝ => F y - primitive y) s := by
      intro x hx
      exact (hzero x hx).differentiableAt.differentiableWithinAt
    have hderiv : ∀ x ∈ s, deriv (fun y : ℝ => F y - primitive y) x = 0 := by
      intro x hx
      exact (hzero x hx).deriv
    by_cases hne : s.Nonempty
    · rcases hne with ⟨x₀, hx₀⟩
      refine ⟨F x₀ - primitive x₀, ?_⟩
      intro x hx
      have hsame : F x - primitive x = F x₀ - primitive x₀ :=
        hopen.is_const_of_deriv_eq_zero hs hdiff hderiv hx hx₀
      calc
        F x = primitive x + (F x - primitive x) := by ring
        _ = primitive x + (F x₀ - primitive x₀) := by rw [hsame]
    · refine ⟨0, ?_⟩
      intro x hx
      exact False.elim (hne ⟨x, hx⟩)
  · intro hF
    change ∃ C, ∀ x ∈ s, F x = primitive x + C at hF
    change IsAntiderivativeOn F integrand s
    rcases hF with ⟨C, hC⟩
    intro x hx
    have hPC : HasDerivAt (fun y : ℝ => primitive y + C) (integrand x) x :=
      (gap2 x (hdom hx)).add_const C
    have heq : F =ᶠ[nhds x] (fun y : ℝ => primitive y + C) := by
      filter_upwards [hopen.mem_nhds hx] with y hy
      exact hC y hy
    exact hPC.congr_of_eventuallyEq heq

end

end ProofGap.Exercise1681
