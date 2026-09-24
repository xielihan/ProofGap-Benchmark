import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1676

noncomputable section

def inner (x : ℝ) : ℝ := 3 - 2 * x ^ 2
def integrand (x : ℝ) : ℝ := x / inner x
def primitive (x : ℝ) : ℝ := -(1 / 4 : ℝ) * Real.log |inner x|
def domain : Set ℝ := {x | inner x ≠ 0}

def IsAntiderivativeOn (F f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, HasDerivAt F (f x) x
def Family (f : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | IsAntiderivativeOn F f s}
def Translates (P : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C, ∀ x ∈ s, F x = P x + C}

private theorem deriv_zero_constant_on_open_preconnected
    {s : Set ℝ} (hopen : IsOpen s) (hs : IsPreconnected s) {G : ℝ → ℝ}
    (hderiv : ∀ x ∈ s, HasDerivAt G 0 x) :
    ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → G x = G y := by
  intro x hx y hy
  exact hopen.is_const_of_deriv_eq_zero hs
    (fun z hz => (hderiv z hz).differentiableAt.differentiableWithinAt)
    (fun z hz => (hderiv z hz).deriv) hx hy

theorem gap1 (x : ℝ) (hx : x ∈ domain) :
    integrand x = -(1 / 4 : ℝ) * deriv inner x / inner x := by
  have hinner : HasDerivAt inner (-4 * x) x := by
    unfold inner
    convert (hasDerivAt_const x (3 : ℝ)).sub
      ((hasDerivAt_const x (2 : ℝ)).mul ((hasDerivAt_id x).pow 2)) using 1 <;>
      simp [id] <;> ring
  unfold integrand
  rw [hinner.deriv]
  ring

theorem gap2 (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt primitive (integrand x) x := by
  have hinner : HasDerivAt inner (-4 * x) x := by
    unfold inner
    convert (hasDerivAt_const x (3 : ℝ)).sub
      ((hasDerivAt_const x (2 : ℝ)).mul ((hasDerivAt_id x).pow 2)) using 1 <;>
      simp [id] <;> ring
  have hlogabs : HasDerivAt (fun y : ℝ => Real.log |inner y|)
      ((-4 * x) / inner x) x := by
    simpa only [Real.log_abs] using hinner.log hx
  change HasDerivAt (fun y : ℝ => -(1 / 4 : ℝ) * Real.log |inner y|)
    (x / inner x) x
  convert hlogabs.const_mul (-(1 / 4 : ℝ)) using 1 <;> ring

theorem gap3 (s : Set ℝ) (hopen : IsOpen s) (hs : IsPreconnected s)
    (hdom : s ⊆ domain) :
    Family integrand s = Translates primitive s := by
  by_cases hempty : s = ∅
  · subst s
    ext F
    simp [Family, Translates, IsAntiderivativeOn]
  · obtain ⟨x₀, hx₀⟩ := Set.nonempty_iff_ne_empty.mpr hempty
    ext F
    change IsAntiderivativeOn F integrand s ↔
      ∃ C, ∀ x ∈ s, F x = primitive x + C
    constructor
    · intro hF
      let G : ℝ → ℝ := fun y => F y - primitive y
      have hzero : ∀ x ∈ s, HasDerivAt G 0 x := by
        intro x hx
        dsimp [G]
        simpa using (hF x hx).sub (gap2 x (hdom hx))
      have hconst := deriv_zero_constant_on_open_preconnected hopen hs hzero
      refine ⟨F x₀ - primitive x₀, ?_⟩
      intro x hx
      have hsame : G x = G x₀ := hconst hx hx₀
      dsimp [G] at hsame
      linarith
    · rintro ⟨C, hC⟩
      intro x hx
      have heq : Filter.EventuallyEq (nhds x) F
          (fun y => primitive y + C) := by
        filter_upwards [hopen.mem_nhds hx] with y hy
        exact hC y hy
      exact ((gap2 x (hdom hx)).add_const C).congr_of_eventuallyEq heq

end

end ProofGap.Exercise1676
