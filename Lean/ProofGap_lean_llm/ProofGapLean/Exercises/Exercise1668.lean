import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1668

noncomputable section

def integrand (x : ℝ) : ℝ := 1 / (1 + Real.cos x)
def primitive (x : ℝ) : ℝ := Real.tan (x / 2)
def domain : Set ℝ := {x | Real.cos (x / 2) ≠ 0}

def IsAntiderivativeOn (F f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, HasDerivAt F (f x) x
def Family (f : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | IsAntiderivativeOn F f s}
def Translates (P : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C, ∀ x ∈ s, F x = P x + C}

private theorem derivative_zero_eqOn {G : ℝ → ℝ} {s : Set ℝ}
    (hs : IsPreconnected s)
    (hG : ∀ x ∈ s, HasDerivAt G 0 x) :
    ∀ ⦃x y⦄, x ∈ s → y ∈ s → G x = G y := by
  have ordered :
      ∀ ⦃a b⦄, a ∈ s → b ∈ s → a < b → G a = G b := by
    intro a b ha hb hab
    have hsord : s.OrdConnected := hs.ordConnected
    have hsub : Set.Icc a b ⊆ s := hsord.out ha hb
    have hcont : ContinuousOn G (Set.Icc a b) := by
      intro z hz
      exact (hG z (hsub hz)).continuousAt.continuousWithinAt
    have hdiff : DifferentiableOn ℝ G (Set.Ioo a b) := by
      intro z hz
      exact (hG z (hsub ⟨hz.1.le, hz.2.le⟩)).differentiableAt.differentiableWithinAt
    rcases exists_deriv_eq_slope G hab hcont hdiff with ⟨z, hz, heq⟩
    have hd0 : deriv G z = 0 :=
      (hG z (hsub ⟨hz.1.le, hz.2.le⟩)).deriv
    have hquot : (G b - G a) / (b - a) = 0 := by
      calc
        (G b - G a) / (b - a) = deriv G z := heq.symm
        _ = 0 := hd0
    have hden : b - a ≠ 0 := sub_ne_zero.mpr hab.ne'
    have hnum : G b - G a = 0 := by
      calc
        G b - G a = ((G b - G a) / (b - a)) * (b - a) := by
          field_simp [hden]
        _ = 0 := by rw [hquot, zero_mul]
    exact (sub_eq_zero.mp hnum).symm
  intro x y hx hy
  rcases lt_trichotomy x y with hxy | hxy | hyx
  · exact ordered hx hy hxy
  · subst y
    rfl
  · exact (ordered hy hx hyx).symm

theorem gap1 (x : ℝ) :
    1 + Real.cos x = 2 * Real.cos (x / 2) ^ 2 := by
  rw [show x = 2 * (x / 2) by ring, Real.cos_two_mul]
  ring

theorem gap2 (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt primitive (integrand x) x := by
  change Real.cos (x / 2) ≠ 0 at hx
  have ht :=
    (Real.hasDerivAt_tan hx).comp x ((hasDerivAt_id x).div_const 2)
  have hcoef :
      integrand x = (1 / Real.cos (x / 2) ^ 2) * (1 / 2) := by
    rw [integrand, gap1]
    field_simp [hx]
  simpa only [primitive, hcoef] using ht

theorem gap3 (s : Set ℝ) (hopen : IsOpen s) (hs : IsPreconnected s)
    (hdom : s ⊆ domain) :
    Family integrand s = Translates primitive s := by
  ext F
  constructor
  · intro hF
    change IsAntiderivativeOn F integrand s at hF
    change ∃ C : ℝ, ∀ x ∈ s, F x = primitive x + C
    by_cases hne : s.Nonempty
    · rcases hne with ⟨x₀, hx₀⟩
      have hzero :
          ∀ z ∈ s, HasDerivAt (fun t => F t - primitive t) 0 z := by
        intro z hz
        simpa using (hF z hz).sub (gap2 z (hdom hz))
      refine ⟨F x₀ - primitive x₀, ?_⟩
      intro x hx
      have heq :
          F x - primitive x = F x₀ - primitive x₀ :=
        derivative_zero_eqOn hs hzero hx hx₀
      calc
        F x = primitive x + (F x - primitive x) := by ring
        _ = primitive x + (F x₀ - primitive x₀) := by rw [heq]
    · refine ⟨0, ?_⟩
      intro x hx
      exact (hne ⟨x, hx⟩).elim
  · intro hF
    change (∃ C : ℝ, ∀ x ∈ s, F x = primitive x + C) at hF
    rcases hF with ⟨C, hC⟩
    change IsAntiderivativeOn F integrand s
    intro x hx
    have hmodel :
        HasDerivAt (fun y => primitive y + C) (integrand x) x :=
      (gap2 x (hdom hx)).add_const C
    have heq :
        F =ᶠ[nhds x] (fun y => primitive y + C) :=
      Filter.mem_of_superset (hopen.mem_nhds hx) (fun y hy => hC y hy)
    exact hmodel.congr_of_eventuallyEq heq

end

end ProofGap.Exercise1668
