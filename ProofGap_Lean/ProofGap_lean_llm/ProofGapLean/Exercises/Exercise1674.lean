import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1674

noncomputable section

def integrand (x : ℝ) : ℝ := x / Real.sqrt (1 - x ^ 2)
def primitive (x : ℝ) : ℝ := -Real.sqrt (1 - x ^ 2)
def domain : Set ℝ := Set.Ioo (-1) 1

def IsAntiderivativeOn (F f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, HasDerivAt F (f x) x
def Family (f : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | IsAntiderivativeOn F f s}
def Translates (P : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C, ∀ x ∈ s, F x = P x + C}

theorem gap1 (x : ℝ) (hx : x ∈ domain) :
    integrand x =
      -(1 / (2 * Real.sqrt (1 - x ^ 2))) * deriv (fun y => 1 - y ^ 2) x := by
  change -1 < x ∧ x < 1 at hx
  have hprod : 0 < (1 - x) * (1 + x) :=
    mul_pos (by linarith) (by linarith)
  have harg : 0 < 1 - x ^ 2 := by
    nlinarith
  have hsqrt : Real.sqrt (1 - x ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 harg)
  have hd : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-2 * x) x := by
    simpa [pow_two] using
      ((hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).pow 2))
  rw [hd.deriv]
  unfold integrand
  field_simp [hsqrt] <;> ring

theorem gap2 (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt primitive (integrand x) x := by
  have hx' : -1 < x ∧ x < 1 := by
    simpa [domain] using hx
  have hprod : 0 < (1 - x) * (1 + x) :=
    mul_pos (by linarith [hx'.2]) (by linarith [hx'.1])
  have harg : 0 < 1 - x ^ 2 := by
    nlinarith
  have hne : 1 - x ^ 2 ≠ 0 := ne_of_gt harg
  have hinner : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-2 * x) x := by
    simpa [pow_two, two_mul] using
      ((hasDerivAt_const x (1 : ℝ)).sub
        ((hasDerivAt_id x).mul (hasDerivAt_id x)))
  have h := ((Real.hasDerivAt_sqrt hne).comp x hinner).neg
  rw [gap1 x hx, hinner.deriv]
  simpa [primitive] using h

theorem gap3 :
    Family integrand domain = Translates primitive domain := by
  ext F
  constructor
  · intro hF
    change IsAntiderivativeOn F integrand domain at hF
    change ∃ C : ℝ, ∀ x ∈ domain, F x = primitive x + C
    let H : ℝ → ℝ := fun z => F z - primitive z
    have hd (z : ℝ) (hz : z ∈ domain) : HasDerivAt H 0 z := by
      simpa [H] using (hF z hz).sub (gap2 z hz)
    have hdiff : DifferentiableOn ℝ H domain := by
      intro z hz
      exact (hd z hz).differentiableAt.differentiableWithinAt
    have hderiv : ∀ z ∈ domain, deriv H z = 0 := by
      intro z hz
      exact (hd z hz).deriv
    have hopen : IsOpen domain := by
      simpa [domain] using
        (isOpen_Ioo : IsOpen (Set.Ioo (-1 : ℝ) 1))
    have hpre : IsPreconnected domain := by
      simpa [domain] using
        (isPreconnected_Ioo : IsPreconnected (Set.Ioo (-1 : ℝ) 1))
    have hconst (a : ℝ) (ha : a ∈ domain) (b : ℝ) (hb : b ∈ domain) :
        H a = H b := by
      exact hopen.is_const_of_deriv_eq_zero hpre hdiff hderiv ha hb
    refine ⟨F 0 - primitive 0, ?_⟩
    intro x hx
    have hzero : (0 : ℝ) ∈ domain := by
      change -1 < (0 : ℝ) ∧ (0 : ℝ) < 1
      constructor <;> linarith
    have heq : H x = H 0 := hconst x hx 0 hzero
    dsimp [H] at heq
    linarith
  · intro hT
    change (∃ C : ℝ, ∀ x ∈ domain, F x = primitive x + C) at hT
    rcases hT with ⟨C, hC⟩
    change IsAntiderivativeOn F integrand domain
    intro x hx
    have hopen : IsOpen domain := by
      simpa [domain] using
        (isOpen_Ioo : IsOpen (Set.Ioo (-1 : ℝ) 1))
    have heq : Filter.EventuallyEq (nhds x) F (fun y => primitive y + C) := by
      filter_upwards [hopen.mem_nhds hx] with y hy
      exact hC y hy
    exact ((gap2 x hx).add_const C).congr_of_eventuallyEq heq

end

end ProofGap.Exercise1674
