import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1793

noncomputable section

def domain : Set ℝ := Set.Ioi 0
def integrand (x : ℝ) : ℝ := (Real.log x / x) ^ 2
def primitive (x : ℝ) : ℝ :=
  -(Real.log x ^ 2 + 2 * Real.log x + 2) / x
def IsAntiderivativeOn (F f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, HasDerivAt F (f x) x
def Family (f : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | IsAntiderivativeOn F f s}
def Translates (P : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C, ∀ x ∈ s, F x = P x + C}

theorem gap1 (x : ℝ) (hx : x ∈ domain) :
    integrand x = Real.log x ^ 2 / x ^ 2 := by
  simp [integrand, div_pow]

theorem gap2 (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt (fun y => -Real.log y ^ 2 / y)
      (Real.log x ^ 2 / x ^ 2 - 2 * Real.log x / x ^ 2) x := by
  have hxpos : 0 < x := hx
  have hx0 : x ≠ 0 := ne_of_gt hxpos
  have h :=
    ((Real.hasDerivAt_log hx0).pow 2).neg.div (hasDerivAt_id x) hx0
  convert h using 1 <;>
    norm_num [id] <;>
    field_simp [hx0] <;>
    ring

theorem gap3 (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt (fun y => -(2 * Real.log y) / y)
      (2 * Real.log x / x ^ 2 - 2 / x ^ 2) x := by
  have hxpos : 0 < x := hx
  have hx0 : x ≠ 0 := ne_of_gt hxpos
  have h :=
    ((Real.hasDerivAt_log hx0).const_mul 2).neg.div (hasDerivAt_id x) hx0
  convert h using 1 <;>
    norm_num [id] <;>
    field_simp [hx0] <;>
    ring

theorem gap4 (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt
      (fun y => -Real.log y ^ 2 / y - 2 * Real.log y / y)
      (integrand x - 2 / x ^ 2) x := by
  rw [gap1 x hx]
  have h := (gap2 x hx).add (gap3 x hx)
  convert h using 1
  · funext y
    dsimp
    ring_nf
  · ring

theorem gap5 (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt (fun y => -2 / y) (2 / x ^ 2) x := by
  have hxpos : 0 < x := hx
  have hx0 : x ≠ 0 := ne_of_gt hxpos
  have h := (hasDerivAt_const x (-2 : ℝ)).div (hasDerivAt_id x) hx0
  convert h using 1 <;> norm_num [id]

theorem gap6 (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt primitive (integrand x) x := by
  have h := (gap4 x hx).add (gap5 x hx)
  convert h using 1
  · funext y
    dsimp [primitive]
    ring
  · ring

theorem gap7 :
    Family integrand domain = Translates primitive domain := by
  ext F
  constructor
  · intro hF
    change IsAntiderivativeOn F integrand domain at hF
    change ∃ C, ∀ x ∈ domain, F x = primitive x + C
    have hzero : ∀ x ∈ domain,
        HasDerivAt (fun y => F y - primitive y) 0 x := by
      intro x hx
      simpa using (hF x hx).sub (gap6 x hx)
    have hdiff : DifferentiableOn ℝ (fun y => F y - primitive y) domain := by
      intro x hx
      exact (hzero x hx).differentiableAt.differentiableWithinAt
    have hderiv : ∀ x ∈ domain,
        deriv (fun y => F y - primitive y) x = 0 := by
      intro x hx
      exact (hzero x hx).deriv
    have hopen : IsOpen domain := by
      simpa [domain] using isOpen_Ioi
    have hpre : IsPreconnected domain := by
      simpa [domain] using isPreconnected_Ioi
    have hone : (1 : ℝ) ∈ domain := by
      norm_num [domain]
    refine ⟨F 1 - primitive 1, ?_⟩
    intro x hx
    have heq : F x - primitive x = F 1 - primitive 1 := by
      exact hopen.is_const_of_deriv_eq_zero hpre hdiff hderiv hx hone
    linarith
  · rintro ⟨C, hC⟩
    change IsAntiderivativeOn F integrand domain
    intro x hx
    have hopen : IsOpen domain := by
      simpa [domain] using isOpen_Ioi
    have hev : F =ᶠ[nhds x] (fun y => primitive y + C) := by
      filter_upwards [hopen.mem_nhds hx] with y hy
      exact hC y hy
    exact ((gap6 x hx).add_const C).congr_of_eventuallyEq hev

end

end ProofGap.Exercise1793
