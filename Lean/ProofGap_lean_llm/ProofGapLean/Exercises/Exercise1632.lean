import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1632

noncomputable section

def domain : Set ℝ := Set.Ioi 0
def integrand (a x : ℝ) : ℝ := a / x + a ^ 2 / x ^ 2 + a ^ 3 / x ^ 3
def primitive (a x : ℝ) : ℝ :=
  a * Real.log |x| - a ^ 2 / x - a ^ 3 / (2 * x ^ 2)
def AntiderivativesOn (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | DifferentiableOn ℝ F domain ∧ ∀ x ∈ domain, deriv F x = g x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ domain, F x = p x + C}

private theorem primitive_hasDerivAt (a x : ℝ) (hx : x ∈ domain) :
    HasDerivAt (primitive a) (integrand a x) x := by
  have hxpos : 0 < x := by
    simpa [domain] using hx
  have hxne : x ≠ 0 := ne_of_gt hxpos
  have hlogabs : HasDerivAt (fun y : ℝ => Real.log |y|) x⁻¹ x := by
    apply (Real.hasDerivAt_log hxne).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hxpos] with y hy
    rw [abs_of_pos hy]
  have hlog : HasDerivAt (fun y : ℝ => a * Real.log |y|) (a * x⁻¹) x :=
    hlogabs.const_mul a
  have ht1raw :
      HasDerivAt (fun y : ℝ => a ^ 2 / y)
        ((0 * x - a ^ 2 * 1) / x ^ 2) x :=
    (hasDerivAt_const x (a ^ 2)).div (hasDerivAt_id x) hxne
  have ht1 :
      HasDerivAt (fun y : ℝ => a ^ 2 / y) (-a ^ 2 / x ^ 2) x := by
    convert ht1raw using 1 <;> ring
  have hdenDeriv :
      HasDerivAt (fun y : ℝ => 2 * y ^ 2) (2 * (2 * x)) x := by
    simpa [mul_assoc] using
      (((hasDerivAt_id x).pow 2).const_mul (2 : ℝ))
  have hden : (2 : ℝ) * x ^ 2 ≠ 0 := by
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hxne)
  have ht2raw :
      HasDerivAt (fun y : ℝ => a ^ 3 / (2 * y ^ 2))
        ((0 * (2 * x ^ 2) - a ^ 3 * (2 * (2 * x))) /
          (2 * x ^ 2) ^ 2) x :=
    (hasDerivAt_const x (a ^ 3)).div hdenDeriv hden
  have ht2 :
      HasDerivAt (fun y : ℝ => a ^ 3 / (2 * y ^ 2))
        (-a ^ 3 / x ^ 3) x := by
    convert ht2raw using 1 <;>
      field_simp [hxne] <;>
      ring
  convert (hlog.sub ht1).sub ht2 using 1
  simp only [integrand]
  field_simp [hxne] <;> ring

theorem gap1 (a : ℝ) :
    AntiderivativesOn (integrand a) = PrimitiveFamily (primitive a) := by
  ext F
  constructor
  · rintro ⟨hFdiff, hFderiv⟩
    let C : ℝ := F 1 - primitive a 1
    let G : ℝ → ℝ := fun x => primitive a x + C
    have hGhas (x : ℝ) (hx : x ∈ domain) :
        HasDerivAt G (integrand a x) x := by
      exact (primitive_hasDerivAt a x hx).add_const C
    have hGdiff : DifferentiableOn ℝ G domain := by
      intro x hx
      exact (hGhas x hx).differentiableAt.differentiableWithinAt
    let H : ℝ → ℝ := fun x => F x - G x
    have hHdiff : DifferentiableOn ℝ H domain := by
      exact hFdiff.sub hGdiff
    have hHzero : ∀ x ∈ domain, deriv H x = 0 := by
      intro x hx
      have hxpos : 0 < x := by
        simpa [domain] using hx
      have hFdiffAt : DifferentiableAt ℝ F x := by
        apply (hFdiff x hx).differentiableAt
        simpa [domain] using Ioi_mem_nhds hxpos
      have hFhas : HasDerivAt F (integrand a x) x := by
        rw [← hFderiv x hx]
        exact hFdiffAt.hasDerivAt
      simpa [H] using (hFhas.sub (hGhas x hx)).deriv
    have hopen : IsOpen domain := by
      simpa [domain] using (isOpen_Ioi : IsOpen (Set.Ioi (0 : ℝ)))
    have hpre : IsPreconnected domain := by
      simpa [domain] using
        (isPreconnected_Ioi : IsPreconnected (Set.Ioi (0 : ℝ)))
    have hconst : ∀ x ∈ domain, ∀ y ∈ domain, H x = H y := by
      intro x hx y hy
      exact hopen.is_const_of_deriv_eq_zero hpre hHdiff hHzero hx hy
    have hone : (1 : ℝ) ∈ domain := by
      simp [domain]
    refine ⟨C, ?_⟩
    intro x hx
    have hHx : H x = H 1 := hconst x hx 1 hone
    have hHone : H 1 = 0 := by
      dsimp [H, G, C]
      ring
    have hzero : H x = 0 := hHx.trans hHone
    dsimp [H, G] at hzero
    exact sub_eq_zero.mp hzero
  · rintro ⟨C, hFC⟩
    have hFhas (x : ℝ) (hx : x ∈ domain) :
        HasDerivAt F (integrand a x) x := by
      have hxpos : 0 < x := by
        simpa [domain] using hx
      apply ((primitive_hasDerivAt a x hx).add_const C).congr_of_eventuallyEq
      filter_upwards [Ioi_mem_nhds hxpos] with y hy
      exact hFC y (by simpa [domain] using hy)
    constructor
    · intro x hx
      exact (hFhas x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      exact (hFhas x hx).deriv

end
end ProofGap.Exercise1632
