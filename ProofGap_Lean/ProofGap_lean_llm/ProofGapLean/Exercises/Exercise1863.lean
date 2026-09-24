import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open Set Real

namespace ProofGap.Exercise1863

noncomputable section

def domain : Set ℝ := Set.Ioi (Real.sqrt (Real.sqrt 2 - 1))

def integrand (x : ℝ) : ℝ :=
  x * Real.sqrt (x ^ 4 + 2 * x ^ 2 - 1)

def rewrittenIntegrand (x : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (2 * x) *
    Real.sqrt ((x ^ 2 + 1) ^ 2 - 2)

def antiderivatives (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | DifferentiableOn ℝ F domain ∧ ∀ x ∈ domain, deriv F x = g x}

def primitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ domain, F x = p x + C}

def primitive (x : ℝ) : ℝ :=
  ((x ^ 2 + 1) / 4) * Real.sqrt (x ^ 4 + 2 * x ^ 2 - 1) -
    (1 / 2 : ℝ) *
      Real.log (x ^ 2 + 1 + Real.sqrt (x ^ 4 + 2 * x ^ 2 - 1))

private def v (x : ℝ) : ℝ := x ^ 2 + 1

private def outer (z : ℝ) : ℝ :=
  (z / 4) * Real.sqrt (z ^ 2 - 2) -
    (1 / 2 : ℝ) * Real.log (z + Real.sqrt (z ^ 2 - 2))

private theorem sqrt_two_sq : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
  Real.sq_sqrt (by norm_num)

private theorem sqrt_two_gt_one : 1 < Real.sqrt 2 := by
  have hsnonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  nlinarith [sqrt_two_sq]

private theorem domain_rad_pos {x : ℝ} (hx : x ∈ domain) :
    0 < x ^ 4 + 2 * x ^ 2 - 1 := by
  have ha : 0 ≤ Real.sqrt 2 - 1 := by
    linarith [sqrt_two_gt_one]
  have hroot_nonneg :
      0 ≤ Real.sqrt (Real.sqrt 2 - 1) :=
    Real.sqrt_nonneg _
  have hroot_sq :
      Real.sqrt (Real.sqrt 2 - 1) ^ 2 = Real.sqrt 2 - 1 :=
    Real.sq_sqrt ha
  have hx' : Real.sqrt (Real.sqrt 2 - 1) < x := hx
  have hxpos : 0 < x := lt_of_le_of_lt hroot_nonneg hx'
  have hprod :
      0 <
        (x - Real.sqrt (Real.sqrt 2 - 1)) *
          (x + Real.sqrt (Real.sqrt 2 - 1)) := by
    exact mul_pos (sub_pos.mpr hx')
      (add_pos_of_pos_of_nonneg hxpos hroot_nonneg)
  have hx_sq : Real.sqrt 2 - 1 < x ^ 2 := by
    nlinarith
  let z : ℝ := x ^ 2 + 1
  have hz : Real.sqrt 2 < z := by
    dsimp [z]
    linarith
  have hzpos : 0 < z := lt_trans (Real.sqrt_pos.2 (by norm_num)) hz
  have hzprod :
      0 < (z - Real.sqrt 2) * (z + Real.sqrt 2) :=
    mul_pos (sub_pos.mpr hz)
      (add_pos hzpos (Real.sqrt_pos.2 (by norm_num)))
  dsimp [z] at hzprod
  nlinarith [sqrt_two_sq]

private theorem outer_hasDerivAt {z : ℝ}
    (hz : 0 < z) (hrad : 0 < z ^ 2 - 2) :
    HasDerivAt outer ((1 / 2 : ℝ) * Real.sqrt (z ^ 2 - 2)) z := by
  have hspos : 0 < Real.sqrt (z ^ 2 - 2) := Real.sqrt_pos.2 hrad
  have hsne : Real.sqrt (z ^ 2 - 2) ≠ 0 := ne_of_gt hspos
  have hsq : Real.sqrt (z ^ 2 - 2) ^ 2 = z ^ 2 - 2 :=
    Real.sq_sqrt hrad.le
  have hinner :
      HasDerivAt (fun y : ℝ => y ^ 2 - 2) (2 * z) z := by
    convert ((hasDerivAt_id z).pow 2).sub_const 2 using 1 <;>
      simp only [id_eq] <;>
      ring
  have hs :
      HasDerivAt (fun y : ℝ => Real.sqrt (y ^ 2 - 2))
        (z / Real.sqrt (z ^ 2 - 2)) z := by
    convert
      (Real.hasDerivAt_sqrt (ne_of_gt hrad)).comp z hinner using 1 <;>
      field_simp [hsne] <;>
      ring
  have harg : 0 < z + Real.sqrt (z ^ 2 - 2) := by
    linarith
  have hlog :
      HasDerivAt
        (fun y : ℝ => Real.log (y + Real.sqrt (y ^ 2 - 2)))
        (1 / Real.sqrt (z ^ 2 - 2)) z := by
    have hraw :=
      (Real.hasDerivAt_log (ne_of_gt harg)).comp z
        ((hasDerivAt_id z).add hs)
    convert hraw using 1 <;>
      field_simp [hsne, ne_of_gt harg] <;>
      ring
  have hprod :
      HasDerivAt
        (fun y : ℝ => (y / 4) * Real.sqrt (y ^ 2 - 2))
        ((1 / 4) * Real.sqrt (z ^ 2 - 2) +
          (z / 4) * (z / Real.sqrt (z ^ 2 - 2))) z := by
    simpa only [id_eq] using
      ((hasDerivAt_id z).div_const 4).mul hs
  unfold outer
  convert hprod.sub (hlog.const_mul (1 / 2 : ℝ)) using 1
  field_simp [hsne]
  rw [hsq]
  ring

private theorem primitive_eq_outer : primitive = outer ∘ v := by
  funext x
  unfold primitive outer v Function.comp
  rw [show x ^ 4 + 2 * x ^ 2 - 1 =
    (x ^ 2 + 1) ^ 2 - 2 by ring]

private theorem primitive_hasDerivAt {x : ℝ} (hx : x ∈ domain) :
    HasDerivAt primitive (integrand x) x := by
  have hv : HasDerivAt v (2 * x) x := by
    unfold v
    convert ((hasDerivAt_id x).pow 2).add_const 1 using 1 <;>
      simp only [id_eq] <;>
      ring
  have hrad : 0 < v x ^ 2 - 2 := by
    unfold v
    nlinarith [domain_rad_pos hx]
  have hvpos : 0 < v x := by
    unfold v
    nlinarith [sq_nonneg x]
  rw [primitive_eq_outer]
  have hcomp := (outer_hasDerivAt hvpos hrad).comp x hv
  dsimp [v] at hcomp
  unfold integrand v
  convert hcomp using 1
  rw [show x ^ 4 + 2 * x ^ 2 - 1 =
    (x ^ 2 + 1) ^ 2 - 2 by ring]
  ring

theorem gap1 :
    antiderivatives integrand = antiderivatives rewrittenIntegrand := by
  have hfun : integrand = rewrittenIntegrand := by
    funext x
    unfold integrand rewrittenIntegrand
    rw [show x ^ 4 + 2 * x ^ 2 - 1 =
      (x ^ 2 + 1) ^ 2 - 2 by ring]
    ring
  rw [hfun]

theorem gap2 : antiderivatives integrand = primitiveFamily primitive := by
  ext F
  simp only [antiderivatives, primitiveFamily, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hFdiff, hFderiv⟩
    let H : ℝ → ℝ := fun x => F x - primitive x
    have hopen : IsOpen domain := by
      simpa [domain] using
        (isOpen_Ioi : IsOpen (Set.Ioi (Real.sqrt (Real.sqrt 2 - 1))))
    have hHzero : ∀ x ∈ domain, HasDerivAt H 0 x := by
      intro x hx
      have hFat : DifferentiableAt ℝ F x :=
        (hFdiff x hx).differentiableAt (hopen.mem_nhds hx)
      have hFder : HasDerivAt F (integrand x) x := by
        simpa only [hFderiv x hx] using hFat.hasDerivAt
      simpa [H] using hFder.sub (primitive_hasDerivAt hx)
    have hHdiff : DifferentiableOn ℝ H domain := by
      intro x hx
      exact (hHzero x hx).differentiableAt.differentiableWithinAt
    have hHderiv : ∀ x ∈ domain, deriv H x = 0 := by
      intro x hx
      exact (hHzero x hx).deriv
    have hpre : IsPreconnected domain := by
      exact (convex_Ioi (Real.sqrt (Real.sqrt 2 - 1))).isPreconnected
    let x₀ : ℝ := Real.sqrt (Real.sqrt 2 - 1) + 1
    have hx₀ : x₀ ∈ domain := by
      change Real.sqrt (Real.sqrt 2 - 1) < x₀
      dsimp [x₀]
      linarith
    refine ⟨F x₀ - primitive x₀, ?_⟩
    intro x hx
    have hc : H x = H x₀ :=
      hopen.is_const_of_deriv_eq_zero hpre hHdiff hHderiv hx hx₀
    dsimp [H] at hc
    linarith
  · rintro ⟨C, hFC⟩
    have hopen : IsOpen domain := by
      simpa [domain] using
        (isOpen_Ioi : IsOpen (Set.Ioi (Real.sqrt (Real.sqrt 2 - 1))))
    have hFat : ∀ x ∈ domain, HasDerivAt F (integrand x) x := by
      intro x hx
      have hsum := (primitive_hasDerivAt hx).add_const C
      have hevent : F =ᶠ[nhds x] fun y => primitive y + C := by
        filter_upwards [hopen.mem_nhds hx] with y hy
        exact hFC y hy
      exact hsum.congr_of_eventuallyEq hevent
    constructor
    · intro x hx
      exact (hFat x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      exact (hFat x hx).deriv

end

end ProofGap.Exercise1863
