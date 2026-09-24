import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1313

noncomputable section

def power (p x : ℝ) : ℝ := Real.rpow x p
def xlogx (x : ℝ) : ℝ := x * Real.log x

private theorem hasDerivAt_power (p x : ℝ) (hx : 0 < x) :
    HasDerivAt (power p)
      (p * Real.rpow x (p - 1)) x := by
  simpa only [power] using
    (Real.hasDerivAt_rpow_const (p := p) (Or.inl hx.ne') :
      HasDerivAt (fun y : ℝ => Real.rpow y p)
        (p * Real.rpow x (p - 1)) x)

private theorem hasDerivAt_deriv_power (p x : ℝ) (hx : 0 < x) :
    HasDerivAt (deriv (power p))
      (p * (p - 1) * Real.rpow x (p - 2)) x := by
  have hlocal :
      deriv (power p) =ᶠ[nhds x]
        (fun y : ℝ => p * Real.rpow y (p - 1)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
    exact (hasDerivAt_power p y hy).deriv
  have hmodel :
      HasDerivAt (fun y : ℝ => p * Real.rpow y (p - 1))
        (p * (p - 1) * Real.rpow x (p - 2)) x := by
    have he : p - 1 - 1 = p - 2 := by ring
    simpa only [power, he, mul_assoc] using
      (hasDerivAt_power (p - 1) x hx).const_mul p
  exact hmodel.congr_of_eventuallyEq hlocal

private theorem hasDerivAt_xlogx (x : ℝ) (hx : 0 < x) :
    HasDerivAt xlogx (Real.log x + 1) x := by
  simpa [xlogx, hx.ne'] using
    (hasDerivAt_id x).mul (Real.hasDerivAt_log hx.ne')

private theorem hasDerivAt_deriv_xlogx (x : ℝ) (hx : 0 < x) :
    HasDerivAt (deriv xlogx) (1 / x) x := by
  have hlocal :
      deriv xlogx =ᶠ[nhds x] (fun y : ℝ => Real.log y + 1) := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
    exact (hasDerivAt_xlogx y hy).deriv
  have hmodel :
      HasDerivAt (fun y : ℝ => Real.log y + 1) (1 / x) x := by
    simpa only [one_div] using (Real.hasDerivAt_log hx.ne').add_const 1
  exact hmodel.congr_of_eventuallyEq hlocal

private theorem deriv_log_eq (x : ℝ) (hx : 0 < x) :
    deriv Real.log x = 1 / x := by
  simpa only [one_div] using (Real.hasDerivAt_log hx.ne').deriv

private theorem hasDerivAt_deriv_log (x : ℝ) (hx : 0 < x) :
    HasDerivAt (deriv Real.log) (-(1 / x ^ 2)) x := by
  have hlocal :
      deriv Real.log =ᶠ[nhds x] (fun y : ℝ => 1 / y) := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
    exact deriv_log_eq y hy
  have hmodel :
      HasDerivAt (fun y : ℝ => 1 / y) (-(1 / x ^ 2)) x := by
    have h := (hasDerivAt_id x).inv hx.ne'
    change HasDerivAt (fun y : ℝ => y⁻¹) (-1 / x ^ 2) x at h
    simpa only [one_div, neg_div] using h
  exact hmodel.congr_of_eventuallyEq hlocal

private theorem deriv_exp_eq : deriv Real.exp = Real.exp := by
  funext x
  exact (Real.hasDerivAt_exp x).deriv

theorem gap1 (p x : ℝ) (hx : 0 < x) :
    deriv (deriv (power p)) x =
      p * (p - 1) * Real.rpow x (p - 2) := by
  exact (hasDerivAt_deriv_power p x hx).deriv

theorem gap2 (p x : ℝ) (hp : 1 < p) (hx : 0 < x) :
    0 < deriv (deriv (power p)) x := by
  rw [gap1 p x hx]
  exact mul_pos
    (mul_pos (lt_trans zero_lt_one hp) (sub_pos.mpr hp))
    (Real.rpow_pos_of_pos hx _)

theorem gap3 (p : ℝ) (hp : 1 < p) :
    StrictConvexOn ℝ (Set.Ioi 0) (power p) := by
  apply strictConvexOn_of_deriv2_pos (convex_Ioi 0)
  · intro x hx
    exact (hasDerivAt_power p x hx).continuousAt.continuousWithinAt
  · intro x hx
    exact gap2 p x hp (by simpa only [isOpen_Ioi.interior_eq] using hx)

theorem gap4 (p x : ℝ) (hp0 : 0 < p) (hp1 : p < 1)
    (hx : 0 < x) :
    deriv (deriv (power p)) x < 0 := by
  rw [gap1 p x hx]
  exact mul_neg_of_neg_of_pos
    (mul_neg_of_pos_of_neg hp0 (sub_neg.mpr hp1))
    (Real.rpow_pos_of_pos hx _)

theorem gap5 (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    StrictConcaveOn ℝ (Set.Ioi 0) (power p) := by
  apply strictConcaveOn_of_deriv2_neg (convex_Ioi 0)
  · intro x hx
    exact (hasDerivAt_power p x hx).continuousAt.continuousWithinAt
  · intro x hx
    exact gap4 p x hp0 hp1 (by simpa only [isOpen_Ioi.interior_eq] using hx)

theorem gap6 (x : ℝ) :
    deriv (deriv Real.exp) x = Real.exp x := by
  rw [deriv_exp_eq]
  exact (Real.hasDerivAt_exp x).deriv

theorem gap7 (x : ℝ) :
    0 < deriv (deriv Real.exp) x := by
  rw [gap6 x]
  exact Real.exp_pos x

theorem gap8 :
    StrictConvexOn ℝ Set.univ Real.exp := by
  apply strictConvexOn_of_deriv2_pos convex_univ
  · intro x hx
    exact (Real.hasDerivAt_exp x).continuousAt.continuousWithinAt
  · intro x hx
    exact gap7 x

theorem gap9 (x : ℝ) (hx : 0 < x) :
    deriv (deriv xlogx) x = 1 / x := by
  exact (hasDerivAt_deriv_xlogx x hx).deriv

theorem gap10 (x : ℝ) (hx : 0 < x) :
    0 < deriv (deriv xlogx) x := by
  rw [gap9 x hx]
  exact one_div_pos.mpr hx

theorem gap11 :
    StrictConvexOn ℝ (Set.Ioi 0) xlogx := by
  apply strictConvexOn_of_deriv2_pos (convex_Ioi 0)
  · intro x hx
    exact (hasDerivAt_xlogx x hx).continuousAt.continuousWithinAt
  · intro x hx
    exact gap10 x (by simpa only [isOpen_Ioi.interior_eq] using hx)

theorem gap12 (x : ℝ) (hx : 0 < x) :
    deriv (deriv Real.log) x = -(1 / x ^ 2) := by
  exact (hasDerivAt_deriv_log x hx).deriv

theorem gap13 (x : ℝ) (hx : 0 < x) :
    deriv (deriv Real.log) x < 0 := by
  rw [gap12 x hx]
  exact neg_lt_zero.mpr (one_div_pos.mpr (sq_pos_of_pos hx))

theorem gap14 :
    StrictConcaveOn ℝ (Set.Ioi 0) Real.log := by
  apply strictConcaveOn_of_deriv2_neg (convex_Ioi 0)
  · intro x hx
    exact (Real.hasDerivAt_log hx.ne').continuousAt.continuousWithinAt
  · intro x hx
    exact gap13 x (by simpa only [isOpen_Ioi.interior_eq] using hx)

theorem gap15 (p : ℝ) :
    (1 < p → StrictConvexOn ℝ (Set.Ioi 0) (power p)) ∧
    (0 < p → p < 1 →
      StrictConcaveOn ℝ (Set.Ioi 0) (power p)) ∧
    StrictConvexOn ℝ Set.univ Real.exp ∧
    StrictConvexOn ℝ (Set.Ioi 0) xlogx ∧
    StrictConcaveOn ℝ (Set.Ioi 0) Real.log := by
  exact ⟨fun hp => gap3 p hp,
    fun hp0 hp1 => gap5 p hp0 hp1,
    gap8, gap11, gap14⟩

end

end ProofGap.Exercise1313
