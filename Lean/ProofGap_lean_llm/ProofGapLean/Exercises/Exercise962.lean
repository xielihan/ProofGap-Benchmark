import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise962

noncomputable section

def xa (a x : ℝ) : ℝ := Real.rpow x a
def ax (a x : ℝ) : ℝ := Real.rpow a x
def xx (x : ℝ) : ℝ := Real.rpow x x

def y (a x : ℝ) : ℝ :=
  Real.rpow x (xa a x) + Real.rpow x (ax a x) +
    Real.rpow a (xx x)

def expandedDerivative (a x : ℝ) : ℝ :=
  Real.rpow x (xa a x) *
      (a * Real.rpow x (a - 1) * Real.log x + xa a x / x) +
    Real.rpow x (ax a x) *
      (ax a x * Real.log a * Real.log x + ax a x / x) +
    Real.rpow a (xx x) * Real.log a * xx x * (1 + Real.log x)

def finalDerivative (a x : ℝ) : ℝ :=
  Real.rpow x (a - 1) * Real.rpow x (xa a x) *
      (1 + a * Real.log x) +
    ax a x * Real.rpow x (ax a x) *
      (1 / x + Real.log a * Real.log x) +
    xx x * Real.rpow a (xx x) * Real.log a * (1 + Real.log x)

private theorem rpow_sub_one_eq_div_xa (a x : ℝ) (hx : 0 < x) :
    Real.rpow x (a - 1) = xa a x / x := by
  apply (eq_div_iff hx.ne').2
  simpa [xa] using (Real.rpow_add hx (a - 1) 1).symm

theorem gap1 (a x : ℝ) (ha : 0 < a) (hx : 0 < x) :
    HasDerivAt (y a) (expandedDerivative a x) x := by
  have hxa :
      HasDerivAt (xa a) (a * Real.rpow x (a - 1)) x := by
    simpa [xa] using
      ((hasDerivAt_id x).rpow (hasDerivAt_const x a) hx)
  have hax :
      HasDerivAt (ax a) (ax a x * Real.log a) x := by
    simpa [ax] using
      ((hasDerivAt_const x a).rpow (hasDerivAt_id x) ha)
  have hxx :
      HasDerivAt xx (xx x * (1 + Real.log x)) x := by
    convert (hasDerivAt_id x).rpow (hasDerivAt_id x) hx using 1 <;>
      simp [xx]
    have hpowxx :
        x ^ (x - 1) = x ^ x / x := by
      change Real.rpow x (x - 1) = Real.rpow x x / x
      exact rpow_sub_one_eq_div_xa x x hx
    rw [hpowxx]
    field_simp [hx.ne'] <;> ring
  have hfirst :
      HasDerivAt (fun t : ℝ => Real.rpow t (xa a t))
        (Real.rpow x (xa a x) *
          (a * Real.rpow x (a - 1) * Real.log x + xa a x / x)) x := by
    convert (hasDerivAt_id x).rpow hxa hx using 1 <;>
      simp [xa]
    have hpowfirst :
        x ^ (x ^ a - 1) = x ^ (x ^ a) / x := by
      change Real.rpow x (Real.rpow x a - 1) =
        Real.rpow x (Real.rpow x a) / x
      exact rpow_sub_one_eq_div_xa (Real.rpow x a) x hx
    rw [hpowfirst]
    field_simp [hx.ne'] <;> ring
  have hsecond :
      HasDerivAt (fun t : ℝ => Real.rpow t (ax a t))
        (Real.rpow x (ax a x) *
          (ax a x * Real.log a * Real.log x + ax a x / x)) x := by
    convert (hasDerivAt_id x).rpow hax hx using 1 <;>
      simp [ax]
    have hpowsecond :
        x ^ (a ^ x - 1) = x ^ (a ^ x) / x := by
      change Real.rpow x (Real.rpow a x - 1) =
        Real.rpow x (Real.rpow a x) / x
      exact rpow_sub_one_eq_div_xa (Real.rpow a x) x hx
    rw [hpowsecond]
    field_simp [hx.ne'] <;> ring
  have hthird :
      HasDerivAt (fun t : ℝ => Real.rpow a (xx t))
        (Real.rpow a (xx x) * Real.log a * xx x *
          (1 + Real.log x)) x := by
    convert (hasDerivAt_const x a).rpow hxx ha using 1 <;>
      simp [xx] <;> ring
  simpa only [y, expandedDerivative] using
    (hfirst.add hsecond).add hthird

theorem gap2 (a x : ℝ) (ha : 0 < a) (hx : 0 < x) :
    expandedDerivative a x = finalDerivative a x := by
  have hpow := rpow_sub_one_eq_div_xa a x hx
  unfold expandedDerivative finalDerivative
  rw [hpow]
  ring

theorem gap3 (a x : ℝ) (ha : 0 < a) (hx : 0 < x) :
    HasDerivAt (y a) (finalDerivative a x) x := by
  rw [← gap2 a x ha hx]
  exact gap1 a x ha hx

end

end ProofGap.Exercise962
