import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1157

noncomputable section

def nthDeriv : ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0, f => f
  | n + 1, f => deriv (nthDeriv n f)

def y (a : ℝ) (m : ℕ) (x : ℝ) : ℝ := a / x ^ m

private theorem hasDerivAt_nat_succ_power_aux1157 (n : ℕ) (x : ℝ) :
    HasDerivAt (fun z : ℝ => z ^ (n + 1))
      (((n + 1 : ℕ) : ℝ) * x ^ n) x := by
  induction n with
  | zero =>
      simpa using (hasDerivAt_id x)
  | succ n ih =>
      convert ih.mul (hasDerivAt_id x) using 1 <;>
        simp [pow_succ, Nat.cast_add, Nat.cast_one] <;> ring

theorem gap1 (a : ℝ) (m : ℕ) (x : ℝ) (hx : x ≠ 0) :
    deriv (y a m) x = -(a * (m : ℝ)) / x ^ (m + 1) := by
  unfold y
  cases m with
  | zero =>
      simpa using (hasDerivAt_const x a).deriv
  | succ n =>
      have hpow : HasDerivAt (fun z : ℝ => z ^ (n + 1))
          (((n + 1 : ℕ) : ℝ) * x ^ n) x :=
        hasDerivAt_nat_succ_power_aux1157 n x
      have hquot : HasDerivAt (fun z : ℝ => a / z ^ (n + 1))
          ((0 * x ^ (n + 1) - a * (((n + 1 : ℕ) : ℝ) * x ^ n)) /
            (x ^ (n + 1)) ^ 2) x :=
        (hasDerivAt_const x a).div hpow (pow_ne_zero (n + 1) hx)
      rw [hquot.deriv]
      simp [pow_succ] <;> field_simp [hx] <;> ring

theorem gap2 (a : ℝ) (m : ℕ) (x : ℝ) (hx : x ≠ 0) :
    nthDeriv 2 (y a m) x =
      a * (m : ℝ) * (m + 1 : ℝ) / x ^ (m + 2) := by
  have hlocal :
      (fun z : ℝ => deriv (y a m) z) =ᶠ[nhds x]
        y (-(a * (m : ℝ))) (m + 1) := by
    filter_upwards [eventually_ne_nhds hx] with z hz
    simpa [y] using (gap1 a m z hz)
  change deriv (fun z : ℝ => deriv (y a m) z) x =
    a * (m : ℝ) * (m + 1 : ℝ) / x ^ (m + 2)
  calc
    deriv (fun z : ℝ => deriv (y a m) z) x =
        deriv (y (-(a * (m : ℝ))) (m + 1)) x := hlocal.deriv_eq
    _ = a * (m : ℝ) * (m + 1 : ℝ) / x ^ (m + 2) := by
      rw [gap1 (-(a * (m : ℝ))) (m + 1) x hx]
      norm_num [Nat.cast_add, Nat.cast_one, Nat.add_assoc] <;> ring

theorem gap3 (a : ℝ) (m : ℕ) (x : ℝ) (hx : x ≠ 0) :
    nthDeriv 3 (y a m) x =
      -(a * (m : ℝ) * (m + 1 : ℝ) * (m + 2 : ℝ)) / x ^ (m + 3) := by
  have hlocal :
      (fun z : ℝ => nthDeriv 2 (y a m) z) =ᶠ[nhds x]
        y (a * (m : ℝ) * (m + 1 : ℝ)) (m + 2) := by
    filter_upwards [eventually_ne_nhds hx] with z hz
    simpa [y] using (gap2 a m z hz)
  change deriv (fun z : ℝ => nthDeriv 2 (y a m) z) x =
    -(a * (m : ℝ) * (m + 1 : ℝ) * (m + 2 : ℝ)) / x ^ (m + 3)
  calc
    deriv (fun z : ℝ => nthDeriv 2 (y a m) z) x =
        deriv (y (a * (m : ℝ) * (m + 1 : ℝ)) (m + 2)) x := hlocal.deriv_eq
    _ = -(a * (m : ℝ) * (m + 1 : ℝ) * (m + 2 : ℝ)) /
        x ^ (m + 3) := by
      rw [gap1 (a * (m : ℝ) * (m + 1 : ℝ)) (m + 2) x hx]
      norm_num [Nat.cast_add, Nat.cast_one, Nat.add_assoc] <;> ring

theorem gap4 (a : ℝ) (m : ℕ) (x : ℝ) (hx : x ≠ 0) :
    -(a * (m : ℝ) * (m + 1 : ℝ) * (m + 2 : ℝ)) / x ^ (m + 3) =
      -(a * (m : ℝ) * (m + 1 : ℝ) * (m + 2 : ℝ) / x ^ (m + 3)) := by
  ring

theorem gap5 (a : ℝ) (m : ℕ) (x : ℝ) (hx : x ≠ 0) :
    nthDeriv 3 (y a m) x =
      -(a * (m : ℝ) * (m + 1 : ℝ) * (m + 2 : ℝ)) / x ^ (m + 3) := by
  exact gap3 a m x hx

end

end ProofGap.Exercise1157
