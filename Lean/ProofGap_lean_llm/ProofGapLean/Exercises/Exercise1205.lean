import ProofGapLean.Prelude.Elementary
import ProofGapLean.Prelude.Finite
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise1205

noncomputable section

open Finset

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  (deriv^[n]) f

def y (x : ℝ) : ℝ :=
  Real.exp x / x

def recip : ℝ → ℝ :=
  fun x => 1 / x

def leibnizSum (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ range (n + 1),
    (Nat.choose n k : ℝ) * Real.exp x * iterDeriv k recip x

def falling (n k : ℕ) : ℝ :=
  ∏ j ∈ range k, ((n - j : ℕ) : ℝ)

def closedSum (n : ℕ) (x : ℝ) : ℝ :=
  1 / x +
    ∑ k ∈ Icc 1 n,
      (-1 : ℝ) ^ k * falling n k / x ^ (k + 1)

private theorem hasDerivAt_recipClosed (n : ℕ) (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt
      (fun z : ℝ => (-1 : ℝ) ^ n * (Nat.factorial n : ℝ) / z ^ (n + 1))
      ((-1 : ℝ) ^ (n + 1) * (Nat.factorial (n + 1) : ℝ) /
        x ^ (n + 2)) x := by
  have hpow := hasDerivAt_pow (n + 1) x
  have h := (hpow.inv (pow_ne_zero (n + 1) hx)).const_mul
    ((-1 : ℝ) ^ n * (Nat.factorial n : ℝ))
  convert h using 1
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one, Nat.add_sub_cancel, pow_succ]
  field_simp [hx]

private theorem iterDeriv_recip (n : ℕ) (x : ℝ) (hx : x ≠ 0) :
    iterDeriv n recip x =
      (-1 : ℝ) ^ n * (Nat.factorial n : ℝ) / x ^ (n + 1) := by
  induction n generalizing x with
  | zero =>
      simp [iterDeriv, recip]
  | succ n ih =>
      have heq : iterDeriv n recip =ᶠ[nhds x]
          (fun z : ℝ =>
            (-1 : ℝ) ^ n * (Nat.factorial n : ℝ) / z ^ (n + 1)) := by
        filter_upwards [eventually_ne_nhds hx] with z hz
        exact ih z hz
      have hsucc :
          iterDeriv (n + 1) recip = deriv (iterDeriv n recip) := by
        simp [iterDeriv, Function.iterate_succ_apply']
      rw [hsucc]
      calc
        deriv (iterDeriv n recip) x =
            deriv
              (fun z : ℝ =>
                (-1 : ℝ) ^ n * (Nat.factorial n : ℝ) / z ^ (n + 1)) x :=
          heq.deriv_eq
        _ = (-1 : ℝ) ^ (n + 1) *
              (Nat.factorial (n + 1) : ℝ) / x ^ (n + 2) :=
          (hasDerivAt_recipClosed n x hx).deriv

private theorem falling_eq_choose_mul_factorial (n k : ℕ) :
    falling n k =
      (Nat.choose n k : ℝ) * (Nat.factorial k : ℝ) := by
  calc
    falling n k = (n.descFactorial k : ℝ) := by
      rw [Nat.descFactorial_eq_prod_range]
      simp [falling]
    _ = (Nat.choose n k : ℝ) * (Nat.factorial k : ℝ) := by
      rw [Nat.descFactorial_eq_factorial_mul_choose]
      push_cast
      ring

theorem gap1 (n : ℕ) (x : ℝ) (hx : x ≠ 0) :
    iterDeriv n y x = leibnizSum n x := by
  have hf : ContDiffAt ℝ ⊤ recip x := by
    exact contDiffAt_const.div contDiffAt_id hx
  have hg : ContDiffAt ℝ ⊤ Real.exp x :=
    Real.contDiff_exp.contDiffAt
  have h := iteratedDeriv_mul (n := n) (x := x)
    (f := recip) (g := Real.exp) (hf.of_le le_top) (hg.of_le le_top)
  have hy : y = recip * Real.exp := by
    funext z
    simp [y, recip, div_eq_mul_inv, mul_comm]
  have hleib :
      iterDeriv n y x =
        ∑ k ∈ range (n + 1),
          (Nat.choose n k : ℝ) * iterDeriv k recip x *
            iterDeriv (n - k) Real.exp x := by
    rw [hy]
    simpa only [iteratedDeriv_eq_iterate, iterDeriv, mul_assoc] using h
  rw [hleib]
  unfold leibnizSum
  apply sum_congr rfl
  intro k hk
  have hexp : iterDeriv (n - k) Real.exp x = Real.exp x := by
    have hexp' := congrFun (iteratedDeriv_exp_const_mul (n - k) 1) x
    simpa only [iteratedDeriv_eq_iterate, iterDeriv, one_mul, one_pow]
      using hexp'
  rw [hexp]
  ring

theorem gap2 (n : ℕ) (x : ℝ) (hx : x ≠ 0) :
    leibnizSum n x = Real.exp x * closedSum n x := by
  have hrange : range (n + 1) = insert 0 (Icc 1 n) := by
    ext k
    simp only [mem_range, mem_insert, mem_Icc]
    omega
  unfold leibnizSum closedSum
  rw [hrange, sum_insert (by simp)]
  have hzero : iterDeriv 0 recip x = 1 / x := by
    rfl
  rw [hzero]
  simp only [Nat.choose_zero_right, Nat.cast_one, one_mul]
  have hsum :
      (∑ k ∈ Icc 1 n,
          (Nat.choose n k : ℝ) * Real.exp x * iterDeriv k recip x) =
        Real.exp x *
          ∑ k ∈ Icc 1 n,
            (-1 : ℝ) ^ k * falling n k / x ^ (k + 1) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro k hk
    rw [iterDeriv_recip k x hx, falling_eq_choose_mul_factorial]
    ring
  rw [hsum]
  ring

theorem gap3 (n : ℕ) (x : ℝ) (hx : x ≠ 0) :
    iterDeriv n y x = Real.exp x * closedSum n x := by
  rw [gap1 n x hx, gap2 n x hx]

end

end ProofGap.Exercise1205
