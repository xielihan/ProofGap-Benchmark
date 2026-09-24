import ProofGapLean.Prelude.Analysis
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace ProofGap.Exercise2844

noncomputable section

def exponentialTerm (a x : ℝ) (n : ℕ) : ℝ :=
  Real.log a ^ n / (Nat.factorial n : ℝ) * x ^ n

def coefficientRoot (a : ℝ) (n : ℕ) : ℝ :=
  Real.rpow |Real.log a ^ n / (Nat.factorial n : ℝ)| (1 / (n : ℝ))

def inverseFactorialRoot (n : ℕ) : ℝ :=
  1 / Real.rpow (Nat.factorial n : ℝ) (1 / (n : ℝ))

def HasInfiniteRadius (c : ℕ → ℝ) : Prop :=
  ∀ x : ℝ, Summable (fun n => c n * x ^ n)

private theorem coefficientRoot_eq_mul_inverseFactorialRoot
    (a : ℝ) {n : ℕ} (hn : n ≠ 0) :
    coefficientRoot a n = |Real.log a| * inverseFactorialRoot n := by
  unfold coefficientRoot inverseFactorialRoot
  rw [abs_div, abs_pow, abs_of_nonneg (by positivity :
    (0 : ℝ) ≤ (Nat.factorial n : ℝ))]
  simp only [Real.rpow_eq_pow]
  rw [Real.div_rpow (pow_nonneg (abs_nonneg _) n)
    (by positivity : (0 : ℝ) ≤ (Nat.factorial n : ℝ))
    (1 / (n : ℝ))]
  rw [one_div, Real.pow_rpow_inv_natCast (abs_nonneg _) hn]
  simp only [div_eq_mul_inv, one_mul]

private theorem pow_self_le_factorial_sq (n : ℕ) :
    (n : ℝ) ^ n ≤ (Nat.factorial n : ℝ) ^ 2 := by
  have hterm : ∀ j ∈ Finset.range n,
      (n : ℝ) ≤ ((j + 1 : ℕ) : ℝ) * ((n - j : ℕ) : ℝ) := by
    intro j hj
    have hjlt : j < n := Finset.mem_range.mp hj
    have hjle : j ≤ n := Nat.le_of_lt hjlt
    have hsub : (1 : ℝ) ≤ (n - j : ℕ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.sub_ne_zero_of_lt hjlt)
    have hsub' : (1 : ℝ) ≤ (n : ℝ) - j := by
      rw [← Nat.cast_sub hjle]
      exact hsub
    have hmul : 0 ≤ (j : ℝ) * ((n : ℝ) - j - 1) :=
      mul_nonneg (by positivity) (by linarith)
    rw [Nat.cast_sub hjle]
    push_cast
    nlinarith
  have hp := Finset.prod_le_prod
    (s := Finset.range n)
    (f := fun _ : ℕ => (n : ℝ))
    (g := fun j : ℕ => ((j + 1 : ℕ) : ℝ) * ((n - j : ℕ) : ℝ))
    (fun _ _ => by positivity) hterm
  have hfirst :
      (∏ j ∈ Finset.range n, ((j + 1 : ℕ) : ℝ)) =
        (Nat.factorial n : ℝ) := by
    exact_mod_cast Finset.prod_range_add_one_eq_factorial n
  have hsecond :
      (∏ j ∈ Finset.range n, ((n - j : ℕ) : ℝ)) =
        (∏ j ∈ Finset.range n, ((j + 1 : ℕ) : ℝ)) := by
    calc
      (∏ j ∈ Finset.range n, ((n - j : ℕ) : ℝ)) =
          ∏ j ∈ Finset.range n, ((n - 1 - j + 1 : ℕ) : ℝ) := by
            apply Finset.prod_congr rfl
            intro j hj
            norm_cast
            have hjlt : j < n := Finset.mem_range.mp hj
            omega
      _ = ∏ j ∈ Finset.range n, ((j + 1 : ℕ) : ℝ) := by
        exact Finset.prod_range_reflect (fun j => ((j + 1 : ℕ) : ℝ)) n
  rw [Finset.prod_const, Finset.card_range, Finset.prod_mul_distrib,
    hfirst, hsecond, hfirst] at hp
  simpa [pow_two] using hp

private theorem inverseFactorialRoot_le_upper (n : ℕ) (hn : 0 < n) :
    inverseFactorialRoot n ≤
      Real.rpow 2 (1 / (n : ℝ)) / Real.sqrt n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let e : ℝ := 1 / (n : ℝ)
  let twoRoot : ℝ := Real.rpow 2 e
  have he : 0 ≤ e := by
    dsimp [e]
    positivity
  have hbase :
      0 ≤ (1 / 2 : ℝ) * Real.rpow n ((n : ℝ) / 2) :=
    mul_nonneg (by norm_num) (Real.rpow_nonneg hnR.le _)
  have hlowerFactorial :
      (1 / 2 : ℝ) * Real.rpow n ((n : ℝ) / 2) ≤
        (Nat.factorial n : ℝ) := by
    have hpow := pow_self_le_factorial_sq n
    have hn0 : (0 : ℝ) ≤ n := by positivity
    have hrpow : 0 ≤ Real.rpow (n : ℝ) ((n : ℝ) / 2) :=
      Real.rpow_nonneg hn0 _
    have hfac : 0 ≤ (Nat.factorial n : ℝ) := by positivity
    have hsquare :
        (Real.rpow (n : ℝ) ((n : ℝ) / 2)) ^ 2 = (n : ℝ) ^ n := by
      calc
        (Real.rpow (n : ℝ) ((n : ℝ) / 2)) ^ 2 =
            Real.rpow (n : ℝ) (((n : ℝ) / 2) * (2 : ℕ)) :=
          (Real.rpow_mul_natCast hn0 _ 2).symm
        _ = Real.rpow (n : ℝ) (n : ℝ) := by congr 1 <;> norm_num
        _ = (n : ℝ) ^ n := Real.rpow_natCast _ _
    rw [← hsquare] at hpow
    nlinarith
  have hroot :
      Real.rpow ((1 / 2 : ℝ) * Real.rpow n ((n : ℝ) / 2)) e ≤
        Real.rpow (Nat.factorial n : ℝ) e :=
    Real.rpow_le_rpow hbase hlowerFactorial he
  have hlower :
      Real.rpow ((1 / 2 : ℝ) * Real.rpow n ((n : ℝ) / 2)) e =
        Real.sqrt n / twoRoot := by
    change ((1 / 2 : ℝ) * (n : ℝ) ^ ((n : ℝ) / 2)) ^ e =
      Real.sqrt n / twoRoot
    have hexp : ((n : ℝ) / 2) * e = 1 / 2 := by
      dsimp [e]
      field_simp
    rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hnR.le _)]
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,
      Real.inv_rpow (by norm_num)]
    rw [← Real.rpow_mul hnR.le, hexp, ← Real.sqrt_eq_rpow]
    simp only [twoRoot, Real.rpow_eq_pow, div_eq_mul_inv]
    ring
  rw [hlower] at hroot
  have hsqrt : 0 < Real.sqrt n := Real.sqrt_pos.2 hnR
  have htwo : 0 < twoRoot := Real.rpow_pos_of_pos (by norm_num) _
  have hquot : 0 < Real.sqrt n / twoRoot := div_pos hsqrt htwo
  calc
    inverseFactorialRoot n =
        1 / Real.rpow (Nat.factorial n : ℝ) e := by
          rfl
    _ ≤ 1 / (Real.sqrt n / twoRoot) :=
      one_div_le_one_div_of_le hquot hroot
    _ = Real.rpow 2 (1 / (n : ℝ)) / Real.sqrt n := by
      dsimp [twoRoot, e]
      field_simp

private theorem inverseFactorialUpper_tendsto_zero :
    Tendsto
      (fun n : ℕ => Real.rpow 2 (1 / (n : ℝ)) / Real.sqrt n)
      atTop (nhds 0) := by
  have hexp :
      Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (nhds 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hnum :
      Tendsto (fun n : ℕ => (2 : ℝ) ^ ((1 : ℝ) / (n : ℝ)))
        atTop (nhds 1) := by
    have h := (tendsto_const_nhds (x := (2 : ℝ))).rpow hexp
      (Or.inl (by norm_num))
    simpa using h
  have hsqrt :
      Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hquot := hnum.div_atTop hsqrt
  simpa only [Real.rpow_eq_pow] using hquot

private theorem inverseFactorialRoot_tendsto_zero :
    Tendsto inverseFactorialRoot atTop (nhds 0) := by
  apply squeeze_zero'
  · filter_upwards with n
    unfold inverseFactorialRoot
    exact one_div_nonneg.mpr
      (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ Nat.factorial n) _)
  · filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
    exact inverseFactorialRoot_le_upper n
      (lt_of_lt_of_le Nat.zero_lt_one hn)
  · exact inverseFactorialUpper_tendsto_zero

theorem gap1
    (f : ℝ → ℝ) (a : ℝ)
    (hf : ∀ x, f x = Real.rpow a x) (ha : 0 < a) (ha1 : a ≠ 1) :
    ∀ x, f x = Real.exp (x * Real.log a) := by
  intro x
  rw [hf x]
  calc
    Real.rpow a x = Real.exp (Real.log a * x) :=
      Real.rpow_def_of_pos ha x
    _ = Real.exp (x * Real.log a) := by rw [mul_comm]

theorem gap2
    (f : ℝ → ℝ) (a : ℝ)
    (hf : ∀ x, f x = Real.rpow a x) (ha : 0 < a) (ha1 : a ≠ 1)
    (hexp : ∀ x, f x = Real.exp (x * Real.log a)) :
    ∀ x, Real.exp (x * Real.log a) = ∑' n, exponentialTerm a x n := by
  intro x
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  apply tsum_congr
  intro n
  unfold exponentialTerm
  rw [mul_pow]
  ring

theorem gap3
    (f : ℝ → ℝ) (a : ℝ)
    (hf : ∀ x, f x = Real.rpow a x) (ha : 0 < a) (ha1 : a ≠ 1)
    (hexp : ∀ x, f x = Real.exp (x * Real.log a))
    (hseries :
      ∀ x, Real.exp (x * Real.log a) = ∑' n, exponentialTerm a x n) :
    ∀ x, f x = ∑' n, exponentialTerm a x n := by
  intro x
  exact (hexp x).trans (hseries x)

theorem gap4
    (f : ℝ → ℝ) (a : ℝ)
    (hf : ∀ x, f x = Real.rpow a x) (ha : 0 < a) (ha1 : a ≠ 1)
    (hexp : ∀ x, f x = Real.exp (x * Real.log a))
    (hseries :
      ∀ x, Real.exp (x * Real.log a) = ∑' n, exponentialTerm a x n)
    (hfseries : ∀ x, f x = ∑' n, exponentialTerm a x n) :
    ∀ L : ℝ, Tendsto inverseFactorialRoot atTop (nhds L) →
      Tendsto (coefficientRoot a) atTop (nhds (|Real.log a| * L)) := by
  intro L hL
  refine (tendsto_const_nhds.mul hL).congr' ?_
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
  exact (coefficientRoot_eq_mul_inverseFactorialRoot a
    (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hn))).symm

theorem gap5
    (f : ℝ → ℝ) (a : ℝ)
    (hf : ∀ x, f x = Real.rpow a x) (ha : 0 < a) (ha1 : a ≠ 1)
    (hexp : ∀ x, f x = Real.exp (x * Real.log a))
    (hseries :
      ∀ x, Real.exp (x * Real.log a) = ∑' n, exponentialTerm a x n)
    (hfseries : ∀ x, f x = ∑' n, exponentialTerm a x n)
    (hroot :
      ∀ L : ℝ, Tendsto inverseFactorialRoot atTop (nhds L) →
        Tendsto (coefficientRoot a) atTop (nhds (|Real.log a| * L))) :
    Tendsto (fun n => |Real.log a| * inverseFactorialRoot n) atTop (nhds 0) := by
  simpa using tendsto_const_nhds.mul inverseFactorialRoot_tendsto_zero

theorem gap6
    (f : ℝ → ℝ) (a : ℝ)
    (hf : ∀ x, f x = Real.rpow a x) (ha : 0 < a) (ha1 : a ≠ 1)
    (hexp : ∀ x, f x = Real.exp (x * Real.log a))
    (hseries :
      ∀ x, Real.exp (x * Real.log a) = ∑' n, exponentialTerm a x n)
    (hfseries : ∀ x, f x = ∑' n, exponentialTerm a x n)
    (hroot :
      ∀ L : ℝ, Tendsto inverseFactorialRoot atTop (nhds L) →
        Tendsto (coefficientRoot a) atTop (nhds (|Real.log a| * L)))
    (hzero :
      Tendsto (fun n => |Real.log a| * inverseFactorialRoot n) atTop (nhds 0)) :
    Tendsto (coefficientRoot a) atTop (nhds 0) := by
  refine hzero.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
  exact (coefficientRoot_eq_mul_inverseFactorialRoot a
    (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hn))).symm

theorem gap7
    (f : ℝ → ℝ) (a : ℝ)
    (hf : ∀ x, f x = Real.rpow a x) (ha : 0 < a) (ha1 : a ≠ 1)
    (hexp : ∀ x, f x = Real.exp (x * Real.log a))
    (hseries :
      ∀ x, Real.exp (x * Real.log a) = ∑' n, exponentialTerm a x n)
    (hfseries : ∀ x, f x = ∑' n, exponentialTerm a x n)
    (hroot :
      ∀ L : ℝ, Tendsto inverseFactorialRoot atTop (nhds L) →
        Tendsto (coefficientRoot a) atTop (nhds (|Real.log a| * L)))
    (hzero :
      Tendsto (fun n => |Real.log a| * inverseFactorialRoot n) atTop (nhds 0))
    (hcoeff : Tendsto (coefficientRoot a) atTop (nhds 0)) :
    HasInfiniteRadius (fun n => Real.log a ^ n / (Nat.factorial n : ℝ)) := by
  intro x
  have hs := Real.summable_pow_div_factorial (Real.log a * x)
  convert hs using 1
  funext n
  rw [mul_pow]
  ring

theorem gap8
    (f : ℝ → ℝ) (a : ℝ)
    (hf : ∀ x, f x = Real.rpow a x) (ha : 0 < a) (ha1 : a ≠ 1)
    (hexp : ∀ x, f x = Real.exp (x * Real.log a))
    (hseries :
      ∀ x, Real.exp (x * Real.log a) = ∑' n, exponentialTerm a x n)
    (hfseries : ∀ x, f x = ∑' n, exponentialTerm a x n)
    (hroot :
      ∀ L : ℝ, Tendsto inverseFactorialRoot atTop (nhds L) →
        Tendsto (coefficientRoot a) atTop (nhds (|Real.log a| * L)))
    (hzero :
      Tendsto (fun n => |Real.log a| * inverseFactorialRoot n) atTop (nhds 0))
    (hcoeff : Tendsto (coefficientRoot a) atTop (nhds 0))
    (hradius :
      HasInfiniteRadius (fun n => Real.log a ^ n / (Nat.factorial n : ℝ))) :
    ∀ x, Summable (exponentialTerm a x) := by
  intro x
  simpa [HasInfiniteRadius, exponentialTerm] using hradius x

end

end ProofGap.Exercise2844
