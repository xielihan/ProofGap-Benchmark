import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise2183
noncomputable section

open Filter
open scoped BigOperators Topology

def q (n : ℕ) : ℝ := Real.rpow 2 (1 / (n : ℝ))
def q32 (n : ℕ) : ℝ := Real.rpow 32 (1 / (n : ℝ))

def lowerSum (n : ℕ) : ℝ :=
  (q n - 1) * ∑ i ∈ Finset.range n, (q n ^ i) ^ 5

def rootRatio (n : ℕ) : ℝ :=
  (q n - 1) / (q32 n - 1)

def reciprocalExpansion (n : ℕ) : ℝ :=
  1 / (Real.rpow 16 (1 / (n : ℝ)) +
    Real.rpow 8 (1 / (n : ℝ)) +
    Real.rpow 4 (1 / (n : ℝ)) + q n + 1)

private theorem rpow_four_eq_q_pow_two (n : ℕ) :
    Real.rpow 4 (1 / (n : ℝ)) = q n ^ 2 := by
  change Real.rpow 4 (1 / (n : ℝ)) =
    (Real.rpow 2 (1 / (n : ℝ))) ^ 2
  calc
    Real.rpow 4 (1 / (n : ℝ)) =
        Real.rpow ((2 : ℝ) * 2) (1 / (n : ℝ)) := by norm_num
    _ = Real.rpow 2 (1 / (n : ℝ)) *
        Real.rpow 2 (1 / (n : ℝ)) :=
      Real.mul_rpow (by norm_num) (by norm_num)
    _ = (Real.rpow 2 (1 / (n : ℝ))) ^ 2 := by ring

private theorem rpow_eight_eq_q_pow_three (n : ℕ) :
    Real.rpow 8 (1 / (n : ℝ)) = q n ^ 3 := by
  have h4 : Real.rpow 4 (1 / (n : ℝ)) =
      (Real.rpow 2 (1 / (n : ℝ))) ^ 2 := by
    simpa only [q] using rpow_four_eq_q_pow_two n
  change Real.rpow 8 (1 / (n : ℝ)) =
    (Real.rpow 2 (1 / (n : ℝ))) ^ 3
  calc
    Real.rpow 8 (1 / (n : ℝ)) =
        Real.rpow ((2 : ℝ) * 4) (1 / (n : ℝ)) := by norm_num
    _ = Real.rpow 2 (1 / (n : ℝ)) *
        Real.rpow 4 (1 / (n : ℝ)) :=
      Real.mul_rpow (by norm_num) (by norm_num)
    _ = Real.rpow 2 (1 / (n : ℝ)) *
        (Real.rpow 2 (1 / (n : ℝ))) ^ 2 := by rw [h4]
    _ = (Real.rpow 2 (1 / (n : ℝ))) ^ 3 := by ring

private theorem rpow_sixteen_eq_q_pow_four (n : ℕ) :
    Real.rpow 16 (1 / (n : ℝ)) = q n ^ 4 := by
  have h8 : Real.rpow 8 (1 / (n : ℝ)) =
      (Real.rpow 2 (1 / (n : ℝ))) ^ 3 := by
    simpa only [q] using rpow_eight_eq_q_pow_three n
  change Real.rpow 16 (1 / (n : ℝ)) =
    (Real.rpow 2 (1 / (n : ℝ))) ^ 4
  calc
    Real.rpow 16 (1 / (n : ℝ)) =
        Real.rpow ((2 : ℝ) * 8) (1 / (n : ℝ)) := by norm_num
    _ = Real.rpow 2 (1 / (n : ℝ)) *
        Real.rpow 8 (1 / (n : ℝ)) :=
      Real.mul_rpow (by norm_num) (by norm_num)
    _ = Real.rpow 2 (1 / (n : ℝ)) *
        (Real.rpow 2 (1 / (n : ℝ))) ^ 3 := by rw [h8]
    _ = (Real.rpow 2 (1 / (n : ℝ))) ^ 4 := by ring

private theorem q32_eq_q_pow_five (n : ℕ) :
    q32 n = q n ^ 5 := by
  have h16 : Real.rpow 16 (1 / (n : ℝ)) =
      (Real.rpow 2 (1 / (n : ℝ))) ^ 4 := by
    simpa only [q] using rpow_sixteen_eq_q_pow_four n
  unfold q32 q
  calc
    Real.rpow 32 (1 / (n : ℝ)) =
        Real.rpow ((2 : ℝ) * 16) (1 / (n : ℝ)) := by norm_num
    _ = Real.rpow 2 (1 / (n : ℝ)) *
        Real.rpow 16 (1 / (n : ℝ)) :=
      Real.mul_rpow (by norm_num) (by norm_num)
    _ = Real.rpow 2 (1 / (n : ℝ)) *
        (Real.rpow 2 (1 / (n : ℝ))) ^ 4 := by rw [h16]
    _ = (Real.rpow 2 (1 / (n : ℝ))) ^ 5 := by ring

private theorem geometric_sum_mul_real (x : ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, x ^ i) * (x - 1) = x ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, pow_succ, add_mul, ih]
      ring

theorem gap1 (n : ℕ) (hn : 0 < n) :
    q n ^ n = 2 := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hfrac : (1 / (n : ℝ)) * (n : ℝ) = 1 := by
    field_simp [hn0]
  calc
    q n ^ n = Real.rpow (q n) (n : ℝ) :=
      (Real.rpow_natCast (q n) n).symm
    _ = Real.rpow (Real.rpow 2 (1 / (n : ℝ))) (n : ℝ) := by
      rfl
    _ = Real.rpow 2 ((1 / (n : ℝ)) * (n : ℝ)) := by
      symm
      exact Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)
        (1 / (n : ℝ)) (n : ℝ)
    _ = Real.rpow 2 1 := by rw [hfrac]
    _ = 2 := by simp

theorem gap2 (n : ℕ) (hn : 0 < n) :
    q n ^ 0 = 1 := by
  simp

theorem gap3 (n : ℕ) (hn : 0 < n) :
    q n ^ 0 < q n ^ 1 := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hexp : 0 < 1 / (n : ℝ) := by positivity
  have hpow :
      Real.rpow 1 (1 / (n : ℝ)) < Real.rpow 2 (1 / (n : ℝ)) :=
    Real.rpow_lt_rpow (by norm_num) (by norm_num) hexp
  simpa [q] using hpow

theorem gap4 (n : ℕ) (hn : 0 < n) :
    q n ^ 1 < q n ^ 2 := by
  have hq : 1 < q n := by
    simpa using gap3 n hn
  have hqpos : 0 < q n := lt_trans zero_lt_one hq
  simpa [pow_succ] using mul_lt_mul_of_pos_left hq hqpos

theorem gap5 (n i : ℕ) (hn : 0 < n) (hi : i < n) :
    q n ^ i < q n ^ (i + 1) := by
  have hq : 1 < q n := by
    simpa using gap3 n hn
  have hqpos : 0 < q n := lt_trans zero_lt_one hq
  simpa [pow_succ] using
    mul_lt_mul_of_pos_left hq (pow_pos hqpos i)

theorem gap6 (n : ℕ) (hn : 0 < n) :
    q n ^ (n - 1) < q n ^ n := by
  have hi : n - 1 < n := Nat.sub_lt hn (by decide)
  have h := gap5 n (n - 1) hn hi
  simpa [Nat.sub_add_cancel hn] using h

theorem gap7 (n : ℕ) (hn : 0 < n) :
    q n ^ n = 2 := by
  exact gap1 n hn

theorem gap8 : (1 : ℝ) < 2 := by
  norm_num

theorem gap9 :
    MonotoneOn (fun x : ℝ => x ^ 4) (Set.Icc 1 2) := by
  intro x hx y hy hxy
  have hsum : 0 ≤ y + x := by linarith [hx.1, hy.1]
  have hsq : x ^ 2 ≤ y ^ 2 := by
    have hprod := mul_nonneg (sub_nonneg.mpr hxy) hsum
    nlinarith
  have hsum2 : 0 ≤ y ^ 2 + x ^ 2 :=
    add_nonneg (sq_nonneg y) (sq_nonneg x)
  have hprod2 := mul_nonneg (sub_nonneg.mpr hsq) hsum2
  nlinarith

theorem gap10 (n : ℕ) (hn : 0 < n) :
    lowerSum n =
      ∑ i ∈ Finset.range n, (q n ^ i) ^ 4 * (q n ^ (i + 1) - q n ^ i) := by
  unfold lowerSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hsucc : q n ^ (i + 1) = q n ^ i * q n := pow_succ (q n) i
  rw [hsucc]
  ring

theorem gap11 (n : ℕ) (hn : 0 < n) :
    (∑ i ∈ Finset.range n,
        (q n ^ i) ^ 4 * (q n ^ (i + 1) - q n ^ i)) =
      (q n - 1) * ∑ i ∈ Finset.range n, (q n ^ i) ^ 5 := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hsucc : q n ^ (i + 1) = q n ^ i * q n := pow_succ (q n) i
  rw [hsucc]
  ring

theorem gap12 (n : ℕ) (hn : 0 < n) :
    lowerSum n =
      (q n - 1) * ∑ i ∈ Finset.range n, (q n ^ i) ^ 5 := by
  rfl

theorem gap13 (n : ℕ) (hn : 0 < n) :
    lowerSum n =
      (q n - 1) * (q n ^ (5 * n) - 1) / (q n ^ 5 - 1) := by
  have hq : 1 < q n := by
    simpa using gap3 n hn
  have hqpos : 0 < q n := lt_trans zero_lt_one hq
  have hrewrite :
      (∑ i ∈ Finset.range n, (q n ^ i) ^ 5) =
        ∑ i ∈ Finset.range n, (q n ^ 5) ^ i := by
    apply Finset.sum_congr rfl
    intro i hi
    calc
      (q n ^ i) ^ 5 = q n ^ (i * 5) :=
        (pow_mul (q n) i 5).symm
      _ = q n ^ (5 * i) := by rw [Nat.mul_comm]
      _ = (q n ^ 5) ^ i := pow_mul (q n) 5 i
  let S : ℝ := q n ^ 4 + q n ^ 3 + q n ^ 2 + q n + 1
  have hfactor : q n ^ 5 - 1 = (q n - 1) * S := by
    dsimp [S]
    ring
  have hne : q n - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hq)
  have hSpos : 0 < S := by
    dsimp [S]
    positivity
  have hS : S ≠ 0 := ne_of_gt hSpos
  have hden : q n ^ 5 - 1 ≠ 0 := by
    rw [hfactor]
    exact mul_ne_zero hne hS
  have hsum :
      (∑ i ∈ Finset.range n, (q n ^ i) ^ 5) =
        (q n ^ (5 * n) - 1) / (q n ^ 5 - 1) := by
    apply (eq_div_iff hden).2
    rw [hrewrite]
    simpa only [pow_mul] using
      geometric_sum_mul_real (q n ^ 5) n
  calc
    lowerSum n = (q n - 1) * ∑ i ∈ Finset.range n, (q n ^ i) ^ 5 :=
      gap12 n hn
    _ = (q n - 1) * ((q n ^ (5 * n) - 1) / (q n ^ 5 - 1)) := by
      rw [hsum]
    _ = (q n - 1) * (q n ^ (5 * n) - 1) / (q n ^ 5 - 1) := by
      ring

theorem gap14 (n : ℕ) (hn : 0 < n) :
    (q n - 1) * (q n ^ (5 * n) - 1) / (q n ^ 5 - 1) =
      31 * (q n - 1) / (q32 n - 1) := by
  have hpow : q n ^ (5 * n) = 32 := by
    calc
      q n ^ (5 * n) = q n ^ (n * 5) := by rw [Nat.mul_comm]
      _ = (q n ^ n) ^ 5 := by rw [pow_mul]
      _ = 32 := by rw [gap1 n hn]; norm_num
  rw [hpow, q32_eq_q_pow_five n]
  ring

theorem gap15 (n : ℕ) (hn : 0 < n) :
    lowerSum n = 31 * (q n - 1) / (q32 n - 1) := by
  calc
    lowerSum n =
        (q n - 1) * (q n ^ (5 * n) - 1) / (q n ^ 5 - 1) :=
      gap13 n hn
    _ = 31 * (q n - 1) / (q32 n - 1) := gap14 n hn

theorem gap16 :
    Tendsto lowerSum atTop (nhds (31 / 5 : ℝ)) ↔
      Tendsto (fun n => 31 * rootRatio n) atTop (nhds (31 / 5 : ℝ)) := by
  apply tendsto_congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hnpos : 0 < n := hn
  simpa [rootRatio, mul_div_assoc] using gap15 n hnpos

theorem gap17 :
    Tendsto (fun n => 31 * rootRatio n) atTop (nhds (31 / 5 : ℝ)) ↔
      Tendsto (fun n => 31 * reciprocalExpansion n) atTop (nhds (31 / 5 : ℝ)) := by
  apply tendsto_congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hnpos : 0 < n := hn
  have hq : 1 < q n := by
    simpa using gap3 n hnpos
  have hqpos : 0 < q n := lt_trans zero_lt_one hq
  let S : ℝ := q n ^ 4 + q n ^ 3 + q n ^ 2 + q n + 1
  have hfactor : q n ^ 5 - 1 = (q n - 1) * S := by
    dsimp [S]
    ring
  have hne : q n - 1 ≠ 0 := ne_of_gt (sub_pos.mpr hq)
  have hSpos : 0 < S := by
    dsimp [S]
    positivity
  have hS : S ≠ 0 := ne_of_gt hSpos
  change
    31 * ((q n - 1) / (q32 n - 1)) =
      31 * (1 /
        (Real.rpow 16 (1 / (n : ℝ)) +
          Real.rpow 8 (1 / (n : ℝ)) +
          Real.rpow 4 (1 / (n : ℝ)) + q n + 1))
  rw [q32_eq_q_pow_five n, rpow_sixteen_eq_q_pow_four n,
    rpow_eight_eq_q_pow_three n, rpow_four_eq_q_pow_two n, hfactor]
  change 31 * ((q n - 1) / ((q n - 1) * S)) = 31 * (1 / S)
  field_simp [hne, hS]

theorem gap18 :
    Tendsto (fun n => 31 * reciprocalExpansion n) atTop (nhds (31 / 5 : ℝ)) := by
  have hexponent :
      Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (nhds 0) := by
    have hcast :
        Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    simpa [one_div] using tendsto_inv_atTop_zero.comp hcast
  have hlog :
      Tendsto (fun _ : ℕ => Real.log 2) atTop (nhds (Real.log 2)) :=
    tendsto_const_nhds
  have hinner :
      Tendsto (fun n : ℕ => Real.log 2 * (1 / (n : ℝ))) atTop (nhds 0) := by
    simpa using hlog.mul hexponent
  have hq_lim : Tendsto q atTop (nhds 1) := by
    have hexp_lim := Real.continuous_exp.continuousAt.tendsto.comp hinner
    change Tendsto
      (fun n : ℕ => Real.exp (Real.log 2 * (1 / (n : ℝ))))
      atTop (nhds (Real.exp 0)) at hexp_lim
    have hrpow (x : ℝ) :
        Real.rpow 2 x = Real.exp (Real.log 2 * x) := by
      change (2 : ℝ) ^ x = Real.exp (Real.log 2 * x)
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    have hfun :
        (fun n : ℕ => Real.rpow 2 (1 / (n : ℝ))) =
          fun n : ℕ => Real.exp (Real.log 2 * (1 / (n : ℝ))) := by
      funext n
      exact hrpow _
    change Tendsto
      (fun n : ℕ => Real.rpow 2 (1 / (n : ℝ))) atTop (nhds 1)
    rw [hfun]
    simpa only [Real.exp_zero] using hexp_lim
  have hone :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have hden_lim :
      Tendsto
        (fun n : ℕ => q n ^ 4 + q n ^ 3 + q n ^ 2 + q n + 1)
        atTop (nhds 5) := by
    convert
      ((((hq_lim.pow 4).add (hq_lim.pow 3)).add (hq_lim.pow 2)).add hq_lim).add hone
      using 1 <;> norm_num
  have hrec :
      Tendsto reciprocalExpansion atTop (nhds (1 / 5 : ℝ)) := by
    have hinv := hden_lim.inv₀ (by norm_num : (5 : ℝ) ≠ 0)
    have hinv' :
        Tendsto
          (fun n : ℕ =>
            1 / (q n ^ 4 + q n ^ 3 + q n ^ 2 + q n + 1))
          atTop (nhds (1 / 5 : ℝ)) := by
      simpa only [one_div] using hinv
    change Tendsto
      (fun n : ℕ =>
        1 / (Real.rpow 16 (1 / (n : ℝ)) +
          Real.rpow 8 (1 / (n : ℝ)) +
          Real.rpow 4 (1 / (n : ℝ)) + q n + 1))
      atTop (nhds (1 / 5 : ℝ))
    simpa only [rpow_sixteen_eq_q_pow_four,
      rpow_eight_eq_q_pow_three, rpow_four_eq_q_pow_two] using hinv'
  have h31 :
      Tendsto (fun _ : ℕ => (31 : ℝ)) atTop (nhds 31) :=
    tendsto_const_nhds
  convert h31.mul hrec using 1 <;> norm_num

theorem gap19 :
    Tendsto lowerSum atTop (nhds (31 / 5 : ℝ)) := by
  apply gap16.mpr
  apply gap17.mpr
  exact gap18

end
end ProofGap.Exercise2183
