import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise2931_1

noncomputable section

open scoped BigOperators

def logIncrementTerm (n k : ℕ) : ℝ :=
  1 /
    (((2 * k + 1 : ℕ) : ℝ) *
      ((2 * n + 1 : ℕ) : ℝ) ^ (2 * k + 1))

def logTwoPartial : ℝ :=
  2 * ∑ k ∈ Finset.range 5, logIncrementTerm 1 k

def logTwoRemainder : ℝ :=
  Real.log 2 - logTwoPartial

def logTwoTail : ℝ :=
  2 * ∑' j : ℕ, logIncrementTerm 1 (j + 5)

def geometricTailBound : ℝ :=
  (2 / (11 * 3 ^ 11 : ℝ)) *
    (1 / (1 - (1 / 3 ^ 2 : ℝ)))

def Approx (u v ε : ℝ) : Prop :=
  |u - v| < ε

private theorem logIncrement_hasSum (n : ℕ) (hn : 0 < n) :
    HasSum (fun k : ℕ => logIncrementTerm n k)
      ((Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ)) / 2) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast hn
  have hratio :
      (1 / (n : ℝ)) / (1 / (n : ℝ) + 2) =
        1 / (((2 * n + 1 : ℕ) : ℝ)) := by
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
    have hden : (1 / (n : ℝ) + 2) ≠ 0 := by positivity
    have hbase : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
    field_simp [ne_of_gt hnR, hden, hbase] <;> ring
  have hraw :
      HasSum
        (fun k : ℕ =>
          2 * (1 / (2 * (k : ℝ) + 1)) *
            ((1 / (n : ℝ)) / ((1 / (n : ℝ)) + 2)) ^ (2 * k + 1))
        (Real.log (1 + 1 / (n : ℝ))) := by
    exact Real.hasSum_log_one_add (a := 1 / (n : ℝ)) (by positivity)
  have hseries :
      HasSum (fun k : ℕ => logIncrementTerm n k)
        ((1 / 2 : ℝ) * Real.log (1 + 1 / (n : ℝ))) := by
    refine (hraw.mul_left (1 / 2 : ℝ)).congr ?_
    intro s
    refine Finset.sum_congr rfl ?_
    intro k hk
    rw [hratio]
    unfold logIncrementTerm
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
    rw [one_div_pow]
    have hkpos : (0 : ℝ) < 2 * (k : ℝ) + 1 := by positivity
    have hbpos : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
    field_simp [ne_of_gt hkpos, ne_of_gt hbpos] <;> ring
  have harg :
      1 + 1 / (n : ℝ) =
        ((n + 1 : ℕ) : ℝ) / (n : ℝ) := by
    norm_num only [Nat.cast_add, Nat.cast_one]
    field_simp [ne_of_gt hnR] <;> ring
  have hlog :
      (1 / 2 : ℝ) * Real.log (1 + 1 / (n : ℝ)) =
        (Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ)) / 2 := by
    rw [harg, Real.log_div (by positivity) (by positivity)]
    ring
  rw [hlog] at hseries
  exact hseries

theorem gap1 :
    ∀ n : ℕ, 0 < n →
      Real.log ((n + 1 : ℕ) : ℝ) =
        Real.log (n : ℝ) +
          2 * ∑' k : ℕ, logIncrementTerm n k := by
  intro n hn
  rw [(logIncrement_hasSum n hn).tsum_eq]
  ring

theorem gap2 :
    Real.log 2 =
      2 * ∑' k : ℕ, logIncrementTerm 1 k := by
  simpa using gap1 1 (by norm_num)

theorem gap3 :
    0 < logTwoRemainder := by
  have hs := (logIncrement_hasSum 1 (by norm_num)).summable
  have hs5 : Summable (fun j : ℕ => logIncrementTerm 1 (j + 5)) := by
    simpa only [Function.comp_apply] using
      hs.comp_injective (fun a b h => by omega)
  have htailSplit :
      logIncrementTerm 1 5 + ∑' j : ℕ, logIncrementTerm 1 (j + 6) =
        ∑' j : ℕ, logIncrementTerm 1 (j + 5) := by
    simpa [Finset.sum_range_succ, add_assoc, add_comm, add_left_comm] using
      hs5.sum_add_tsum_nat_add 1
  have hrest : 0 ≤ ∑' j : ℕ, logIncrementTerm 1 (j + 6) := by
    apply tsum_nonneg
    intro j
    unfold logIncrementTerm
    positivity
  have hfirst : 0 < logIncrementTerm 1 5 := by
    norm_num [logIncrementTerm]
  have htail : 0 < ∑' j : ℕ, logIncrementTerm 1 (j + 5) := by
    linarith
  have hsplit :
      (∑ k ∈ Finset.range 5, logIncrementTerm 1 k) +
          ∑' j : ℕ, logIncrementTerm 1 (j + 5) =
        ∑' k : ℕ, logIncrementTerm 1 k := by
    simpa [add_comm] using hs.sum_add_tsum_nat_add 5
  unfold logTwoRemainder logTwoPartial
  rw [gap2, ← hsplit]
  linarith

theorem gap4 :
    logTwoRemainder = logTwoTail := by
  have hs := (logIncrement_hasSum 1 (by norm_num)).summable
  have hsplit :
      (∑ k ∈ Finset.range 5, logIncrementTerm 1 k) +
          ∑' j : ℕ, logIncrementTerm 1 (j + 5) =
        ∑' k : ℕ, logIncrementTerm 1 k := by
    simpa [add_comm] using hs.sum_add_tsum_nat_add 5
  unfold logTwoRemainder logTwoPartial logTwoTail
  rw [gap2, ← hsplit]
  ring

theorem gap5 :
    logTwoTail < geometricTailBound := by
  have hs := (logIncrement_hasSum 1 (by norm_num)).summable
  have hs5 : Summable (fun j : ℕ => logIncrementTerm 1 (j + 5)) := by
    simpa only [Function.comp_apply] using
      hs.comp_injective (fun a b h => by omega)
  have hs6 : Summable (fun j : ℕ => logIncrementTerm 1 (j + 6)) := by
    simpa only [Function.comp_apply] using
      hs.comp_injective (fun a b h => by omega)
  have htailSplit :
      logIncrementTerm 1 5 + ∑' j : ℕ, logIncrementTerm 1 (j + 6) =
        ∑' j : ℕ, logIncrementTerm 1 (j + 5) := by
    simpa [Finset.sum_range_succ, add_assoc, add_comm, add_left_comm] using
      hs5.sum_add_tsum_nat_add 1
  let c : ℝ := 1 / (13 * 3 ^ 13 : ℝ)
  let q : ℝ := 1 / 9
  have hpoint : ∀ j : ℕ,
      logIncrementTerm 1 (j + 6) ≤ c * q ^ j := by
    intro j
    have hcoeff : (13 : ℝ) ≤ ((2 * (j + 6) + 1 : ℕ) : ℝ) := by
      norm_cast
      omega
    have hpow :
        (3 : ℝ) ^ (2 * (j + 6) + 1) =
          (3 : ℝ) ^ 13 * 9 ^ j := by
      rw [show 2 * (j + 6) + 1 = 13 + 2 * j by omega, pow_add, pow_mul]
      norm_num
    have h9 : (9 : ℝ) ^ j ≠ 0 := pow_ne_zero _ (by norm_num)
    have hrhs : c * q ^ j =
        1 / ((13 : ℝ) * ((3 : ℝ) ^ 13 * 9 ^ j)) := by
      dsimp [c, q]
      rw [one_div_pow]
      field_simp [h9] <;> ring
    rw [hrhs]
    unfold logIncrementTerm
    norm_num only [Nat.cast_ofNat]
    rw [hpow]
    have hthree : (3 : ℝ) ^ 13 = 1594323 := by norm_num
    rw [hthree]
    have hp : (0 : ℝ) < 1594323 * (9 : ℝ) ^ j := by
      positivity
    have h13 : (0 : ℝ) < 13 := by norm_num
    have hA :
        (0 : ℝ) < ((2 * (j + 6) + 1 : ℕ) : ℝ) :=
      lt_of_lt_of_le h13 hcoeff
    apply (div_le_div_iff₀ (mul_pos hA hp) (mul_pos h13 hp)).2
    simpa only [one_mul] using
      (mul_le_mul_of_nonneg_right hcoeff hp.le)
  have hgeom :=
    hasSum_geometric_of_norm_lt_one (by norm_num : ‖q‖ < 1)
  have hg : HasSum (fun j : ℕ => c * q ^ j) (c * (1 - q)⁻¹) := by
    simpa using hgeom.mul_left c
  have hsumle :
      (∑' j : ℕ, logIncrementTerm 1 (j + 6)) ≤
        ∑' j : ℕ, c * q ^ j := by
    exact Summable.tsum_le_tsum hpoint hs6 hg.summable
  rw [hg.tsum_eq] at hsumle
  unfold logTwoTail geometricTailBound
  rw [← htailSplit]
  dsimp [c, q] at hsumle
  norm_num [logIncrementTerm] at hsumle ⊢
  linarith

theorem gap6 :
    geometricTailBound < (2 / 10 ^ 6 : ℝ) := by
  norm_num [geometricTailBound]

theorem gap7 :
    (0 : ℝ) < 2 / 10 ^ 6 := by
  norm_num

theorem gap8 :
    (693146 / 1000000 : ℝ) < Real.log 2 := by
  have h := gap3
  unfold logTwoRemainder logTwoPartial at h
  norm_num [logIncrementTerm, Finset.sum_range_succ] at h ⊢
  linarith

theorem gap9 :
    Real.log 2 < (693148 / 1000000 : ℝ) := by
  have h : logTwoRemainder < geometricTailBound := by
    rw [gap4]
    exact gap5
  unfold logTwoRemainder geometricTailBound logTwoPartial at h
  norm_num [logIncrementTerm, Finset.sum_range_succ] at h ⊢
  linarith

theorem gap10 :
    (693146 / 1000000 : ℝ) <
      (693148 / 1000000 : ℝ) := by
  norm_num

theorem gap11 :
    Approx (Real.log 2) (69315 / 100000 : ℝ)
      (1 / 10 ^ 5 : ℝ) := by
  unfold Approx
  rw [abs_lt]
  have hlo := gap8
  have hhi := gap9
  norm_num at hlo hhi ⊢
  constructor <;> linarith

end

end ProofGap.Exercise2931_1
