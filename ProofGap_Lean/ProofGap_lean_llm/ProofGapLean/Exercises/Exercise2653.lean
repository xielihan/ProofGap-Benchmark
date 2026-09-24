import ProofGapLean.Prelude.Analysis
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace ProofGap.Exercise2653

noncomputable section

open Filter
open scoped BigOperators

def x (n : ℕ) : ℝ :=
  (∑ k ∈ Finset.Icc 1 n, 1 / Real.sqrt k) - 2 * Real.sqrt n

def explicitDifference (n : ℕ) : ℝ :=
  1 / Real.sqrt (n + 1) - 2 * Real.sqrt (n + 1) + 2 * Real.sqrt n

def rationalizedDifference (n : ℕ) : ℝ :=
  1 / Real.sqrt (n + 1) -
    2 / (Real.sqrt (n + 1) + Real.sqrt n)

def quotientDifference (n : ℕ) : ℝ :=
  (Real.sqrt n - Real.sqrt (n + 1)) /
    (Real.sqrt (n + 1) * (Real.sqrt (n + 1) + Real.sqrt n))

def finalDifference (n : ℕ) : ℝ :=
  -1 /
    (Real.sqrt (n + 1) * (Real.sqrt (n + 1) + Real.sqrt n) ^ 2)

def comparison (n : ℕ) : ℝ :=
  1 / Real.rpow n (3 / 2 : ℝ)

theorem gap1 :
    ∀ n : ℕ, x (n + 1) - x n = explicitDifference n := by
  intro n
  have hset : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hnot : n + 1 ∉ Finset.Icc 1 n := by simp
  unfold x explicitDifference
  rw [hset, Finset.sum_insert hnot]
  norm_num only [Nat.cast_add, Nat.cast_one]
  ring

theorem gap2 :
    ∀ n : ℕ, explicitDifference n = rationalizedDifference n := by
  intro n
  have hs₁ : Real.sqrt ((n + 1 : ℕ) : ℝ) ^ 2 = ((n + 1 : ℕ) : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hs₀ : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hden : 0 < Real.sqrt ((n + 1 : ℕ) : ℝ) + Real.sqrt (n : ℝ) :=
    add_pos_of_pos_of_nonneg (Real.sqrt_pos.2 (by positivity)) (Real.sqrt_nonneg _)
  have hdiff : Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt (n : ℝ) =
      1 / (Real.sqrt ((n + 1 : ℕ) : ℝ) + Real.sqrt (n : ℝ)) := by
    rw [eq_div_iff hden.ne']
    calc
      (Real.sqrt ((n + 1 : ℕ) : ℝ) - Real.sqrt (n : ℝ)) *
          (Real.sqrt ((n + 1 : ℕ) : ℝ) + Real.sqrt (n : ℝ)) =
          Real.sqrt ((n + 1 : ℕ) : ℝ) ^ 2 - Real.sqrt (n : ℝ) ^ 2 := by ring
      _ = 1 := by
        rw [hs₁, hs₀]
        push_cast
        ring
  unfold explicitDifference rationalizedDifference
  norm_num only [Nat.cast_add, Nat.cast_one] at hdiff ⊢
  calc
    1 / Real.sqrt ((n : ℝ) + 1) - 2 * Real.sqrt ((n : ℝ) + 1) +
        2 * Real.sqrt (n : ℝ) =
        1 / Real.sqrt ((n : ℝ) + 1) -
          2 * (Real.sqrt ((n : ℝ) + 1) - Real.sqrt (n : ℝ)) := by ring
    _ = 1 / Real.sqrt ((n : ℝ) + 1) -
        2 / (Real.sqrt ((n : ℝ) + 1) + Real.sqrt (n : ℝ)) := by
      rw [hdiff]
      ring

theorem gap3 :
    ∀ n : ℕ, rationalizedDifference n = quotientDifference n := by
  intro n
  have hspos : 0 < Real.sqrt ((n + 1 : ℕ) : ℝ) := Real.sqrt_pos.2 (by positivity)
  have hsumpos : 0 < Real.sqrt ((n + 1 : ℕ) : ℝ) + Real.sqrt (n : ℝ) :=
    add_pos_of_pos_of_nonneg hspos (Real.sqrt_nonneg _)
  unfold rationalizedDifference quotientDifference
  field_simp [hspos.ne', hsumpos.ne']
  ring

theorem gap4 :
    ∀ n : ℕ, quotientDifference n = finalDifference n := by
  intro n
  have hs₁ : Real.sqrt ((n + 1 : ℕ) : ℝ) ^ 2 = ((n + 1 : ℕ) : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hs₀ : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hspos : 0 < Real.sqrt ((n + 1 : ℕ) : ℝ) := Real.sqrt_pos.2 (by positivity)
  have hsumpos : 0 < Real.sqrt ((n + 1 : ℕ) : ℝ) + Real.sqrt (n : ℝ) :=
    add_pos_of_pos_of_nonneg hspos (Real.sqrt_nonneg _)
  unfold quotientDifference finalDifference
  field_simp [hspos.ne', hsumpos.ne']
  norm_num only [Nat.cast_add, Nat.cast_one] at hs₁
  nlinarith

private theorem rpow_three_halves (m : ℕ) (hm : 0 < m) :
    Real.rpow (m : ℝ) (3 / 2 : ℝ) = Real.sqrt (m : ℝ) * (m : ℝ) := by
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast hm
  calc
    Real.rpow (m : ℝ) (3 / 2 : ℝ) =
        Real.rpow (m : ℝ) ((1 / 2 : ℝ) + 1) := by norm_num
    _ = Real.rpow (m : ℝ) (1 / 2 : ℝ) * Real.rpow (m : ℝ) 1 :=
      Real.rpow_add hmpos (1 / 2 : ℝ) 1
    _ = Real.rpow (m : ℝ) (1 / 2 : ℝ) * (m : ℝ) := by
      congr 1
      exact Real.rpow_one _
    _ = Real.sqrt (m : ℝ) * (m : ℝ) := by
      congr 1
      exact (Real.sqrt_eq_rpow _).symm

theorem gap5 :
    Asymptotics.IsBigO atTop
      (fun n : ℕ => finalDifference (n + 1))
      (fun n : ℕ => comparison (n + 1)) := by
  refine Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall fun n => ?_)
  let m : ℕ := n + 1
  have hm : 0 < m := by dsimp only [m]; omega
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast hm
  have hmnext : 0 < ((m + 1 : ℕ) : ℝ) := by positivity
  have hsqrtSq : Real.sqrt (m : ℝ) ^ 2 = (m : ℝ) :=
    Real.sq_sqrt hmpos.le
  have hsqrtle : Real.sqrt (m : ℝ) ≤ Real.sqrt ((m + 1 : ℕ) : ℝ) := by
    apply Real.sqrt_le_sqrt
    exact_mod_cast Nat.le_succ m
  have hsumle : Real.sqrt (m : ℝ) ≤
      Real.sqrt ((m + 1 : ℕ) : ℝ) + Real.sqrt (m : ℝ) :=
    le_add_of_nonneg_left (Real.sqrt_nonneg _)
  have hsqle : Real.sqrt (m : ℝ) ^ 2 ≤
      (Real.sqrt ((m + 1 : ℕ) : ℝ) + Real.sqrt (m : ℝ)) ^ 2 :=
    pow_le_pow_left₀ (Real.sqrt_nonneg _) hsumle 2
  have hdenBound : Real.rpow (m : ℝ) (3 / 2 : ℝ) ≤
      Real.sqrt ((m + 1 : ℕ) : ℝ) *
        (Real.sqrt ((m + 1 : ℕ) : ℝ) + Real.sqrt (m : ℝ)) ^ 2 := by
    calc
      Real.rpow (m : ℝ) (3 / 2 : ℝ) =
          Real.sqrt (m : ℝ) * Real.sqrt (m : ℝ) ^ 2 := by
        rw [rpow_three_halves m hm, hsqrtSq]
      _ ≤ Real.sqrt ((m + 1 : ℕ) : ℝ) *
          (Real.sqrt ((m + 1 : ℕ) : ℝ) + Real.sqrt (m : ℝ)) ^ 2 :=
        mul_le_mul hsqrtle hsqle (sq_nonneg _) (Real.sqrt_nonneg _)
  have hrpowpos : 0 < Real.rpow (m : ℝ) (3 / 2 : ℝ) :=
    Real.rpow_pos_of_pos hmpos _
  have hdenpos : 0 < Real.sqrt ((m + 1 : ℕ) : ℝ) *
      (Real.sqrt ((m + 1 : ℕ) : ℝ) + Real.sqrt (m : ℝ)) ^ 2 := by
    positivity
  unfold finalDifference comparison
  simp only [m] at hdenBound hrpowpos hdenpos ⊢
  norm_num only [Nat.cast_add, Nat.cast_one] at hdenBound hrpowpos hdenpos ⊢
  simp only [Real.norm_eq_abs, abs_div, abs_neg, abs_one, abs_of_pos hdenpos,
    abs_of_pos hrpowpos, one_mul]
  exact one_div_le_one_div_of_le hrpowpos hdenBound

theorem gap6 :
    Asymptotics.IsBigO atTop
      (fun n : ℕ => x (n + 2) - x (n + 1))
      (fun n : ℕ => comparison (n + 1)) := by
  have heq : (fun n : ℕ => x (n + 2) - x (n + 1)) =
      (fun n : ℕ => finalDifference (n + 1)) := by
    funext n
    rw [show n + 2 = (n + 1) + 1 by omega, gap1 (n + 1),
      gap2 (n + 1), gap3 (n + 1), gap4 (n + 1)]
  rw [heq]
  exact gap5

theorem gap7 :
    Summable (fun n : ℕ => comparison (n + 1)) := by
  have hall : Summable comparison := by
    unfold comparison
    exact Real.summable_one_div_nat_rpow.mpr (by norm_num)
  exact (summable_nat_add_iff 1).mpr hall

theorem gap8 :
    ∀ n : ℕ,
      x n = ∑ k ∈ Finset.Icc 1 n, (x k - x (k - 1)) := by
  intro n
  induction n with
  | zero => simp [x]
  | succ n ih =>
      have hset : Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
        ext k
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      have hnot : n + 1 ∉ Finset.Icc 1 n := by simp
      rw [hset, Finset.sum_insert hnot, ← ih]
      simp only [Nat.add_sub_cancel]
      ring

theorem gap9
    (hbigO : Asymptotics.IsBigO atTop
      (fun n : ℕ => x (n + 2) - x (n + 1))
      (fun n : ℕ => comparison (n + 1)))
    (hsum : Summable (fun n : ℕ => comparison (n + 1))) :
    ∃ L : ℝ, Tendsto x atTop (nhds L) := by
  let d : ℕ → ℝ := fun n => x (n + 2) - x (n + 1)
  have hd : Summable d := by
    exact summable_of_isBigO_nat hsum hbigO
  have hpartial : ∀ n : ℕ,
      (∑ k ∈ Finset.range n, d k) = x (n + 1) - x 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        dsimp only [d]
        ring
  have hdiff : Tendsto (fun n : ℕ => x (n + 1) - x 1) atTop
      (nhds (∑' n : ℕ, d n)) := by
    apply hd.hasSum.tendsto_sum_nat.congr'
    exact Eventually.of_forall (fun n => hpartial n)
  have hconst : Tendsto (fun _ : ℕ => x 1) atTop (nhds (x 1)) :=
    tendsto_const_nhds
  have hshift : Tendsto (fun n : ℕ => x (n + 1)) atTop
      (nhds ((∑' n : ℕ, d n) + x 1)) := by
    convert hdiff.add hconst using 1 <;> ring
  refine ⟨(∑' n : ℕ, d n) + x 1, ?_⟩
  apply (tendsto_add_atTop_iff_nat 1).mp
  simpa [Nat.add_comm] using hshift

theorem gap10
    (hlimit : ∃ L : ℝ, Tendsto x atTop (nhds L)) :
    ProofGap.ConvergentSeq x := by
  unfold ProofGap.ConvergentSeq
  exact hlimit

theorem gap11
    (hconv : ProofGap.ConvergentSeq x) :
    ProofGap.ConvergentSeq x := by
  exact hconv

end

end ProofGap.Exercise2653
