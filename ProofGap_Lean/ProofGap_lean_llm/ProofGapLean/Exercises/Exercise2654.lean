import ProofGapLean.Prelude.Analysis
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace ProofGap.Exercise2654

noncomputable section

open Filter
open scoped BigOperators

def x (n : ℕ) : ℝ :=
  (∑ k ∈ Finset.Icc 1 n, Real.log k / k) - Real.log n ^ 2 / 2

def rawDifference (n : ℕ) : ℝ :=
  Real.log n / n -
    (1 / 2 : ℝ) * (Real.log n ^ 2 - Real.log (n - 1) ^ 2)

def logarithmicDifference (n : ℕ) : ℝ :=
  Real.log n / n -
    (1 / 2 : ℝ) * Real.log (n / (n - 1 : ℝ)) * Real.log (n * (n - 1))

def comparison (n : ℕ) : ℝ :=
  Real.log n / (n : ℝ) ^ 2

private def firstError (n : ℕ) : ℝ :=
  Real.log ((n + 2 : ℝ) / (n + 1)) - 1 / (n + 2 : ℝ)

private def secondError (n : ℕ) : ℝ :=
  Real.log ((n + 2 : ℝ) * (n + 1)) -
    (2 * Real.log (n + 2) - 1 / (n + 2 : ℝ))

private def quadraticScale (n : ℕ) : ℝ :=
  1 / ((n + 2 : ℝ) ^ 2)

private def inverseScale (n : ℕ) : ℝ :=
  1 / (n + 2 : ℝ)

private def logScale (n : ℕ) : ℝ :=
  Real.log (n + 2)

private theorem ratio_eq_one_add (n : ℕ) :
    (n + 2 : ℝ) / (n + 1) = 1 + 1 / (n + 1 : ℝ) := by
  field_simp
  ring

private theorem firstError_nonneg (n : ℕ) : 0 ≤ firstError n := by
  rw [firstError, ratio_eq_one_add]
  have ht : 0 ≤ 1 / (n + 1 : ℝ) := by positivity
  have hlog := Real.le_log_one_add_of_nonneg ht
  have hreform :
      2 * (1 / (n + 1 : ℝ)) / (1 / (n + 1 : ℝ) + 2) =
        2 / (2 * (n : ℝ) + 3) := by
    field_simp
    ring
  have halgebra :
      1 / (n + 2 : ℝ) ≤
        2 * (1 / (n + 1 : ℝ)) / (1 / (n + 1 : ℝ) + 2) := by
    rw [hreform, div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  exact sub_nonneg.mpr (halgebra.trans hlog)

private theorem firstError_le (n : ℕ) :
    firstError n ≤ 2 * quadraticScale n := by
  rw [firstError, ratio_eq_one_add]
  have hlog : Real.log (1 + 1 / (n + 1 : ℝ)) ≤ 1 / (n + 1 : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + 1 / (n + 1 : ℝ))
    linarith
  calc
    Real.log (1 + 1 / (n + 1 : ℝ)) - 1 / (n + 2 : ℝ) ≤
        1 / (n + 1 : ℝ) - 1 / (n + 2 : ℝ) := sub_le_sub_right hlog _
    _ = 1 / ((n + 1 : ℝ) * (n + 2 : ℝ)) := by
      field_simp
      ring
    _ ≤ 2 * quadraticScale n := by
      unfold quadraticScale
      rw [show 2 * (1 / (n + 2 : ℝ) ^ 2) =
        2 / ((n + 2 : ℝ) ^ 2) by ring]
      rw [div_le_div_iff₀ (mul_pos (by positivity) (by positivity))
        (sq_pos_of_pos (by positivity))]
      nlinarith [sq_nonneg (n : ℝ)]

private theorem secondError_eq_neg (n : ℕ) :
    secondError n = -firstError n := by
  have hn2 : (n + 2 : ℝ) ≠ 0 := by positivity
  have hn1 : (n + 1 : ℝ) ≠ 0 := by positivity
  unfold secondError firstError
  rw [Real.log_mul hn2 hn1, Real.log_div hn2 hn1]
  ring

theorem gap1 :
    ∀ n : ℕ, 2 ≤ n → x n - x (n - 1) = rawDifference n := by
  intro n hn
  have hset : Finset.Icc 1 n = insert n (Finset.Icc 1 (n - 1)) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hnmem : n ∉ Finset.Icc 1 (n - 1) := by
    simp only [Finset.mem_Icc, not_and_or]
    omega
  have hsum :
      (∑ k ∈ Finset.Icc 1 n, Real.log k / k) =
        (∑ k ∈ Finset.Icc 1 (n - 1), Real.log k / k) + Real.log n / n := by
    rw [hset, Finset.sum_insert hnmem]
    ring
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  unfold x rawDifference
  rw [hsum, hcast]
  ring

theorem gap2 :
    ∀ n : ℕ, 2 ≤ n → rawDifference n = logarithmicDifference n := by
  intro n hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hn)
  have hn1pos : 0 < (n : ℝ) - 1 := by
    have hone : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
    linarith
  unfold rawDifference logarithmicDifference
  rw [Real.log_div hnpos.ne' hn1pos.ne', Real.log_mul hnpos.ne' hn1pos.ne']
  ring

theorem gap3 :
    ∀ n : ℕ, 2 ≤ n → x n - x (n - 1) = logarithmicDifference n := by
  intro n hn
  rw [gap1 n hn, gap2 n hn]

theorem gap4 :
    Asymptotics.IsBigO atTop
      (fun n : ℕ =>
        Real.log ((n + 2 : ℝ) / (n + 1)) - 1 / (n + 2 : ℝ))
      (fun n : ℕ => 1 / ((n + 2 : ℝ) ^ 2)) := by
  change Asymptotics.IsBigO atTop firstError quadraticScale
  refine Asymptotics.IsBigO.of_bound 2 (Filter.Eventually.of_forall fun n => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (firstError_nonneg n)]
  have hq : 0 ≤ quadraticScale n := by
    unfold quadraticScale
    positivity
  rw [abs_of_nonneg hq]
  exact firstError_le n

theorem gap5 :
    Asymptotics.IsBigO atTop
      (fun n : ℕ =>
        Real.log ((n + 2 : ℝ) * (n + 1)) -
          (2 * Real.log (n + 2) - 1 / (n + 2 : ℝ)))
      (fun n : ℕ => 1 / ((n + 2 : ℝ) ^ 2)) := by
  change Asymptotics.IsBigO atTop secondError quadraticScale
  exact gap4.neg_left.congr_left (fun n => (secondError_eq_neg n).symm)

private theorem difference_expansion (n : ℕ) :
    x (n + 2) - x (n + 1) =
      (1 / 2 : ℝ) * quadraticScale n -
        (1 / 2 : ℝ) * (secondError n * inverseScale n) -
        firstError n * logScale n +
        (1 / 2 : ℝ) * (firstError n * inverseScale n) -
        (1 / 2 : ℝ) * (firstError n * secondError n) := by
  have hscale : quadraticScale n = inverseScale n ^ 2 := by
    unfold quadraticScale inverseScale
    field_simp
  rw [← show n + 2 - 1 = n + 1 by omega]
  rw [gap3 (n + 2) (by omega)]
  rw [hscale]
  unfold logarithmicDifference firstError secondError inverseScale logScale
  push_cast
  ring_nf

private theorem quadraticScale_isBigO_comparison :
    Asymptotics.IsBigO atTop quadraticScale
      (fun n : ℕ => comparison (n + 2)) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine Asymptotics.IsBigO.of_bound (1 / Real.log 2)
    (Filter.Eventually.of_forall fun n => ?_)
  have hm : 0 < (((n + 2 : ℕ) : ℝ)) := by positivity
  have hlognonneg : 0 ≤ Real.log (((n + 2 : ℕ) : ℝ)) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ n + 2 by omega))
  have hlogle : Real.log 2 ≤ Real.log (((n + 2 : ℕ) : ℝ)) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast (show 2 ≤ n + 2 by omega))
  have hfactor : 1 ≤ (1 / Real.log 2) * Real.log (((n + 2 : ℕ) : ℝ)) := by
    rw [one_div_mul_eq_div, le_div_iff₀ hlog2]
    simpa using hlogle
  push_cast at hm hlognonneg hlogle hfactor ⊢
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  unfold quadraticScale comparison
  push_cast
  rw [abs_of_pos (one_div_pos.mpr (sq_pos_of_pos hm)),
    abs_of_nonneg (div_nonneg hlognonneg (sq_nonneg _))]
  calc
    1 / ((n : ℝ) + 2) ^ 2 ≤
        ((1 / Real.log 2) * Real.log ((n : ℝ) + 2)) *
          (1 / ((n : ℝ) + 2) ^ 2) :=
      le_mul_of_one_le_left (by positivity) hfactor
    _ = (1 / Real.log 2) *
        (Real.log ((n : ℝ) + 2) / ((n : ℝ) + 2) ^ 2) := by ring

private theorem inverseScale_isBigO_one :
    Asymptotics.IsBigO atTop inverseScale (fun _ : ℕ => (1 : ℝ)) := by
  refine Asymptotics.IsBigO.of_bound 1
    (Filter.Eventually.of_forall fun n => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by
    unfold inverseScale
    positivity : 0 < inverseScale n)]
  simp only [abs_one, one_mul]
  unfold inverseScale
  simpa only [one_div_one] using
    (one_div_le_one_div_of_le zero_lt_one
      (show (1 : ℝ) ≤ (n : ℝ) + 2 by
        exact_mod_cast (show 1 ≤ n + 2 by omega)))

private theorem quadraticScale_sq_isBigO :
    Asymptotics.IsBigO atTop (fun n => quadraticScale n * quadraticScale n)
      quadraticScale := by
  refine Asymptotics.IsBigO.of_bound 1
    (Filter.Eventually.of_forall fun n => ?_)
  have hq0 : 0 ≤ quadraticScale n := by unfold quadraticScale; positivity
  have hq1 : quadraticScale n ≤ 1 := by
    unfold quadraticScale
    simpa only [one_div_one] using
      (one_div_le_one_div_of_le zero_lt_one
        (one_le_pow₀ (show (1 : ℝ) ≤ (n : ℝ) + 2 by
          exact_mod_cast (show 1 ≤ n + 2 by omega)) :
          (1 : ℝ) ≤ ((n : ℝ) + 2) ^ 2))
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hq0,
    abs_of_nonneg (mul_nonneg hq0 hq0), one_mul]
  nlinarith

theorem gap6 :
    Asymptotics.IsBigO atTop
      (fun n : ℕ => x (n + 2) - x (n + 1))
      (fun n : ℕ => comparison (n + 2)) := by
  have hA : Asymptotics.IsBigO atTop firstError quadraticScale := gap4
  have hB : Asymptotics.IsBigO atTop secondError quadraticScale := gap5
  have hAlog : Asymptotics.IsBigO atTop
      (fun n => firstError n * logScale n)
      (fun n => comparison (n + 2)) := by
    exact (hA.mul (Asymptotics.isBigO_refl logScale atTop)).congr_right fun n => by
      unfold quadraticScale logScale comparison
      push_cast
      ring
  have hBr : Asymptotics.IsBigO atTop
      (fun n => secondError n * inverseScale n)
      (fun n => comparison (n + 2)) := by
    have hq : Asymptotics.IsBigO atTop
        (fun n => secondError n * inverseScale n) quadraticScale :=
      (hB.mul inverseScale_isBigO_one).congr_right (fun n => by simp)
    exact hq.trans quadraticScale_isBigO_comparison
  have hAr : Asymptotics.IsBigO atTop
      (fun n => firstError n * inverseScale n)
      (fun n => comparison (n + 2)) := by
    have hq : Asymptotics.IsBigO atTop
        (fun n => firstError n * inverseScale n) quadraticScale :=
      (hA.mul inverseScale_isBigO_one).congr_right (fun n => by simp)
    exact hq.trans quadraticScale_isBigO_comparison
  have hAB : Asymptotics.IsBigO atTop
      (fun n => firstError n * secondError n)
      (fun n => comparison (n + 2)) := by
    have hq : Asymptotics.IsBigO atTop
        (fun n => firstError n * secondError n) quadraticScale :=
      (hA.mul hB).trans quadraticScale_sq_isBigO
    exact hq.trans quadraticScale_isBigO_comparison
  have hcombined :=
    ((((quadraticScale_isBigO_comparison.const_mul_left (1 / 2 : ℝ)).sub
      (hBr.const_mul_left (1 / 2 : ℝ))).sub hAlog).add
      (hAr.const_mul_left (1 / 2 : ℝ))).sub
      (hAB.const_mul_left (1 / 2 : ℝ))
  exact hcombined.congr_left (fun n => (difference_expansion n).symm)

theorem gap7 :
    Summable (fun n : ℕ => comparison (n + 2)) := by
  have hbase : Summable (fun n : ℕ => 1 / |(n : ℝ) + 2| ^ (3 / 2 : ℝ)) :=
    (Real.summable_one_div_nat_add_rpow 2 (3 / 2)).mpr (by norm_num)
  have hmajorant : Summable (fun n : ℕ => 2 / |(n : ℝ) + 2| ^ (3 / 2 : ℝ)) := by
    simpa [div_eq_mul_inv] using hbase.mul_left 2
  apply hmajorant.of_nonneg_of_le
  · intro n
    unfold comparison
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ n + 2 by omega)))
      (sq_nonneg _)
  · intro n
    have hm : 0 < (((n + 2 : ℕ) : ℝ)) := by positivity
    have hlog := Real.log_natCast_le_rpow_div (n + 2)
      (by norm_num : (0 : ℝ) < 1 / 2)
    calc
      comparison (n + 2) =
          Real.log (((n + 2 : ℕ) : ℝ)) / (((n + 2 : ℕ) : ℝ)) ^ 2 := by
        unfold comparison
        rfl
      _ ≤ ((((n + 2 : ℕ) : ℝ)) ^ (1 / 2 : ℝ) / (1 / 2 : ℝ)) /
          (((n + 2 : ℕ) : ℝ)) ^ 2 :=
        div_le_div_of_nonneg_right hlog (sq_nonneg _)
      _ = 2 / |(n : ℝ) + 2| ^ (3 / 2 : ℝ) := by
        have hadd :
            (((n + 2 : ℕ) : ℝ)) ^ (1 / 2 : ℝ) *
                (((n + 2 : ℕ) : ℝ)) ^ (3 / 2 : ℝ) =
              (((n + 2 : ℕ) : ℝ)) ^ 2 := by
          rw [← Real.rpow_add hm]
          norm_num
        rw [abs_of_pos (by positivity : 0 < (n : ℝ) + 2)]
        push_cast at hadd ⊢
        calc
          ((((n : ℝ) + 2) ^ (1 / 2 : ℝ) / (1 / 2 : ℝ)) /
              ((n : ℝ) + 2) ^ 2) =
              2 * ((n : ℝ) + 2) ^ (1 / 2 : ℝ) / ((n : ℝ) + 2) ^ 2 := by ring
          _ = 2 / ((n : ℝ) + 2) ^ (3 / 2 : ℝ) := by
            apply (div_eq_div_iff (pow_ne_zero 2 (by positivity))
              (Real.rpow_pos_of_pos (by positivity) _).ne').2
            rw [mul_assoc, hadd]

theorem gap8
    (hbigO : Asymptotics.IsBigO atTop
      (fun n : ℕ => x (n + 2) - x (n + 1))
      (fun n : ℕ => comparison (n + 2)))
    (hsum : Summable (fun n : ℕ => comparison (n + 2))) :
    Summable (fun n : ℕ => x (n + 2) - x (n + 1)) := by
  exact summable_of_isBigO_nat hsum hbigO

theorem gap9 :
    ∀ n : ℕ,
      x n = ∑ k ∈ Finset.Icc 2 n, (x k - x (k - 1)) := by
  intro n
  induction n with
  | zero => simp [x]
  | succ n ih =>
      by_cases hn : 2 ≤ n + 1
      · have hset : Finset.Icc 2 (n + 1) =
            insert (n + 1) (Finset.Icc 2 n) := by
          ext k
          simp only [Finset.mem_Icc, Finset.mem_insert]
          omega
        have hnot : n + 1 ∉ Finset.Icc 2 n := by
          simp only [Finset.mem_Icc, not_and_or]
          omega
        rw [hset, Finset.sum_insert hnot, ← ih]
        rw [show n + 1 - 1 = n by omega]
        ring
      · have hn0 : n = 0 := by omega
        subst n
        simp [x]

theorem gap10
    (hsum : Summable (fun n : ℕ => x (n + 2) - x (n + 1)))
    (htelescope : ∀ n : ℕ,
      x n = ∑ k ∈ Finset.Icc 2 n, (x k - x (k - 1))) :
    ∃ L : ℝ, Tendsto x atTop (nhds L) := by
  let d : ℕ → ℝ := fun n => x (n + 2) - x (n + 1)
  refine ⟨∑' n, d n, ?_⟩
  apply (tendsto_add_atTop_iff_nat 1).mp
  have hpartial : Tendsto (fun n => ∑ i ∈ Finset.range n, d i)
      atTop (nhds (∑' n, d n)) := hsum.hasSum.tendsto_sum_nat
  refine Tendsto.congr' (Filter.Eventually.of_forall fun n => ?_) hpartial
  simp only [d]
  rw [htelescope (n + 1)]
  have hIcc : Finset.Icc 2 (n + 1) = Finset.Ico 2 (n + 2) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [hIcc, Finset.sum_Ico_eq_sum_range]
  rw [show n + 2 - 2 = n by omega]
  simp [add_comm]

theorem gap11
    (hlimit : ∃ L : ℝ, Tendsto x atTop (nhds L)) :
    ProofGap.ConvergentSeq x := by
  unfold ProofGap.ConvergentSeq
  exact hlimit

theorem gap12
    (hconv : ProofGap.ConvergentSeq x) :
    ProofGap.ConvergentSeq x := by
  exact hconv

end

end ProofGap.Exercise2654
