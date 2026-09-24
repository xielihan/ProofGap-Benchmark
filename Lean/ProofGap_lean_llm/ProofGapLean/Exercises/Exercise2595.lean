import ProofGapLean.Prelude.Analysis
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Order.Filter.Tendsto
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise2595

noncomputable section

def nthRoot (n : ℕ) (x : ℝ) : ℝ :=
  Real.rpow x (1 / (n : ℝ))

def term (n : ℕ) : ℝ :=
  (2 + (-1 : ℝ) ^ n) / (2 : ℝ) ^ n

def transformedRoot (n : ℕ) : ℝ :=
  nthRoot n (2 + (-1 : ℝ) ^ n) / 2

private lemma numerator_bounds (n : ℕ) :
    (1 : ℝ) ≤ 2 + (-1 : ℝ) ^ n ∧ 2 + (-1 : ℝ) ^ n ≤ 3 := by
  have hlo : (-1 : ℝ) ≤ (-1 : ℝ) ^ n := by
    have h := neg_abs_le ((-1 : ℝ) ^ n)
    simpa [abs_pow] using h
  have hhi : (-1 : ℝ) ^ n ≤ 1 := by
    have h := le_abs_self ((-1 : ℝ) ^ n)
    simpa [abs_pow] using h
  constructor <;> linarith

theorem gap1
    (a : ℕ → ℝ) (ha : ∀ n, a n = term n) :
    ∀ L : ℝ, Tendsto (fun n => nthRoot n (a n)) atTop (nhds L) ↔
      Tendsto transformedRoot atTop (nhds L) := by
  intro L
  have heq :
      (fun n => nthRoot n (a n)) =ᶠ[atTop] transformedRoot := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with n hn
    rw [ha n]
    have hn0 : n ≠ 0 := Nat.ne_of_gt hn
    have hnum : 0 ≤ 2 + (-1 : ℝ) ^ n :=
      le_trans (by norm_num) (numerator_bounds n).1
    have hpow : 0 ≤ (2 : ℝ) ^ n :=
      pow_nonneg (by norm_num) n
    have hden :
        Real.rpow ((2 : ℝ) ^ n) (1 / (n : ℝ)) = 2 := by
      simpa [one_div] using
        (Real.pow_rpow_inv_natCast (show 0 ≤ (2 : ℝ) by norm_num) hn0)
    have hdiv :
        Real.rpow
            ((2 + (-1 : ℝ) ^ n) / (2 : ℝ) ^ n)
            (1 / (n : ℝ)) =
          Real.rpow (2 + (-1 : ℝ) ^ n) (1 / (n : ℝ)) /
            Real.rpow ((2 : ℝ) ^ n) (1 / (n : ℝ)) := by
      exact Real.div_rpow (z := (1 / (n : ℝ))) hnum hpow
    unfold term transformedRoot nthRoot
    calc
      Real.rpow
          ((2 + (-1 : ℝ) ^ n) / (2 : ℝ) ^ n)
          (1 / (n : ℝ)) =
          Real.rpow (2 + (-1 : ℝ) ^ n) (1 / (n : ℝ)) /
            Real.rpow ((2 : ℝ) ^ n) (1 / (n : ℝ)) := hdiv
      _ = Real.rpow (2 + (-1 : ℝ) ^ n) (1 / (n : ℝ)) / 2 := by
        rw [hden]
  constructor
  · intro h
    exact h.congr' heq
  · intro h
    exact h.congr' heq.symm

theorem gap2 :
    Tendsto transformedRoot atTop (nhds (1 / 2 : ℝ)) := by
  have hinv :
      Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (nhds 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hmul :
      Tendsto (fun n : ℕ => Real.log 3 * (1 / (n : ℝ))) atTop (nhds 0) := by
    convert tendsto_const_nhds.mul hinv using 1 <;> simp
  have hexp :
      Tendsto (fun n : ℕ => Real.exp (Real.log 3 * (1 / (n : ℝ))))
        atTop (nhds (Real.exp 0)) :=
    (Real.continuous_exp.tendsto 0).comp hmul
  have hpow3 :
      Tendsto (fun n : ℕ => Real.rpow 3 (1 / (n : ℝ)))
        atTop (nhds 1) := by
    simpa [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)] using hexp
  have hupper :
      Tendsto (fun n : ℕ => Real.rpow 3 (1 / (n : ℝ)) / 2)
        atTop (nhds (1 / 2 : ℝ)) := by
    simpa using hpow3.div_const (2 : ℝ)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hupper ?_ ?_
  · intro n
    unfold transformedRoot nthRoot
    have hb := (numerator_bounds n).1
    have he : 0 ≤ (1 / (n : ℝ)) :=
      div_nonneg (by norm_num) (Nat.cast_nonneg n)
    have hr :
        (1 : ℝ) ≤ Real.rpow (2 + (-1 : ℝ) ^ n) (1 / (n : ℝ)) := by
      simpa using
        (Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1) hb he)
    exact (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).2 hr
  · intro n
    unfold transformedRoot nthRoot
    have hb := numerator_bounds n
    have hbase : 0 ≤ 2 + (-1 : ℝ) ^ n :=
      le_trans (by norm_num) hb.1
    have he : 0 ≤ (1 / (n : ℝ)) :=
      div_nonneg (by norm_num) (Nat.cast_nonneg n)
    have hr :
        Real.rpow (2 + (-1 : ℝ) ^ n) (1 / (n : ℝ)) ≤
          Real.rpow 3 (1 / (n : ℝ)) :=
      Real.rpow_le_rpow hbase hb.2 he
    exact (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 2)).2 hr

theorem gap3 :
    (1 / 2 : ℝ) < 1 := by
  norm_num

theorem gap4
    (a : ℕ → ℝ) (ha : ∀ n, a n = term n)
    (hroot : ∀ L : ℝ,
      Tendsto (fun n => nthRoot n (a n)) atTop (nhds L) ↔
        Tendsto transformedRoot atTop (nhds L))
    (htransformed : Tendsto transformedRoot atTop (nhds (1 / 2 : ℝ)))
    (hlt : (1 / 2 : ℝ) < 1) :
    Tendsto (fun n => nthRoot n (a n)) atTop (nhds (1 / 2 : ℝ)) ∧
      (1 / 2 : ℝ) < 1 := by
  refine ⟨?_, hlt⟩
  exact (hroot (1 / 2 : ℝ)).2 htransformed

theorem gap5
    (hroot : Tendsto (fun n => nthRoot n (term n)) atTop
      (nhds (1 / 2 : ℝ)))
    (hlt : (1 / 2 : ℝ) < 1) :
    Summable term := by
  have hpos : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  have hneg : Summable (fun n : ℕ => (-1 / 2 : ℝ) ^ n) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  have hseries :
      Summable (fun n : ℕ =>
        (2 : ℝ) * (1 / 2 : ℝ) ^ n + (-1 / 2 : ℝ) ^ n) :=
    (hpos.mul_left (2 : ℝ)).add hneg
  refine hseries.congr ?_
  intro n
  unfold term
  simp only [div_pow, one_pow]
  ring

theorem gap6
    (hsum : Summable term) :
    Summable term := by
  exact hsum

end

end ProofGap.Exercise2595
