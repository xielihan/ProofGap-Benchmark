import ProofGapLean.Prelude.Analysis
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise2684

noncomputable section

open Filter

def signExponent (n : ℕ) : ℕ :=
  n * (n - 1) / 2

def positiveTerm (n : ℕ) : ℝ :=
  (n : ℝ) ^ 100 / (2 : ℝ) ^ n

def signedTerm (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ signExponent n * positiveTerm n

def ratio (n : ℕ) : ℝ :=
  positiveTerm (n + 1) / positiveTerm n

def ratioModel (n : ℕ) : ℝ :=
  (1 / 2 : ℝ) * (1 + 1 / (n : ℝ)) ^ 100

private theorem abs_signedTerm (n : ℕ) :
    |signedTerm n| = positiveTerm n := by
  unfold signedTerm
  rw [abs_mul]
  have hp : 0 ≤ positiveTerm n := by
    unfold positiveTerm
    positivity
  simp [hp]

theorem gap1 :
    ∑' n : ℕ, |signedTerm (n + 1)| =
      ∑' n : ℕ, positiveTerm (n + 1) := by
  apply tsum_congr
  intro n
  exact abs_signedTerm (n + 1)

theorem gap2 :
    ∀ n : ℕ, 1 ≤ n → ratio n = ratioModel n := by
  intro n hn
  have hn_nat : n ≠ 0 := by
    intro h
    subst n
    norm_num at hn
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast hn_nat
  unfold ratio ratioModel positiveTerm
  simp only [Nat.cast_add, Nat.cast_one]
  have hpow : (2 : ℝ) ^ (n + 1) = (2 : ℝ) ^ n * 2 := pow_succ _ _
  rw [hpow]
  field_simp [hn0]

theorem gap3 :
    Tendsto (fun n : ℕ => ratioModel (n + 1)) atTop
      (nhds (1 / 2 : ℝ)) := by
  have hzero :
      Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hone :
      Tendsto (fun n : ℕ => (1 : ℝ) + 1 / (n + 1)) atTop
        (nhds ((1 : ℝ) + 0)) :=
    tendsto_const_nhds.add hzero
  have hpow :
      Tendsto (fun n : ℕ => ((1 : ℝ) + 1 / (n + 1)) ^ 100) atTop
        (nhds (((1 : ℝ) + 0) ^ 100)) :=
    hone.pow 100
  have hhalf :
      Tendsto (fun _ : ℕ => (1 / 2 : ℝ)) atTop (nhds (1 / 2 : ℝ)) :=
    tendsto_const_nhds
  simpa [ratioModel, Nat.cast_add, Nat.cast_one] using hhalf.mul hpow

theorem gap4 : (1 / 2 : ℝ) < 1 := by
  norm_num

theorem gap5 :
    Tendsto (fun n : ℕ => ratio (n + 1)) atTop
      (nhds (1 / 2 : ℝ)) ∧ (1 / 2 : ℝ) < 1 := by
  constructor
  · have hfun :
        (fun n : ℕ => ratio (n + 1)) =
          (fun n : ℕ => ratioModel (n + 1)) := by
      funext n
      exact gap2 (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
    rw [hfun]
    exact gap3
  · exact gap4

theorem gap6 :
    Summable (fun n : ℕ => positiveTerm (n + 1)) := by
  have hnonneg (n : ℕ) : 0 ≤ positiveTerm n := by
    unfold positiveTerm
    positivity
  have hevent :
      ∀ᶠ n : ℕ in atTop, ratio (n + 1) < (3 / 4 : ℝ) :=
    gap5.1.eventually_lt_const (by norm_num)
  refine summable_of_ratio_norm_eventually_le
    (f := fun n : ℕ => positiveTerm (n + 1))
    (r := (3 / 4 : ℝ)) (by norm_num) ?_
  filter_upwards [hevent] with n hn
  have hpos : 0 < positiveTerm (n + 1) := by
    unfold positiveTerm
    positivity
  have hmul :
      positiveTerm ((n + 1) + 1) <
        (3 / 4 : ℝ) * positiveTerm (n + 1) :=
    (div_lt_iff₀ hpos).mp (by simpa only [ratio] using hn)
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg (hnonneg ((n + 1) + 1)),
    abs_of_nonneg (hnonneg (n + 1))] using hmul.le

theorem gap7 :
    Summable (fun n : ℕ => |signedTerm (n + 1)|) := by
  simpa only [abs_signedTerm] using gap6

end

end ProofGap.Exercise2684
