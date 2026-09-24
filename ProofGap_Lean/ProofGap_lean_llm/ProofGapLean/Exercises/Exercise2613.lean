import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Defs.Filter
import Mathlib.Order.Filter.AtTopBot.Defs

namespace ProofGap.Exercise2613

noncomputable section

open Filter

def exponent (k : ℝ) (n : ℕ) : ℝ :=
  1 + k / Real.log n

def term (k : ℝ) (n : ℕ) : ℝ :=
  1 / Real.rpow n (exponent k n)

def exponentialForm (k : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-(exponent k n) * Real.log n)

def harmonicModel (k : ℝ) (n : ℕ) : ℝ :=
  (1 / (n : ℝ)) * Real.exp (-k)

def converges (k : ℝ) : Prop :=
  Summable (fun n : ℕ => term k (n + 2))

theorem gap1 (k : ℝ) (n : ℕ) (hn : 2 ≤ n) :
    term k n = Real.rpow n (-(exponent k n)) := by
  unfold term
  rw [one_div]
  exact (Real.rpow_neg (show (0 : ℝ) ≤ (n : ℝ) by positivity)
    (exponent k n)).symm

theorem gap2 (k : ℝ) (n : ℕ) (hn : 2 ≤ n) :
    Real.rpow n (-(exponent k n)) = exponentialForm k n := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    linarith
  unfold exponentialForm
  change ((n : ℝ) ^ (-(exponent k n))) =
    Real.exp (-(exponent k n) * Real.log (n : ℝ))
  calc
    ((n : ℝ) ^ (-(exponent k n))) =
        Real.exp (Real.log (n : ℝ) * (-(exponent k n))) :=
      Real.rpow_def_of_pos hnpos _
    _ = Real.exp (-(exponent k n) * Real.log (n : ℝ)) := by
      congr 1
      ring

theorem gap3 (k : ℝ) (n : ℕ) (hn : 2 ≤ n) :
    exponentialForm k n = Real.exp (-(Real.log n + k)) := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn
  have hlog : Real.log (n : ℝ) ≠ 0 := by
    exact ne_of_gt (Real.log_pos (by linarith))
  unfold exponentialForm exponent
  apply congrArg Real.exp
  field_simp [hlog] <;> ring

theorem gap4 (k : ℝ) (n : ℕ) (hn : 2 ≤ n) :
    Real.exp (-(Real.log n + k)) = harmonicModel k n := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    linarith
  simp [harmonicModel, neg_add, Real.exp_add, Real.exp_neg,
    Real.exp_log hnpos, one_div, mul_comm]

theorem gap5 (k : ℝ) :
    Asymptotics.IsBigO atTop
      (fun n : ℕ => harmonicModel k (n + 2))
      (fun n : ℕ => 1 / ((n + 2 : ℕ) : ℝ)) := by
  refine Asymptotics.isBigO_iff.2 ⟨‖Real.exp (-k)‖, ?_⟩
  filter_upwards with n
  simp [harmonicModel, norm_mul, mul_comm]

theorem gap6 (k : ℝ) :
    Asymptotics.IsBigO atTop
      (fun n : ℕ => term k (n + 2))
      (fun n : ℕ => 1 / ((n + 2 : ℕ) : ℝ)) := by
  have heq :
      (fun n : ℕ => term k (n + 2)) =
        (fun n : ℕ => harmonicModel k (n + 2)) := by
    funext n
    have hn : 2 ≤ n + 2 := by omega
    calc
      term k (n + 2) = Real.rpow (((n + 2 : ℕ) : ℝ))
          (-(exponent k (n + 2))) := gap1 k (n + 2) hn
      _ = exponentialForm k (n + 2) := gap2 k (n + 2) hn
      _ = Real.exp (-(Real.log (((n + 2 : ℕ) : ℝ)) + k)) :=
        gap3 k (n + 2) hn
      _ = harmonicModel k (n + 2) := gap4 k (n + 2) hn
  rw [heq]
  exact gap5 k

theorem gap7 (k : ℝ) :
    ¬ converges k := by
  intro hk
  unfold converges at hk
  have hterm (n : ℕ) : term k (n + 2) = harmonicModel k (n + 2) := by
    have hn : 2 ≤ n + 2 := by omega
    calc
      term k (n + 2) = Real.rpow (((n + 2 : ℕ) : ℝ))
          (-(exponent k (n + 2))) := gap1 k (n + 2) hn
      _ = exponentialForm k (n + 2) := gap2 k (n + 2) hn
      _ = Real.exp (-(Real.log (((n + 2 : ℕ) : ℝ)) + k)) :=
        gap3 k (n + 2) hn
      _ = harmonicModel k (n + 2) := gap4 k (n + 2) hn
  have htail : Summable (fun n : ℕ => 1 / ((n + 2 : ℕ) : ℝ)) := by
    have hs := hk.mul_right (Real.exp k)
    simpa only [hterm, harmonicModel, mul_assoc, ← Real.exp_add,
      neg_add_cancel, Real.exp_zero, mul_one] using hs
  have hall : Summable (fun n : ℕ => 1 / (n : ℝ)) := by
    exact (summable_nat_add_iff 2).1 htail
  rcases hall with ⟨s, hs⟩
  have hrange :
      Tendsto (fun m : ℕ => Finset.range m) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro t
    let m : ℕ := t.sum (fun i => i) + 1
    have htm : t ⊆ Finset.range m := by
      intro x hx
      apply Finset.mem_range.mpr
      dsimp [m]
      exact Nat.lt_succ_of_le
        (Finset.single_le_sum (fun i _ => Nat.zero_le i) hx)
    filter_upwards [eventually_ge_atTop m] with n hn
    exact le_trans htm (Finset.range_mono hn)
  have hs' :
      Tendsto
        (fun t : Finset ℕ =>
          t.sum (fun n => 1 / (n : ℝ)))
        atTop (nhds s) := hs
  have hpartial :
      Tendsto
        (fun m : ℕ =>
          (Finset.range m).sum (fun n => 1 / (n : ℝ)))
        atTop (nhds s) := by
    simpa only [Function.comp_apply] using hs'.comp hrange
  obtain ⟨N0, hN0⟩ :=
    (Metric.tendsto_atTop.1 hpartial) (1 / 4) (by norm_num)
  let N : ℕ := N0 + 1
  have hN0N : N0 ≤ N := by
    simp [N]
  have hNpos : 0 < N := by
    simp [N]
  have hN0two : N0 ≤ 2 * N := by
    omega
  have hcloseN := hN0 N hN0N
  have hcloseTwo := hN0 (2 * N) hN0two
  have hcloseN' :
      |(Finset.range N).sum (fun n => 1 / (n : ℝ)) - s| <
        (1 / 4 : ℝ) := by
    simpa only [Real.dist_eq] using hcloseN
  have hcloseTwo' :
      |(Finset.range (2 * N)).sum (fun n => 1 / (n : ℝ)) - s| <
        (1 / 4 : ℝ) := by
    simpa only [Real.dist_eq] using hcloseTwo
  have hdiff_lt :
      (Finset.range (2 * N)).sum (fun n => 1 / (n : ℝ)) -
          (Finset.range N).sum (fun n => 1 / (n : ℝ)) <
        (1 / 2 : ℝ) := by
    have hupper := (abs_lt.mp hcloseTwo').2
    have hlower := (abs_lt.mp hcloseN').1
    linarith
  have hNrealpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast hNpos
  have hNrealne : (N : ℝ) ≠ 0 := ne_of_gt hNrealpos
  have hblock :
      (1 / 2 : ℝ) ≤
        (Finset.range N).sum
          (fun i => 1 / ((N + i : ℕ) : ℝ)) := by
    calc
      (1 / 2 : ℝ) =
          (Finset.range N).sum
            (fun _i => 1 / (((2 * N : ℕ) : ℝ))) := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          Nat.cast_mul]
        field_simp [hNrealne] <;> norm_num
      _ ≤ (Finset.range N).sum
          (fun i => 1 / ((N + i : ℕ) : ℝ)) := by
        refine Finset.sum_le_sum ?_
        intro i hi
        have hiN : i < N := Finset.mem_range.mp hi
        have hposNat : 0 < N + i := by omega
        have hleNat : N + i ≤ 2 * N := by omega
        have hposReal : (0 : ℝ) < ((N + i : ℕ) : ℝ) := by
          exact_mod_cast hposNat
        have hleReal :
            (((N + i : ℕ) : ℝ)) ≤ (((2 * N : ℕ) : ℝ)) := by
          exact_mod_cast hleNat
        exact one_div_le_one_div_of_le hposReal hleReal
  have hdiff_eq :
      (Finset.range (2 * N)).sum (fun n => 1 / (n : ℝ)) -
          (Finset.range N).sum (fun n => 1 / (n : ℝ)) =
        (Finset.range N).sum
          (fun i => 1 / ((N + i : ℕ) : ℝ)) := by
    rw [show 2 * N = N + N by omega, Finset.sum_range_add]
    ring
  have hdiff_ge :
      (1 / 2 : ℝ) ≤
        (Finset.range (2 * N)).sum (fun n => 1 / (n : ℝ)) -
          (Finset.range N).sum (fun n => 1 / (n : ℝ)) := by
    rw [hdiff_eq]
    exact hblock
  linarith

theorem gap8 :
    ∀ k : ℝ, ¬ Summable (fun n : ℕ => term k (n + 2)) := by
  intro k
  simpa [converges] using gap7 k

end

end ProofGap.Exercise2613
