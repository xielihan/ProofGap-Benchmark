import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace ProofGap.Exercise2731

noncomputable section

open Filter

def term (x : ℝ) (n : ℕ) : ℝ :=
  (n + x) ^ n / Real.rpow n (n + x)

def comparison (x : ℝ) (n : ℕ) : ℝ :=
  Real.rpow n (-x)

theorem gap1 (x : ℝ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 0 < term x n := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max 0 (-x))
  refine ⟨N, fun n hn ↦ ?_⟩
  have hN0 : 0 < (N : ℝ) := (le_max_left 0 (-x)).trans_lt hN
  have hNx : -x < (N : ℝ) := (le_max_right 0 (-x)).trans_lt hN
  have hNn : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) := hN0.trans_le hNn
  have hnx : 0 < (n : ℝ) + x := by linarith
  exact div_pos (pow_pos hnx n) (Real.rpow_pos_of_pos hn0 _)

theorem gap2 (x : ℝ) :
    Tendsto
      (fun n : ℕ => term x (n + 1) / comparison x (n + 1))
      atTop
      (nhds (Real.exp x)) := by
  apply ((Real.tendsto_one_add_div_pow_exp x).comp (tendsto_add_atTop_nat 1)).congr'
  filter_upwards with n
  let k : ℕ := n + 1
  change (1 + x / (k : ℝ)) ^ k = term x k / comparison x k
  symm
  have hk : 0 < (k : ℝ) := by
    dsimp [k]
    positivity
  have hrpow : Real.rpow (k : ℝ) x ≠ 0 := (Real.rpow_pos_of_pos hk x).ne'
  simp only [term, comparison]
  rw [show Real.rpow (k : ℝ) ((k : ℝ) + x) =
      Real.rpow (k : ℝ) (k : ℝ) * Real.rpow (k : ℝ) x from
        Real.rpow_add hk (k : ℝ) x]
  rw [show Real.rpow (k : ℝ) (k : ℝ) = (k : ℝ) ^ k from
        Real.rpow_natCast (k : ℝ) k]
  rw [show Real.rpow (k : ℝ) (-x) = (Real.rpow (k : ℝ) x)⁻¹ from
        Real.rpow_neg hk.le x]
  rw [div_inv_eq_mul]
  calc
    _ = (((k : ℝ) + x) / (k : ℝ)) ^ k := by
      rw [div_pow]
      field_simp [hrpow]
    _ = (1 + x / (k : ℝ)) ^ k := by
      congr 1
      field_simp

theorem gap3 (x : ℝ) :
    Tendsto
      (fun n : ℕ => (1 + x / ((n + 1 : ℕ) : ℝ)) ^ (n + 1))
      atTop (nhds (Real.exp x)) := by
  exact (Real.tendsto_one_add_div_pow_exp x).comp (tendsto_add_atTop_nat 1)

theorem gap4 (x : ℝ) :
    Tendsto
      (fun n : ℕ => term x (n + 1) / comparison x (n + 1))
      atTop (nhds (Real.exp x)) := by
  exact gap2 x

theorem gap5 (x : ℝ) (hx : 1 < x) :
    Summable (fun n : ℕ => |term x (n + 1)|) := by
  have hcomparison : Summable (fun n : ℕ => comparison x (n + 1)) := by
    simpa [comparison] using
      (summable_nat_add_iff (f := fun n : ℕ => Real.rpow n (-x)) 1).2
        ((Real.summable_nat_rpow (p := -x)).2 (by linarith))
  have htheta :
      (fun n : ℕ => comparison x (n + 1)) =Θ[atTop]
        (fun n : ℕ => term x (n + 1)) :=
    Asymptotics.isTheta_of_div_tendsto_nhds_ne_zero (gap2 x) (Real.exp_ne_zero x)
  have hterm : Summable (fun n : ℕ => term x (n + 1)) :=
    summable_of_isBigO_nat hcomparison htheta.2
  simpa [Real.norm_eq_abs] using hterm.norm

theorem gap6 (x : ℝ) (hx : x ≤ 1) :
    ¬ Summable (fun n : ℕ => term x (n + 1)) := by
  intro hterm
  have htheta :
      (fun n : ℕ => comparison x (n + 1)) =Θ[atTop]
        (fun n : ℕ => term x (n + 1)) :=
    Asymptotics.isTheta_of_div_tendsto_nhds_ne_zero (gap2 x) (Real.exp_ne_zero x)
  have hcomparison : Summable (fun n : ℕ => comparison x (n + 1)) :=
    summable_of_isBigO_nat hterm htheta.1
  have hbase : Summable (fun n : ℕ => comparison x n) := by
    apply (summable_nat_add_iff (f := comparison x) 1).1
    simpa using hcomparison
  have hneg : -x < -1 :=
    (Real.summable_nat_rpow (p := -x)).1 (by simpa [comparison] using hbase)
  have hx' : 1 < x := by linarith
  linarith

theorem gap7 (x : ℝ) :
    1 < x ↔ Summable (fun n : ℕ => term x (n + 1)) := by
  constructor
  · intro hx
    have hnorm : Summable (fun n : ℕ => ‖term x (n + 1)‖) := by
      simpa [Real.norm_eq_abs] using gap5 x hx
    exact hnorm.of_norm
  · intro hterm
    by_contra hx
    exact gap6 x (le_of_not_gt hx) hterm

end

end ProofGap.Exercise2731
