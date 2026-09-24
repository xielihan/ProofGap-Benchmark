import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise2740

noncomputable section

open Filter

def weightedTerm (a : ℕ → ℝ) (x : ℝ) (n : ℕ) : ℝ :=
  a n / Real.rpow n x

def multiplier (x x₀ : ℝ) (n : ℕ) : ℝ :=
  1 / Real.rpow n (x - x₀)

private theorem _root_.Real.tendsto_rpow_atTop {p : ℝ} (hp : 0 < p) :
    Tendsto (fun y : ℝ => Real.rpow y p) atTop atTop := by
  have hlog : Tendsto (fun y : ℝ => Real.log y) atTop atTop :=
    Real.tendsto_log_atTop
  have hmul : Tendsto (fun y : ℝ => Real.log y * p) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    filter_upwards [(tendsto_atTop.1 hlog) (b / p)] with y hy
    calc
      b = (b / p) * p := by
        field_simp [ne_of_gt hp]
      _ ≤ Real.log y * p :=
        mul_le_mul_of_nonneg_right hy (le_of_lt hp)
  have hexp :
      Tendsto (fun y : ℝ => Real.exp (Real.log y * p)) atTop atTop :=
    Real.tendsto_exp_atTop.comp hmul
  refine hexp.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
  exact (Real.rpow_def_of_pos hy p).symm

theorem gap1 (a : ℕ → ℝ) (x x₀ : ℝ) :
    ∀ n : ℕ, 1 ≤ n →
      weightedTerm a x n = weightedTerm a x₀ n * multiplier x x₀ n := by
  intro n hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)
  simp only [weightedTerm, multiplier]
  change a n / ((n : ℝ) ^ x) =
    (a n / ((n : ℝ) ^ x₀)) * (1 / ((n : ℝ) ^ (x - x₀)))
  have hpow :
      ((n : ℝ) ^ x) =
        ((n : ℝ) ^ x₀) * ((n : ℝ) ^ (x - x₀)) := by
    calc
      ((n : ℝ) ^ x) = ((n : ℝ) ^ (x₀ + (x - x₀))) := by
        congr 1
        ring
      _ = ((n : ℝ) ^ x₀) * ((n : ℝ) ^ (x - x₀)) := by
        exact Real.rpow_add hnpos x₀ (x - x₀)
  rw [hpow]
  field_simp [ne_of_gt (Real.rpow_pos_of_pos hnpos x₀),
    ne_of_gt (Real.rpow_pos_of_pos hnpos (x - x₀))]

theorem gap2 (a : ℕ → ℝ) (x₀ : ℝ)
    (h : Summable (fun n : ℕ => weightedTerm a x₀ (n + 1))) :
    Summable (fun n : ℕ => weightedTerm a x₀ (n + 1)) := by
  exact h

theorem gap3 (x x₀ : ℝ) (hxx : x₀ < x) :
    Antitone (fun n : ℕ => multiplier x x₀ (n + 1)) ∧
      Tendsto (fun n : ℕ => multiplier x x₀ (n + 1)) atTop (nhds 0) := by
  have hp : 0 < x - x₀ := sub_pos.mpr hxx
  constructor
  · intro m n hmn
    simp only [multiplier]
    have hbase : ((m + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.add_le_add_right hmn 1)
    have hrpow :
        Real.rpow ((m + 1 : ℕ) : ℝ) (x - x₀) ≤
          Real.rpow ((n + 1 : ℕ) : ℝ) (x - x₀) := by
      exact Real.rpow_le_rpow (by positivity) hbase (le_of_lt hp)
    exact one_div_le_one_div_of_le
      (Real.rpow_pos_of_pos (by positivity) (x - x₀)) hrpow
  · have hshift : Tendsto (fun n : ℕ => n + 1) atTop atTop := by
      refine tendsto_atTop.2 ?_
      intro b
      filter_upwards [eventually_ge_atTop b] with n hn
      omega
    have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    have hden :
        Tendsto
          (fun n : ℕ => Real.rpow ((n + 1 : ℕ) : ℝ) (x - x₀))
          atTop atTop :=
      (Real.tendsto_rpow_atTop hp).comp (hcast.comp hshift)
    simpa only [multiplier, one_div] using
      (tendsto_inv_atTop_zero.comp hden)

theorem gap4 (a : ℕ → ℝ) (x x₀ : ℝ) (hxx : x₀ < x)
    (h : Summable (fun n : ℕ => weightedTerm a x₀ (n + 1))) :
    Summable (fun n : ℕ => weightedTerm a x (n + 1)) := by
  have hm := gap3 x x₀ hxx
  have hmult : ∀ n : ℕ,
      ‖multiplier x x₀ (n + 1)‖ ≤ (1 : ℝ) := by
    intro n
    have hpos : 0 < multiplier x x₀ (n + 1) := by
      simp only [multiplier]
      exact one_div_pos.mpr
        (Real.rpow_pos_of_pos (by positivity) (x - x₀))
    rw [Real.norm_eq_abs, abs_of_pos hpos]
    simpa [multiplier] using (hm.1 (Nat.zero_le n))
  have habs : Summable (fun n : ℕ =>
      |weightedTerm a x₀ (n + 1)|) :=
    (summable_abs_iff).2 h
  have hs : Summable (fun n : ℕ =>
      weightedTerm a x₀ (n + 1) * multiplier x x₀ (n + 1)) := by
    refine habs.of_norm_bounded ?_
    intro n
    simpa only [norm_mul, Real.norm_eq_abs, abs_mul, abs_abs, mul_one] using
      (mul_le_mul_of_nonneg_left (hmult n)
        (abs_nonneg (weightedTerm a x₀ (n + 1))))
  refine hs.congr ?_
  intro n
  exact (gap1 a x x₀ (n + 1)
    (Nat.succ_le_succ (Nat.zero_le n))).symm

theorem gap5 (a : ℕ → ℝ) (x x₀ : ℝ) (hxx : x₀ < x)
    (h : Summable (fun n : ℕ => weightedTerm a x₀ (n + 1))) :
    Summable (fun n : ℕ => weightedTerm a x (n + 1)) := by
  exact gap4 a x x₀ hxx h

end

end ProofGap.Exercise2740
