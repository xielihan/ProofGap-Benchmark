import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise2830

noncomputable section

open Filter
open scoped BigOperators Topology

def coefficient (n : ℕ) : ℝ :=
  1 / (2 : ℝ) ^ n

def term (n : ℕ) (x : ℝ) : ℝ :=
  x ^ (n ^ 2) / (2 : ℝ) ^ n

def SeriesConvergesAt (x : ℝ) : Prop :=
  Summable (fun k : ℕ => term (k + 1) x)

def HasLacunaryConvergenceRadiusOne : Prop :=
  (∀ x : ℝ, |x| < 1 → SeriesConvergesAt x) ∧
    (∀ x : ℝ, 1 < |x| → ¬ SeriesConvergesAt x)

private theorem summable_half_pow_shift :
    Summable (fun k : ℕ => (1 / 2 : ℝ) ^ (k + 1)) := by
  have h : Summable (fun k : ℕ => (1 / 2 : ℝ) ^ k) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  simpa [pow_succ, mul_comm] using h.mul_left (1 / 2 : ℝ)

private theorem seriesConvergesAt_of_abs_lt_one {x : ℝ} (hx : |x| < 1) :
    SeriesConvergesAt x := by
  unfold SeriesConvergesAt
  refine Summable.of_norm_bounded summable_half_pow_shift ?_
  intro k
  have hpow : |x| ^ ((k + 1) ^ 2) ≤ 1 :=
    pow_le_one₀ (abs_nonneg x) (le_of_lt hx)
  have hden : 0 ≤ (2 : ℝ) ^ (k + 1) := by positivity
  have hdiv :
      |x| ^ ((k + 1) ^ 2) / (2 : ℝ) ^ (k + 1) ≤
        1 / (2 : ℝ) ^ (k + 1) :=
    div_le_div_of_nonneg_right hpow hden
  simpa [term, norm_div, norm_pow, Real.norm_eq_abs, one_div_pow] using hdiv

private theorem not_seriesConvergesAt_of_one_lt_abs {x : ℝ}
    (hx : 1 < |x|) : ¬ SeriesConvergesAt x := by
  intro hs
  unfold SeriesConvergesAt at hs
  have hnorm :
      Tendsto (fun k : ℕ => ‖term (k + 1) x‖) atTop (nhds 0) := by
    simpa using hs.tendsto_atTop_zero.norm
  have hsmall : ∀ᶠ k : ℕ in atTop, ‖term (k + 1) x‖ < 1 :=
    (tendsto_order.1 hnorm).2 1 (by norm_num)
  have hbase : ∀ᶠ k : ℕ in atTop, (2 : ℝ) ≤ |x| ^ k :=
    (tendsto_pow_atTop_atTop_of_one_lt hx).eventually
      (eventually_ge_atTop (2 : ℝ))
  have hcontra : ∀ᶠ k : ℕ in atTop, False := by
    filter_upwards [hsmall, hbase] with k hk hb
    have hb' : (2 : ℝ) ≤ |x| ^ (k + 1) := by
      calc
        (2 : ℝ) ≤ |x| ^ k := hb
        _ = |x| ^ k * 1 := by simp
        _ ≤ |x| ^ k * |x| :=
          mul_le_mul_of_nonneg_left (le_of_lt hx)
            (pow_nonneg (abs_nonneg x) k)
        _ = |x| ^ (k + 1) := by rw [pow_succ]
    have hnum :
        (2 : ℝ) ^ (k + 1) ≤ |x| ^ ((k + 1) ^ 2) := by
      calc
        (2 : ℝ) ^ (k + 1) ≤ (|x| ^ (k + 1)) ^ (k + 1) :=
          pow_le_pow_left₀ (by norm_num) hb' (k + 1)
        _ = |x| ^ ((k + 1) ^ 2) := by
          rw [pow_two, pow_mul]
    have hden : 0 < (2 : ℝ) ^ (k + 1) := by positivity
    have hlarge : 1 ≤ ‖term (k + 1) x‖ := by
      calc
        (1 : ℝ) = (2 : ℝ) ^ (k + 1) / (2 : ℝ) ^ (k + 1) := by
          field_simp
        _ ≤ |x| ^ ((k + 1) ^ 2) / (2 : ℝ) ^ (k + 1) :=
          div_le_div_of_nonneg_right hnum hden.le
        _ = ‖term (k + 1) x‖ := by
          simp [term, norm_div, norm_pow, Real.norm_eq_abs]
    exact (not_lt_of_ge hlarge) hk
  rcases hcontra.exists with ⟨k, hk⟩
  exact hk

theorem gap1 :
    Tendsto
      (fun n : ℕ =>
        Real.rpow (coefficient (n + 1))
          (1 / (((n + 1 : ℕ) : ℝ))))
      atTop (𝓝 (1 / 2 : ℝ)) := by
  have hseq :
      (fun n : ℕ =>
        Real.rpow (coefficient (n + 1))
          (1 / (((n + 1 : ℕ) : ℝ)))) =
        (fun _ : ℕ => (1 / 2 : ℝ)) := by
    funext n
    have hn : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have hc : 0 < coefficient (n + 1) := by
      unfold coefficient
      positivity
    have hlog :
        Real.log (coefficient (n + 1)) =
          -(((n + 1 : ℕ) : ℝ) * Real.log 2) := by
      unfold coefficient
      rw [Real.log_div
        (by norm_num : (1 : ℝ) ≠ 0)
        (by positivity : (2 : ℝ) ^ (n + 1) ≠ 0),
        Real.log_one, Real.log_pow]
      ring
    have hcancel :
        (-(((n + 1 : ℕ) : ℝ) * Real.log 2)) *
            (1 / (((n + 1 : ℕ) : ℝ))) =
          -Real.log 2 := by
      field_simp [ne_of_gt hn] <;> ring
    calc
      Real.rpow (coefficient (n + 1))
          (1 / (((n + 1 : ℕ) : ℝ))) =
          Real.exp
            (Real.log (coefficient (n + 1)) *
              (1 / (((n + 1 : ℕ) : ℝ)))) := by
            change (coefficient (n + 1)) ^
              (1 / (((n + 1 : ℕ) : ℝ))) = _
            exact Real.rpow_def_of_pos hc
              (1 / (((n + 1 : ℕ) : ℝ)))
      _ = (1 / 2 : ℝ) := by
        rw [hlog, hcancel, Real.exp_neg,
          Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        norm_num
  rw [hseq]
  exact tendsto_const_nhds

theorem gap2 :
    Tendsto
      (fun n : ℕ => Real.rpow (1 / 2 : ℝ) (1 / (((n + 1 : ℕ) : ℝ))))
      atTop (𝓝 1) := by
  have hinv :
      Tendsto (fun n : ℕ => (1 : ℝ) / (((n + 1 : ℕ) : ℝ)))
        atTop (nhds 0) := by
    simpa using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (nhds 0))
  have hconst :
      Tendsto (fun _ : ℕ => Real.log (1 / 2 : ℝ)) atTop
        (nhds (Real.log (1 / 2 : ℝ))) :=
    tendsto_const_nhds
  have hmul :
      Tendsto
        (fun n : ℕ =>
          Real.log (1 / 2 : ℝ) * (1 / (((n + 1 : ℕ) : ℝ))))
        atTop (nhds 0) := by
    simpa only [mul_zero] using hconst.mul hinv
  have hexp :
      Tendsto
        (fun n : ℕ =>
          Real.exp
            (Real.log (1 / 2 : ℝ) *
              (1 / (((n + 1 : ℕ) : ℝ)))))
        atTop (nhds (Real.exp 0)) :=
    (Real.continuous_exp.tendsto 0).comp hmul
  have heq :
      (fun n : ℕ =>
        Real.rpow (1 / 2 : ℝ) (1 / (((n + 1 : ℕ) : ℝ)))) =
      (fun n : ℕ =>
        Real.exp
          (Real.log (1 / 2 : ℝ) *
            (1 / (((n + 1 : ℕ) : ℝ))))) := by
    funext n
    change (1 / 2 : ℝ) ^ (1 / (((n + 1 : ℕ) : ℝ))) = _
    exact Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 1 / 2)
      (1 / (((n + 1 : ℕ) : ℝ)))
  rw [heq]
  simpa using hexp

theorem gap3 :
    HasLacunaryConvergenceRadiusOne := by
  constructor
  · intro x hx
    exact seriesConvergesAt_of_abs_lt_one hx
  · intro x hx
    exact not_seriesConvergesAt_of_one_lt_abs hx

theorem gap4 :
    ∀ x : ℝ, |x| < 1 → SeriesConvergesAt x := by
  exact gap3.1

theorem gap5 :
    ∀ x : ℝ, |x| = 1 →
      (∑' k : ℕ, |term (k + 1) x|) =
        ∑' k : ℕ, 1 / (2 : ℝ) ^ (k + 1) := by
  intro x hx
  apply tsum_congr
  intro k
  simp [term, abs_div, abs_pow, hx]

theorem gap6 :
    ∀ x : ℝ, |x| = 1 →
      Summable (fun k : ℕ => |term (k + 1) x|) := by
  intro x hx
  refine summable_half_pow_shift.congr ?_
  intro k
  simp [term, abs_div, abs_pow, hx]

theorem gap7 :
    ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 ↔ SeriesConvergesAt x := by
  intro x
  constructor
  · intro hx
    have hle : |x| ≤ 1 := by
      exact (abs_le).2 hx
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact gap4 x hlt
    · apply Summable.of_norm
      simpa [SeriesConvergesAt, Real.norm_eq_abs] using gap6 x heq
  · intro hs
    have hle : |x| ≤ 1 := by
      by_contra hnot
      have hgt : 1 < |x| := lt_of_not_ge hnot
      exact (gap3.2 x hgt) hs
    exact (abs_le).1 hle

end

end ProofGap.Exercise2830
