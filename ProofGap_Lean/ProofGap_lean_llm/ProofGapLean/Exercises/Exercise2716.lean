import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Topology.Defs.Filter
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise2716

noncomputable section

open Filter

def term (x : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) / x ^ n

def powerSeriesTerm (y : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) * y ^ n

def ConditionallySummable (x : ℝ) : Prop :=
  Summable (fun n : ℕ => term x (n + 1)) ∧
    ¬ Summable (fun n : ℕ => |term x (n + 1)|)

private theorem tendsto_natCast_add_one_pow_inv_atTop :
    Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (1 / ((n + 1 : ℕ) : ℝ)))
      atTop (nhds 1) := by
  have hsqrt :
      Tendsto (fun n : ℕ => Real.sqrt (((n + 1 : ℕ) : ℝ)))
        atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    obtain ⟨N : ℕ, hN⟩ := exists_nat_ge (b ^ 2)
    filter_upwards [eventually_ge_atTop N] with n hn
    have hbound :
        b ^ 2 ≤ (((n + 1 : ℕ) : ℝ)) := by
      calc
        b ^ 2 ≤ (N : ℝ) := hN
        _ ≤ (n : ℝ) := by exact Nat.cast_le.2 hn
        _ ≤ (((n + 1 : ℕ) : ℝ)) := by norm_num
    have hsquare :
        (Real.sqrt (((n + 1 : ℕ) : ℝ))) ^ 2 =
          (((n + 1 : ℕ) : ℝ)) :=
      Real.sq_sqrt (by positivity)
    have hsnonneg :
        0 ≤ Real.sqrt (((n + 1 : ℕ) : ℝ)) :=
      Real.sqrt_nonneg _
    nlinarith
  have hinv :
      Tendsto
        (fun n : ℕ => (Real.sqrt (((n + 1 : ℕ) : ℝ)))⁻¹)
        atTop (nhds 0) :=
    (tendsto_inv_atTop_zero :
      Tendsto (fun y : ℝ => y⁻¹) atTop (nhds 0)).comp hsqrt
  have hupper :
      Tendsto
        (fun n : ℕ => 2 / Real.sqrt (((n + 1 : ℕ) : ℝ)))
        atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds.mul hinv :
        Tendsto
          (fun n : ℕ =>
            (2 : ℝ) * (Real.sqrt (((n + 1 : ℕ) : ℝ)))⁻¹)
          atTop (nhds ((2 : ℝ) * 0)))
  have hlog :
      Tendsto
        (fun n : ℕ =>
          Real.log (((n + 1 : ℕ) : ℝ)) / ((n + 1 : ℕ) : ℝ))
        atTop (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
      hupper ?_ ?_
    · filter_upwards [eventually_ge_atTop (0 : ℕ)] with n hn
      have hone : (1 : ℝ) ≤ (((n + 1 : ℕ) : ℝ)) := by norm_num
      exact div_nonneg (Real.log_nonneg hone) (by positivity)
    · filter_upwards [eventually_ge_atTop (0 : ℕ)] with n hn
      let a : ℝ := (((n + 1 : ℕ) : ℝ))
      change Real.log a / a ≤ 2 / Real.sqrt a
      have ha_pos : 0 < a := by
        dsimp [a]
        positivity
      have hs_pos : 0 < Real.sqrt a := Real.sqrt_pos.2 ha_pos
      have hs_sq : (Real.sqrt a) ^ 2 = a :=
        Real.sq_sqrt (le_of_lt ha_pos)
      have hs_mul : Real.sqrt a * Real.sqrt a = a := by
        simpa [pow_two] using hs_sq
      have hlog_sqrt :
          Real.log (Real.sqrt a) ≤ Real.sqrt a - 1 :=
        Real.log_le_sub_one_of_pos hs_pos
      have hlog_eq :
          Real.log a =
            Real.log (Real.sqrt a) + Real.log (Real.sqrt a) := by
        calc
          Real.log a = Real.log (Real.sqrt a * Real.sqrt a) := by
            rw [hs_mul]
          _ = Real.log (Real.sqrt a) + Real.log (Real.sqrt a) :=
            Real.log_mul (ne_of_gt hs_pos) (ne_of_gt hs_pos)
      have hlog_bound : Real.log a ≤ 2 * Real.sqrt a := by
        rw [hlog_eq]
        nlinarith [hlog_sqrt]
      have hmul :
          Real.log a * Real.sqrt a ≤
            (2 * Real.sqrt a) * Real.sqrt a :=
        mul_le_mul_of_nonneg_right hlog_bound (Real.sqrt_nonneg a)
      apply (div_le_div_iff₀ ha_pos hs_pos).2
      nlinarith [hmul, hs_mul]
  have hexp := (Real.continuous_exp.tendsto 0).comp hlog
  convert hexp using 1
  · funext n
    rw [Real.rpow_def_of_pos (by positivity)]
    congr 1
    simp [div_eq_mul_inv]
  · norm_num

private theorem tendsto_natCast_atTop_atTop.not_tendsto_const_nhds
    (h : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop (nhds 0)) : False := by
  have hevent : ∀ᶠ n : ℕ in atTop, (n : ℝ) + 1 < 1 :=
    (tendsto_order.1 h).2 1 (by norm_num)
  rcases (eventually_atTop.1 hevent) with ⟨N, hN⟩
  exact
    (not_lt_of_ge (by norm_num : (1 : ℝ) ≤ (N : ℝ) + 1))
      (hN N le_rfl)

theorem gap1 (x : ℝ) (hx : x ≠ 0) :
    ∀ n : ℕ, 1 ≤ n → term x n = powerSeriesTerm (1 / x) n := by
  intro n hn
  unfold term powerSeriesTerm
  rw [one_div, inv_pow]
  field_simp

theorem gap2 :
    Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (1 / ((n + 1 : ℕ) : ℝ)))
      atTop (nhds 1) := by
  simpa using tendsto_natCast_add_one_pow_inv_atTop

theorem gap3 (x : ℝ) (hx : x ≠ 0) :
    |1 / x| < 1 ↔ 1 < |x| := by
  rw [abs_div, abs_one, one_div]
  exact inv_lt_one₀ (abs_pos.mpr hx)

theorem gap4 (x : ℝ) (hx : 1 < |x|) :
    Summable (fun n : ℕ => |term x (n + 1)|) := by
  have hx0 : x ≠ 0 := by
    intro h
    subst x
    norm_num at hx
  have hr : |1 / x| < 1 := (gap3 x hx0).2 hx
  have hyr : ‖(|1 / x| : ℝ)‖ < 1 := by
    simpa only [Real.norm_eq_abs, abs_abs] using hr
  have hs : Summable (fun n : ℕ => (n : ℝ) * |1 / x| ^ n) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hyr).summable
  have hinj : Function.Injective (fun n : ℕ => n + 1) := by
    intro a b h
    exact Nat.add_right_cancel h
  have hs' :
      Summable
        (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * |1 / x| ^ (n + 1)) :=
    hs.comp_injective hinj
  apply hs'.congr
  intro n
  rw [gap1 x hx0 (n + 1) (Nat.succ_le_succ (Nat.zero_le n))]
  simp only [powerSeriesTerm, abs_mul, abs_pow,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ))]

theorem gap5 (x : ℝ) (hx : |x| = 1) :
    ∀ n : ℕ, 1 ≤ n → |term x n| = n := by
  intro n hn
  unfold term
  rw [abs_div, abs_pow, hx, one_pow]
  simp

theorem gap6 (x : ℝ) (hx : |x| = 1) :
    ¬ Tendsto (fun n : ℕ => term x (n + 1)) atTop (nhds 0) := by
  intro ht
  have habs : Tendsto (fun n : ℕ => |term x (n + 1)|) atTop (nhds |(0 : ℝ)|) :=
    (continuous_abs.tendsto 0).comp ht
  have hform : (fun n : ℕ => |term x (n + 1)|) = fun n : ℕ => ((n + 1 : ℕ) : ℝ) := by
    funext n
    exact gap5 x hx (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
  rw [hform] at habs
  norm_num at habs
  exact tendsto_natCast_atTop_atTop.not_tendsto_const_nhds habs

theorem gap7 (x : ℝ) (hx : |x| = 1) :
    ¬ Summable (fun n : ℕ => term x (n + 1)) := by
  intro hs
  exact gap6 x hx (hs.tendsto_atTop_zero)

theorem gap8 (x : ℝ) (hx0 : x ≠ 0) (hx : |x| < 1) :
    ¬ Summable (fun n : ℕ => term x (n + 1)) := by
  intro hs
  have ht := hs.tendsto_atTop_zero
  have hbase : 1 < |1 / x| := by
    rw [abs_div, abs_one, one_div]
    exact (one_lt_inv₀ (abs_pos.mpr hx0)).2 hx
  have hterm :
      ∀ n : ℕ,
        term x (n + 1) = ((n + 1 : ℕ) : ℝ) * (1 / x) ^ (n + 1) := by
    intro n
    exact gap1 x hx0 (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
  have hlarge : ∀ n : ℕ, 1 ≤ |term x (n + 1)| := by
    intro n
    rw [hterm n, abs_mul, abs_pow,
      abs_of_nonneg (by positivity : 0 ≤ ((n + 1 : ℕ) : ℝ))]
    have hp : 1 ≤ |1 / x| ^ (n + 1) :=
      one_le_pow₀ (le_of_lt hbase)
    have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by norm_num
    simpa using
      (mul_le_mul hn hp (by norm_num : (0 : ℝ) ≤ 1)
        (by positivity : 0 ≤ ((n + 1 : ℕ) : ℝ)))
  have habs :
      Tendsto (fun n : ℕ => |term x (n + 1)|) atTop (nhds 0) := by
    simpa using (continuous_abs.tendsto (0 : ℝ)).comp ht
  have hevent : ∀ᶠ n : ℕ in atTop, |term x (n + 1)| < 1 :=
    (tendsto_order.1 habs).2 1 (by norm_num)
  rcases (eventually_atTop.1 hevent) with ⟨N, hN⟩
  exact (not_lt_of_ge (hlarge N)) (hN N le_rfl)

theorem gap9 :
    ¬ ∃ x : ℝ, x ≠ 0 ∧ ConditionallySummable x := by
  rintro ⟨x, hx0, hs, habs⟩
  by_cases hx : 1 < |x|
  · exact habs (gap4 x hx)
  · have hxle : |x| ≤ 1 := le_of_not_gt hx
    rcases lt_or_eq_of_le hxle with hxlt | hxeq
    · exact gap8 x hx0 hxlt hs
    · exact gap7 x hxeq hs

theorem gap10 (x : ℝ) (hx : x ≠ 0) :
    (1 < |x| → Summable (fun n : ℕ => |term x (n + 1)|)) ∧
    (|x| ≤ 1 → ¬ Summable (fun n : ℕ => term x (n + 1))) ∧
    ¬ ConditionallySummable x := by
  refine ⟨gap4 x, ?_, ?_⟩
  · intro hxle
    rcases lt_or_eq_of_le hxle with hxlt | hxeq
    · exact gap8 x hx hxlt
    · exact gap7 x hxeq
  · intro hc
    exact gap9 ⟨x, hx, hc⟩

end

end ProofGap.Exercise2716
