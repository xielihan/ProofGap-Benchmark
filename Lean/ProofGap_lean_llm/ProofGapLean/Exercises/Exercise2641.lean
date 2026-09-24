import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace ProofGap.Exercise2641

noncomputable section

open Filter

def term (a : ℝ) (n : ℕ) : ℝ :=
  Real.rpow n (Real.rpow n a) - 1

def powerModel (a : ℝ) (n : ℕ) : ℝ :=
  1 / Real.rpow n |a|

def converges (a : ℝ) : Prop :=
  Summable (fun n : ℕ => term a (n + 1))

private theorem tendsto_log_mul_rpow_zero (a : ℝ) (ha : a < 0) :
    Tendsto (fun x : ℝ => Real.log x * x ^ a) atTop (nhds 0) := by
  have h :=
    (isLittleO_log_rpow_atTop (neg_pos.mpr ha)).tendsto_div_nhds_zero
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  simpa only [Real.rpow_neg hx.le, div_inv_eq_mul]

private theorem tendsto_exp_sub_one_div :
    Tendsto (fun t : ℝ => (Real.exp t - 1) / t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  simpa [div_eq_mul_inv, mul_comm] using
    (Real.hasDerivAt_exp 0).tendsto_slope_zero_right

private theorem tendsto_term_div_log_mul_rpow (a : ℝ) (ha : a < 0) :
    Tendsto
      (fun x : ℝ => (x ^ (x ^ a) - 1) / (Real.log x * x ^ a))
      atTop (nhds 1) := by
  have hy0 := tendsto_log_mul_rpow_zero a ha
  have hypos : ∀ᶠ x : ℝ in atTop, 0 < Real.log x * x ^ a := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact mul_pos (Real.log_pos hx) (Real.rpow_pos_of_pos (zero_lt_one.trans hx) _)
  have hy :
      Tendsto (fun x : ℝ => Real.log x * x ^ a)
        atTop (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hy0, hypos⟩
  have h := tendsto_exp_sub_one_div.comp hy
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  simp only [Function.comp_apply]
  rw [Real.rpow_def_of_pos (zero_lt_one.trans hx) (x ^ a)]

private theorem term_nonneg_of_one_le (a : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    0 ≤ term a n := by
  have hbase : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hexp : 0 ≤ (n : ℝ) ^ a := (Real.rpow_pos_of_pos (zero_lt_one.trans_le hbase) a).le
  have hpow : (1 : ℝ) ≤ (n : ℝ) ^ ((n : ℝ) ^ a) :=
    Real.one_le_rpow hbase hexp
  simpa [term] using sub_nonneg.mpr hpow

theorem gap1 (a : ℝ) (ha : 0 ≤ a) :
    Tendsto (fun n : ℕ => term a (n + 1)) atTop atTop := by
  refine tendsto_atTop_mono' atTop ?_ tendsto_natCast_atTop_atTop
  filter_upwards with n
  have hbase : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hexp : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ a :=
    Real.one_le_rpow hbase ha
  have hp :
      ((n + 1 : ℕ) : ℝ) ^ (1 : ℝ) ≤
        ((n + 1 : ℕ) : ℝ) ^ (((n + 1 : ℕ) : ℝ) ^ a) :=
    Real.rpow_le_rpow_of_exponent_le hbase hexp
  rw [Real.rpow_one] at hp
  change (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ (((n + 1 : ℕ) : ℝ) ^ a) - 1
  calc
    (n : ℝ) = ((n + 1 : ℕ) : ℝ) - 1 := by norm_num
    _ ≤ ((n + 1 : ℕ) : ℝ) ^ (((n + 1 : ℕ) : ℝ) ^ a) - 1 :=
      sub_le_sub_right hp 1

theorem gap2 (a : ℝ) (ha : 0 ≤ a) :
    ¬ converges a := by
  intro hs
  have hzero :
      Tendsto (fun n : ℕ => term a (n + 1)) atTop (nhds 0) := by
    simpa only [Nat.cofinite_eq_atTop] using hs.tendsto_cofinite_zero
  exact not_tendsto_nhds_of_tendsto_atTop (gap1 a ha) 0 hzero

theorem gap3 (a : ℝ) (ha₀ : -1 ≤ a) (ha₁ : a < 0) :
    Tendsto
      (fun x : ℝ => (Real.rpow x (Real.rpow x a) - 1) /
        (1 / Real.rpow x |a|))
      atTop atTop := by
  have h :=
    (tendsto_term_div_log_mul_rpow a ha₁).pos_mul_atTop
      zero_lt_one Real.tendsto_log_atTop
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hlog : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  have hrpow : x ^ a ≠ 0 := (Real.rpow_pos_of_pos hx0 a).ne'
  rw [abs_of_neg ha₁]
  have hneg : Real.rpow x (-a) = (Real.rpow x a)⁻¹ := Real.rpow_neg hx0.le a
  rw [hneg]
  simp only [one_div, inv_inv]
  change
    (x ^ (x ^ a) - 1) / (Real.log x * x ^ a) * Real.log x =
      (x ^ (x ^ a) - 1) / x ^ a
  field_simp

theorem gap4 (a : ℝ) (ha₀ : -1 ≤ a) (ha₁ : a < 0) :
    ∃ K > 0, ∃ N : ℕ, ∀ n ≥ N,
      K * powerModel a n ≤ term a n := by
  have he : ∀ᶠ n : ℕ in atTop, 1 ≤ term a n / powerModel a n := by
    have hcomp := (gap3 a ha₀ ha₁).comp tendsto_natCast_atTop_atTop
    filter_upwards [hcomp.eventually_ge_atTop 1, eventually_ge_atTop 1]
      with n hn hnone
    simpa [term, powerModel] using hn
  rcases eventually_atTop.mp he with ⟨N, hN⟩
  refine ⟨1, zero_lt_one, N + 1, ?_⟩
  intro n hn
  have hNn : N ≤ n := by omega
  have hnpos : 0 < n := by omega
  have hp : 0 < powerModel a n := by
    unfold powerModel
    exact one_div_pos.mpr (Real.rpow_pos_of_pos (by exact_mod_cast hnpos) _)
  exact (le_div_iff₀ hp).mp (hN n hNn)

theorem gap5 (a : ℝ) (ha₀ : -1 ≤ a) (ha₁ : a < 0) :
    ¬ Summable (fun n : ℕ => powerModel a (n + 1)) := by
  intro hs
  have hs' :
      Summable (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ) ^ |a|)) := by
    simpa [powerModel] using hs
  have hfull : Summable (fun n : ℕ => 1 / ((n : ℝ) ^ |a|)) :=
    (summable_nat_add_iff 1).mp hs'
  have hp : 1 < |a| := Real.summable_one_div_nat_rpow.mp hfull
  rw [abs_of_neg ha₁] at hp
  linarith

theorem gap6 (a : ℝ) (ha₀ : -1 ≤ a) (ha₁ : a < 0) :
    ¬ converges a := by
  intro hs
  rcases gap4 a ha₀ ha₁ with ⟨K, hK, N, hbound⟩
  have hscaled : Summable (fun n : ℕ => term a (n + 1) / K) :=
    hs.div_const K
  have hpowers : Summable (fun n : ℕ => powerModel a (n + 1)) :=
    hscaled.of_norm_bounded_eventually_nat (by
      filter_upwards [eventually_ge_atTop N] with n hn
      have hcomp := hbound (n + 1) (by omega)
      have hpnonneg : 0 ≤ powerModel a (n + 1) := by
        unfold powerModel
        exact (one_div_pos.mpr
          (Real.rpow_pos_of_pos (by exact_mod_cast Nat.succ_pos n) _)).le
      rw [Real.norm_eq_abs, abs_of_nonneg hpnonneg]
      exact (le_div_iff₀ hK).mpr (by simpa [mul_comm] using hcomp))
  exact gap5 a ha₀ ha₁ hpowers

theorem gap7 (a β : ℝ) (ha : a < -1) (hab : a < β) (hβ : β < -1) :
    |β| < |a| := by
  rw [abs_of_neg (hβ.trans (by norm_num)), abs_of_neg (ha.trans (by norm_num))]
  linarith

theorem gap8 (a β : ℝ) (ha : a < -1) (hab : a < β) (hβ : β < -1) :
    1 < |β| := by
  rw [abs_of_neg (hβ.trans (by norm_num))]
  linarith

theorem gap9 (a : ℝ) (ha : a < -1) :
    1 < |a| := by
  rw [abs_of_neg (ha.trans (by norm_num))]
  linarith

theorem gap10 (a β : ℝ) (ha : a < -1) (hab : a < β) (hβ : β < -1) :
    Tendsto
      (fun x : ℝ => (Real.rpow x (Real.rpow x a) - 1) /
        (1 / Real.rpow x |β|))
      atTop (nhds 0) := by
  have ha0 : a < 0 := ha.trans (by norm_num)
  have hβ0 : β < 0 := hβ.trans (by norm_num)
  have hsmall :
      Tendsto (fun x : ℝ => Real.log x / x ^ (β - a)) atTop (nhds 0) :=
    (isLittleO_log_rpow_atTop (sub_pos.mpr hab)).tendsto_div_nhds_zero
  have h := (tendsto_term_div_log_mul_rpow a ha0).mul hsmall
  simp only [one_mul] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hlog : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  have hra : x ^ a ≠ 0 := (Real.rpow_pos_of_pos hx0 a).ne'
  have hrβ : x ^ β ≠ 0 := (Real.rpow_pos_of_pos hx0 β).ne'
  rw [abs_of_neg hβ0]
  have hneg : Real.rpow x (-β) = (Real.rpow x β)⁻¹ := Real.rpow_neg hx0.le β
  rw [hneg]
  simp only [one_div, inv_inv]
  change
    (x ^ (x ^ a) - 1) / (Real.log x * x ^ a) *
        (Real.log x / x ^ (β - a)) =
      (x ^ (x ^ a) - 1) / x ^ β
  have hsub : x ^ (β - a) = x ^ β / x ^ a := Real.rpow_sub hx0 β a
  rw [hsub]
  field_simp

theorem gap11 (β : ℝ) (hβ : β < -1) :
    Summable (fun n : ℕ => powerModel β (n + 1)) := by
  have hfull : Summable (fun n : ℕ => 1 / ((n : ℝ) ^ |β|)) :=
    Real.summable_one_div_nat_rpow.mpr (gap9 β hβ)
  have hshift :
      Summable (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ) ^ |β|)) :=
    (summable_nat_add_iff 1).mpr hfull
  simpa [powerModel] using hshift

theorem gap12 (a : ℝ) (ha : a < -1) :
    converges a := by
  let β : ℝ := (a - 1) / 2
  have hab : a < β := by dsimp [β]; linarith
  have hβ : β < -1 := by dsimp [β]; linarith
  have hlim := (gap10 a β ha hab hβ).comp
    (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hupper :
      ∀ᶠ n : ℕ in atTop,
        (Real.rpow (((n + 1 : ℕ) : ℝ))
            (Real.rpow (((n + 1 : ℕ) : ℝ)) a) - 1) /
            (1 / Real.rpow (((n + 1 : ℕ) : ℝ)) |β|) < 1 :=
    (tendsto_order.mp hlim).2 1 zero_lt_one
  have hmodel := gap11 β hβ
  unfold converges
  refine hmodel.of_norm_bounded_eventually_nat ?_
  filter_upwards [hupper] with n hn
  have hp : 0 < powerModel β (n + 1) := by
    unfold powerModel
    exact one_div_pos.mpr
      (Real.rpow_pos_of_pos (by exact_mod_cast Nat.succ_pos n) _)
  have hratio : term a (n + 1) / powerModel β (n + 1) < 1 := by
    simpa [term, powerModel] using hn
  have hle : term a (n + 1) ≤ powerModel β (n + 1) := by
    have := (div_lt_iff₀ hp).mp hratio
    linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (term_nonneg_of_one_le a (n + 1) (by omega))]
  exact hle

theorem gap13 (a : ℝ) :
    a ∈ {r : ℝ | r < -1} ↔ converges a := by
  change a < -1 ↔ converges a
  constructor
  · exact gap12 a
  · intro hs
    by_contra hnot
    have hge : -1 ≤ a := le_of_not_gt hnot
    by_cases ha0 : 0 ≤ a
    · exact gap2 a ha0 hs
    · exact gap6 a hge (lt_of_not_ge ha0) hs

end

end ProofGap.Exercise2641
