import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.PSeries

namespace ProofGap.Exercise2612

noncomputable section

open Filter

def approximant (n : ℕ) : ℝ :=
  (1 + 1 / (n : ℝ)) ^ n

def base (n : ℕ) : ℝ :=
  Real.exp 1 - approximant n

def term (p : ℝ) (n : ℕ) : ℝ :=
  Real.rpow (base n) p

def logRemainder (n : ℕ) : ℝ :=
  Real.log (1 + 1 / (n : ℝ)) -
    (1 / (n : ℝ) - 1 / (2 * (n : ℝ) ^ 2))

def scaledRemainder (n : ℕ) : ℝ :=
  (n : ℝ) * logRemainder n

def asymptoticModel (p : ℝ) (n : ℕ) : ℝ :=
  Real.rpow (Real.exp 1 / 2) p * Real.rpow n (-p)

def comparison (p : ℝ) (n : ℕ) : ℝ :=
  Real.rpow n (-p)

private def exponentError (n : ℕ) : ℝ :=
  -1 / (2 * (n : ℝ)) + scaledRemainder n

private def baseModel (n : ℕ) : ℝ :=
  Real.exp 1 / (2 * (n : ℝ))

def converges (p : ℝ) : Prop :=
  Summable (fun n : ℕ => term p (n + 1))

theorem gap1 (n : ℕ) (hn : 1 ≤ n) :
    approximant n = Real.exp ((n : ℝ) * Real.log (1 + 1 / (n : ℝ))) := by
  have hbase : 0 < (1 + 1 / (n : ℝ)) := by positivity
  unfold approximant
  rw [← Real.rpow_natCast]
  rw [Real.rpow_def_of_pos hbase]
  congr 1
  ring

theorem gap2 :
    Asymptotics.IsBigO atTop
      (fun n : ℕ => logRemainder (n + 1))
      (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ 3) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨2, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hmnat : 2 ≤ n + 1 := by omega
  have hmpos : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have hm : (2 : ℝ) ≤ (n + 1 : ℕ) := by exact_mod_cast hmnat
  let x : ℝ := -1 / (n + 1 : ℕ)
  have hxabs : |x| < 1 := by
    dsimp [x]
    rw [abs_div, abs_neg, abs_one, abs_of_pos hmpos]
    exact (div_lt_one hmpos).2 (by exact_mod_cast (show 1 < n + 1 by omega))
  have hbound := Real.abs_log_sub_add_sum_range_le hxabs 2
  have hxnorm : |x| = 1 / (n + 1 : ℕ) := by
    dsimp [x]
    rw [abs_div, abs_neg, abs_one, abs_of_pos hmpos]
  have hleft :
      (∑ i ∈ Finset.range 2, x ^ (i + 1) / (i + 1)) + Real.log (1 - x) =
        logRemainder (n + 1) := by
    dsimp [x]
    unfold logRemainder
    norm_num [Finset.sum_range_succ]
    field_simp [hmpos.ne']
    ring
  rw [hleft, hxnorm] at hbound
  have hhalf : (1 : ℝ) / (n + 1 : ℕ) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hmpos (by norm_num : (0 : ℝ) < 2)]
    nlinarith
  have hden : 0 < (1 : ℝ) - 1 / (n + 1 : ℕ) := by linarith
  have hdeninv : ((1 : ℝ) - 1 / (n + 1 : ℕ))⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ hden (by norm_num : (0 : ℝ) < 2)]
    nlinarith
  have ht : 0 ≤ ((1 : ℝ) / (n + 1 : ℕ)) ^ 3 := by positivity
  have hpow : ((1 : ℝ) / (n + 1 : ℕ)) ^ 3 =
      1 / (((n + 1 : ℕ) : ℝ) ^ 3) := by
    field_simp [hmpos.ne']
  calc
    ‖logRemainder (n + 1)‖ = |logRemainder (n + 1)| := Real.norm_eq_abs _
    _ ≤ ((1 : ℝ) / (n + 1 : ℕ)) ^ 3 /
        (1 - 1 / (n + 1 : ℕ)) := hbound
    _ ≤ ((1 : ℝ) / (n + 1 : ℕ)) ^ 3 * 2 := by
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left hdeninv ht
    _ = 2 * ‖1 / (((n + 1 : ℕ) : ℝ) ^ 3)‖ := by
      rw [hpow, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      ring

theorem gap3 :
    Asymptotics.IsBigO atTop
      (fun n : ℕ => scaledRemainder (n + 1))
      (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ 2) := by
  have hmul := (Asymptotics.isBigO_refl
    (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop).mul gap2
  apply hmul.congr
  · intro n
    rfl
  · intro n
    have hm : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    field_simp [hm]

theorem gap4 (n : ℕ) (hn : 1 ≤ n) :
    approximant n =
      Real.exp (1 - 1 / (2 * (n : ℝ)) + scaledRemainder n) := by
  rw [gap1 n hn]
  congr 1
  unfold scaledRemainder logRemainder
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  field_simp [hn0]
  ring

theorem gap5 (p : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    0 < term p n := by
  unfold term
  apply Real.rpow_pos_of_pos
  unfold base
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hargpos : 0 < (1 + 1 / (n : ℝ)) := by positivity
  have hargne : (1 + 1 / (n : ℝ)) ≠ 1 := by
    have : 0 < (1 : ℝ) / n := by positivity
    linarith
  have hloglt := Real.log_lt_sub_one_of_pos hargpos hargne
  have hexponent :
      (n : ℝ) * Real.log (1 + 1 / (n : ℝ)) < 1 := by
    calc
      (n : ℝ) * Real.log (1 + 1 / (n : ℝ)) <
          (n : ℝ) * ((1 + 1 / (n : ℝ)) - 1) :=
        mul_lt_mul_of_pos_left hloglt hnpos
      _ = 1 := by field_simp [hnpos.ne']; ring
  rw [gap1 n hn]
  exact sub_pos.mpr ((Real.exp_lt_exp).2 hexponent)

theorem gap6 (p : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    term p n =
      Real.rpow
        (Real.exp 1 *
          (1 - Real.exp (-1 / (2 * (n : ℝ)) + scaledRemainder n))) p := by
  unfold term base
  congr 1
  rw [gap4 n hn]
  rw [show 1 - 1 / (2 * (n : ℝ)) + scaledRemainder n =
      1 + (-1 / (2 * (n : ℝ)) + scaledRemainder n) by ring,
    Real.exp_add]
  ring

private theorem inv_succ_tendsto :
    Tendsto (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ)) atTop (nhds 0) := by
  have hcast : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop := by
    simpa [Nat.cast_add, Nat.cast_one] using
      tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  simpa [one_div] using tendsto_inv_atTop_zero.comp hcast

private theorem inv_succ_sq_tendsto :
    Tendsto (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ) ^ 2)) atTop (nhds 0) := by
  have h := inv_succ_tendsto.pow 2
  have h' : Tendsto (fun n : ℕ => (1 / (((n + 1 : ℕ) : ℝ))) ^ 2)
      atTop (nhds 0) := by simpa using h
  apply h'.congr'
  filter_upwards [] with n
  have hm : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  field_simp [hm]

private theorem one_sub_exp_div_neg_tendsto :
    Tendsto (fun x : ℝ => (1 - Real.exp x) / (-x))
      (nhdsWithin 0 (Set.compl {0})) (nhds 1) := by
  have h := (Real.hasDerivAt_exp 0).tendsto_slope_zero
  convert h using 1
  · funext t
    simp only [zero_add, Real.exp_zero, smul_eq_mul, div_eq_mul_inv, inv_neg]
    ring
  · norm_num

private theorem base_isEquivalent_baseModel :
    Asymptotics.IsEquivalent atTop
      (fun n : ℕ => base (n + 1))
      (fun n : ℕ => baseModel (n + 1)) := by
  have hscaled0 : Tendsto (fun n : ℕ => scaledRemainder (n + 1))
      atTop (nhds 0) := gap3.trans_tendsto inv_succ_sq_tendsto
  have hmulO := (Asymptotics.isBigO_refl
    (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop).mul gap3
  have htarget : Tendsto (fun n : ℕ =>
      ((n + 1 : ℕ) : ℝ) * (1 / (((n + 1 : ℕ) : ℝ) ^ 2)))
      atTop (nhds 0) := by
    apply inv_succ_tendsto.congr'
    filter_upwards [] with n
    have hm : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    field_simp [hm]
  have hscaledMul : Tendsto (fun n : ℕ =>
      ((n + 1 : ℕ) : ℝ) * scaledRemainder (n + 1))
      atTop (nhds 0) := hmulO.trans_tendsto htarget
  have hfirst : Tendsto (fun n : ℕ =>
      -1 / (2 * (((n + 1 : ℕ) : ℝ)))) atTop (nhds 0) := by
    have h := Filter.Tendsto.const_mul (-1 / 2 : ℝ) inv_succ_tendsto
    have h' : Tendsto (fun n : ℕ =>
        (-1 / 2 : ℝ) * (1 / (((n + 1 : ℕ) : ℝ)))) atTop (nhds 0) := by
      simpa using h
    apply h'.congr'
    filter_upwards [] with n
    have hm : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    field_simp [hm]
  have hz0 : Tendsto (fun n : ℕ => exponentError (n + 1))
      atTop (nhds 0) := by
    simpa [exponentError] using hfirst.add hscaled0
  have hfactor : Tendsto (fun n : ℕ =>
      (-exponentError (n + 1)) * (2 * (((n + 1 : ℕ) : ℝ))))
      atTop (nhds 1) := by
    have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    have h := hconst.sub (Filter.Tendsto.const_mul (2 : ℝ) hscaledMul)
    have h' : Tendsto (fun n : ℕ =>
        1 - 2 * ((((n + 1 : ℕ) : ℝ)) * scaledRemainder (n + 1)))
        atTop (nhds 1) := by simpa using h
    apply h'.congr'
    filter_upwards [] with n
    have hm : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    unfold exponentError
    field_simp [hm]
    ring
  have hzne : ∀ᶠ n : ℕ in atTop, exponentError (n + 1) ≠ 0 := by
    filter_upwards [hfactor.eventually_ne one_ne_zero] with n hn
    intro hz
    apply hn
    rw [hz]
    norm_num
  have hz : Tendsto (fun n : ℕ => exponentError (n + 1))
      atTop (nhdsWithin 0 (Set.compl {0})) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hz0, by simpa using hzne⟩
  have hslope := one_sub_exp_div_neg_tendsto.comp hz
  have hprod := hslope.mul hfactor
  apply Asymptotics.isEquivalent_of_tendsto_one
  have hprod' : Tendsto (fun n : ℕ =>
      ((1 - Real.exp (exponentError (n + 1))) / (-exponentError (n + 1))) *
        ((-exponentError (n + 1)) * (2 * (((n + 1 : ℕ) : ℝ)))))
      atTop (nhds 1) := by
    simpa [Function.comp_def] using hprod
  apply hprod'.congr'
  filter_upwards [hzne] with n hzn
  simp only [Function.comp_apply, Pi.div_apply]
  unfold base baseModel
  rw [gap4 (n + 1) (by omega)]
  rw [show 1 - 1 / (2 * (((n + 1 : ℕ) : ℝ))) + scaledRemainder (n + 1) =
      1 + exponentError (n + 1) by unfold exponentError; ring,
    Real.exp_add]
  have hm : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  field_simp [hzn, hm, Real.exp_ne_zero]

theorem gap7 (p : ℝ) :
    Asymptotics.IsEquivalent atTop
      (fun n : ℕ => term p (n + 1))
      (fun n : ℕ => asymptoticModel p (n + 1)) := by
  have hrpow : Asymptotics.IsEquivalent atTop
      (fun n : ℕ => Real.rpow (base (n + 1)) p)
      (fun n : ℕ => Real.rpow (baseModel (n + 1)) p) :=
    Asymptotics.IsEquivalent.rpow
      (fun n => (show 0 ≤ baseModel (n + 1) by unfold baseModel; positivity))
      base_isEquivalent_baseModel
  apply (hrpow.congr_left (Filter.Eventually.of_forall fun n => by
    rfl)).congr_right
  filter_upwards [] with n
  unfold baseModel asymptoticModel
  have hmpos : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  rw [show Real.exp 1 / (2 * (((n + 1 : ℕ) : ℝ))) =
      (Real.exp 1 / 2) / (((n + 1 : ℕ) : ℝ)) by ring]
  have hdiv := Real.div_rpow
    (show (0 : ℝ) ≤ Real.exp 1 / 2 by positivity) hmpos.le p
  change Real.rpow ((Real.exp 1 / 2) / (((n + 1 : ℕ) : ℝ))) p =
    Real.rpow (Real.exp 1 / 2) p * Real.rpow (n + 1 : ℕ) (-p)
  rw [show Real.rpow ((Real.exp 1 / 2) / (((n + 1 : ℕ) : ℝ))) p =
      Real.rpow (Real.exp 1 / 2) p /
        Real.rpow (((n + 1 : ℕ) : ℝ)) p by
        change ((Real.exp 1 / 2) / (((n + 1 : ℕ) : ℝ))) ^ p =
          (Real.exp 1 / 2) ^ p / (((n + 1 : ℕ) : ℝ)) ^ p
        exact hdiv]
  have hneg : Real.rpow (((n + 1 : ℕ) : ℝ)) (-p) =
      (Real.rpow (((n + 1 : ℕ) : ℝ)) p)⁻¹ := by
    change (((n + 1 : ℕ) : ℝ)) ^ (-p) =
      ((((n + 1 : ℕ) : ℝ)) ^ p)⁻¹
    exact Real.rpow_neg hmpos.le p
  rw [hneg]
  simp only [div_eq_mul_inv]

theorem gap8 (p : ℝ) :
    Asymptotics.IsBigO atTop
      (fun n : ℕ => asymptoticModel p (n + 1))
      (fun n : ℕ => comparison p (n + 1)) := by
  unfold asymptoticModel comparison
  exact Asymptotics.isBigO_const_mul_self
    (Real.rpow (Real.exp 1 / 2) p)
    (fun n : ℕ => Real.rpow (n + 1 : ℕ) (-p)) atTop

theorem gap9 (p : ℝ) (hp : 1 < p) :
    converges p := by
  have hall : Summable (fun n : ℕ => comparison p n) := by
    unfold comparison
    exact Real.summable_nat_rpow.mpr (by linarith)
  have hshift : Summable (fun n : ℕ => comparison p (n + 1)) :=
    (summable_nat_add_iff 1).mpr hall
  unfold converges
  exact summable_of_isBigO_nat hshift
    ((gap7 p).isBigO.trans (gap8 p))

theorem gap10 (p : ℝ) :
    converges p ↔ 1 < p := by
  constructor
  · intro hterm
    have hC : Real.rpow (Real.exp 1 / 2) p ≠ 0 :=
      (Real.rpow_pos_of_pos (by positivity) p).ne'
    have hcomparisonModel : Asymptotics.IsBigO atTop
        (fun n : ℕ => comparison p (n + 1))
        (fun n : ℕ => asymptoticModel p (n + 1)) := by
      unfold comparison asymptoticModel
      exact Asymptotics.isBigO_self_const_mul hC
        (fun n : ℕ => Real.rpow (n + 1 : ℕ) (-p)) atTop
    have hcomparisonTerm :=
      hcomparisonModel.trans (gap7 p).isBigO_symm
    have hshift : Summable (fun n : ℕ => comparison p (n + 1)) := by
      exact summable_of_isBigO_nat hterm hcomparisonTerm
    have hall : Summable (fun n : ℕ => comparison p n) :=
      (summable_nat_add_iff 1).mp hshift
    simpa [comparison] using hall
  · exact gap9 p

end

end ProofGap.Exercise2612
