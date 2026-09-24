import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

namespace ProofGap.Exercise2620

noncomputable section

open Filter Set
open scoped Interval

def integrand (p q x : ℝ) : ℝ :=
  1 / (x * Real.rpow (Real.log x) p *
    Real.rpow (Real.log (Real.log x)) q)

def transformed (p q t : ℝ) : ℝ :=
  1 / (Real.rpow t p * Real.rpow (Real.log t) q)

def criticalPrimitive (q x : ℝ) : ℝ :=
  if q = 1 then Real.log (Real.log (Real.log x))
  else Real.rpow (Real.log (Real.log x)) (1 - q) / (1 - q)

def converges (p q : ℝ) : Prop :=
  Summable (fun n : ℕ => integrand p q (n + 3))

private def basicLogTerm (q x : ℝ) : ℝ :=
  1 / (x * Real.rpow (Real.log x) q)

private def basicLogExponent (q t : ℝ) : ℝ :=
  -t - q * Real.log t

private theorem basicLogTerm_pos (q x : ℝ) (hx : 2 ≤ x) :
    0 < basicLogTerm q x := by
  unfold basicLogTerm
  have hxpos : 0 < x := by linarith
  have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
  exact one_div_pos.mpr (mul_pos hxpos (Real.rpow_pos_of_pos hlogpos _))

private theorem basicLog_eq_exp (q x : ℝ) (hx : 1 < x) :
    basicLogTerm q x = Real.exp (basicLogExponent q (Real.log x)) := by
  have hxpos : 0 < x := by linarith
  have hlogpos : 0 < Real.log x := Real.log_pos hx
  have hrpow : Real.rpow (Real.log x) q =
      Real.exp (Real.log (Real.log x) * q) := by
    change (Real.log x) ^ q = Real.exp (Real.log (Real.log x) * q)
    exact Real.rpow_def_of_pos hlogpos _
  unfold basicLogTerm basicLogExponent
  rw [hrpow]
  have hxinv : x⁻¹ = Real.exp (-Real.log x) := by
    rw [Real.exp_neg, Real.exp_log hxpos]
  simp only [one_div, mul_inv]
  rw [hxinv, ← Real.exp_neg, ← Real.exp_add]
  congr 1
  ring

private theorem basicLog_eventually_antitone (q : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      basicLogTerm q (((n + 1 : ℕ) : ℝ)) ≤ basicLogTerm q (n : ℝ) := by
  let B : ℝ := max 1 (-q)
  let A : ℝ := Real.exp B
  have hB1 : 1 ≤ B := le_max_left _ _
  have hA2 : 2 ≤ A := (le_of_lt Real.exp_one_gt_two).trans
    (Real.exp_le_exp.mpr hB1)
  have hE : AntitoneOn (basicLogExponent q) (Ici B) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos
      (f' := fun t => -1 - q * (1 / t)) (convex_Ici B)
    · intro t ht
      have htpos : 0 < t := lt_of_lt_of_le zero_lt_one
        (hB1.trans (Set.mem_Ici.mp ht))
      exact (continuousAt_id.neg.sub
        (continuousAt_const.mul
          (Real.continuousAt_log htpos.ne'))).continuousWithinAt
    · intro t ht
      have htB : B < t := by simpa [interior_Ici] using ht
      have htpos : 0 < t := lt_of_lt_of_le zero_lt_one (hB1.trans htB.le)
      unfold basicLogExponent
      convert ((hasDerivAt_id t).neg.sub
        ((Real.hasDerivAt_log htpos.ne').const_mul q)).hasDerivWithinAt using 1 <;>
        ring
    · intro t ht
      have htB : B < t := by simpa [interior_Ici] using ht
      have htpos : 0 < t := lt_of_lt_of_le zero_lt_one (hB1.trans htB.le)
      have htq : 0 ≤ t + q := by
        have : -q ≤ t := (le_max_right 1 (-q)).trans htB.le
        linarith
      have hfrac : 0 ≤ 1 + q / t := by
        have heq : 1 + q / t = (t + q) / t := by
          field_simp [htpos.ne']
        rw [heq]
        exact div_nonneg htq htpos.le
      rw [show -1 - q * (1 / t) = -(1 + q / t) by ring]
      exact neg_nonpos.mpr hfrac
  have hanti : AntitoneOn (basicLogTerm q) (Ici A) := by
    intro x hx y hy hxy
    have hAx : A ≤ x := Set.mem_Ici.mp hx
    have hAy : A ≤ y := Set.mem_Ici.mp hy
    have hxpos : 0 < x := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2)
      (hA2.trans hAx)
    have hypos : 0 < y := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2)
      (hA2.trans hAy)
    have hlogxB : B ≤ Real.log x := (Real.le_log_iff_exp_le hxpos).2 hAx
    have hlogyB : B ≤ Real.log y := (Real.le_log_iff_exp_le hypos).2 hAy
    have hlogxy : Real.log x ≤ Real.log y :=
      Real.strictMonoOn_log.monotoneOn (Set.mem_Ioi.mpr hxpos)
        (Set.mem_Ioi.mpr hypos) hxy
    have hx1 : 1 < x := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2)
      (hA2.trans hAx)
    have hy1 : 1 < y := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2)
      (hA2.trans hAy)
    rw [basicLog_eq_exp q x hx1, basicLog_eq_exp q y hy1]
    exact Real.exp_le_exp.mpr (hE hlogxB hlogyB hlogxy)
  filter_upwards [eventually_ge_atTop ⌈A⌉₊] with n hn
  have hAn : A ≤ (n : ℝ) := (Nat.le_ceil A).trans (Nat.cast_le.mpr hn)
  have hAn1 : A ≤ ((n + 1 : ℕ) : ℝ) :=
    hAn.trans (by exact_mod_cast Nat.le_succ n)
  exact hanti (Set.mem_Ici.mpr hAn) (Set.mem_Ici.mpr hAn1)
    (by exact_mod_cast Nat.le_succ n)

private theorem basicLog_condensed_eq (q : ℝ) (k : ℕ) :
    (2 : ℝ) ^ k * basicLogTerm q (((2 ^ k : ℕ) : ℝ)) =
      Real.rpow (Real.log 2) (-q) * Real.rpow k (-q) := by
  by_cases hk : k = 0
  · subst k
    simp only [pow_zero, basicLogTerm]
    norm_num only [Nat.cast_one, Real.log_one, one_mul]
    by_cases hq : q = 0
    · subst q
      norm_num
    · have hz : Real.rpow 0 q = 0 := by
        change (0 : ℝ) ^ q = 0
        exact Real.zero_rpow hq
      have hzn : Real.rpow 0 (-q) = 0 := by
        change (0 : ℝ) ^ (-q) = 0
        exact Real.zero_rpow (neg_ne_zero.mpr hq)
      rw [hz]
      norm_num only [Nat.cast_zero]
      rw [hzn]
      norm_num
  · have hkpos : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
    have htwoPowPos : (0 : ℝ) < (2 : ℝ) ^ k := pow_pos (by norm_num) _
    have hlog2pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    have hbasepos : 0 < (k : ℝ) * Real.log 2 := mul_pos hkpos hlog2pos
    have hrq : Real.rpow ((k : ℝ) * Real.log 2) q ≠ 0 :=
      (Real.rpow_pos_of_pos hbasepos q).ne'
    unfold basicLogTerm
    push_cast
    rw [Real.log_pow]
    calc
      (2 : ℝ) ^ k *
          (1 / ((2 : ℝ) ^ k * Real.rpow ((k : ℝ) * Real.log 2) q)) =
          1 / Real.rpow ((k : ℝ) * Real.log 2) q := by
        field_simp [htwoPowPos.ne', hrq]
      _ = Real.rpow ((k : ℝ) * Real.log 2) (-q) := by
        have hneg : Real.rpow ((k : ℝ) * Real.log 2) (-q) =
            (Real.rpow ((k : ℝ) * Real.log 2) q)⁻¹ := by
          change (((k : ℝ) * Real.log 2) ^ (-q)) =
            ((((k : ℝ) * Real.log 2) ^ q))⁻¹
          exact Real.rpow_neg hbasepos.le q
        rw [hneg]
        simp only [one_div]
      _ = Real.rpow k (-q) * Real.rpow (Real.log 2) (-q) := by
        change (((k : ℝ) * Real.log 2) ^ (-q)) =
          (k : ℝ) ^ (-q) * (Real.log 2) ^ (-q)
        exact Real.mul_rpow hkpos.le hlog2pos.le
      _ = Real.rpow (Real.log 2) (-q) * Real.rpow k (-q) := by ring

private theorem basicLog_summable_iff (q : ℝ) :
    Summable (fun n : ℕ => basicLogTerm q (n : ℝ)) ↔ 1 < q := by
  have hnonneg : 0 ≤ᶠ[atTop] (fun n : ℕ => basicLogTerm q n) := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    exact (basicLogTerm_pos q n (by exact_mod_cast hn)).le
  have hcondiff := summable_condensed_iff_of_eventually_nonneg
    hnonneg (basicLog_eventually_antitone q)
  have hC : Real.rpow (Real.log 2) (-q) ≠ 0 :=
    (Real.rpow_pos_of_pos (Real.log_pos (by norm_num)) _).ne'
  constructor
  · intro hall
    have hcondensed : Summable (fun k : ℕ =>
        (2 : ℝ) ^ k * basicLogTerm q (((2 ^ k : ℕ) : ℝ))) := hcondiff.mpr hall
    have hc : Summable (fun k : ℕ =>
        Real.rpow (Real.log 2) (-q) * Real.rpow k (-q)) :=
      hcondensed.congr (fun k => basicLog_condensed_eq q k)
    have hrpow : Summable (fun k : ℕ => Real.rpow k (-q)) :=
      (summable_mul_left_iff hC).mp hc
    have hexponent := Real.summable_nat_rpow.mp hrpow
    linarith
  · intro hq
    have hrpow : Summable (fun k : ℕ => Real.rpow k (-q)) :=
      Real.summable_nat_rpow.mpr (by linarith)
    have hc : Summable (fun k : ℕ =>
        Real.rpow (Real.log 2) (-q) * Real.rpow k (-q)) := hrpow.mul_left _
    have hcondensed : Summable (fun k : ℕ =>
        (2 : ℝ) ^ k * basicLogTerm q (((2 ^ k : ℕ) : ℝ))) :=
      hc.congr (fun k => (basicLog_condensed_eq q k).symm)
    exact hcondiff.mp hcondensed

private def shiftedBasicLogTerm (q : ℝ) (k : ℕ) : ℝ :=
  1 / ((k : ℝ) * Real.rpow (Real.log ((k : ℝ) * Real.log 2)) q)

private theorem critical_condensed_eq (q : ℝ) (k : ℕ) :
    (2 : ℝ) ^ k * integrand 1 q (((2 ^ k : ℕ) : ℝ)) =
      (1 / Real.log 2) * shiftedBasicLogTerm q k := by
  by_cases hk : k = 0
  · subst k
    simp [integrand, shiftedBasicLogTerm]
  · have hkpos : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
    have htwoPowPos : (0 : ℝ) < (2 : ℝ) ^ k := pow_pos (by norm_num) _
    have hlog2pos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    have hbasepos : 0 < (k : ℝ) * Real.log 2 := mul_pos hkpos hlog2pos
    have houter : Real.rpow ((k : ℝ) * Real.log 2) 1 =
        (k : ℝ) * Real.log 2 := by
      change (((k : ℝ) * Real.log 2) ^ (1 : ℝ)) = (k : ℝ) * Real.log 2
      exact Real.rpow_one _
    unfold integrand shiftedBasicLogTerm
    push_cast
    rw [Real.log_pow, houter]
    field_simp [htwoPowPos.ne', hkpos.ne', hlog2pos.ne']

private theorem shiftedBasic_isEquivalent_basic (q : ℝ) :
    Asymptotics.IsEquivalent atTop
      (fun k : ℕ => shiftedBasicLogTerm q k)
      (fun k : ℕ => basicLogTerm q (k : ℝ)) := by
  let c : ℝ := Real.log 2
  have hcpos : 0 < c := Real.log_pos (by norm_num)
  have hlog : Tendsto (fun k : ℕ => Real.log (k : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hkc : Tendsto (fun k : ℕ => (k : ℝ) * c) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const hcpos
  have hsmall : Tendsto (fun k : ℕ => Real.log c / Real.log (k : ℝ))
      atTop (nhds 0) := tendsto_const_nhds.div_atTop hlog
  have hden : Tendsto (fun k : ℕ =>
      1 + Real.log c / Real.log (k : ℝ)) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add hsmall
  have hone : Tendsto (fun k : ℕ =>
      1 / (1 + Real.log c / Real.log (k : ℝ))) atTop (nhds 1) := by
    have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    have hh := hconst.div hden (by norm_num : (1 : ℝ) ≠ 0)
    convert hh using 1
    · norm_num
  have hbase : Tendsto (fun k : ℕ =>
      Real.log (k : ℝ) / Real.log ((k : ℝ) * c)) atTop (nhds 1) := by
    apply hone.congr'
    filter_upwards [hlog.eventually (eventually_ge_atTop 1),
      hkc.eventually (eventually_ge_atTop 2)] with k hklog hkc2
    have hkpos : (0 : ℝ) < k := by
      by_contra hk
      have : (k : ℝ) = 0 := le_antisymm (not_lt.mp hk) (Nat.cast_nonneg k)
      rw [this, Real.log_zero] at hklog
      norm_num at hklog
    have hlogk : Real.log (k : ℝ) ≠ 0 := by linarith
    have hcne : c ≠ 0 := hcpos.ne'
    rw [Real.log_mul hkpos.ne' hcne]
    field_simp [hlogk]
  have hrpow : Tendsto (fun k : ℕ => Real.rpow
      (Real.log (k : ℝ) / Real.log ((k : ℝ) * c)) q) atTop (nhds 1) := by
    simpa using hbase.rpow_const (Or.inl (by norm_num : (1 : ℝ) ≠ 0))
  apply Asymptotics.isEquivalent_of_tendsto_one
  apply hrpow.congr'
  filter_upwards [hlog.eventually (eventually_ge_atTop 1),
    hkc.eventually (eventually_ge_atTop 2)] with k hklog hkc2
  have hkpos : (0 : ℝ) < k := by
    by_contra hk
    have : (k : ℝ) = 0 := le_antisymm (not_lt.mp hk) (Nat.cast_nonneg k)
    rw [this, Real.log_zero] at hklog
    norm_num at hklog
  have hlogkpos : 0 < Real.log (k : ℝ) := by linarith
  have hlogkcpos : 0 < Real.log ((k : ℝ) * c) :=
    Real.log_pos (by linarith)
  have hdiv : Real.rpow
      (Real.log (k : ℝ) / Real.log ((k : ℝ) * c)) q =
      Real.rpow (Real.log (k : ℝ)) q /
        Real.rpow (Real.log ((k : ℝ) * c)) q := by
    change (Real.log (k : ℝ) / Real.log ((k : ℝ) * c)) ^ q =
      (Real.log (k : ℝ)) ^ q / (Real.log ((k : ℝ) * c)) ^ q
    exact Real.div_rpow hlogkpos.le hlogkcpos.le q
  simp only [Pi.div_apply]
  unfold shiftedBasicLogTerm basicLogTerm
  rw [show Real.log ((k : ℝ) * Real.log 2) = Real.log ((k : ℝ) * c) by rfl,
    hdiv]
  have hkne : (k : ℝ) ≠ 0 := hkpos.ne'
  have hL : Real.rpow (Real.log (k : ℝ)) q ≠ 0 :=
    (Real.rpow_pos_of_pos hlogkpos _).ne'
  have hLc : Real.rpow (Real.log ((k : ℝ) * c)) q ≠ 0 :=
    (Real.rpow_pos_of_pos hlogkcpos _).ne'
  field_simp [hkne, hL, hLc]

private def fullLogExponent (p q t : ℝ) : ℝ :=
  -t - p * Real.log t - q * Real.log (Real.log t)

private theorem integrand_eq_exp_full (p q x : ℝ)
    (hx : Real.exp (Real.exp 1) < x) :
    integrand p q x = Real.exp (fullLogExponent p q (Real.log x)) := by
  have hxpos : 0 < x := (Real.exp_pos _).trans hx
  have hlogLarge : Real.exp 1 < Real.log x :=
    (Real.lt_log_iff_exp_lt hxpos).2 hx
  have hlogpos : 0 < Real.log x := (Real.exp_pos 1).trans hlogLarge
  have hloglogpos : 0 < Real.log (Real.log x) :=
    Real.log_pos (one_lt_two.trans (Real.exp_one_gt_two.trans hlogLarge))
  have hrp : Real.rpow (Real.log x) p =
      Real.exp (Real.log (Real.log x) * p) := by
    change (Real.log x) ^ p = Real.exp (Real.log (Real.log x) * p)
    exact Real.rpow_def_of_pos hlogpos _
  have hrq : Real.rpow (Real.log (Real.log x)) q =
      Real.exp (Real.log (Real.log (Real.log x)) * q) := by
    change (Real.log (Real.log x)) ^ q =
      Real.exp (Real.log (Real.log (Real.log x)) * q)
    exact Real.rpow_def_of_pos hloglogpos _
  unfold integrand fullLogExponent
  rw [hrp, hrq]
  have hxinv : x⁻¹ = Real.exp (-Real.log x) := by
    rw [Real.exp_neg, Real.exp_log hxpos]
  simp only [one_div, mul_inv]
  rw [hxinv, ← Real.exp_neg, ← Real.exp_neg, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

theorem gap1 (p q x : ℝ) (hx : 3 ≤ x) :
    0 < integrand p q x := by
  unfold integrand
  have hxpos : 0 < x := by linarith
  have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
  have honeLog : 1 < Real.log x :=
    (Real.lt_log_iff_exp_lt hxpos).2
      (Real.exp_one_lt_three.trans_le hx)
  have hloglogpos : 0 < Real.log (Real.log x) := Real.log_pos honeLog
  exact one_div_pos.mpr (mul_pos
    (mul_pos hxpos (Real.rpow_pos_of_pos hlogpos _))
    (Real.rpow_pos_of_pos hloglogpos _))

theorem gap2 (p q : ℝ) :
    ∃ A ≥ 3, AntitoneOn (integrand p q) (Ici A) := by
  let B : ℝ := max (Real.exp 1 + 1) (|p| + |q| + 1)
  let A : ℝ := max 3 (Real.exp B)
  have hBlarge : Real.exp 1 + 1 ≤ B := le_max_left _ _
  have hBexp : Real.exp 1 ≤ B := (le_add_of_nonneg_right zero_le_one).trans hBlarge
  have hBstrict : Real.exp 1 < B := (lt_add_one (Real.exp 1)).trans_le hBlarge
  have hBpq : |p| + |q| + 1 ≤ B := le_max_right _ _
  have hA3 : 3 ≤ A := le_max_left _ _
  have hAexp : Real.exp B ≤ A := le_max_right _ _
  have hE : AntitoneOn (fullLogExponent p q) (Ici B) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos
      (f' := fun t => -1 - p * (1 / t) - q * (1 / (t * Real.log t)))
      (convex_Ici B)
    · intro t ht
      have htB := Set.mem_Ici.mp ht
      have htpos : 0 < t := (Real.exp_pos 1).trans_le (hBexp.trans htB)
      have hlogpos : 0 < Real.log t :=
        Real.log_pos (one_lt_two.trans (Real.exp_one_gt_two.trans_le (hBexp.trans htB)))
      exact ((continuousAt_id.neg.sub
        (continuousAt_const.mul (Real.continuousAt_log htpos.ne'))).sub
          (continuousAt_const.mul
            ((Real.continuousAt_log htpos.ne').log hlogpos.ne'))).continuousWithinAt
    · intro t ht
      have htB : B < t := by simpa [interior_Ici] using ht
      have htpos : 0 < t := (Real.exp_pos 1).trans (hBexp.trans_lt htB)
      have hlogpos : 0 < Real.log t :=
        Real.log_pos (one_lt_two.trans (Real.exp_one_gt_two.trans (hBexp.trans_lt htB)))
      unfold fullLogExponent
      convert (((hasDerivAt_id t).neg.sub
        ((Real.hasDerivAt_log htpos.ne').const_mul p)).sub
          (((Real.hasDerivAt_log htpos.ne').log hlogpos.ne').const_mul q)
        ).hasDerivWithinAt using 1 <;> ring
    · intro t ht
      have htB : B < t := by simpa [interior_Ici] using ht
      have htpos : 0 < t := (Real.exp_pos 1).trans (hBexp.trans_lt htB)
      have hlogone : 1 ≤ Real.log t :=
        (Real.le_log_iff_exp_le htpos).2 (hBexp.trans htB.le)
      have htp : |q| ≤ t + p := by
        have hpLower : -|p| ≤ p := neg_abs_le p
        have := hBpq.trans htB.le
        linarith
      have htppos : 0 ≤ t + p := (abs_nonneg q).trans htp
      have hmul : |q| ≤ (t + p) * Real.log t := by
        exact htp.trans (le_mul_of_one_le_right htppos hlogone)
      have hnum : 0 ≤ (t + p) * Real.log t + q := by
        linarith [neg_abs_le q]
      have hdenpos : 0 < t * Real.log t := mul_pos htpos (zero_lt_one.trans_le hlogone)
      have hfrac : 0 ≤ 1 + p / t + q / (t * Real.log t) := by
        have heq : 1 + p / t + q / (t * Real.log t) =
            ((t + p) * Real.log t + q) / (t * Real.log t) := by
          field_simp [htpos.ne', (zero_lt_one.trans_le hlogone).ne']
        rw [heq]
        exact div_nonneg hnum hdenpos.le
      rw [show -1 - p * (1 / t) - q * (1 / (t * Real.log t)) =
          -(1 + p / t + q / (t * Real.log t)) by ring]
      exact neg_nonpos.mpr hfrac
  refine ⟨A, hA3, ?_⟩
  intro x hx y hy hxy
  have hAx : A ≤ x := Set.mem_Ici.mp hx
  have hAy : A ≤ y := Set.mem_Ici.mp hy
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3)
    (hA3.trans hAx)
  have hypos : 0 < y := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 3)
    (hA3.trans hAy)
  have hlogxB : B ≤ Real.log x :=
    (Real.le_log_iff_exp_le hxpos).2 (hAexp.trans hAx)
  have hlogyB : B ≤ Real.log y :=
    (Real.le_log_iff_exp_le hypos).2 (hAexp.trans hAy)
  have hlogxy : Real.log x ≤ Real.log y :=
    Real.strictMonoOn_log.monotoneOn (Set.mem_Ioi.mpr hxpos)
      (Set.mem_Ioi.mpr hypos) hxy
  have hxLarge : Real.exp (Real.exp 1) < x := by
    exact (Real.exp_lt_exp.mpr hBstrict).trans_le (hAexp.trans hAx)
  have hyLarge : Real.exp (Real.exp 1) < y := by
    exact (Real.exp_lt_exp.mpr hBstrict).trans_le (hAexp.trans hAy)
  rw [integrand_eq_exp_full p q x hxLarge,
    integrand_eq_exp_full p q y hyLarge]
  exact Real.exp_le_exp.mpr (hE hlogxB hlogyB hlogxy)

theorem gap3 (q x : ℝ) (hx : Real.exp 1 < x) :
    HasDerivAt (criticalPrimitive q) (integrand 1 q x) x := by
  have hxpos : 0 < x := (Real.exp_pos 1).trans hx
  have honeLog : 1 < Real.log x := (Real.lt_log_iff_exp_lt hxpos).2 hx
  have hlogpos : 0 < Real.log x := zero_lt_one.trans honeLog
  have hloglogpos : 0 < Real.log (Real.log x) := Real.log_pos honeLog
  have hlog := Real.hasDerivAt_log hxpos.ne'
  have hloglog := hlog.log hlogpos.ne'
  by_cases hq : q = 1
  · subst q
    have htriple := hloglog.log hloglogpos.ne'
    convert htriple using 1
    · funext y
      simp [criticalPrimitive]
    · unfold integrand
      have hrone1 : Real.rpow (Real.log x) 1 = Real.log x := by
        change (Real.log x) ^ (1 : ℝ) = Real.log x
        exact Real.rpow_one _
      have hrone2 : Real.rpow (Real.log (Real.log x)) 1 =
          Real.log (Real.log x) := by
        change (Real.log (Real.log x)) ^ (1 : ℝ) = Real.log (Real.log x)
        exact Real.rpow_one _
      rw [hrone1, hrone2]
      field_simp [hxpos.ne', hlogpos.ne', hloglogpos.ne']
  · have hr := hloglog.rpow_const
      (p := 1 - q) (Or.inl hloglogpos.ne')
    have hdiv := hr.div_const (1 - q)
    convert hdiv using 1
    · funext y
      simp [criticalPrimitive, hq]
    · unfold integrand
      have hrone : Real.rpow (Real.log x) 1 = Real.log x := by
        change (Real.log x) ^ (1 : ℝ) = Real.log x
        exact Real.rpow_one _
      rw [hrone]
      have hpowrel : (Real.log (Real.log x)) ^ (1 - q - 1) =
          ((Real.log (Real.log x)) ^ q)⁻¹ := by
        rw [show 1 - q - 1 = -q by ring]
        exact Real.rpow_neg hloglogpos.le q
      rw [hpowrel]
      have hq1 : 1 - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
      have hrq : Real.rpow (Real.log (Real.log x)) q ≠ 0 :=
        (Real.rpow_pos_of_pos hloglogpos q).ne'
      field_simp [hq1, hxpos.ne', hlogpos.ne', hrq]
      change Real.rpow (Real.log (Real.log x)) q =
        Real.rpow (Real.log (Real.log x)) q
      rfl

private theorem critical_summable_iff (q : ℝ) :
    Summable (fun n : ℕ => integrand 1 q (n : ℝ)) ↔ 1 < q := by
  have hnonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ integrand 1 q (n : ℝ) := by
    filter_upwards [eventually_ge_atTop 3] with n hn
    exact (gap1 1 q (n : ℝ) (by exact_mod_cast hn)).le
  obtain ⟨A, hA3, hanti⟩ := gap2 1 q
  have hmono : ∀ᶠ n : ℕ in atTop,
      integrand 1 q (((n + 1 : ℕ) : ℝ)) ≤ integrand 1 q (n : ℝ) := by
    filter_upwards [eventually_ge_atTop ⌈A⌉₊] with n hn
    have hAn : A ≤ (n : ℝ) := (Nat.le_ceil A).trans (Nat.cast_le.mpr hn)
    have hAn1 : A ≤ ((n + 1 : ℕ) : ℝ) :=
      hAn.trans (by exact_mod_cast Nat.le_succ n)
    exact hanti (Set.mem_Ici.mpr hAn) (Set.mem_Ici.mpr hAn1)
      (by exact_mod_cast Nat.le_succ n)
  have hcondiff := summable_condensed_iff_of_eventually_nonneg hnonneg hmono
  have hc : (1 / Real.log 2 : ℝ) ≠ 0 := by
    exact one_div_ne_zero (Real.log_pos (by norm_num)).ne'
  constructor
  · intro hall
    have hcondensed : Summable (fun k : ℕ =>
        (2 : ℝ) ^ k * integrand 1 q (((2 ^ k : ℕ) : ℝ))) :=
      hcondiff.mpr hall
    have hscaled : Summable (fun k : ℕ =>
        (1 / Real.log 2) * shiftedBasicLogTerm q k) :=
      hcondensed.congr (fun k => critical_condensed_eq q k)
    have hshifted : Summable (fun k : ℕ => shiftedBasicLogTerm q k) :=
      (summable_mul_left_iff hc).mp hscaled
    have hbasic : Summable (fun k : ℕ => basicLogTerm q (k : ℝ)) :=
      summable_of_isBigO_nat hshifted
        (shiftedBasic_isEquivalent_basic q).isBigO_symm
    exact (basicLog_summable_iff q).mp hbasic
  · intro hq
    have hbasic : Summable (fun k : ℕ => basicLogTerm q (k : ℝ)) :=
      (basicLog_summable_iff q).mpr hq
    have hshifted : Summable (fun k : ℕ => shiftedBasicLogTerm q k) :=
      summable_of_isBigO_nat hbasic
        (shiftedBasic_isEquivalent_basic q).isBigO
    have hscaled : Summable (fun k : ℕ =>
        (1 / Real.log 2) * shiftedBasicLogTerm q k) :=
      hshifted.mul_left _
    have hcondensed : Summable (fun k : ℕ =>
        (2 : ℝ) ^ k * integrand 1 q (((2 ^ k : ℕ) : ℝ))) :=
      hscaled.congr (fun k => (critical_condensed_eq q k).symm)
    exact hcondiff.mp hcondensed

theorem gap4 (q : ℝ) (hq : 1 < q) :
    converges 1 q := by
  have hall : Summable (fun n : ℕ => integrand 1 q (n : ℝ)) :=
    (critical_summable_iff q).mpr hq
  simpa [converges, Nat.cast_add] using (summable_nat_add_iff 3).mpr hall

theorem gap5 (q : ℝ) (hq : q ≤ 1) :
    ¬ converges 1 q := by
  intro hconv
  have hshift : Summable (fun n : ℕ =>
      integrand 1 q (((n + 3 : ℕ) : ℝ))) := by
    simpa [converges, Nat.cast_add] using hconv
  have hall : Summable (fun n : ℕ => integrand 1 q (n : ℝ)) :=
    (summable_nat_add_iff 3).mp hshift
  have := (critical_summable_iff q).mp hall
  linarith

theorem gap6 (p q A : ℝ) (hA : 3 ≤ A) :
    (∫ x in (3 : ℝ)..A, integrand p q x) =
      ∫ t in Real.log 3..Real.log A, transformed p q t := by
  have hderiv : ∀ x ∈ Set.uIcc (3 : ℝ) A,
      HasDerivAt Real.log (1 / x) x := by
    intro x hx
    rw [Set.uIcc_of_le hA] at hx
    have hx3 : (3 : ℝ) ≤ x := hx.1
    have hxpos : 0 < x := by linarith
    simpa [one_div] using Real.hasDerivAt_log hxpos.ne'
  have hderivCont : ContinuousOn (fun x : ℝ => 1 / x) (Set.uIcc 3 A) := by
    apply ContinuousOn.div continuousOn_const continuousOn_id
    intro x hx
    rw [Set.uIcc_of_le hA] at hx
    have hx3 : (3 : ℝ) ≤ x := hx.1
    change x ≠ 0
    linarith
  have htransCont : ContinuousOn (transformed p q)
      ((fun x : ℝ => Real.log x) '' [[(3 : ℝ), A]]) := by
    intro t ht
    rcases ht with ⟨x, hx, rfl⟩
    rw [Set.uIcc_of_le hA] at hx
    have hx3 : (3 : ℝ) ≤ x := hx.1
    have hxpos : 0 < x := by linarith
    have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
    have hloglogpos : 0 < Real.log (Real.log x) := by
      exact Real.log_pos ((Real.lt_log_iff_exp_lt hxpos).2
        (Real.exp_one_lt_three.trans_le hx.1))
    have hpcont : ContinuousAt (fun t : ℝ => Real.rpow t p) (Real.log x) :=
      continuousAt_id.rpow_const (Or.inl hlogpos.ne')
    have hqcont : ContinuousAt
        (fun t : ℝ => Real.rpow (Real.log t) q) (Real.log x) :=
      (Real.continuousAt_log hlogpos.ne').rpow_const (Or.inl hloglogpos.ne')
    unfold transformed
    exact (continuousAt_const.div (hpcont.mul hqcont)
      (mul_ne_zero (Real.rpow_pos_of_pos hlogpos p).ne'
        (Real.rpow_pos_of_pos hloglogpos q).ne')).continuousWithinAt
  have H := intervalIntegral.integral_comp_mul_deriv'
    (a := (3 : ℝ)) (b := A)
    (f := Real.log) (f' := fun x : ℝ => 1 / x)
    (g := transformed p q) hderiv hderivCont htransCont
  calc
    (∫ x in (3 : ℝ)..A, integrand p q x) =
        ∫ x in (3 : ℝ)..A,
          (transformed p q ∘ Real.log) x * (1 / x) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le hA] at hx
      have hx3 : (3 : ℝ) ≤ x := hx.1
      have hxpos : 0 < x := by linarith
      have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
      have hloglogpos : 0 < Real.log (Real.log x) := by
        exact Real.log_pos ((Real.lt_log_iff_exp_lt hxpos).2
          (Real.exp_one_lt_three.trans_le hx.1))
      unfold integrand transformed
      simp only [Function.comp_apply]
      field_simp [hxpos.ne',
        (Real.rpow_pos_of_pos hlogpos p).ne',
        (Real.rpow_pos_of_pos hloglogpos q).ne']
    _ = ∫ t in Real.log 3..Real.log A, transformed p q t := H

theorem gap7 (p q η t : ℝ) (ht : 1 < t) :
    Real.rpow t (p - η) * transformed p q t =
      1 / (Real.rpow t η * Real.rpow (Real.log t) q) := by
  have htpos : 0 < t := zero_lt_one.trans ht
  have hlogpos : 0 < Real.log t := Real.log_pos ht
  have hsub : Real.rpow t (p - η) =
      Real.rpow t p / Real.rpow t η := by
    change t ^ (p - η) = t ^ p / t ^ η
    exact Real.rpow_sub htpos _ _
  have htp : Real.rpow t p ≠ 0 := (Real.rpow_pos_of_pos htpos _).ne'
  have htη : Real.rpow t η ≠ 0 := (Real.rpow_pos_of_pos htpos _).ne'
  have hlq : Real.rpow (Real.log t) q ≠ 0 :=
    (Real.rpow_pos_of_pos hlogpos _).ne'
  unfold transformed
  rw [hsub]
  field_simp [htp, htη, hlq]

theorem gap8 (q η : ℝ) (hη : 0 < η) :
    Tendsto
      (fun t : ℝ => 1 / (Real.rpow t η * Real.rpow (Real.log t) q))
      atTop (nhds 0) := by
  have h := (isLittleO_log_rpow_rpow_atTop (-q) hη).tendsto_div_nhds_zero
  apply h.congr'
  filter_upwards [eventually_gt_atTop 1] with t ht
  have htpos : 0 < t := zero_lt_one.trans ht
  have hlogpos : 0 < Real.log t := Real.log_pos ht
  have hneg : (Real.log t) ^ (-q) =
      ((Real.log t) ^ q)⁻¹ := by
    exact Real.rpow_neg hlogpos.le q
  rw [hneg]
  have htη : Real.rpow t η ≠ 0 := (Real.rpow_pos_of_pos htpos _).ne'
  have hlq : Real.rpow (Real.log t) q ≠ 0 :=
    (Real.rpow_pos_of_pos hlogpos _).ne'
  field_simp [htη, hlq]
  change Real.rpow t η * Real.rpow (Real.log t) q =
    Real.rpow (Real.log t) q * Real.rpow t η
  ring

theorem gap9 (p q η : ℝ) (hη : 0 < η) :
    Tendsto
      (fun t : ℝ => Real.rpow t (p - η) * transformed p q t)
      atTop (nhds 0) := by
  apply (gap8 q η hη).congr'
  filter_upwards [eventually_gt_atTop 1] with t ht
  exact (gap7 p q η t ht).symm

theorem gap10 (p q : ℝ) (hp : 1 < p) :
    converges p q := by
  let η : ℝ := (p - 1) / 2
  let r : ℝ := p - η
  have hη : 0 < η := by
    dsimp only [η]
    linarith
  have hr : 1 < r := by
    dsimp only [r, η]
    linarith
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlim := (gap9 p q η hη).comp hlog
  have hratio : Tendsto (fun n : ℕ =>
      integrand p q (n : ℝ) / basicLogTerm r (n : ℝ)) atTop (nhds 0) := by
    apply hlim.congr'
    filter_upwards [eventually_ge_atTop 3] with n hn
    have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
    have hnpos : (0 : ℝ) < n := by linarith
    have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
    have hloglogpos : 0 < Real.log (Real.log (n : ℝ)) := by
      exact Real.log_pos ((Real.lt_log_iff_exp_lt hnpos).2
        (Real.exp_one_lt_three.trans_le hn3))
    dsimp only [r]
    unfold integrand basicLogTerm transformed
    simp only [Function.comp_apply]
    field_simp [hnpos.ne',
      (Real.rpow_pos_of_pos hlogpos p).ne',
      (Real.rpow_pos_of_pos hlogpos (p - η)).ne',
      (Real.rpow_pos_of_pos hloglogpos q).ne']
  have hO : (fun n : ℕ => integrand p q (n : ℝ)) =O[atTop]
      (fun n : ℕ => basicLogTerm r (n : ℝ)) := by
    refine Asymptotics.isBigO_of_div_tendsto_nhds ?_ 0 hratio
    filter_upwards [eventually_ge_atTop 2] with n hn hzero
    exact ((basicLogTerm_pos r (n : ℝ) (by exact_mod_cast hn)).ne' hzero).elim
  have hbasic : Summable (fun n : ℕ => basicLogTerm r (n : ℝ)) :=
    (basicLog_summable_iff r).mpr hr
  have hall : Summable (fun n : ℕ => integrand p q (n : ℝ)) :=
    summable_of_isBigO_nat hbasic hO
  simpa [converges, Nat.cast_add] using (summable_nat_add_iff 3).mpr hall

theorem gap11 (p q τ t : ℝ) (ht : 1 < t) :
    Real.rpow t (p + τ) * transformed p q t =
      Real.rpow t τ / Real.rpow (Real.log t) q := by
  have htpos : 0 < t := zero_lt_one.trans ht
  have hlogpos : 0 < Real.log t := Real.log_pos ht
  have hadd : Real.rpow t (p + τ) =
      Real.rpow t p * Real.rpow t τ := by
    change t ^ (p + τ) = t ^ p * t ^ τ
    exact Real.rpow_add htpos _ _
  have htp : Real.rpow t p ≠ 0 := (Real.rpow_pos_of_pos htpos _).ne'
  have hlq : Real.rpow (Real.log t) q ≠ 0 :=
    (Real.rpow_pos_of_pos hlogpos _).ne'
  unfold transformed
  rw [hadd]
  field_simp [htp, hlq]

theorem gap12 (q τ : ℝ) (hτ : 0 < τ) :
    Tendsto
      (fun t : ℝ => Real.rpow t τ / Real.rpow (Real.log t) q)
      atTop atTop := by
  let f : ℝ → ℝ := fun t =>
    1 / (Real.rpow t τ * Real.rpow (Real.log t) (-q))
  have hf0 : Tendsto f atTop (nhds 0) := by
    simpa [f] using gap8 (-q) τ hτ
  have hfpos : ∀ᶠ t : ℝ in atTop, 0 < f t := by
    filter_upwards [eventually_gt_atTop 1] with t ht
    unfold f
    exact one_div_pos.mpr (mul_pos
      (Real.rpow_pos_of_pos (zero_lt_one.trans ht) _)
      (Real.rpow_pos_of_pos (Real.log_pos ht) _))
  have hfwithin : Tendsto f atTop (nhdsWithin 0 (Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hf0, by simpa only [mem_Ioi] using hfpos⟩
  have hinv := hfwithin.inv_tendsto_nhdsGT_zero
  apply hinv.congr'
  filter_upwards [eventually_gt_atTop 1] with t ht
  have htpos : 0 < t := zero_lt_one.trans ht
  have hlogpos : 0 < Real.log t := Real.log_pos ht
  have hneg : Real.rpow (Real.log t) (-q) =
      (Real.rpow (Real.log t) q)⁻¹ := by
    change (Real.log t) ^ (-q) = ((Real.log t) ^ q)⁻¹
    exact Real.rpow_neg hlogpos.le q
  change (1 / (Real.rpow t τ * Real.rpow (Real.log t) (-q)))⁻¹ =
    Real.rpow t τ / Real.rpow (Real.log t) q
  rw [hneg]
  have htτ : Real.rpow t τ ≠ 0 := (Real.rpow_pos_of_pos htpos _).ne'
  have hlq : Real.rpow (Real.log t) q ≠ 0 :=
    (Real.rpow_pos_of_pos hlogpos _).ne'
  field_simp [htτ, hlq]

theorem gap13 (p q τ : ℝ) (hτ : 0 < τ) :
    Tendsto
      (fun t : ℝ => Real.rpow t (p + τ) * transformed p q t)
      atTop atTop := by
  apply (gap12 q τ hτ).congr'
  filter_upwards [eventually_gt_atTop 1] with t ht
  exact (gap11 p q τ t ht).symm

theorem gap14 (p q : ℝ) (hp : p < 1) :
    ¬ converges p q := by
  let τ : ℝ := (1 - p) / 2
  let s : ℝ := p + τ
  have hτ : 0 < τ := by
    dsimp only [τ]
    linarith
  have hs : s < 1 := by
    dsimp only [s, τ]
    linarith
  have hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlim := (gap13 p q τ hτ).comp hlog
  have hinv := hlim.inv_tendsto_atTop
  have hratio : Tendsto (fun n : ℕ =>
      basicLogTerm s (n : ℝ) / integrand p q (n : ℝ)) atTop (nhds 0) := by
    apply hinv.congr'
    filter_upwards [eventually_ge_atTop 3] with n hn
    have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
    have hnpos : (0 : ℝ) < n := by linarith
    have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
    have hloglogpos : 0 < Real.log (Real.log (n : ℝ)) := by
      exact Real.log_pos ((Real.lt_log_iff_exp_lt hnpos).2
        (Real.exp_one_lt_three.trans_le hn3))
    dsimp only [s]
    unfold integrand basicLogTerm transformed
    simp only [Pi.inv_apply, Function.comp_apply]
    field_simp [hnpos.ne',
      (Real.rpow_pos_of_pos hlogpos p).ne',
      (Real.rpow_pos_of_pos hlogpos (p + τ)).ne',
      (Real.rpow_pos_of_pos hloglogpos q).ne']
  have hO : (fun n : ℕ => basicLogTerm s (n : ℝ)) =O[atTop]
      (fun n : ℕ => integrand p q (n : ℝ)) := by
    refine Asymptotics.isBigO_of_div_tendsto_nhds ?_ 0 hratio
    filter_upwards [eventually_ge_atTop 3] with n hn hzero
    exact ((gap1 p q (n : ℝ) (by exact_mod_cast hn)).ne' hzero).elim
  intro hconv
  have hshift : Summable (fun n : ℕ =>
      integrand p q (((n + 3 : ℕ) : ℝ))) := by
    simpa [converges, Nat.cast_add] using hconv
  have hall : Summable (fun n : ℕ => integrand p q (n : ℝ)) :=
    (summable_nat_add_iff 3).mp hshift
  have hbasic : Summable (fun n : ℕ => basicLogTerm s (n : ℝ)) :=
    summable_of_isBigO_nat hall hO
  have hs1 := (basicLog_summable_iff s).mp hbasic
  linarith

theorem gap15 (p q : ℝ) :
    converges p q ↔ 1 < p ∨ (p = 1 ∧ 1 < q) := by
  constructor
  · intro hconv
    by_cases hp : 1 < p
    · exact Or.inl hp
    · have hple : p ≤ 1 := le_of_not_gt hp
      have hpge : 1 ≤ p := by
        by_contra hnot
        exact (gap14 p q (lt_of_not_ge hnot)) hconv
      have hpeq : p = 1 := le_antisymm hple hpge
      subst p
      have hq : 1 < q := by
        by_contra hnot
        exact (gap5 q (le_of_not_gt hnot)) hconv
      exact Or.inr ⟨rfl, hq⟩
  · rintro (hp | ⟨rfl, hq⟩)
    · exact gap10 p q hp
    · exact gap4 q hq

end

end ProofGap.Exercise2620
