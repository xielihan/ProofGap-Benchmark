import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise2190
noncomputable section

open Filter
open scoped BigOperators Interval

def q (a b : ℝ) (n : ℕ) : ℝ :=
  Real.rpow (b / a) (1 / (n : ℝ))

def powM (x m : ℝ) : ℝ := Real.rpow x m

def lowerSum (a b m : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n,
    powM (a * q a b n ^ i) m *
      (a * q a b n ^ (i + 1) - a * q a b n ^ i)

def ratio (a b m : ℝ) (n : ℕ) : ℝ :=
  (q a b n - 1) / (powM (q a b n) (m + 1) - 1)

theorem gap1 (a b : ℝ) (n : ℕ)
    (ha : 0 < a) (hab : a < b) (hn : 0 < n) :
    a < a * q a b n := by
  have hba : 1 < b / a := (one_lt_div ha).2 hab
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.2 hn
  have he : 0 < 1 / (n : ℝ) := div_pos zero_lt_one hn'
  simpa [q] using
    (mul_lt_mul_of_pos_left (Real.one_lt_rpow hba he) ha)

theorem gap2 (a b : ℝ) (n : ℕ)
    (ha : 0 < a) (hab : a < b) (hn : 0 < n) :
    a * q a b n < a * q a b n ^ 2 := by
  have hq : 1 < q a b n :=
    (lt_mul_iff_one_lt_right ha).mp (gap1 a b n ha hab hn)
  have hqa : 0 < a * q a b n :=
    mul_pos ha (lt_trans zero_lt_one hq)
  calc
    a * q a b n < (a * q a b n) * q a b n :=
      lt_mul_of_one_lt_right hqa hq
    _ = a * q a b n ^ 2 := by ring

theorem gap3 (a b : ℝ) (n i : ℕ)
    (ha : 0 < a) (hab : a < b) (hn : 0 < n) (hi : i < n) :
    a * q a b n ^ i < a * q a b n ^ (i + 1) := by
  have hq : 1 < q a b n :=
    (lt_mul_iff_one_lt_right ha).mp (gap1 a b n ha hab hn)
  have hq0 : 0 < q a b n := lt_trans zero_lt_one hq
  have hbase : 0 < a * q a b n ^ i :=
    mul_pos ha (pow_pos hq0 i)
  calc
    a * q a b n ^ i < (a * q a b n ^ i) * q a b n :=
      lt_mul_of_one_lt_right hbase hq
    _ = a * q a b n ^ (i + 1) := by
      rw [pow_succ]
      ring

theorem gap4 (a b : ℝ) (n : ℕ)
    (ha : 0 < a) (hab : a < b) (hn : 0 < n) :
    a * q a b n ^ (n - 1) < a * q a b n ^ n := by
  have hle : 1 ≤ n := hn
  have hpred : n - 1 < n := Nat.sub_lt hn (by norm_num)
  have hstep := gap3 a b n (n - 1) ha hab hn hpred
  simpa [Nat.sub_add_cancel hle] using hstep

theorem gap5 (a b : ℝ) (n : ℕ)
    (ha : 0 < a) (hab : a < b) (hn : 0 < n) :
    a * q a b n ^ n = b := by
  have hba : 0 < b / a := div_pos (lt_trans ha hab) ha
  have hn' : (n : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.2 hn)
  have hmul : (1 / (n : ℝ)) * (n : ℝ) = 1 := by
    field_simp
  unfold q
  calc
    a * Real.rpow (b / a) (1 / (n : ℝ)) ^ n =
        a * Real.rpow (Real.rpow (b / a) (1 / (n : ℝ))) (n : ℝ) := by
      exact congrArg (fun x : ℝ => a * x)
        (Real.rpow_natCast (Real.rpow (b / a) (1 / (n : ℝ))) n).symm
    _ = a * Real.rpow (b / a) ((1 / (n : ℝ)) * (n : ℝ)) := by
      exact congrArg (fun x : ℝ => a * x)
        (Real.rpow_mul hba.le (1 / (n : ℝ)) (n : ℝ)).symm
    _ = a * Real.rpow (b / a) 1 := by rw [hmul]
    _ = a * (b / a) := by
      exact congrArg (fun x : ℝ => a * x) (Real.rpow_one (b / a))
    _ = b := by
      field_simp [ne_of_gt ha]

theorem gap6 (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    a < b := by
  exact hab

theorem gap7 (a b m : ℝ) (n : ℕ)
    (ha : 0 < a) (hab : a < b) (hm : m ≠ -1) (hn : 0 < n) :
    lowerSum a b m n =
      ∑ i ∈ Finset.range n,
        powM (a * q a b n ^ i) m *
          (a * q a b n ^ (i + 1) - a * q a b n ^ i) := by
  rfl

theorem gap8 (a b m : ℝ) (n : ℕ)
    (ha : 0 < a) (hab : a < b) (hm : m ≠ -1) (hn : 0 < n) :
    (∑ i ∈ Finset.range n,
        powM (a * q a b n ^ i) m *
          (a * q a b n ^ (i + 1) - a * q a b n ^ i)) =
      powM a (m + 1) * (q a b n - 1) *
        ∑ i ∈ Finset.range n, powM (q a b n) ((m + 1) * (i : ℝ)) := by
  have hq1 : 1 < q a b n :=
    (lt_mul_iff_one_lt_right ha).mp (gap1 a b n ha hab hn)
  have hq0 : 0 < q a b n := lt_trans zero_lt_one hq1
  have hsummand (i : ℕ) :
      powM (a * q a b n ^ i) m *
          (a * q a b n ^ (i + 1) - a * q a b n ^ i) =
        (powM a (m + 1) * (q a b n - 1)) *
          powM (q a b n) ((m + 1) * (i : ℝ)) := by
    have hmul :
        powM (a * q a b n ^ i) m =
          powM a m * powM (q a b n ^ i) m := by
      change Real.rpow (a * q a b n ^ i) m =
        Real.rpow a m * Real.rpow (q a b n ^ i) m
      exact Real.mul_rpow ha.le (pow_pos hq0 i).le
    have hqi :
        powM (q a b n ^ i) m =
          powM (q a b n) (m * (i : ℝ)) := by
      change Real.rpow (q a b n ^ i) m =
        Real.rpow (q a b n) (m * (i : ℝ))
      calc
        Real.rpow (q a b n ^ i) m =
            Real.rpow (q a b n) ((i : ℝ) * m) :=
          (Real.rpow_natCast_mul hq0.le i m).symm
        _ = Real.rpow (q a b n) (m * (i : ℝ)) := by
          rw [mul_comm]
    have haadd :
        powM a (m + 1) = powM a m * a := by
      unfold powM
      calc
        Real.rpow a (m + 1) = Real.rpow a m * Real.rpow a 1 :=
          Real.rpow_add ha m 1
        _ = Real.rpow a m * a := by
          exact congrArg (fun x : ℝ => Real.rpow a m * x)
            (Real.rpow_one a)
    have hqadd :
        powM (q a b n) ((m + 1) * (i : ℝ)) =
          powM (q a b n) (m * (i : ℝ)) * q a b n ^ i := by
      unfold powM
      calc
        Real.rpow (q a b n) ((m + 1) * (i : ℝ)) =
            Real.rpow (q a b n) (m * (i : ℝ) + (i : ℝ)) := by
          congr 1
          ring
        _ = Real.rpow (q a b n) (m * (i : ℝ)) *
              Real.rpow (q a b n) (i : ℝ) :=
          Real.rpow_add hq0 (m * (i : ℝ)) (i : ℝ)
        _ = Real.rpow (q a b n) (m * (i : ℝ)) * q a b n ^ i := by
          exact congrArg
            (fun x : ℝ => Real.rpow (q a b n) (m * (i : ℝ)) * x)
            (Real.rpow_natCast (q a b n) i)
    rw [hmul, hqi, haadd, hqadd, pow_succ]
    ring
  calc
    (∑ i ∈ Finset.range n,
        powM (a * q a b n ^ i) m *
          (a * q a b n ^ (i + 1) - a * q a b n ^ i)) =
      ∑ i ∈ Finset.range n,
        (powM a (m + 1) * (q a b n - 1)) *
          powM (q a b n) ((m + 1) * (i : ℝ)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hsummand i
    _ = powM a (m + 1) * (q a b n - 1) *
        ∑ i ∈ Finset.range n,
          powM (q a b n) ((m + 1) * (i : ℝ)) := by
      rw [Finset.mul_sum]

theorem gap9 (a b m : ℝ) (n : ℕ)
    (ha : 0 < a) (hab : a < b) (hm : m ≠ -1) (hn : 0 < n) :
    lowerSum a b m n =
      powM a (m + 1) * (q a b n - 1) *
        ∑ i ∈ Finset.range n, powM (q a b n) ((m + 1) * (i : ℝ)) := by
  calc
    lowerSum a b m n =
        ∑ i ∈ Finset.range n,
          powM (a * q a b n ^ i) m *
            (a * q a b n ^ (i + 1) - a * q a b n ^ i) :=
      gap7 a b m n ha hab hm hn
    _ = powM a (m + 1) * (q a b n - 1) *
          ∑ i ∈ Finset.range n,
            powM (q a b n) ((m + 1) * (i : ℝ)) :=
      gap8 a b m n ha hab hm hn

theorem gap10 (a b m : ℝ) (n : ℕ)
    (ha : 0 < a) (hab : a < b) (hm : m ≠ -1) (hn : 0 < n) :
    lowerSum a b m n =
      powM a (m + 1) * (q a b n - 1) *
        (powM (q a b n) ((n : ℝ) * (m + 1)) - 1) /
          (powM (q a b n) (m + 1) - 1) := by
  have hq1 : 1 < q a b n :=
    (lt_mul_iff_one_lt_right ha).mp (gap1 a b n ha hab hn)
  have hq0 : 0 < q a b n := lt_trans zero_lt_one hq1
  have hp : m + 1 ≠ 0 := by
    intro h
    apply hm
    linarith only [h]
  have hr : powM (q a b n) (m + 1) ≠ 1 := by
    rcases lt_or_gt_of_ne hp with hpneg | hppos
    · have hlt : powM (q a b n) (m + 1) < 1 := by
        exact Real.rpow_lt_one_of_one_lt_of_neg hq1 hpneg
      exact ne_of_lt hlt
    · have hgt : 1 < powM (q a b n) (m + 1) := by
        exact Real.one_lt_rpow hq1 hppos
      exact ne_of_gt hgt
  have hterm (i : ℕ) :
      powM (q a b n) ((m + 1) * (i : ℝ)) =
        powM (q a b n) (m + 1) ^ i := by
    unfold powM
    calc
      Real.rpow (q a b n) ((m + 1) * (i : ℝ)) =
          Real.rpow (Real.rpow (q a b n) (m + 1)) (i : ℝ) :=
        Real.rpow_mul hq0.le (m + 1) (i : ℝ)
      _ = Real.rpow (q a b n) (m + 1) ^ i :=
        Real.rpow_natCast (Real.rpow (q a b n) (m + 1)) i
  have hgeom (k : ℕ) :
      (∑ i ∈ Finset.range k, powM (q a b n) (m + 1) ^ i) *
          (powM (q a b n) (m + 1) - 1) =
        powM (q a b n) (m + 1) ^ k - 1 := by
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Finset.sum_range_succ, add_mul, ih, pow_succ]
        ring
  have hsum :
      (∑ i ∈ Finset.range n,
          powM (q a b n) ((m + 1) * (i : ℝ))) =
        (powM (q a b n) ((n : ℝ) * (m + 1)) - 1) /
          (powM (q a b n) (m + 1) - 1) := by
    rw [Finset.sum_congr rfl (fun i hi => hterm i)]
    apply (eq_div_iff (sub_ne_zero.mpr hr)).2
    calc
      (∑ i ∈ Finset.range n, powM (q a b n) (m + 1) ^ i) *
          (powM (q a b n) (m + 1) - 1) =
          powM (q a b n) (m + 1) ^ n - 1 := hgeom n
      _ = powM (q a b n) ((m + 1) * (n : ℝ)) - 1 := by
        rw [hterm n]
      _ = powM (q a b n) ((n : ℝ) * (m + 1)) - 1 := by
        rw [mul_comm (m + 1) (n : ℝ)]
  rw [gap9 a b m n ha hab hm hn, hsum]
  ring

theorem gap11 (a b m : ℝ) (n : ℕ)
    (ha : 0 < a) (hab : a < b) (hm : m ≠ -1) (hn : 0 < n) :
    powM a (m + 1) * (q a b n - 1) *
        (powM (q a b n) ((n : ℝ) * (m + 1)) - 1) /
          (powM (q a b n) (m + 1) - 1) =
      (powM b (m + 1) - powM a (m + 1)) *
        (q a b n - 1) / (powM (q a b n) (m + 1) - 1) := by
  have hq1 : 1 < q a b n :=
    (lt_mul_iff_one_lt_right ha).mp (gap1 a b n ha hab hn)
  have hq0 : 0 < q a b n := lt_trans zero_lt_one hq1
  have hqn : a * q a b n ^ n = b := gap5 a b n ha hab hn
  have hbpow :
      powM b (m + 1) =
        powM a (m + 1) *
          powM (q a b n) ((n : ℝ) * (m + 1)) := by
    calc
      powM b (m + 1) = powM (a * q a b n ^ n) (m + 1) := by
        rw [hqn]
      _ = powM a (m + 1) * powM (q a b n ^ n) (m + 1) := by
        change Real.rpow (a * q a b n ^ n) (m + 1) =
          Real.rpow a (m + 1) * Real.rpow (q a b n ^ n) (m + 1)
        exact Real.mul_rpow ha.le (pow_pos hq0 n).le
      _ = powM a (m + 1) *
          powM (q a b n) ((n : ℝ) * (m + 1)) := by
        congr 1
        change Real.rpow (q a b n ^ n) (m + 1) =
          Real.rpow (q a b n) ((n : ℝ) * (m + 1))
        exact (Real.rpow_natCast_mul hq0.le n (m + 1)).symm
  rw [hbpow]
  ring

theorem gap12 (a b m : ℝ) (n : ℕ)
    (ha : 0 < a) (hab : a < b) (hm : m ≠ -1) (hn : 0 < n) :
    lowerSum a b m n =
      (powM b (m + 1) - powM a (m + 1)) *
        (q a b n - 1) / (powM (q a b n) (m + 1) - 1) := by
  calc
    lowerSum a b m n =
        powM a (m + 1) * (q a b n - 1) *
          (powM (q a b n) ((n : ℝ) * (m + 1)) - 1) /
            (powM (q a b n) (m + 1) - 1) :=
      gap10 a b m n ha hab hm hn
    _ = (powM b (m + 1) - powM a (m + 1)) *
          (q a b n - 1) /
            (powM (q a b n) (m + 1) - 1) :=
      gap11 a b m n ha hab hm hn

theorem gap13 (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    Tendsto (q a b) atTop (nhds (1 : ℝ)) := by
  have hba : 0 < b / a := div_pos (lt_trans ha hab) ha
  have hcast :
      Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hinv :
      Tendsto (fun n : ℕ => ((n : ℝ)⁻¹)) atTop (nhds (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp hcast
  have hlog :
      Tendsto (fun _ : ℕ => Real.log (b / a)) atTop
        (nhds (Real.log (b / a))) :=
    tendsto_const_nhds
  have harg :
      Tendsto (fun n : ℕ => Real.log (b / a) * (1 / (n : ℝ)))
        atTop (nhds (0 : ℝ)) := by
    have hmul := hlog.mul hinv
    simpa only [one_div, mul_zero] using hmul
  have hexp :
      Tendsto Real.exp (nhds (0 : ℝ)) (nhds (1 : ℝ)) := by
    have hexp0 : ContinuousAt Real.exp (0 : ℝ) :=
      Real.continuous_exp.continuousAt
    change Tendsto Real.exp (nhds (0 : ℝ)) (nhds (Real.exp 0)) at hexp0
    simpa only [Real.exp_zero] using hexp0
  have hcomp := hexp.comp harg
  have hfun :
      Tendsto
        (fun n : ℕ => Real.exp (Real.log (b / a) * (1 / (n : ℝ))))
        atTop (nhds (1 : ℝ)) := by
    simpa only [Function.comp_apply] using hcomp
  have heq :
      (fun n : ℕ => Real.exp (Real.log (b / a) * (1 / (n : ℝ)))) =
        q a b := by
    funext n
    unfold q
    change Real.exp (Real.log (b / a) * (1 / (n : ℝ))) =
      (b / a) ^ (1 / (n : ℝ))
    exact (Real.rpow_def_of_pos hba (1 / (n : ℝ))).symm
  rw [← heq]
  exact hfun

theorem gap14 (a b m : ℝ)
    (ha : 0 < a) (hab : a < b) (hm : m ≠ -1) :
    Tendsto (lowerSum a b m) atTop
        (nhds ((powM b (m + 1) - powM a (m + 1)) / (m + 1))) ↔
      Tendsto
        (fun n => (powM b (m + 1) - powM a (m + 1)) * ratio a b m n)
        atTop (nhds ((powM b (m + 1) - powM a (m + 1)) / (m + 1))) := by
  apply tendsto_congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  simpa [ratio, div_eq_mul_inv, mul_assoc] using
    (gap12 a b m n ha hab hm hn)

theorem gap15 (a b m : ℝ)
    (ha : 0 < a) (hab : a < b) (hm : m ≠ -1) :
    Tendsto
      (fun n => (powM b (m + 1) - powM a (m + 1)) * ratio a b m n)
      atTop (nhds ((powM b (m + 1) - powM a (m + 1)) / (m + 1))) := by
  have hp : m + 1 ≠ 0 := by
    intro h
    apply hm
    linarith only [h]
  have hderiv :
      HasDerivAt (fun x : ℝ => powM x (m + 1)) (m + 1) 1 := by
    simpa [powM] using
      (Real.hasDerivAt_rpow_const (p := m + 1) (Or.inl one_ne_zero))
  have hq_ne : ∀ᶠ n : ℕ in atTop, q a b n ∈ ({1}ᶜ : Set ℝ) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hq1 : 1 < q a b n :=
      (lt_mul_iff_one_lt_right ha).mp (gap1 a b n ha hab hn)
    simpa using ne_of_gt hq1
  have hq_within :
      Tendsto (q a b) atTop (nhdsWithin (1 : ℝ) ({1}ᶜ : Set ℝ)) :=
    tendsto_nhdsWithin_iff.2 ⟨gap13 a b ha hab, hq_ne⟩
  have hslope :
      Tendsto
        (fun n => slope (fun x : ℝ => powM x (m + 1)) 1 (q a b n))
        atTop (nhds (m + 1)) :=
    ((hasDerivAt_iff_tendsto_slope).1 hderiv).comp hq_within
  have hinv :
      Tendsto
        (fun n => 1 /
          slope (fun x : ℝ => powM x (m + 1)) 1 (q a b n))
        atTop (nhds (1 / (m + 1))) :=
    ((continuousAt_const.div continuousAt_id hp).tendsto.comp hslope)
  have hmul :=
    (tendsto_const_nhds.mul hinv :
      Tendsto
        (fun n =>
          (powM b (m + 1) - powM a (m + 1)) *
            (1 / slope (fun x : ℝ => powM x (m + 1)) 1 (q a b n)))
        atTop
        (nhds
          ((powM b (m + 1) - powM a (m + 1)) *
            (1 / (m + 1)))))
  simpa [ratio, slope, powM, one_div, inv_div, div_eq_mul_inv,
    mul_comm, mul_left_comm, mul_assoc] using hmul

theorem gap16 (a b m : ℝ)
    (ha : 0 < a) (hab : a < b) (hm : m ≠ -1) :
    Tendsto (lowerSum a b m) atTop
      (nhds ((powM b (m + 1) - powM a (m + 1)) / (m + 1))) := by
  exact (gap14 a b m ha hab hm).2 (gap15 a b m ha hab hm)

theorem gap17 (a b m : ℝ)
    (ha : 0 < a) (hab : a < b) (hm : m ≠ -1) :
    (∫ x in a..b, powM x m) =
      (powM b (m + 1) - powM a (m + 1)) / (m + 1) := by
  have hp : m + 1 ≠ 0 := by
    intro h
    apply hm
    linarith only [h]
  have hpos : ∀ x ∈ Set.uIcc a b, 0 < x := by
    intro x hx
    rw [Set.uIcc_of_le hab.le] at hx
    exact lt_of_lt_of_le ha hx.1
  have hderiv :
      ∀ x ∈ Set.uIcc a b,
        HasDerivAt
          (fun y : ℝ => powM y (m + 1) / (m + 1))
          (powM x m) x := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (hpos x hx)
    have hd :=
      (Real.hasDerivAt_rpow_const (p := m + 1) (Or.inl hx0)).div_const
        (m + 1)
    simpa [powM, hp] using hd
  have hcont :
      ContinuousOn (fun x : ℝ => powM x m) (Set.uIcc a b) := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (hpos x hx)
    simpa [powM] using
      (Real.hasDerivAt_rpow_const (p := m) (Or.inl hx0)).continuousAt.continuousWithinAt
  have hint :
      IntervalIntegrable (fun x : ℝ => powM x m) MeasureTheory.volume a b :=
    hcont.intervalIntegrable
  have hFTC :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  calc
    (∫ x in a..b, powM x m) =
        powM b (m + 1) / (m + 1) -
          powM a (m + 1) / (m + 1) := by
      simpa using hFTC
    _ = (powM b (m + 1) - powM a (m + 1)) / (m + 1) := by
      ring

end
end ProofGap.Exercise2190
