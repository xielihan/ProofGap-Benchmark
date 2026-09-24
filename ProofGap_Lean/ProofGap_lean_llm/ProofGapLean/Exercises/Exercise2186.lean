import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise2186
noncomputable section

open Filter
open scoped BigOperators Interval

def h (n : ℕ) : ℝ := 1 / (n : ℝ)
def aPow (a x : ℝ) : ℝ := Real.rpow a x
def riemannSum (a : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, h n * aPow a ((i : ℝ) * h n)
def differenceQuotient (a : ℝ) (n : ℕ) : ℝ :=
  (a - 1) / ((aPow a (1 / (n : ℝ)) - 1) / (1 / (n : ℝ)))

private theorem rpow_mesh_facts (a : ℝ) (ha : 0 < a) (ha1 : a ≠ 1)
    (n : ℕ) (hn : 0 < n) :
    (n : ℝ) ≠ 0 ∧ Real.log a ≠ 0 ∧
      aPow a (h n) ≠ 1 ∧ (aPow a (h n)) ^ n = a := by
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
  have hlog : Real.log a ≠ 0 := by
    intro hzero
    apply ha1
    rw [← Real.exp_log ha, hzero, Real.exp_zero]
  have hh : h n ≠ 0 := by
    simp [h, hnR]
  have hrpos : 0 < aPow a (h n) := by
    exact Real.rpow_pos_of_pos ha _
  have hr : aPow a (h n) ≠ 1 := by
    intro heq
    have hexp :
        Real.exp (Real.log a * h n) = Real.exp 0 := by
      simpa [aPow, Real.rpow_def_of_pos ha] using heq
    have hzero : Real.log a * h n = 0 := Real.exp_injective hexp
    exact (mul_ne_zero hlog hh) hzero
  have hhn : h n * (n : ℝ) = 1 := by
    simp [h, hnR]
  have hcast :
      (aPow a (h n)) ^ (n : ℝ) = (aPow a (h n)) ^ n := by
    exact Real.rpow_natCast (aPow a (h n)) n
  have hrmul :
      aPow a (h n * (n : ℝ)) =
        (aPow a (h n)) ^ (n : ℝ) := by
    simpa only [aPow] using
      (Real.rpow_mul ha.le (h n) (n : ℝ))
  have hrn : (aPow a (h n)) ^ n = a := by
    calc
      (aPow a (h n)) ^ n = (aPow a (h n)) ^ (n : ℝ) := hcast.symm
      _ = aPow a (h n * (n : ℝ)) := hrmul.symm
      _ = aPow a 1 := by rw [hhn]
      _ = a := by
        simp [aPow, Real.rpow_def_of_pos ha, Real.exp_log ha]
  exact ⟨hnR, hlog, hr, hrn⟩

theorem gap1 (a : ℝ) (ha : 0 < a) (ha1 : a ≠ 1)
    (n : ℕ) (hn : 0 < n) :
    riemannSum a n =
      ∑ i ∈ Finset.range n, h n * aPow a ((i : ℝ) * h n) := by
  rfl

theorem gap2 (a : ℝ) (ha : 0 < a) (ha1 : a ≠ 1)
    (n : ℕ) (hn : 0 < n) :
    (∑ i ∈ Finset.range n, h n * aPow a ((i : ℝ) * h n)) =
      h n * (a - 1) / (aPow a (h n) - 1) := by
  let r : ℝ := aPow a (h n)
  have hfacts := rpow_mesh_facts a ha ha1 n hn
  have hr : r ≠ 1 := by
    simpa [r] using hfacts.2.2.1
  have hrn : r ^ n = a := by
    simpa [r] using hfacts.2.2.2
  have hterm (i : ℕ) : aPow a ((i : ℝ) * h n) = r ^ i := by
    have hrpow :
        aPow a (h n * (i : ℝ)) =
          (aPow a (h n)) ^ (i : ℝ) := by
      simpa only [aPow] using
        (Real.rpow_mul ha.le (h n) (i : ℝ))
    have hcast :
        (aPow a (h n)) ^ (i : ℝ) =
          (aPow a (h n)) ^ i := by
      exact Real.rpow_natCast (aPow a (h n)) i
    calc
      aPow a ((i : ℝ) * h n) = aPow a (h n * (i : ℝ)) := by
        rw [mul_comm]
      _ = (aPow a (h n)) ^ (i : ℝ) := hrpow
      _ = (aPow a (h n)) ^ i := hcast
      _ = r ^ i := by rfl
  have hgeom : ∀ m : ℕ,
      (∑ i ∈ Finset.range m, r ^ i) * (r - 1) = r ^ m - 1 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [Finset.sum_range_succ, pow_succ, add_mul, ih]
        ring
  calc
    (∑ i ∈ Finset.range n, h n * aPow a ((i : ℝ) * h n)) =
        h n * (∑ i ∈ Finset.range n, r ^ i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hterm i]
    _ = h n * ((a - 1) / (r - 1)) := by
      congr 1
      apply (eq_div_iff (sub_ne_zero.mpr hr)).2
      simpa [hrn] using hgeom n
    _ = h n * (a - 1) / (aPow a (h n) - 1) := by
      simp only [r]
      ring

theorem gap3 (a : ℝ) (ha : 0 < a) (ha1 : a ≠ 1)
    (n : ℕ) (hn : 0 < n) :
    h n * (a - 1) / (aPow a (h n) - 1) =
      (a - 1) / ((n : ℝ) * (aPow a (1 / (n : ℝ)) - 1)) := by
  have hfacts := rpow_mesh_facts a ha ha1 n hn
  have hnR : (n : ℝ) ≠ 0 := hfacts.1
  have hr : aPow a (1 / (n : ℝ)) ≠ 1 := by
    simpa [h] using hfacts.2.2.1
  simp only [h]
  field_simp [hnR, sub_ne_zero.mpr hr]
  <;> ring

theorem gap4 (a : ℝ) (ha : 0 < a) (ha1 : a ≠ 1)
    (n : ℕ) (hn : 0 < n) :
    riemannSum a n =
      (a - 1) / ((n : ℝ) * (aPow a (1 / (n : ℝ)) - 1)) := by
  calc
    riemannSum a n =
        ∑ i ∈ Finset.range n, h n * aPow a ((i : ℝ) * h n) :=
      gap1 a ha ha1 n hn
    _ = h n * (a - 1) / (aPow a (h n) - 1) :=
      gap2 a ha ha1 n hn
    _ = (a - 1) / ((n : ℝ) * (aPow a (1 / (n : ℝ)) - 1)) :=
      gap3 a ha ha1 n hn

theorem gap5 (a : ℝ) (ha : 0 < a) (ha1 : a ≠ 1) :
    Tendsto (riemannSum a) atTop (nhds ((a - 1) / Real.log a)) ↔
      Tendsto (differenceQuotient a) atTop (nhds ((a - 1) / Real.log a)) := by
  have heq : riemannSum a =ᶠ[atTop] differenceQuotient a := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hfacts := rpow_mesh_facts a ha ha1 n hn
    have hnR : (n : ℝ) ≠ 0 := hfacts.1
    have hr : aPow a (1 / (n : ℝ)) ≠ 1 := by
      simpa [h] using hfacts.2.2.1
    rw [gap4 a ha ha1 n hn]
    unfold differenceQuotient
    field_simp [hnR, sub_ne_zero.mpr hr]
    <;> ring
  constructor
  · intro hlim
    exact hlim.congr' heq
  · intro hlim
    exact hlim.congr' heq.symm

theorem gap6 (a : ℝ) (ha : 0 < a) (ha1 : a ≠ 1) :
    Tendsto (differenceQuotient a) atTop (nhds ((a - 1) / Real.log a)) := by
  have hlog : Real.log a ≠ 0 :=
    (rpow_mesh_facts a ha ha1 1 (Nat.zero_lt_succ 0)).2.1
  have hlinDeriv :
      HasDerivAt (fun x : ℝ => Real.log a * x) (Real.log a) 0 := by
    simpa using (hasDerivAt_id 0).const_mul (Real.log a)
  have hderiv : HasDerivAt (fun x : ℝ => aPow a x) (Real.log a) 0 := by
    simpa [aPow, Real.rpow_def_of_pos ha, Function.comp_def, mul_comm] using
      (Real.hasDerivAt_exp (Real.log a * 0)).comp 0 hlinDeriv
  have hslope :
      Tendsto (slope (fun x : ℝ => aPow a x) 0)
        (nhdsWithin 0 {0}ᶜ) (nhds (Real.log a)) :=
    (hasDerivAt_iff_tendsto_slope).mp hderiv
  have hseq0 :
      Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (nhds 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hseq :
      Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop
        (nhdsWithin 0 {0}ᶜ) := by
    refine tendsto_nhdsWithin_iff.2 ⟨hseq0, ?_⟩
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    change (1 / (n : ℝ)) ≠ 0
    exact one_div_ne_zero (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn))
  have hslopeSeq :
      Tendsto
        (slope (fun x : ℝ => aPow a x) 0 ∘
          fun n : ℕ => 1 / (n : ℝ))
        atTop (nhds (Real.log a)) :=
    hslope.comp hseq
  have ha0 : aPow a 0 = 1 := by
    simp [aPow, Real.rpow_def_of_pos ha]
  have hquot :
      Tendsto
        (fun n : ℕ =>
          (aPow a (1 / (n : ℝ)) - 1) / (1 / (n : ℝ)))
        atTop (nhds (Real.log a)) := by
    apply hslopeSeq.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    simp only [Function.comp_apply]
    unfold slope
    change
      (1 / (n : ℝ) - 0)⁻¹ *
          (aPow a (1 / (n : ℝ)) - aPow a 0) =
        (aPow a (1 / (n : ℝ)) - 1) / (1 / (n : ℝ))
    rw [ha0]
    simp only [sub_zero, div_eq_mul_inv]
    ring
  have hconst :
      Tendsto (fun _ : ℕ => a - 1) atTop (nhds (a - 1)) :=
    tendsto_const_nhds
  simpa only [differenceQuotient] using hconst.div hquot hlog

theorem gap7 (a : ℝ) (ha : 0 < a) (ha1 : a ≠ 1) :
    Tendsto (riemannSum a) atTop (nhds ((a - 1) / Real.log a)) := by
  exact (gap5 a ha ha1).mpr (gap6 a ha ha1)

theorem gap8 (a : ℝ) (ha : 0 < a) (ha1 : a ≠ 1) :
    (∫ x in (0 : ℝ)..1, aPow a x) = (a - 1) / Real.log a := by
  have hlog : Real.log a ≠ 0 :=
    (rpow_mesh_facts a ha ha1 1 (Nat.zero_lt_succ 0)).2.1
  have hlin : Continuous (fun x : ℝ => Real.log a * x) :=
    continuous_const.mul continuous_id
  have hcont : Continuous (fun x : ℝ => aPow a x) := by
    simpa [aPow, Real.rpow_def_of_pos ha, Function.comp_def] using
      Real.continuous_exp.comp hlin
  have hbase (x : ℝ) :
      HasDerivAt (fun y : ℝ => aPow a y)
        (Real.log a * aPow a x) x := by
    have hlinDeriv :
        HasDerivAt (fun y : ℝ => Real.log a * y) (Real.log a) x := by
      simpa using (hasDerivAt_id x).const_mul (Real.log a)
    simpa [aPow, Real.rpow_def_of_pos ha, Function.comp_def, mul_comm] using
      (Real.hasDerivAt_exp (Real.log a * x)).comp x hlinDeriv
  have hanti (x : ℝ) :
      HasDerivAt (fun y : ℝ => aPow a y / Real.log a)
        (aPow a x) x := by
    convert (hbase x).div_const (Real.log a) using 1
    field_simp [hlog]
  have hFTC :
      (∫ x in (0 : ℝ)..1, aPow a x) =
        aPow a 1 / Real.log a - aPow a 0 / Real.log a := by
    exact intervalIntegral.integral_deriv_eq_sub'
      (fun y : ℝ => aPow a y / Real.log a)
      (funext fun x => (hanti x).deriv)
      (fun x _ => (hanti x).differentiableAt)
      hcont.continuousOn
  have ha0 : aPow a 0 = 1 := by
    simp [aPow, Real.rpow_def_of_pos ha]
  have haone : aPow a 1 = a := by
    simp [aPow, Real.rpow_def_of_pos ha, Real.exp_log ha]
  calc
    (∫ x in (0 : ℝ)..1, aPow a x) =
        aPow a 1 / Real.log a - aPow a 0 / Real.log a := hFTC
    _ = (a - 1) / Real.log a := by
      rw [haone, ha0]
      field_simp [hlog]
      <;> ring

theorem gap9 (a : ℝ) (ha : 0 < a) (ha1 : a = 1) :
    (∫ x in (0 : ℝ)..1, aPow a x) = 1 := by
  subst a
  simp [aPow]

end
end ProofGap.Exercise2186
