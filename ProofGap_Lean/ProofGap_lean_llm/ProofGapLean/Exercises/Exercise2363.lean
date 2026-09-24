import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise2363
noncomputable section

open Filter MeasureTheory

def integrand (m n x : ℝ) : ℝ :=
  Real.rpow x m / (1 + Real.rpow x n)

def NearZeroIntegrable (m n : ℝ) : Prop :=
  IntegrableOn (integrand m n) (Set.Ioc (0 : ℝ) 1)
def TailIntegrable (m n : ℝ) : Prop :=
  IntegrableOn (integrand m n) (Set.Ioi (1 : ℝ))
def FullIntegrable (m n : ℝ) : Prop :=
  IntegrableOn (integrand m n) (Set.Ioi (0 : ℝ))

def zeroNormalized (m n x : ℝ) : ℝ :=
  Real.rpow x (-m) * integrand m n x
def infinityNormalized (m n x : ℝ) : ℝ :=
  Real.rpow x (n - m) * integrand m n x

private theorem integrand_continuousOn_pos (m n : ℝ) :
    ContinuousOn (integrand m n) (Set.Ioi (0 : ℝ)) := by
  intro x hx
  have hm := continuousAt_id.rpow_const (Or.inl hx.ne') (p := m)
  have hn := continuousAt_id.rpow_const (Or.inl hx.ne') (p := n)
  unfold integrand
  exact (hm.div (continuousAt_const.add hn) (by
    change 1 + Real.rpow x n ≠ 0
    have hp : 0 < Real.rpow x n := Real.rpow_pos_of_pos hx n
    exact ne_of_gt (by linarith))).continuousWithinAt

private theorem near_bounds {m n x : ℝ} (hn : 0 < n)
    (hx : x ∈ Set.Ioc (0 : ℝ) 1) :
    0 ≤ integrand m n x ∧ integrand m n x ≤ Real.rpow x m ∧
      Real.rpow x m ≤ 2 * integrand m n x := by
  have hxp : 0 < x := hx.1
  have hpm : 0 < Real.rpow x m := Real.rpow_pos_of_pos hxp m
  have hpn : 0 < Real.rpow x n := Real.rpow_pos_of_pos hxp n
  have hpn1 : Real.rpow x n ≤ 1 := Real.rpow_le_one hxp.le hx.2 hn.le
  have hden : 0 < 1 + Real.rpow x n := by positivity
  unfold integrand
  constructor
  · positivity
  constructor
  · apply (div_le_iff₀ hden).2
    nlinarith [mul_nonneg hpm.le hpn.le]
  · rw [show 2 * (Real.rpow x m / (1 + Real.rpow x n)) =
      (2 * Real.rpow x m) / (1 + Real.rpow x n) by ring]
    apply (le_div_iff₀ hden).2
    nlinarith [mul_nonneg hpm.le (sub_nonneg.mpr hpn1)]

private theorem tail_bounds {m n x : ℝ} (hn : 0 < n)
    (hx : x ∈ Set.Ioi (1 : ℝ)) :
    0 ≤ integrand m n x ∧ integrand m n x ≤ Real.rpow x (m - n) ∧
      Real.rpow x (m - n) ≤ 2 * integrand m n x := by
  have hxp : 0 < x := zero_lt_one.trans hx
  have hpm : 0 < Real.rpow x m := Real.rpow_pos_of_pos hxp m
  have hpn : 0 < Real.rpow x n := Real.rpow_pos_of_pos hxp n
  have hpn1 : 1 ≤ Real.rpow x n := Real.one_le_rpow hx.le hn.le
  have hden : 0 < 1 + Real.rpow x n := by positivity
  have hsub : Real.rpow x (m - n) = Real.rpow x m / Real.rpow x n :=
    Real.rpow_sub hxp m n
  unfold integrand
  constructor
  · positivity
  constructor
  · rw [hsub]
    exact div_le_div_of_nonneg_left hpm.le hpn (by linarith)
  · rw [hsub]
    rw [show 2 * (Real.rpow x m / (1 + Real.rpow x n)) =
      (2 * Real.rpow x m) / (1 + Real.rpow x n) by ring]
    apply (div_le_div_iff₀ hpn hden).2
    nlinarith [mul_nonneg hpm.le (sub_nonneg.mpr hpn1)]

theorem gap1 (m n : ℝ) :
    FullIntegrable m n ↔ NearZeroIntegrable m n ∧ TailIntegrable m n := by
  unfold FullIntegrable NearZeroIntegrable TailIntegrable
  have hset : Set.Ioc (0 : ℝ) 1 ∪ Set.Ioi (1 : ℝ) = Set.Ioi 0 := by
    ext x
    simp only [Set.mem_union, Set.mem_Ioc, Set.mem_Ioi]
    constructor
    · rintro (hx | hx) <;> linarith
    · intro hx
      by_cases h : x ≤ 1
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr (lt_of_not_ge h)
  rw [← hset, integrableOn_union]

theorem gap2 (m n : ℝ) (hn : 0 < n) :
    Tendsto (zeroNormalized m n)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have hr : Tendsto (fun x : ℝ => Real.rpow x n)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hc := (Real.continuousAt_rpow_const 0 n (Or.inr hn.le)).tendsto
    simpa [Real.zero_rpow hn.ne'] using hc.mono_left inf_le_left
  have hlim : Tendsto (fun x : ℝ => 1 / (1 + Real.rpow x n))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    have hone : Tendsto (fun _ : ℝ => (1 : ℝ))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := tendsto_const_nhds
    simpa only [Pi.div_apply, Pi.add_apply, Pi.one_apply, add_zero, div_one] using
      hone.div (hone.add hr) (by norm_num)
  have heq : zeroNormalized m n =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun x : ℝ => 1 / (1 + Real.rpow x n)) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hxm0 : Real.rpow x m ≠ 0 :=
      (Real.rpow_pos_of_pos hx m).ne'
    have hneg : Real.rpow x (-m) = (Real.rpow x m)⁻¹ := by
      exact Real.rpow_neg hx.le m
    unfold zeroNormalized integrand
    rw [hneg]
    field_simp [hxm0]
  exact hlim.congr' heq.symm

theorem gap3 (m n : ℝ) (hn : 0 < n) :
    NearZeroIntegrable m n ↔ -1 < m := by
  unfold NearZeroIntegrable
  have hpow_iff :
      IntegrableOn (fun x : ℝ => Real.rpow x m) (Set.Ioc (0 : ℝ) 1) ↔
        -1 < m := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one
  have hpow_meas : AEStronglyMeasurable (fun x : ℝ => Real.rpow x m)
      (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    (continuousOn_id.rpow_const (fun x hx => Or.inl hx.1.ne')).aestronglyMeasurable
      measurableSet_Ioc
  have hint_meas : AEStronglyMeasurable (integrand m n)
      (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    ((integrand_continuousOn_pos m n).mono fun x hx => hx.1).aestronglyMeasurable
      measurableSet_Ioc
  constructor
  · intro hint
    have hscaled : IntegrableOn (fun x => 2 * integrand m n x)
        (Set.Ioc (0 : ℝ) 1) := hint.const_mul 2
    have hpow : IntegrableOn (fun x : ℝ => Real.rpow x m)
        (Set.Ioc (0 : ℝ) 1) := by
      apply hscaled.integrable.mono' hpow_meas
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      have hb := near_bounds (m := m) (n := n) hn hx
      have hpow_nonneg : 0 ≤ Real.rpow x m := Real.rpow_nonneg hx.1.le m
      rw [Real.norm_eq_abs, abs_of_nonneg hpow_nonneg]
      exact hb.2.2
    exact hpow_iff.mp hpow
  · intro hm
    have hpow := hpow_iff.mpr hm
    apply hpow.integrable.mono' hint_meas
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hb := near_bounds (m := m) (n := n) hn hx
    rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
    exact hb.2.1

theorem gap4 (m n : ℝ) (hn : 0 < n) :
    Tendsto (infinityNormalized m n) atTop (nhds 1) := by
  have hr : Tendsto (fun x : ℝ => Real.rpow x (-n)) atTop (nhds 0) :=
    tendsto_rpow_neg_atTop hn
  have hlim : Tendsto (fun x : ℝ => 1 / (1 + Real.rpow x (-n)))
      atTop (nhds 1) := by
    have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    simpa only [Pi.div_apply, Pi.add_apply, Pi.one_apply, add_zero, div_one] using
      hone.div (hone.add hr) (by norm_num)
  have heq : infinityNormalized m n =ᶠ[atTop]
      (fun x : ℝ => 1 / (1 + Real.rpow x (-n))) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hxn0 : Real.rpow x n ≠ 0 :=
      (Real.rpow_pos_of_pos hx n).ne'
    have hmul : Real.rpow x (n - m) * Real.rpow x m = Real.rpow x n := by
      calc
        Real.rpow x (n - m) * Real.rpow x m =
            Real.rpow x ((n - m) + m) := (Real.rpow_add hx _ _).symm
        _ = Real.rpow x n := by congr 1 <;> ring
    have hneg : Real.rpow x (-n) = (Real.rpow x n)⁻¹ := by
      exact Real.rpow_neg hx.le n
    unfold infinityNormalized integrand
    rw [show Real.rpow x (n - m) *
        (Real.rpow x m / (1 + Real.rpow x n)) =
          (Real.rpow x (n - m) * Real.rpow x m) /
            (1 + Real.rpow x n) by ring]
    rw [hmul, hneg]
    field_simp [hxn0]
    ring
  exact hlim.congr' heq.symm

theorem gap5 (m n : ℝ) (hn : 0 < n) :
    TailIntegrable m n ↔ 1 < n - m := by
  unfold TailIntegrable
  have hpow_iff :
      IntegrableOn (fun x : ℝ => Real.rpow x (m - n)) (Set.Ioi (1 : ℝ)) ↔
        1 < n - m := by
    have hbase :
        IntegrableOn (fun x : ℝ => Real.rpow x (m - n)) (Set.Ioi (1 : ℝ)) ↔
          m - n < -1 := by
      exact integrableOn_Ioi_rpow_iff zero_lt_one
    exact hbase.trans (by constructor <;> intro h <;> linarith)
  have hpow_meas : AEStronglyMeasurable
      (fun x : ℝ => Real.rpow x (m - n))
      (MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))) :=
    (continuousOn_id.rpow_const (fun x hx =>
      Or.inl (ne_of_gt (zero_lt_one.trans hx)))).aestronglyMeasurable measurableSet_Ioi
  have hint_meas : AEStronglyMeasurable (integrand m n)
      (MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))) :=
    ((integrand_continuousOn_pos m n).mono
      (show Set.Ioi (1 : ℝ) ⊆ Set.Ioi (0 : ℝ) by
        intro x hx
        exact zero_lt_one.trans (Set.mem_Ioi.mp hx))).aestronglyMeasurable measurableSet_Ioi
  constructor
  · intro hint
    have hscaled : IntegrableOn (fun x => 2 * integrand m n x)
        (Set.Ioi (1 : ℝ)) := hint.const_mul 2
    have hpow : IntegrableOn (fun x : ℝ => Real.rpow x (m - n))
        (Set.Ioi (1 : ℝ)) := by
      apply hscaled.integrable.mono' hpow_meas
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hb := tail_bounds (m := m) (n := n) hn hx
      have hpow_nonneg : 0 ≤ Real.rpow x (m - n) :=
        Real.rpow_nonneg (zero_lt_one.trans hx).le _
      rw [Real.norm_eq_abs, abs_of_nonneg hpow_nonneg]
      exact hb.2.2
    exact hpow_iff.mp hpow
  · intro hmn
    have hpow := hpow_iff.mpr hmn
    apply hpow.integrable.mono' hint_meas
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hb := tail_bounds (m := m) (n := n) hn hx
    rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
    exact hb.2.1

theorem gap6 (m n : ℝ) (hn : 0 < n) :
    (-1 < m ∧ 1 < n - m) ↔ FullIntegrable m n := by
  constructor
  · rintro ⟨hm, htail⟩
    exact (gap1 m n).mpr ⟨(gap3 m n hn).mpr hm, (gap5 m n hn).mpr htail⟩
  · intro hfull
    obtain ⟨hzero, htail⟩ := (gap1 m n).mp hfull
    exact ⟨(gap3 m n hn).mp hzero, (gap5 m n hn).mp htail⟩

end
end ProofGap.Exercise2363
