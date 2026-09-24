import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise2366
noncomputable section

open Filter MeasureTheory

def integrand (m n x : ℝ) : ℝ :=
  Real.rpow x m * Real.arctan x / (2 + Real.rpow x n)
def zeroNormalized (m n x : ℝ) : ℝ :=
  Real.rpow x (-m - 1) * integrand m n x
def zeroModel (x : ℝ) : ℝ := (1 / 2 : ℝ) * (Real.arctan x / x)
def infinityNormalized (m n x : ℝ) : ℝ :=
  Real.rpow x (n - m) * integrand m n x
def infinityModel (n x : ℝ) : ℝ :=
  Real.rpow x n * Real.arctan x / (2 + Real.rpow x n)
def NearZeroIntegrable (m n : ℝ) : Prop :=
  IntegrableOn (integrand m n) (Set.Ioc (0 : ℝ) 1)
def TailIntegrable (m n : ℝ) : Prop :=
  IntegrableOn (integrand m n) (Set.Ioi (1 : ℝ))
def FullIntegrable (m n : ℝ) : Prop :=
  IntegrableOn (integrand m n) (Set.Ioi (0 : ℝ))

private theorem arctan_le_self_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    Real.arctan x ≤ x := by
  let f : ℝ → ℝ := fun u => u - Real.arctan u
  have hf (u : ℝ) : HasDerivAt f (u ^ 2 / (1 + u ^ 2)) u := by
    dsimp only [f]
    convert (hasDerivAt_id u).sub (Real.hasDerivAt_arctan u) using 1
    field_simp [show (1 + u ^ 2 : ℝ) ≠ 0 by positivity]
    ring
  have hmono : Monotone f := by
    apply monotone_of_deriv_nonneg
    · exact fun u => (hf u).differentiableAt
    · intro u
      rw [(hf u).deriv]
      positivity
  have h := hmono hx
  simpa [f] using h

private theorem half_self_le_arctan_of_mem_Ioc {x : ℝ}
    (hx : x ∈ Set.Ioc (0 : ℝ) 1) : x / 2 ≤ Real.arctan x := by
  let f : ℝ → ℝ := fun u => Real.arctan u - u / 2
  have hf (u : ℝ) :
      HasDerivAt f (1 / (1 + u ^ 2) - 1 / 2) u := by
    dsimp only [f]
    exact (Real.hasDerivAt_arctan u).sub ((hasDerivAt_id u).div_const 2)
  have hmono : MonotoneOn f (Set.Icc (0 : ℝ) 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) 1) ?_ ?_ ?_
    · intro u hu
      exact (hf u).continuousAt.continuousWithinAt
    · intro u hu
      exact (hf u).differentiableAt.differentiableWithinAt
    · intro u hu
      rw [(hf u).deriv]
      have hu' : u ∈ Set.Icc (0 : ℝ) 1 := interior_subset hu
      have hden : 0 < 1 + u ^ 2 := by positivity
      apply sub_nonneg.mpr
      apply (le_div_iff₀ hden).2
      nlinarith [sq_nonneg u, mul_nonneg (sub_nonneg.mpr hu'.2) hu'.1]
  have h := hmono (by simp) ⟨hx.1.le, hx.2⟩ hx.1.le
  simpa [f] using h

private theorem near_arctan_bounds {x : ℝ} (hx : x ∈ Set.Ioc (0 : ℝ) 1) :
    x / 2 ≤ Real.arctan x ∧ Real.arctan x ≤ x :=
  ⟨half_self_le_arctan_of_mem_Ioc hx, arctan_le_self_of_nonneg hx.1.le⟩

private theorem tail_arctan_bounds {x : ℝ} (hx : x ∈ Set.Ioi (1 : ℝ)) :
    (1 / 2 : ℝ) ≤ Real.arctan x ∧ Real.arctan x ≤ 2 := by
  have hl : Real.arctan 1 ≤ Real.arctan x := Real.arctan_mono hx.le
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hu := Real.arctan_lt_pi_div_two x
  rw [Real.arctan_one] at hl
  constructor <;> linarith [Real.pi_lt_four]

private theorem integrand_continuousOn_pos (m n : ℝ) :
    ContinuousOn (integrand m n) (Set.Ioi (0 : ℝ)) := by
  intro x hx
  have hm := continuousAt_id.rpow_const (Or.inl hx.ne') (p := m)
  have hn := continuousAt_id.rpow_const (Or.inl hx.ne') (p := n)
  unfold integrand
  exact ((hm.mul Real.continuous_arctan.continuousAt).div
    (continuousAt_const.add hn) (by
      change 2 + Real.rpow x n ≠ 0
      have hp : 0 < Real.rpow x n := Real.rpow_pos_of_pos hx n
      exact ne_of_gt (by linarith))).continuousWithinAt

private theorem near_power_bounds {m n x : ℝ} (hn : 0 ≤ n)
    (hx : x ∈ Set.Ioc (0 : ℝ) 1) :
    0 ≤ integrand m n x ∧
      integrand m n x ≤ Real.rpow x (m + 1) ∧
      Real.rpow x (m + 1) ≤ 6 * integrand m n x := by
  have hxp : 0 < x := hx.1
  let P := Real.rpow x m
  let q := Real.rpow x n
  let A := Real.arctan x
  let R := Real.rpow x (m + 1)
  have hP : 0 < P := Real.rpow_pos_of_pos hxp m
  have hq : 0 < q := Real.rpow_pos_of_pos hxp n
  have hq1 : q ≤ 1 := Real.rpow_le_one hxp.le hx.2 hn
  have hA := near_arctan_bounds hx
  have hR : R = P * x := by
    dsimp only [R, P]
    calc
      Real.rpow x (m + 1) = Real.rpow x m * Real.rpow x 1 :=
        Real.rpow_add hxp m 1
      _ = Real.rpow x m * x := by
        apply congrArg (fun z : ℝ => Real.rpow x m * z)
        exact Real.rpow_one x
  have hR0 : 0 ≤ R := Real.rpow_nonneg hxp.le _
  have hden : 0 < 2 + q := by positivity
  have hden1 : 1 ≤ 2 + q := by linarith
  have hden3 : 2 + q ≤ 3 := by linarith
  unfold integrand
  change 0 ≤ P * A / (2 + q) ∧
    P * A / (2 + q) ≤ R ∧ R ≤ 6 * (P * A / (2 + q))
  constructor
  · positivity
  constructor
  · apply (div_le_iff₀ hden).2
    calc
      P * A ≤ P * x := mul_le_mul_of_nonneg_left hA.2 hP.le
      _ = R := hR.symm
      _ ≤ R * (2 + q) := by
        nlinarith [mul_nonneg hR0 (sub_nonneg.mpr hden1)]
  · rw [show 6 * (P * A / (2 + q)) = (6 * (P * A)) / (2 + q) by ring]
    apply (le_div_iff₀ hden).2
    have hhalf : P * (x / 2) ≤ P * A :=
      mul_le_mul_of_nonneg_left hA.1 hP.le
    calc
      R * (2 + q) ≤ R * 3 := mul_le_mul_of_nonneg_left hden3 hR0
      _ = 6 * (P * (x / 2)) := by rw [hR]; ring
      _ ≤ 6 * (P * A) := mul_le_mul_of_nonneg_left hhalf (by norm_num)

private theorem tail_power_bounds {m n x : ℝ} (hn : 0 ≤ n)
    (hx : x ∈ Set.Ioi (1 : ℝ)) :
    0 ≤ integrand m n x ∧
      integrand m n x ≤ 2 * Real.rpow x (m - n) ∧
      Real.rpow x (m - n) ≤ 6 * integrand m n x := by
  have hxp : 0 < x := zero_lt_one.trans hx
  let P := Real.rpow x m
  let q := Real.rpow x n
  let A := Real.arctan x
  let R := Real.rpow x (m - n)
  have hP : 0 < P := Real.rpow_pos_of_pos hxp m
  have hq : 0 < q := Real.rpow_pos_of_pos hxp n
  have hq1 : 1 ≤ q := Real.one_le_rpow hx.le hn
  have hA := tail_arctan_bounds hx
  have hR : R = P / q := by
    exact Real.rpow_sub hxp m n
  have hden : 0 < 2 + q := by positivity
  have hqden : q ≤ 2 + q := by linarith
  have hden3q : 2 + q ≤ 3 * q := by linarith
  unfold integrand
  change 0 ≤ P * A / (2 + q) ∧
    P * A / (2 + q) ≤ 2 * R ∧ R ≤ 6 * (P * A / (2 + q))
  constructor
  · positivity
  constructor
  · have hPA : P * A ≤ 2 * P := by
      nlinarith [mul_nonneg hP.le (sub_nonneg.mpr hA.2)]
    calc
      P * A / (2 + q) ≤ (2 * P) / (2 + q) :=
        div_le_div_of_nonneg_right hPA hden.le
      _ ≤ (2 * P) / q :=
        div_le_div_of_nonneg_left (by positivity) hq hqden
      _ = 2 * R := by rw [hR]; ring
  · rw [hR]
    rw [show 6 * (P * A / (2 + q)) = (6 * (P * A)) / (2 + q) by ring]
    apply (div_le_div_iff₀ hq hden).2
    have hhalf : P * (1 / 2 : ℝ) ≤ P * A :=
      mul_le_mul_of_nonneg_left hA.1 hP.le
    calc
      P * (2 + q) ≤ P * (3 * q) :=
        mul_le_mul_of_nonneg_left hden3q hP.le
      _ = (6 * (P * (1 / 2 : ℝ))) * q := by ring
      _ ≤ (6 * (P * A)) * q :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hhalf (by norm_num)) hq.le

private theorem near_integrable_iff (m n : ℝ) (hn : 0 ≤ n) :
    IntegrableOn (integrand m n) (Set.Ioc (0 : ℝ) 1) ↔ -2 < m := by
  have hpow_iff :
      IntegrableOn (fun x : ℝ => Real.rpow x (m + 1)) (Set.Ioc (0 : ℝ) 1) ↔
        -2 < m := by
    have hbase :
        IntegrableOn (fun x : ℝ => Real.rpow x (m + 1)) (Set.Ioc (0 : ℝ) 1) ↔
          -1 < m + 1 := by
      rw [integrableOn_Ioc_iff_integrableOn_Ioo]
      exact intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one
    exact hbase.trans (by constructor <;> intro h <;> linarith)
  have hpow_meas : AEStronglyMeasurable (fun x : ℝ => Real.rpow x (m + 1))
      (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    (continuousOn_id.rpow_const (fun x hx => Or.inl hx.1.ne')).aestronglyMeasurable
      measurableSet_Ioc
  have hint_meas : AEStronglyMeasurable (integrand m n)
      (MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) 1)) :=
    ((integrand_continuousOn_pos m n).mono fun x hx => hx.1).aestronglyMeasurable
      measurableSet_Ioc
  constructor
  · intro hint
    have hscaled : IntegrableOn (fun x => 6 * integrand m n x)
        (Set.Ioc (0 : ℝ) 1) := hint.const_mul 6
    have hpow : IntegrableOn (fun x : ℝ => Real.rpow x (m + 1))
        (Set.Ioc (0 : ℝ) 1) := by
      apply hscaled.integrable.mono' hpow_meas
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      have hb := near_power_bounds (m := m) (n := n) hn hx
      have hpow_nonneg : 0 ≤ Real.rpow x (m + 1) :=
        Real.rpow_nonneg hx.1.le _
      rw [Real.norm_eq_abs, abs_of_nonneg hpow_nonneg]
      exact hb.2.2
    exact hpow_iff.mp hpow
  · intro hm
    have hpow := hpow_iff.mpr hm
    apply hpow.integrable.mono' hint_meas
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hb := near_power_bounds (m := m) (n := n) hn hx
    rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
    exact hb.2.1

private theorem tail_integrable_iff (m n : ℝ) (hn : 0 ≤ n) :
    IntegrableOn (integrand m n) (Set.Ioi (1 : ℝ)) ↔ 1 < n - m := by
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
    have hscaled : IntegrableOn (fun x => 6 * integrand m n x)
        (Set.Ioi (1 : ℝ)) := hint.const_mul 6
    have hpow : IntegrableOn (fun x : ℝ => Real.rpow x (m - n))
        (Set.Ioi (1 : ℝ)) := by
      apply hscaled.integrable.mono' hpow_meas
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      have hb := tail_power_bounds (m := m) (n := n) hn hx
      have hpow_nonneg : 0 ≤ Real.rpow x (m - n) :=
        Real.rpow_nonneg (zero_lt_one.trans hx).le _
      rw [Real.norm_eq_abs, abs_of_nonneg hpow_nonneg]
      exact hb.2.2
    exact hpow_iff.mp hpow
  · intro hmn
    have hpow := hpow_iff.mpr hmn
    have hscaled : IntegrableOn (fun x => 2 * Real.rpow x (m - n))
        (Set.Ioi (1 : ℝ)) := hpow.const_mul 2
    apply hscaled.integrable.mono' hint_meas
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hb := tail_power_bounds (m := m) (n := n) hn hx
    rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
    exact hb.2.1

private theorem arctan_div_tendsto_zero_pos :
    Tendsto (fun t : ℝ => Real.arctan t / t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have h := hasDerivAt_iff_tendsto_slope.mp (Real.hasDerivAt_arctan 0)
  have heq : (fun t : ℝ => Real.arctan t / t) = slope Real.arctan 0 := by
    funext t
    dsimp only [slope]
    simp [div_eq_mul_inv, mul_comm]
  rw [heq]
  have h' : Tendsto (slope Real.arctan 0)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by simpa using h
  apply h'.mono_left
  apply nhdsWithin_mono
  intro x hx
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
  exact (ne_of_gt (Set.mem_Ioi.mp hx))

private theorem zeroModel_tendsto :
    Tendsto zeroModel (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 / 2)) := by
  unfold zeroModel
  have hc : Tendsto (fun _ : ℝ => (1 / 2 : ℝ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 / 2)) := tendsto_const_nhds
  simpa only [Pi.mul_apply, mul_one] using hc.mul arctan_div_tendsto_zero_pos

private theorem zeroNormalized_tendsto (m n : ℝ) (hn : 0 < n) :
    Tendsto (zeroNormalized m n)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 / 2)) := by
  have hr : Tendsto (fun x : ℝ => Real.rpow x n)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hc := (Real.continuousAt_rpow_const 0 n (Or.inr hn.le)).tendsto
    simpa [Real.zero_rpow hn.ne'] using hc.mono_left inf_le_left
  have hden : Tendsto (fun x : ℝ => 2 + Real.rpow x n)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 2) := by
    have hc : Tendsto (fun _ : ℝ => (2 : ℝ))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 2) := tendsto_const_nhds
    simpa only [Pi.add_apply, add_zero] using hc.add hr
  have hlim : Tendsto (fun x : ℝ =>
      (Real.arctan x / x) / (2 + Real.rpow x n))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 / 2)) := by
    simpa only [Pi.div_apply] using
      arctan_div_tendsto_zero_pos.div hden (by norm_num)
  have heq : zeroNormalized m n =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun x : ℝ => (Real.arctan x / x) / (2 + Real.rpow x n)) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hP0 : Real.rpow x m ≠ 0 := (Real.rpow_pos_of_pos hx m).ne'
    have hmul : Real.rpow x (-m - 1) * Real.rpow x m =
        Real.rpow x (-1) := by
      calc
        Real.rpow x (-m - 1) * Real.rpow x m =
            Real.rpow x ((-m - 1) + m) := (Real.rpow_add hx _ _).symm
        _ = Real.rpow x (-1) := by congr 1 <;> ring
    have hnegone : Real.rpow x (-1) = x⁻¹ := by
      exact Real.rpow_neg_one x
    unfold zeroNormalized integrand
    rw [show Real.rpow x (-m - 1) *
        (Real.rpow x m * Real.arctan x / (2 + Real.rpow x n)) =
          (Real.rpow x (-m - 1) * Real.rpow x m) * Real.arctan x /
            (2 + Real.rpow x n) by ring]
    rw [hmul, hnegone]
    field_simp [(Set.mem_Ioi.mp hx).ne', hP0]
  exact hlim.congr' heq.symm

private theorem infinityModel_tendsto (n : ℝ) (hn : 0 < n) :
    Tendsto (infinityModel n) atTop (nhds (Real.pi / 2)) := by
  have hr : Tendsto (fun x : ℝ => Real.rpow x (-n)) atTop (nhds 0) :=
    tendsto_rpow_neg_atTop hn
  have har : Tendsto Real.arctan atTop (nhds (Real.pi / 2)) :=
    Real.tendsto_arctan_atTop.mono_right inf_le_left
  have hden : Tendsto (fun x : ℝ => 2 * Real.rpow x (-n) + 1)
      atTop (nhds 1) := by
    have htwo : Tendsto (fun _ : ℝ => (2 : ℝ)) atTop (nhds 2) :=
      tendsto_const_nhds
    have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    simpa only [Pi.mul_apply, Pi.add_apply, mul_zero, zero_add] using
      htwo.mul hr |>.add hone
  have hlim : Tendsto (fun x : ℝ =>
      Real.arctan x / (2 * Real.rpow x (-n) + 1))
      atTop (nhds (Real.pi / 2)) := by
    simpa only [Pi.div_apply, div_one] using har.div hden one_ne_zero
  have heq : infinityModel n =ᶠ[atTop]
      (fun x : ℝ => Real.arctan x / (2 * Real.rpow x (-n) + 1)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hq0 : Real.rpow x n ≠ 0 := (Real.rpow_pos_of_pos hx n).ne'
    have hneg : Real.rpow x (-n) = (Real.rpow x n)⁻¹ := by
      exact Real.rpow_neg hx.le n
    unfold infinityModel
    rw [hneg]
    field_simp [hq0]
  exact hlim.congr' heq.symm

private theorem infinityNormalized_tendsto (m n : ℝ) (hn : 0 < n) :
    Tendsto (infinityNormalized m n) atTop (nhds (Real.pi / 2)) := by
  have heq : infinityNormalized m n =ᶠ[atTop] infinityModel n := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hmul : Real.rpow x (n - m) * Real.rpow x m = Real.rpow x n := by
      calc
        Real.rpow x (n - m) * Real.rpow x m =
            Real.rpow x ((n - m) + m) := (Real.rpow_add hx _ _).symm
        _ = Real.rpow x n := by congr 1 <;> ring
    unfold infinityNormalized infinityModel integrand
    rw [show Real.rpow x (n - m) *
        (Real.rpow x m * Real.arctan x / (2 + Real.rpow x n)) =
          (Real.rpow x (n - m) * Real.rpow x m) * Real.arctan x /
            (2 + Real.rpow x n) by ring]
    rw [hmul]
  exact (infinityModel_tendsto n hn).congr' heq.symm

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
    Tendsto (zeroNormalized m n) (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 / 2)) ↔
      Tendsto zeroModel (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 / 2)) := by
  constructor
  · intro h
    exact zeroModel_tendsto
  · intro h
    exact zeroNormalized_tendsto m n hn

theorem gap3 :
    Tendsto zeroModel (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 / 2)) := by
  exact zeroModel_tendsto

theorem gap4 (m n : ℝ) (hn : 0 < n) :
    Tendsto (zeroNormalized m n)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 / 2)) := by
  exact zeroNormalized_tendsto m n hn

theorem gap5 (m n : ℝ) (hn : 0 < n) :
    NearZeroIntegrable m n ↔ -2 < m := by
  unfold NearZeroIntegrable
  exact near_integrable_iff m n hn.le

theorem gap6 (m n : ℝ) (hn : 0 < n) :
    Tendsto (infinityNormalized m n) atTop (nhds (Real.pi / 2)) ↔
      Tendsto (infinityModel n) atTop (nhds (Real.pi / 2)) := by
  constructor
  · intro h
    exact infinityModel_tendsto n hn
  · intro h
    exact infinityNormalized_tendsto m n hn

theorem gap7 (n : ℝ) (hn : 0 < n) :
    Tendsto (infinityModel n) atTop (nhds (Real.pi / 2)) := by
  exact infinityModel_tendsto n hn

theorem gap8 (m n : ℝ) (hn : 0 < n) :
    Tendsto (infinityNormalized m n) atTop (nhds (Real.pi / 2)) := by
  exact infinityNormalized_tendsto m n hn

theorem gap9 (m n : ℝ) (hn : 0 < n) :
    TailIntegrable m n ↔ 1 < n - m := by
  unfold TailIntegrable
  exact tail_integrable_iff m n hn.le

theorem gap10 (m n : ℝ) (hn : 0 < n) :
    (-2 < m ∧ 1 < n - m) ↔ FullIntegrable m n := by
  constructor
  · rintro ⟨hm, htail⟩
    exact (gap1 m n).mpr ⟨(gap5 m n hn).mpr hm, (gap9 m n hn).mpr htail⟩
  · intro hfull
    obtain ⟨hzero, htail⟩ := (gap1 m n).mp hfull
    exact ⟨(gap5 m n hn).mp hzero, (gap9 m n hn).mp htail⟩

end
end ProofGap.Exercise2366
