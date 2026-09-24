import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Asymptotics
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace ProofGap.Exercise2374
noncomputable section

open Filter MeasureTheory

def integrand (p q x : ℝ) : ℝ :=
  1 / (Real.rpow x p * Real.rpow (Real.log x) q)
def NearOneIntegrable (p q : ℝ) : Prop :=
  IntegrableOn (integrand p q) (Set.Ioc (1 : ℝ) 2)
def TailIntegrable (p q : ℝ) : Prop :=
  IntegrableOn (integrand p q) (Set.Ioi (2 : ℝ))
def FullIntegrable (p q : ℝ) : Prop :=
  IntegrableOn (integrand p q) (Set.Ioi (1 : ℝ))
def oneNormalized (p q x : ℝ) : ℝ :=
  Real.rpow (x - 1) q * integrand p q x
def oneModel (p q x : ℝ) : ℝ :=
  (1 / Real.rpow x p) * Real.rpow ((x - 1) / Real.log x) q
def alpha (p : ℝ) : ℝ := (p - 1) / 2
def tailWeighted (p q α x : ℝ) : ℝ :=
  Real.rpow x (p - α) * integrand p q x
def slowTail (q α x : ℝ) : ℝ :=
  1 / (Real.rpow x α * Real.rpow (Real.log x) q)

private theorem integrand_continuousOn_Icc (p q a b : ℝ) (ha : 1 < a) :
    ContinuousOn (integrand p q) (Set.Icc a b) := by
  apply continuousOn_of_forall_continuousAt
  intro x hx
  have hx0 : 0 < x := zero_lt_one.trans (ha.trans_le hx.1)
  have hlog : 0 < Real.log x := Real.log_pos (ha.trans_le hx.1)
  have hxp : ContinuousAt (fun y : ℝ => Real.rpow y p) x :=
    continuousAt_id.rpow_const (Or.inl hx0.ne')
  have hlogcont : ContinuousAt Real.log x := Real.continuousAt_log hx0.ne'
  have hlq : ContinuousAt (fun y : ℝ => Real.rpow (Real.log y) q) x :=
    hlogcont.rpow_const (Or.inl hlog.ne')
  exact continuousAt_const.div (hxp.mul hlq)
    (mul_ne_zero (Real.rpow_pos_of_pos hx0 p).ne'
      (Real.rpow_pos_of_pos hlog q).ne')

private theorem integrand_continuousOn_Ici (p q a : ℝ) (ha : 1 < a) :
    ContinuousOn (integrand p q) (Set.Ici a) := by
  apply continuousOn_of_forall_continuousAt
  intro x hx
  have hx0 : 0 < x := zero_lt_one.trans (ha.trans_le hx)
  have hlog : 0 < Real.log x := Real.log_pos (ha.trans_le hx)
  have hxp : ContinuousAt (fun y : ℝ => Real.rpow y p) x :=
    continuousAt_id.rpow_const (Or.inl hx0.ne')
  have hlogcont : ContinuousAt Real.log x := Real.continuousAt_log hx0.ne'
  have hlq : ContinuousAt (fun y : ℝ => Real.rpow (Real.log y) q) x :=
    hlogcont.rpow_const (Or.inl hlog.ne')
  exact continuousAt_const.div (hxp.mul hlq)
    (mul_ne_zero (Real.rpow_pos_of_pos hx0 p).ne'
      (Real.rpow_pos_of_pos hlog q).ne')

private theorem oneNormalized_eq_oneModel (p q x : ℝ) (hx : 1 < x) :
    oneNormalized p q x = oneModel p q x := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hsub : 0 ≤ x - 1 := (sub_pos.mpr hx).le
  have hlog : 0 ≤ Real.log x := (Real.log_pos hx).le
  have hdiv : Real.rpow ((x - 1) / Real.log x) q =
      Real.rpow (x - 1) q / Real.rpow (Real.log x) q :=
    Real.div_rpow hsub hlog q
  unfold oneNormalized oneModel integrand
  rw [hdiv]
  field_simp [(Real.rpow_pos_of_pos hx0 p).ne',
    (Real.rpow_pos_of_pos (Real.log_pos hx) q).ne']

private theorem oneNormalized_mul (p q x : ℝ) (hx : 1 < x) :
    oneNormalized p q x * Real.rpow (x - 1) (-q) = integrand p q x := by
  have hsub : 0 < x - 1 := sub_pos.mpr hx
  have hpow : Real.rpow (x - 1) q * Real.rpow (x - 1) (-q) = 1 := by
    simp only [Real.rpow_eq_pow]
    rw [(Real.rpow_add hsub q (-q)).symm]
    norm_num
  unfold oneNormalized
  calc
    (Real.rpow (x - 1) q * integrand p q x) * Real.rpow (x - 1) (-q) =
        (Real.rpow (x - 1) q * Real.rpow (x - 1) (-q)) * integrand p q x := by
      ring
    _ = integrand p q x := by rw [hpow, one_mul]

private theorem tailWeighted_eq_slowTail (p q α x : ℝ) (hx : 1 < x) :
    tailWeighted p q α x = slowTail q α x := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hp : Real.rpow x (p - α) * Real.rpow x α = Real.rpow x p := by
    simp only [Real.rpow_eq_pow]
    rw [(Real.rpow_add hx0 (p - α) α).symm]
    congr 1
    ring
  unfold tailWeighted slowTail integrand
  field_simp [(Real.rpow_pos_of_pos hx0 p).ne',
    (Real.rpow_pos_of_pos hx0 α).ne',
    (Real.rpow_pos_of_pos hlog q).ne']
  exact hp

private theorem tailWeighted_mul (p q α x : ℝ) (hx : 0 < x) :
    tailWeighted p q α x * Real.rpow x (-(p - α)) = integrand p q x := by
  have hpow : Real.rpow x (p - α) * Real.rpow x (-(p - α)) = 1 := by
    simp only [Real.rpow_eq_pow]
    rw [(Real.rpow_add hx (p - α) (-(p - α))).symm]
    norm_num
  unfold tailWeighted
  calc
    (Real.rpow x (p - α) * integrand p q x) * Real.rpow x (-(p - α)) =
        (Real.rpow x (p - α) * Real.rpow x (-(p - α))) * integrand p q x := by
      ring
    _ = integrand p q x := by rw [hpow, one_mul]

private def tailAntiderivative (q x : ℝ) : ℝ :=
  Real.rpow (Real.log x) (1 - q) / (1 - q)

private theorem tailAntiderivative_hasDerivAt
    (q x : ℝ) (hq : q < 1) (hx : 1 < x) :
    HasDerivAt (tailAntiderivative q) (integrand 1 q x) x := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hlog : 0 < Real.log x := Real.log_pos hx
  have hp := (Real.hasDerivAt_log hx0.ne').rpow_const
    (p := 1 - q) (Or.inl hlog.ne')
  have hd := hp.div_const (1 - q)
  unfold tailAntiderivative
  convert hd using 1
  unfold integrand
  simp only [Real.rpow_eq_pow]
  rw [show 1 - q - 1 = -q by ring, Real.rpow_one]
  have hq1 : 1 - q ≠ 0 := by linarith
  rw [Real.rpow_neg hlog.le q]
  field_simp [hx0.ne', hq1, (Real.rpow_pos_of_pos hlog q).ne']

theorem gap1 (p q : ℝ) :
    FullIntegrable p q ↔ NearOneIntegrable p q ∧ TailIntegrable p q := by
  unfold FullIntegrable NearOneIntegrable TailIntegrable
  rw [← Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (1 : ℝ) ≤ 2),
    MeasureTheory.integrableOn_union]

theorem gap2 (p q : ℝ) :
    Tendsto (oneNormalized p q) (nhdsWithin 1 (Set.Ioi 1)) (nhds 1) ↔
      Tendsto (oneModel p q) (nhdsWithin 1 (Set.Ioi 1)) (nhds 1) := by
  have heq : oneNormalized p q =ᶠ[nhdsWithin 1 (Set.Ioi 1)] oneModel p q := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact oneNormalized_eq_oneModel p q x hx
  constructor
  · intro h
    exact h.congr' heq
  · intro h
    exact h.congr' heq.symm

theorem gap3 (p q : ℝ) :
    Tendsto (oneModel p q)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 1) := by
  have hs : Tendsto (fun x : ℝ => Real.log x / (x - 1))
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 1) := by
    have h := (Real.hasDerivAt_log one_ne_zero).tendsto_slope.mono_left
      (nhdsGT_le_nhdsNE (1 : ℝ))
    convert h using 1
    · funext x
      rw [slope_def_field]
      norm_num
    · norm_num
  have hinv := hs.inv₀ one_ne_zero
  have hinv' : Tendsto (fun x : ℝ => (Real.log x / (x - 1))⁻¹)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 1) := by
    simpa using hinv
  have hratio : Tendsto (fun x : ℝ => (x - 1) / Real.log x)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 1) := by
    apply hinv'.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hlog : Real.log x ≠ 0 := (Real.log_pos hx).ne'
    have hsub : x - 1 ≠ 0 := (sub_pos.mpr hx).ne'
    field_simp
  have hxp : Tendsto (fun x : ℝ => 1 / Real.rpow x p)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 1) := by
    have hr := (continuousAt_id.rpow_const (p := p) (Or.inl one_ne_zero)).tendsto
    have hi := hr.inv₀ (Real.rpow_pos_of_pos one_pos p).ne'
    simpa using hi.mono_left inf_le_left
  have hrq := hratio.rpow_const (p := q) (Or.inl one_ne_zero)
  have hm := hxp.mul hrq
  have hm' : Tendsto (oneModel p q)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (1 * Real.rpow 1 q)) := hm
  simpa using hm'

theorem gap4 (p q : ℝ) :
    Tendsto (oneNormalized p q)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds 1) := by
  exact (gap2 p q).2 (gap3 p q)

theorem gap5 (p q : ℝ) :
    NearOneIntegrable p q ↔ q < 1 := by
  let base : ℝ → ℝ := fun x => Real.rpow (x - 1) (-q)
  have hbase_meas : AEStronglyMeasurable base volume := by
    apply Measurable.aestronglyMeasurable
    unfold base
    measurability
  constructor
  · intro hint
    have hintAt : IntegrableAtFilter (integrand p q)
        (nhdsWithin 1 (Set.Ioi 1)) volume := by
      refine ⟨Set.Ioc 1 2, Ioc_mem_nhdsGT (by norm_num), ?_⟩
      exact hint
    have hclose := (Metric.tendsto_nhds.1 (gap4 p q)) (1 / 2) (by norm_num)
    have hge : ∀ᶠ x : ℝ in nhdsWithin 1 (Set.Ioi 1),
        (1 / 2 : ℝ) ≤ oneNormalized p q x := by
      filter_upwards [hclose] with x hx
      rw [Real.dist_eq] at hx
      linarith [(abs_lt.mp hx).1]
    have hO : base =O[nhdsWithin 1 (Set.Ioi 1)] integrand p q := by
      apply Asymptotics.isBigO_iff.mpr
      refine ⟨2, ?_⟩
      filter_upwards [self_mem_nhdsWithin, hge] with x hx hn
      have hb0 : 0 ≤ base x := by
        unfold base
        exact Real.rpow_nonneg (sub_pos.mpr hx).le (-q)
      have hi0 : 0 ≤ integrand p q x := by
        have hx0 : 0 < x := zero_lt_one.trans hx
        have hlog : 0 < Real.log x := Real.log_pos hx
        unfold integrand
        exact one_div_nonneg.mpr (mul_nonneg
          (Real.rpow_nonneg hx0.le p) (Real.rpow_nonneg hlog.le q))
      have heq := oneNormalized_mul p q x hx
      have hle : base x ≤ 2 * integrand p q x := by
        have hm := mul_le_mul_of_nonneg_right hn hb0
        rw [heq] at hm
        linarith
      simpa [Real.norm_eq_abs, abs_of_nonneg hb0, abs_of_nonneg hi0] using hle
    have hbaseAt : IntegrableAtFilter base (nhdsWithin 1 (Set.Ioi 1)) volume :=
      hO.integrableAtFilter hbase_meas.stronglyMeasurableAtFilter hintAt
    obtain ⟨s, hs, hsint⟩ := hbaseAt
    obtain ⟨c, hc, hcs⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1 hs
    let d : ℝ := min c (3 / 2)
    have hd1 : 1 < d := lt_min hc (by norm_num)
    have hbaseOn : IntegrableOn base (Set.Ioo 1 d) :=
      hsint.mono (fun x hx => hcs ⟨hx.1, hx.2.trans_le (min_le_left _ _)⟩) le_rfl
    have hintShift : IntervalIntegrable (fun y : ℝ => Real.rpow y (-q))
        volume 0 (d - 1) := by
      have hintBase : IntervalIntegrable base volume 1 d :=
        (intervalIntegrable_iff_integrableOn_Ioo_of_le hd1.le).2 hbaseOn
      have hshift := (IntervalIntegrable.comp_sub_right_iff
        (f := fun y : ℝ => Real.rpow y (-q))
        (a := 0) (b := d - 1) (c := 1)).mp
          (by simpa only [base, zero_add, sub_add_cancel] using hintBase)
      simpa using hshift
    have hpowOn : IntegrableOn (fun y : ℝ => Real.rpow y (-q))
        (Set.Ioo 0 (d - 1)) :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith)).1 hintShift
    have hexp : -1 < -q :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff (by linarith : 0 < d - 1)).1
        (by simpa only [Real.rpow_eq_pow] using hpowOn)
    linarith
  · intro hq
    have hexp : -1 < -q := by linarith
    have hpowOn : IntegrableOn (fun y : ℝ => Real.rpow y (-q)) (Set.Ioo 0 1) := by
      have h := (intervalIntegral.integrableOn_Ioo_rpow_iff
        (by norm_num : (0 : ℝ) < 1)).2 hexp
      simpa only [Real.rpow_eq_pow] using h
    have hpowInt : IntervalIntegrable (fun y : ℝ => Real.rpow y (-q)) volume 0 1 :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)).2 hpowOn
    have hbaseInt : IntervalIntegrable base volume 1 2 := by
      have hshift := (IntervalIntegrable.comp_sub_right_iff
        (f := fun y : ℝ => Real.rpow y (-q))
        (a := 0) (b := 1) (c := 1)).2 hpowInt
      simpa only [base, zero_add, one_add_one_eq_two] using hshift
    have hbaseOn : IntegrableOn base (Set.Ioo (1 : ℝ) 2) :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)).1 hbaseInt
    have hbaseAt : IntegrableAtFilter base (nhdsWithin 1 (Set.Ioi 1)) volume :=
      ⟨Set.Ioo 1 2, Ioo_mem_nhdsGT (by norm_num), hbaseOn⟩
    have hOnorm : oneNormalized p q =O[nhdsWithin 1 (Set.Ioi 1)]
        (fun _ : ℝ => (1 : ℝ)) := (gap4 p q).isBigO_one ℝ
    have hOprod := hOnorm.mul
      (Asymptotics.isBigO_refl base (nhdsWithin 1 (Set.Ioi 1)))
    have heq : (fun x => oneNormalized p q x * base x) =ᶠ[nhdsWithin 1 (Set.Ioi 1)]
        integrand p q := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact oneNormalized_mul p q x hx
    have hright : (fun x => (1 : ℝ) * base x) =ᶠ[nhdsWithin 1 (Set.Ioi 1)] base :=
      Filter.Eventually.of_forall (fun x => by simp)
    have hO : integrand p q =O[nhdsWithin 1 (Set.Ioi 1)] base :=
      hOprod.congr' heq hright
    have hmeas : AEStronglyMeasurable (integrand p q) volume := by
      apply Measurable.aestronglyMeasurable
      unfold integrand
      measurability
    have hintAt : IntegrableAtFilter (integrand p q)
        (nhdsWithin 1 (Set.Ioi 1)) volume :=
      hO.integrableAtFilter hmeas.stronglyMeasurableAtFilter hbaseAt
    obtain ⟨s, hs, hsint⟩ := hintAt
    obtain ⟨c, hc, hcs⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1 hs
    let d : ℝ := min c (3 / 2)
    have hd1 : 1 < d := lt_min hc (by norm_num)
    have hd2 : d < 2 := (min_le_right _ _).trans_lt (by norm_num)
    have hnear : IntegrableOn (integrand p q) (Set.Ioo 1 d) :=
      hsint.mono (fun x hx => hcs ⟨hx.1, hx.2.trans_le (min_le_left _ _)⟩) le_rfl
    have hfar : IntegrableOn (integrand p q) (Set.Icc d 2) :=
      (integrand_continuousOn_Icc p q d 2 hd1).integrableOn_Icc
    have hu := hnear.union hfar
    unfold NearOneIntegrable
    rwa [Set.Ioo_union_Icc_eq_Ioc hd1 hd2.le] at hu

theorem gap6 (p : ℝ) (hp : 1 < p) :
    0 < alpha p := by
  unfold alpha
  linarith

theorem gap7 (p : ℝ) (hp : 1 < p) :
    1 < p - alpha p := by
  unfold alpha
  linarith

theorem gap8 (p q : ℝ) (hp : 1 < p) :
    Tendsto (tailWeighted p q (alpha p)) atTop (nhds 0) ↔
      Tendsto (slowTail q (alpha p)) atTop (nhds 0) := by
  have heq : tailWeighted p q (alpha p) =ᶠ[atTop] slowTail q (alpha p) := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact tailWeighted_eq_slowTail p q (alpha p) x hx
  constructor
  · intro h
    exact h.congr' heq
  · intro h
    exact h.congr' heq.symm

theorem gap9 (p q : ℝ) (hp : 1 < p) :
    Tendsto (slowTail q (alpha p)) atTop (nhds 0) := by
  have hmain : Tendsto
      (fun x : ℝ => Real.rpow (Real.log x) (-q) / Real.rpow x (alpha p))
      atTop (nhds 0) :=
    Asymptotics.IsLittleO.tendsto_div_nhds_zero
      (isLittleO_log_rpow_rpow_atTop (-q) (gap6 p hp))
  apply hmain.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hlog : 0 < Real.log x := Real.log_pos hx
  unfold slowTail
  simp only [Real.rpow_eq_pow]
  rw [Real.rpow_neg hlog.le q]
  field_simp [(Real.rpow_pos_of_pos hx0 (alpha p)).ne',
    (Real.rpow_pos_of_pos hlog q).ne']

theorem gap10 (p q : ℝ) (hp : 1 < p) :
    Tendsto (tailWeighted p q (alpha p)) atTop (nhds 0) := by
  exact (gap8 p q hp).2 (gap9 p q hp)

theorem gap11 (p q : ℝ) (hp : 1 < p) :
    TailIntegrable p q := by
  let base : ℝ → ℝ := fun x => Real.rpow x (-(p - alpha p))
  have hbaseAt : IntegrableAtFilter base atTop volume := by
    have hexp : -(p - alpha p) < -1 := by linarith [gap7 p hp]
    have h := (integrableAtFilter_rpow_atTop_iff (s := -(p - alpha p))).2 hexp
    simpa only [base, Real.rpow_eq_pow] using h
  have hOweighted : tailWeighted p q (alpha p) =O[atTop]
      (fun _ : ℝ => (1 : ℝ)) := (gap10 p q hp).isBigO_one ℝ
  have hOprod := hOweighted.mul (Asymptotics.isBigO_refl base atTop)
  have heq : (fun x => tailWeighted p q (alpha p) x * base x) =ᶠ[atTop]
      integrand p q := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact tailWeighted_mul p q (alpha p) x hx
  have hright : (fun x => (1 : ℝ) * base x) =ᶠ[atTop] base :=
    Filter.Eventually.of_forall (fun x => by simp)
  have hO : integrand p q =O[atTop] base := hOprod.congr' heq hright
  have hlocal : LocallyIntegrableOn (integrand p q) (Set.Ici (2 : ℝ)) volume :=
    (integrand_continuousOn_Ici p q 2 (by norm_num)).locallyIntegrableOn measurableSet_Ici
  have hintIci : IntegrableOn (integrand p q) (Set.Ici (2 : ℝ)) :=
    hlocal.integrableOn_of_isBigO_atTop hO hbaseAt
  unfold TailIntegrable
  exact hintIci.mono Set.Ioi_subset_Ici_self le_rfl

theorem gap12 (p q x : ℝ) (hp : p ≤ 1) (hq : q < 1) (hx : 2 ≤ x) :
    integrand 1 q x ≤ integrand p q x := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hpow : Real.rpow x p ≤ Real.rpow x 1 :=
    Real.rpow_le_rpow_of_exponent_le hx1 hp
  have hden : Real.rpow x p * Real.rpow (Real.log x) q ≤
      Real.rpow x 1 * Real.rpow (Real.log x) q :=
    mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hlog.le q)
  unfold integrand
  exact one_div_le_one_div_of_le
    (mul_pos (Real.rpow_pos_of_pos hx0 p) (Real.rpow_pos_of_pos hlog q)) hden

theorem gap13 (q : ℝ) (hq : q < 1) :
    Tendsto (fun A => ∫ x in (2 : ℝ)..A, integrand 1 q x)
      atTop atTop := by
  have hexp : 0 < 1 - q := by linarith
  have hlog : Tendsto (fun A : ℝ => Real.log A) atTop atTop := Real.tendsto_log_atTop
  have hrpow : Tendsto (fun A : ℝ => Real.rpow (Real.log A) (1 - q)) atTop atTop :=
    (tendsto_rpow_atTop hexp).comp hlog
  have hanti : Tendsto (tailAntiderivative q) atTop atTop := by
    have h := hrpow.atTop_div_const hexp
    simpa only [tailAntiderivative] using h
  have hlim : Tendsto (fun A => tailAntiderivative q A - tailAntiderivative q 2)
      atTop atTop := by
    have h := atTop.tendsto_atTop_add_const_right
      (-tailAntiderivative q 2) hanti
    simpa [sub_eq_add_neg] using h
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (2 : ℝ)] with A hA
  have hder : ∀ x ∈ Set.uIcc (2 : ℝ) A,
      HasDerivAt (tailAntiderivative q) (integrand 1 q x) x := by
    intro x hx
    rw [Set.uIcc_of_le hA.le] at hx
    exact tailAntiderivative_hasDerivAt q x hq (by linarith [hx.1])
  have hcont : ContinuousOn (integrand 1 q) (Set.uIcc (2 : ℝ) A) := by
    rw [Set.uIcc_of_le hA.le]
    exact integrand_continuousOn_Icc 1 q 2 A (by norm_num)
  have hint : IntervalIntegrable (integrand 1 q) volume (2 : ℝ) A :=
    hcont.intervalIntegrable
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt hder hint).symm

theorem gap14 (p q : ℝ) (hp : p ≤ 1) (hq : q < 1) :
    Tendsto (fun A => ∫ x in (2 : ℝ)..A, integrand p q x)
      atTop atTop := by
  have hle : ∀ᶠ A : ℝ in atTop,
      (∫ x in (2 : ℝ)..A, integrand 1 q x) ≤
        ∫ x in (2 : ℝ)..A, integrand p q x := by
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with A hA
    have hcont1 : ContinuousOn (integrand 1 q) (Set.uIcc (2 : ℝ) A) := by
      rw [Set.uIcc_of_le hA]
      exact integrand_continuousOn_Icc 1 q 2 A (by norm_num)
    have hcontp : ContinuousOn (integrand p q) (Set.uIcc (2 : ℝ) A) := by
      rw [Set.uIcc_of_le hA]
      exact integrand_continuousOn_Icc p q 2 A (by norm_num)
    apply intervalIntegral.integral_mono_on hA
      hcont1.intervalIntegrable hcontp.intervalIntegrable
    intro x hx
    exact gap12 p q x hp hq hx.1
  exact tendsto_atTop_mono' atTop hle (gap13 q hq)

theorem gap15 (p q : ℝ) :
    (1 < p ∧ q < 1) ↔ FullIntegrable p q := by
  constructor
  · rintro ⟨hp, hq⟩
    exact (gap1 p q).2 ⟨(gap5 p q).2 hq, gap11 p q hp⟩
  · intro hfull
    have hparts := (gap1 p q).1 hfull
    have hq : q < 1 := (gap5 p q).1 hparts.1
    have hp : 1 < p := by
      by_contra hn
      have hple : p ≤ 1 := le_of_not_gt hn
      have hfinite : Tendsto (fun A => ∫ x in (2 : ℝ)..A, integrand p q x)
          atTop (nhds (∫ x in Set.Ioi (2 : ℝ), integrand p q x)) :=
        intervalIntegral_tendsto_integral_Ioi 2 hparts.2 tendsto_id
      exact (not_tendsto_atTop_of_tendsto_nhds hfinite) (gap14 p q hple hq)
    exact ⟨hp, hq⟩

end
end ProofGap.Exercise2374
