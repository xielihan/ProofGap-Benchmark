import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
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

namespace ProofGap.Exercise2362
noncomputable section

open Filter MeasureTheory

def integrand (p q x : ℝ) : ℝ :=
  Real.rpow x p * Real.rpow (Real.log (1 / x)) q

def IntegrableAtZero (p q : ℝ) : Prop :=
  IntegrableOn (integrand p q) (Set.Ioc (0 : ℝ) (1 / 2))
def IntegrableAtOne (p q : ℝ) : Prop :=
  IntegrableOn (integrand p q) (Set.Ioo (1 / 2 : ℝ) 1)
def IntegrableUnit (p q : ℝ) : Prop :=
  IntegrableOn (integrand p q) (Set.Ioo (0 : ℝ) 1)

def tau (p : ℝ) : ℝ := (p + 1) / 2
def oneEndpointNormalized (p q x : ℝ) : ℝ :=
  Real.rpow (1 - x) (-q) * integrand p q x
def oneEndpointRatio (p q x : ℝ) : ℝ :=
  Real.rpow x p * Real.rpow (Real.log (1 / x) / (1 - x)) q
def slowRatio (q τ x : ℝ) : ℝ :=
  Real.rpow (Real.log (1 / x)) q / Real.rpow (1 / x) τ
def zeroWeighted (p q τ x : ℝ) : ℝ :=
  Real.rpow x (-p + τ) * integrand p q x

private theorem integrand_continuousOn_Icc (p q a b : ℝ)
    (ha : 0 < a) (hb : b < 1) :
    ContinuousOn (integrand p q) (Set.Icc a b) := by
  apply continuousOn_of_forall_continuousAt
  intro x hx
  have hx0 : 0 < x := ha.trans_le hx.1
  have hx1 : x < 1 := hx.2.trans_lt hb
  have h1 : ContinuousAt (fun y : ℝ => Real.rpow y p) x :=
    continuousAt_id.rpow_const (Or.inl hx0.ne')
  have hu0 := (hasDerivAt_inv hx0.ne').log (by simpa using hx0.ne')
  have hu : ContinuousAt (fun y : ℝ => Real.log (1 / y)) x := by
    simpa [one_div] using hu0.continuousAt
  have h2 : ContinuousAt (fun y : ℝ => Real.rpow (Real.log (1 / y)) q) x :=
    hu.rpow_const (Or.inl (Real.log_pos (one_lt_one_div hx0 hx1)).ne')
  exact h1.mul h2

private theorem oneEndpoint_eq (p q x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    oneEndpointNormalized p q x = oneEndpointRatio p q x := by
  have ha : 0 ≤ 1 - x := by linarith
  have hl : 0 ≤ Real.log (1 / x) :=
    (Real.log_pos (one_lt_one_div hx0 hx1)).le
  have hneg : Real.rpow (1 - x) (-q) = (Real.rpow (1 - x) q)⁻¹ :=
    Real.rpow_neg ha q
  have hdiv : Real.rpow (Real.log (1 / x) / (1 - x)) q =
      Real.rpow (Real.log (1 / x)) q / Real.rpow (1 - x) q :=
    Real.div_rpow hl ha q
  unfold oneEndpointNormalized oneEndpointRatio integrand
  rw [hneg, hdiv]
  simp only [div_eq_mul_inv]
  ring

private theorem oneEndpointNormalized_mul (p q x : ℝ) (hx : x < 1) :
    oneEndpointNormalized p q x * Real.rpow (1 - x) q = integrand p q x := by
  have ha : 0 < 1 - x := sub_pos.mpr hx
  have hpow : Real.rpow (1 - x) (-q) * Real.rpow (1 - x) q = 1 := by
    simp only [Real.rpow_eq_pow]
    rw [(Real.rpow_add ha _ _).symm]
    norm_num
  unfold oneEndpointNormalized
  calc
    (Real.rpow (1 - x) (-q) * integrand p q x) * Real.rpow (1 - x) q =
        (Real.rpow (1 - x) (-q) * Real.rpow (1 - x) q) * integrand p q x := by
      ring
    _ = integrand p q x := by rw [hpow, one_mul]

private theorem zeroWeighted_eq_slowRatio (p q τ x : ℝ) (hx : 0 < x) :
    zeroWeighted p q τ x = slowRatio q τ x := by
  have hmul : Real.rpow x (-p + τ) * Real.rpow x p = Real.rpow x τ := by
    calc
      Real.rpow x (-p + τ) * Real.rpow x p =
          Real.rpow x ((-p + τ) + p) := (Real.rpow_add hx _ _).symm
      _ = Real.rpow x τ := by
        congr 1
        ring
  have hden : Real.rpow (1 / x) τ = (Real.rpow x τ)⁻¹ := by
    simpa [one_div] using Real.inv_rpow hx.le τ
  unfold zeroWeighted integrand slowRatio
  rw [(mul_assoc _ _ _).symm, hmul, hden]
  simp only [div_inv_eq_mul]
  ring

private theorem zeroWeighted_mul (p q τ x : ℝ) (hx : 0 < x) :
    zeroWeighted p q τ x * Real.rpow x (p - τ) = integrand p q x := by
  have hpow : Real.rpow x (-p + τ) * Real.rpow x p * Real.rpow x (p - τ) =
      Real.rpow x p := by
    simp only [Real.rpow_eq_pow]
    calc
      x ^ (-p + τ) * x ^ p * x ^ (p - τ) =
          x ^ ((-p + τ) + p) * x ^ (p - τ) := by
        rw [(Real.rpow_add hx _ _).symm]
      _ = x ^ (((-p + τ) + p) + (p - τ)) := by
        rw [(Real.rpow_add hx _ _).symm]
      _ = x ^ p := by
        congr 1
        ring
  calc
    zeroWeighted p q τ x * Real.rpow x (p - τ) =
        (Real.rpow x (-p + τ) * Real.rpow x p * Real.rpow x (p - τ)) *
          Real.rpow (Real.log (1 / x)) q := by
      unfold zeroWeighted integrand
      ring
    _ = integrand p q x := by
      rw [hpow]
      rfl

private theorem endpointBaseDiverges (q d : ℝ) (hq : q ≤ -1) (hd1 : d < 1) :
    Tendsto (fun b => ∫ x in d..b, Real.rpow (1 - x) q)
      (nhdsWithin 1 (Set.Iio 1)) atTop := by
  let L := nhdsWithin (1 : ℝ) (Set.Iio 1)
  have hz : Tendsto (fun b : ℝ => 1 - b) L (nhdsWithin 0 (Set.Ioi 0)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    case left =>
      have hid : Tendsto (fun x : ℝ => x) L (nhds 1) :=
        continuousAt_id.tendsto.mono_left inf_le_left
      have hc : Tendsto (fun _ : ℝ => (1 : ℝ)) L (nhds 1) := tendsto_const_nhds
      simpa using hc.sub hid
    case right =>
      have hmem : ∀ᶠ x : ℝ in L, x < 1 := eventually_mem_nhdsWithin
      exact hmem.mono (fun x hx => sub_pos.mpr hx)
  by_cases heq : q = -1
  case pos =>
    have hinv0 : Tendsto (fun z : ℝ => 1 / z) (nhdsWithin 0 (Set.Ioi 0)) atTop := by
      simpa [one_div] using tendsto_inv_nhdsGT_zero
    have hinv : Tendsto (fun b : ℝ => 1 / (1 - b)) L atTop := hinv0.comp hz
    have hcpos : 0 < 1 - d := sub_pos.mpr hd1
    have hratio : Tendsto (fun b : ℝ => (1 - d) / (1 - b)) L atTop := by
      have h := hinv.atTop_mul_const hcpos
      simpa [div_eq_mul_inv, mul_comm] using h
    have hlog : Tendsto (fun b : ℝ => Real.log ((1 - d) / (1 - b))) L atTop :=
      Real.tendsto_log_atTop.comp hratio
    apply hlog.congr'
    filter_upwards [Ioo_mem_nhdsLT hd1] with b hb
    have hzb : 0 < 1 - b := sub_pos.mpr hb.2
    have hle : 1 - b ≤ 1 - d := by linarith [hb.1]
    have hzero : 0 ∉ Set.uIcc (1 - b) (1 - d) := by
      rw [Set.uIcc_of_le hle]
      intro h0
      exact (not_lt_of_ge h0.1) hzb
    symm
    calc
      (∫ x in d..b, Real.rpow (1 - x) q) =
          ∫ y in (1 - b)..(1 - d), y⁻¹ := by
        subst q
        have ht := intervalIntegral.integral_comp_sub_left
          (fun y : ℝ => y ^ (-1 : ℝ)) 1 (a := d) (b := b)
        simpa only [Real.rpow_eq_pow, Real.rpow_neg_one] using ht
      _ = Real.log ((1 - d) / (1 - b)) := integral_inv hzero
  case neg =>
    have hlt : q < -1 := lt_of_le_of_ne hq heq
    have hr : q + 1 < 0 := by linarith
    have hp0 : Tendsto (fun z : ℝ => Real.rpow z (q + 1))
        (nhdsWithin 0 (Set.Ioi 0)) atTop := by
      simpa only [Real.rpow_eq_pow] using tendsto_rpow_neg_nhdsGT_zero hr
    have hp : Tendsto (fun b : ℝ => Real.rpow (1 - b) (q + 1)) L atTop :=
      hp0.comp hz
    let C : ℝ := Real.rpow (1 - d) (q + 1)
    have hshift : Tendsto (fun b : ℝ => Real.rpow (1 - b) (q + 1) - C) L atTop := by
      have h := L.tendsto_atTop_add_const_right (-C) hp
      simpa [sub_eq_add_neg] using h
    have hmain : Tendsto
        (fun b : ℝ => (Real.rpow (1 - b) (q + 1) - C) / (-(q + 1))) L atTop :=
      hshift.atTop_div_const (by linarith)
    apply hmain.congr'
    filter_upwards [Ioo_mem_nhdsLT hd1] with b hb
    have hzb : 0 < 1 - b := sub_pos.mpr hb.2
    have hle : 1 - b ≤ 1 - d := by linarith [hb.1]
    have hzero : 0 ∉ Set.uIcc (1 - b) (1 - d) := by
      rw [Set.uIcc_of_le hle]
      intro h0
      exact (not_lt_of_ge h0.1) hzb
    symm
    calc
      (∫ x in d..b, Real.rpow (1 - x) q) =
          ∫ y in (1 - b)..(1 - d), y ^ q := by
        have ht := intervalIntegral.integral_comp_sub_left
          (fun y : ℝ => y ^ q) 1 (a := d) (b := b)
        simpa only [Real.rpow_eq_pow] using ht
      _ = (((1 - d) ^ (q + 1) - (1 - b) ^ (q + 1)) / (q + 1)) :=
        integral_rpow (Or.inr ⟨heq, hzero⟩)
      _ = (Real.rpow (1 - b) (q + 1) - C) / (-(q + 1)) := by
        unfold C
        rw [Real.rpow_eq_pow, Real.rpow_eq_pow]
        have hne : q + 1 ≠ 0 := by linarith
        field_simp [hne]
        ring

private def borderlineAntiderivative (q x : ℝ) : ℝ :=
  -(Real.rpow (Real.log (1 / x)) (q + 1) / (q + 1))

private theorem borderlineAntiderivative_hasDerivAt
    (q x : ℝ) (hq : -1 < q) (hx : 0 < x) (hx1 : x < 1) :
    HasDerivAt (borderlineAntiderivative q) (integrand (-1) q x) x := by
  have hu0 := (hasDerivAt_inv hx.ne').log (by simpa using hx.ne')
  have hu : HasDerivAt (fun y : ℝ => Real.log (1 / y))
      (-((x ^ 2)⁻¹) / x⁻¹) x := by
    simpa [one_div] using hu0
  have hulog : 0 < Real.log (1 / x) := Real.log_pos (one_lt_one_div hx hx1)
  have hp := hu.rpow_const (p := q + 1) (Or.inl hulog.ne')
  have hd := (hp.div_const (q + 1)).neg
  unfold borderlineAntiderivative
  convert hd using 1
  unfold integrand
  have hrneg : Real.rpow x (-1) = x⁻¹ := Real.rpow_neg_one x
  rw [hrneg, show q + 1 - 1 = q by ring]
  have hq1 : q + 1 ≠ 0 := by linarith
  field_simp [hx.ne', hq1]
  exact Real.rpow_eq_pow _ _

private theorem primitive_tendsto_right {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hint : IntervalIntegrable f volume a b) :
    Tendsto (fun x => ∫ t in a..x, f t) (nhdsWithin b (Set.Iio b))
      (nhds (∫ t in a..b, f t)) := by
  have hu : IntegrableOn f (Set.uIcc a b) := (intervalIntegrable_iff').1 hint
  have hc := (intervalIntegral.continuousOn_primitive_interval hu) b
    (by rw [Set.uIcc_of_le hab.le]; exact ⟨hab.le, le_rfl⟩)
  have hfilter : nhdsWithin b (Set.Iio b) ≤ nhdsWithin b (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab.le]
    exact le_inf inf_le_left (Filter.le_principal_iff.mpr (Icc_mem_nhdsLT hab))
  exact hc.tendsto.mono_left hfilter

private theorem primitive_tendsto_left {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hint : IntervalIntegrable f volume a b) :
    Tendsto (fun x => ∫ t in x..b, f t) (nhdsWithin a (Set.Ioi a))
      (nhds (∫ t in a..b, f t)) := by
  have hu : IntegrableOn f (Set.uIcc a b) := (intervalIntegrable_iff').1 hint
  have hc := (intervalIntegral.continuousOn_primitive_interval_left hu) a
    (by rw [Set.uIcc_of_le hab.le]; exact ⟨le_rfl, hab.le⟩)
  have hfilter : nhdsWithin a (Set.Ioi a) ≤ nhdsWithin a (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab.le]
    exact le_inf inf_le_left (Filter.le_principal_iff.mpr (Icc_mem_nhdsGT hab))
  exact hc.tendsto.mono_left hfilter

theorem gap1 (p q : ℝ) :
    IntegrableUnit p q ↔ IntegrableAtZero p q ∧ IntegrableAtOne p q := by
  unfold IntegrableUnit IntegrableAtZero IntegrableAtOne
  rw [(Set.Ioc_union_Ioo_eq_Ioo (a := (0 : ℝ)) (b := 1 / 2) (c := 1)
      (by norm_num) (by norm_num)).symm,
    MeasureTheory.integrableOn_union]

theorem gap2 (p q : ℝ) :
    Tendsto (oneEndpointNormalized p q)
        (nhdsWithin 1 (Set.Iio 1)) (nhds 1) ↔
      Tendsto (oneEndpointRatio p q)
        (nhdsWithin 1 (Set.Iio 1)) (nhds 1) := by
  have hx0 : ∀ᶠ x : ℝ in nhdsWithin 1 (Set.Iio 1), 0 < x :=
    Filter.Eventually.filter_mono inf_le_left (Ioi_mem_nhds one_pos)
  have heq : oneEndpointNormalized p q =ᶠ[nhdsWithin 1 (Set.Iio 1)]
      oneEndpointRatio p q := by
    filter_upwards [self_mem_nhdsWithin, hx0] with x hx1 hx0
    exact oneEndpoint_eq p q x hx0 hx1
  constructor
  · intro h
    exact h.congr' heq
  · intro h
    exact h.congr' heq.symm

theorem gap3 (p q : ℝ) :
    Tendsto (oneEndpointRatio p q)
      (nhdsWithin 1 (Set.Iio 1)) (nhds 1) := by
  have hd : HasDerivAt (fun x : ℝ => Real.log (1 / x)) (-1) 1 := by
    convert (hasDerivAt_inv one_ne_zero).log (by norm_num) using 1 <;>
      norm_num [one_div]
  have hs : Tendsto (fun x : ℝ => Real.log (1 / x) / (x - 1))
      (nhdsWithin 1 (Set.Iio 1)) (nhds (-1)) := by
    have h := hd.tendsto_slope.mono_left (nhdsLT_le_nhdsNE (1 : ℝ))
    convert h using 1
    funext x
    rw [slope_def_field]
    norm_num
  have hn : Tendsto (fun x : ℝ => -(Real.log (1 / x) / (x - 1)))
      (nhdsWithin 1 (Set.Iio 1)) (nhds 1) := by
    simpa using hs.neg
  have hratio : Tendsto (fun x : ℝ => Real.log (1 / x) / (1 - x))
      (nhdsWithin 1 (Set.Iio 1)) (nhds 1) := by
    apply hn.congr'
    filter_upwards with x
    rw [show 1 - x = -(x - 1) by ring, div_neg]
  have hxp : Tendsto (fun x : ℝ => Real.rpow x p)
      (nhdsWithin 1 (Set.Iio 1)) (nhds 1) := by
    have h := (continuousAt_id.rpow_const (p := p) (Or.inl one_ne_zero)).tendsto
    simpa using h.mono_left inf_le_left
  have hrq := hratio.rpow_const (p := q) (Or.inl one_ne_zero)
  have hm := hxp.mul hrq
  have hm' : Tendsto (oneEndpointRatio p q)
      (nhdsWithin 1 (Set.Iio 1)) (nhds (1 * Real.rpow 1 q)) := hm
  simpa using hm'

theorem gap4 (p q : ℝ) :
    Tendsto (oneEndpointNormalized p q)
      (nhdsWithin 1 (Set.Iio 1)) (nhds 1) := by
  exact (gap2 p q).2 (gap3 p q)

theorem gap5 (p q : ℝ) (hq : -1 < q) :
    IntegrableAtOne p q := by
  let base : ℝ → ℝ := fun x => Real.rpow (1 - x) q
  have h0 : IntervalIntegrable (fun x : ℝ => x ^ q) volume 0 (1 / 2) :=
    intervalIntegral.intervalIntegrable_rpow' hq
  have h1 := (h0.comp_sub_left 1).symm
  have hbint : IntervalIntegrable base volume (1 / 2) 1 := by
    simpa only [base, Real.rpow_eq_pow, sub_zero, sub_half] using h1
  have hbase : IntegrableOn base (Set.Ioo (1 / 2 : ℝ) 1) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)).1 hbint
  have hbaseAt : IntegrableAtFilter base (nhdsWithin 1 (Set.Iio 1)) volume :=
    ⟨Set.Ioo (1 / 2) 1, Ioo_mem_nhdsLT (by norm_num), hbase⟩
  have hOnorm : oneEndpointNormalized p q =O[nhdsWithin 1 (Set.Iio 1)]
      (fun _ : ℝ => (1 : ℝ)) := (gap4 p q).isBigO_one ℝ
  have hOprod := hOnorm.mul
    (Asymptotics.isBigO_refl base (nhdsWithin 1 (Set.Iio 1)))
  have heq : (fun x => oneEndpointNormalized p q x * base x) =ᶠ[nhdsWithin 1 (Set.Iio 1)]
      integrand p q := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact oneEndpointNormalized_mul p q x hx
  have hright : (fun x => (1 : ℝ) * base x) =ᶠ[nhdsWithin 1 (Set.Iio 1)] base :=
    Filter.Eventually.of_forall (fun x => by simp)
  have hO : integrand p q =O[nhdsWithin 1 (Set.Iio 1)] base :=
    hOprod.congr' heq hright
  have hmeas : AEStronglyMeasurable (integrand p q) volume := by
    apply Measurable.aestronglyMeasurable
    unfold integrand
    measurability
  have hAt : IntegrableAtFilter (integrand p q) (nhdsWithin 1 (Set.Iio 1)) volume :=
    hO.integrableAtFilter hmeas.stronglyMeasurableAtFilter hbaseAt
  obtain ⟨s, hs, hsint⟩ := hAt
  obtain ⟨c, hc, hcs⟩ := (mem_nhdsLT_iff_exists_Ioo_subset).1 hs
  let d : ℝ := max c (3 / 4)
  have hdhalf : (1 / 2 : ℝ) < d :=
    (by norm_num : (1 / 2 : ℝ) < 3 / 4).trans_le (le_max_right _ _)
  have hd1 : d < 1 := max_lt hc (by norm_num)
  have htail : IntegrableOn (integrand p q) (Set.Ioo d 1) :=
    hsint.mono (fun x hx => hcs ⟨(le_max_left _ _).trans_lt hx.1, hx.2⟩) le_rfl
  have hheadcc : IntegrableOn (integrand p q) (Set.Icc (1 / 2) d) :=
    (integrand_continuousOn_Icc p q (1 / 2) d (by norm_num) hd1).integrableOn_Icc
  have hhead : IntegrableOn (integrand p q) (Set.Ioc (1 / 2) d) :=
    hheadcc.mono Set.Ioc_subset_Icc_self le_rfl
  have hu := hhead.union htail
  unfold IntegrableAtOne
  rwa [Set.Ioc_union_Ioo_eq_Ioo hdhalf.le hd1] at hu

theorem gap6 (p q : ℝ) (hq : q ≤ -1) :
    Tendsto (fun b => ∫ x in (1 / 2 : ℝ)..b, integrand p q x)
      (nhdsWithin 1 (Set.Iio 1)) atTop := by
  let L := nhdsWithin (1 : ℝ) (Set.Iio 1)
  have hclose := (Metric.tendsto_nhds.1 (gap4 p q)) (1 / 2) (by norm_num)
  have hge : ∀ᶠ x : ℝ in L, (1 / 2 : ℝ) ≤ oneEndpointNormalized p q x := by
    filter_upwards [hclose] with x hx
    rw [Real.dist_eq] at hx
    linarith [(abs_lt.mp hx).1]
  obtain ⟨c, hc, hcs⟩ := (mem_nhdsLT_iff_exists_Ioo_subset).1 hge
  let e : ℝ := max c (1 / 2)
  let d : ℝ := (e + 1) / 2
  have hce : c ≤ e := le_max_left _ _
  have hhe : (1 / 2 : ℝ) ≤ e := le_max_right _ _
  have he1 : e < 1 := max_lt hc (by norm_num)
  have hcd : c < d := by unfold d; linarith
  have hhalfd : (1 / 2 : ℝ) < d := by unfold d; linarith
  have hd1 : d < 1 := by unfold d; linarith
  have hbdiv := endpointBaseDiverges q d hq hd1
  have hscaled : Tendsto
      (fun b => (1 / 2 : ℝ) * ∫ x in d..b, Real.rpow (1 - x) q) L atTop := by
    have h := hbdiv.atTop_mul_const (by norm_num : (0 : ℝ) < 1 / 2)
    simpa [mul_comm] using h
  have hle : ∀ᶠ b : ℝ in L,
      (1 / 2 : ℝ) * (∫ x in d..b, Real.rpow (1 - x) q) ≤
        ∫ x in (1 / 2 : ℝ)..b, integrand p q x := by
    filter_upwards [Ioo_mem_nhdsLT hd1] with b hb
    have hhalfb : (1 / 2 : ℝ) ≤ b := (hhalfd.trans hb.1).le
    have hfcont : ContinuousOn (integrand p q) (Set.uIcc (1 / 2) b) := by
      rw [Set.uIcc_of_le hhalfb]
      exact integrand_continuousOn_Icc p q (1 / 2) b (by norm_num) hb.2
    have hfb : IntervalIntegrable (integrand p q) volume (1 / 2) b :=
      hfcont.intervalIntegrable
    have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioc (1 / 2) b)] integrand p q := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      have hx0 : 0 < x := by linarith [hx.1]
      have hx1 : x < 1 := hx.2.trans_lt hb.2
      exact mul_nonneg (Real.rpow_nonneg hx0.le p)
        (Real.rpow_nonneg (Real.log_pos (one_lt_one_div hx0 hx1)).le q)
    have htailfull : (∫ x in d..b, integrand p q x) ≤
        ∫ x in (1 / 2 : ℝ)..b, integrand p q x :=
      intervalIntegral.integral_mono_interval hhalfd.le hb.1.le le_rfl hnonneg hfb
    have hbasecont : ContinuousOn (fun x : ℝ => Real.rpow (1 - x) q)
        (Set.uIcc d b) := by
      rw [Set.uIcc_of_le hb.1.le]
      apply continuousOn_of_forall_continuousAt
      intro x hx
      exact (continuousAt_const.sub continuousAt_id).rpow_const
        (Or.inl (sub_pos.mpr (hx.2.trans_lt hb.2)).ne')
    have hbint : IntervalIntegrable (fun x : ℝ => Real.rpow (1 - x) q) volume d b :=
      hbasecont.intervalIntegrable
    have hfcont2 : ContinuousOn (integrand p q) (Set.uIcc d b) := by
      rw [Set.uIcc_of_le hb.1.le]
      exact integrand_continuousOn_Icc p q d b (by linarith) hb.2
    have hfint : IntervalIntegrable (integrand p q) volume d b :=
      hfcont2.intervalIntegrable
    have hpoint : ∀ x ∈ Set.Icc d b,
        (1 / 2 : ℝ) * Real.rpow (1 - x) q ≤ integrand p q x := by
      intro x hx
      have hxlt : x < 1 := hx.2.trans_lt hb.2
      have hn := hcs ⟨hcd.trans_le hx.1, hxlt⟩
      calc
        (1 / 2 : ℝ) * Real.rpow (1 - x) q ≤
            oneEndpointNormalized p q x * Real.rpow (1 - x) q :=
          mul_le_mul_of_nonneg_right hn (Real.rpow_nonneg (by linarith) q)
        _ = integrand p q x := oneEndpointNormalized_mul p q x hxlt
    have htail : (∫ x in d..b, (1 / 2 : ℝ) * Real.rpow (1 - x) q) ≤
        ∫ x in d..b, integrand p q x :=
      intervalIntegral.integral_mono_on hb.1.le (hbint.const_mul (1 / 2)) hfint hpoint
    rw [intervalIntegral.integral_const_mul] at htail
    exact htail.trans htailfull
  exact tendsto_atTop_mono' L hle hscaled

theorem gap7 (p : ℝ) (hp : -1 < p) :
    0 < tau p := by
  unfold tau
  linarith

theorem gap8 (p : ℝ) (hp : -1 < p) :
    -1 < p - tau p := by
  unfold tau
  linarith

theorem gap9 (p q : ℝ) (hp : -1 < p) :
    Tendsto (zeroWeighted p q (tau p))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ↔
      Tendsto (slowRatio q (tau p))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have heq : zeroWeighted p q (tau p) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      slowRatio q (tau p) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact zeroWeighted_eq_slowRatio p q (tau p) x hx
  constructor
  · intro h
    exact h.congr' heq
  · intro h
    exact h.congr' heq.symm

theorem gap10 (p q : ℝ) (hp : -1 < p) :
    Tendsto (slowRatio q (tau p))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have htop : Tendsto
      (fun y : ℝ => Real.rpow (Real.log y) q / Real.rpow y (tau p))
      atTop (nhds 0) :=
    Asymptotics.IsLittleO.tendsto_div_nhds_zero
      (isLittleO_log_rpow_rpow_atTop q (gap7 p hp))
  have hinv : Tendsto (fun x : ℝ => 1 / x)
      (nhdsWithin 0 (Set.Ioi 0)) atTop := by
    simpa [one_div] using tendsto_inv_nhdsGT_zero
  have hc := htop.comp hinv
  simpa only [slowRatio] using hc

theorem gap11 (p q : ℝ) (hp : -1 < p) :
    Tendsto (zeroWeighted p q (tau p))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  exact (gap9 p q hp).2 (gap10 p q hp)

theorem gap12 (p : ℝ) (hp : -1 < p) :
    -p + tau p < 1 := by
  unfold tau
  linarith

theorem gap13 (p q : ℝ) (hp : -1 < p) :
    IntegrableAtZero p q := by
  let base : ℝ → ℝ := fun x => Real.rpow x (p - tau p)
  have hbase : IntegrableOn base (Set.Ioo (0 : ℝ) (1 / 2)) := by
    have hb := (intervalIntegral.integrableOn_Ioo_rpow_iff
      (by norm_num : (0 : ℝ) < 1 / 2)).2 (gap8 p hp)
    simpa only [base, Real.rpow_eq_pow] using hb
  have hbaseAt : IntegrableAtFilter base (nhdsWithin 0 (Set.Ioi 0)) volume :=
    ⟨Set.Ioo 0 (1 / 2), Ioo_mem_nhdsGT (by norm_num), hbase⟩
  have hOzero : zeroWeighted p q (tau p) =O[nhdsWithin 0 (Set.Ioi 0)]
      (fun _ : ℝ => (1 : ℝ)) := (gap11 p q hp).isBigO_one ℝ
  have hOprod := hOzero.mul
    (Asymptotics.isBigO_refl base (nhdsWithin 0 (Set.Ioi 0)))
  have heq : (fun x => zeroWeighted p q (tau p) x * base x) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      integrand p q := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact zeroWeighted_mul p q (tau p) x hx
  have hright : (fun x => (1 : ℝ) * base x) =ᶠ[nhdsWithin 0 (Set.Ioi 0)] base :=
    Filter.Eventually.of_forall (fun x => by simp)
  have hO : integrand p q =O[nhdsWithin 0 (Set.Ioi 0)] base :=
    hOprod.congr' heq hright
  have hmeas : AEStronglyMeasurable (integrand p q) volume := by
    apply Measurable.aestronglyMeasurable
    unfold integrand
    measurability
  have hAt : IntegrableAtFilter (integrand p q) (nhdsWithin 0 (Set.Ioi 0)) volume :=
    hO.integrableAtFilter hmeas.stronglyMeasurableAtFilter hbaseAt
  obtain ⟨s, hs, hsint⟩ := hAt
  obtain ⟨c, hc, hcs⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1 hs
  let d : ℝ := min c (1 / 4)
  have hd0 : 0 < d := lt_min hc (by norm_num)
  have hdhalf : d < (1 / 2 : ℝ) := (min_le_right _ _).trans_lt (by norm_num)
  have hnear : IntegrableOn (integrand p q) (Set.Ioo 0 d) :=
    hsint.mono (fun x hx => hcs ⟨hx.1, hx.2.trans_le (min_le_left _ _)⟩) le_rfl
  have hfar : IntegrableOn (integrand p q) (Set.Icc d (1 / 2)) :=
    (integrand_continuousOn_Icc p q d (1 / 2) hd0 (by norm_num)).integrableOn_Icc
  have hu := hnear.union hfar
  unfold IntegrableAtZero
  rwa [Set.Ioo_union_Icc_eq_Ioc hd0 hdhalf.le] at hu

theorem gap14 (p q x : ℝ) (hp : p ≤ -1) (hq : -1 < q)
    (hx0 : 0 < x) (hx1 : x ≤ 1 / 2) :
    integrand (-1) q x ≤ integrand p q x := by
  have hxle : x ≤ 1 := by linarith
  have hlog : 0 ≤ Real.log (1 / x) :=
    (Real.log_pos (one_lt_one_div hx0 (by linarith))).le
  unfold integrand
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_ge hx0 hxle hp)
    (Real.rpow_nonneg hlog q)

theorem gap15 (q : ℝ) (hq : -1 < q) :
    Tendsto (fun a => ∫ x in a..(1 / 2 : ℝ), integrand (-1) q x)
      (nhdsWithin 0 (Set.Ioi 0)) atTop := by
  have hq1 : 0 < q + 1 := by linarith
  have hinv : Tendsto (fun a : ℝ => 1 / a)
      (nhdsWithin 0 (Set.Ioi 0)) atTop := by
    simpa [one_div] using tendsto_inv_nhdsGT_zero
  have hlog : Tendsto (fun a : ℝ => Real.log (1 / a))
      (nhdsWithin 0 (Set.Ioi 0)) atTop := Real.tendsto_log_atTop.comp hinv
  have hrpow : Tendsto (fun a : ℝ => Real.rpow (Real.log (1 / a)) (q + 1))
      (nhdsWithin 0 (Set.Ioi 0)) atTop := (tendsto_rpow_atTop hq1).comp hlog
  have hdiv : Tendsto
      (fun a : ℝ => Real.rpow (Real.log (1 / a)) (q + 1) / (q + 1))
      (nhdsWithin 0 (Set.Ioi 0)) atTop := hrpow.atTop_div_const hq1
  have hanti : Tendsto (borderlineAntiderivative q)
      (nhdsWithin 0 (Set.Ioi 0)) atBot := by
    have hn := tendsto_neg_atTop_atBot.comp hdiv
    simpa only [borderlineAntiderivative, Function.comp_apply] using hn
  have hneganti : Tendsto (fun a => -(borderlineAntiderivative q a))
      (nhdsWithin 0 (Set.Ioi 0)) atTop := tendsto_neg_atBot_atTop.comp hanti
  have hlim : Tendsto
      (fun a => borderlineAntiderivative q (1 / 2) - borderlineAntiderivative q a)
      (nhdsWithin 0 (Set.Ioi 0)) atTop := by
    have h := (nhdsWithin 0 (Set.Ioi 0)).tendsto_atTop_add_const_left
      (borderlineAntiderivative q (1 / 2)) hneganti
    simpa [sub_eq_add_neg] using h
  apply hlim.congr'
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with a ha
  have hder : ∀ x ∈ Set.uIcc a (1 / 2 : ℝ),
      HasDerivAt (borderlineAntiderivative q) (integrand (-1) q x) x := by
    intro x hx
    rw [Set.uIcc_of_le ha.2.le] at hx
    exact borderlineAntiderivative_hasDerivAt q x hq
      (ha.1.trans_le hx.1) (hx.2.trans_lt (by norm_num))
  have hcont : ContinuousOn (integrand (-1) q) (Set.uIcc a (1 / 2 : ℝ)) := by
    rw [Set.uIcc_of_le ha.2.le]
    exact integrand_continuousOn_Icc (-1) q a (1 / 2) ha.1 (by norm_num)
  have hint : IntervalIntegrable (integrand (-1) q) volume a (1 / 2 : ℝ) :=
    hcont.intervalIntegrable
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt hder hint).symm

theorem gap16 (p q : ℝ) (hp : p ≤ -1) (hq : -1 < q) :
    Tendsto (fun a => ∫ x in a..(1 / 2 : ℝ), integrand p q x)
      (nhdsWithin 0 (Set.Ioi 0)) atTop := by
  let L := nhdsWithin (0 : ℝ) (Set.Ioi 0)
  have hle : ∀ᶠ a : ℝ in L,
      (∫ x in a..(1 / 2 : ℝ), integrand (-1) q x) ≤
        ∫ x in a..(1 / 2 : ℝ), integrand p q x := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with a ha
    have hcont1 : ContinuousOn (integrand (-1) q) (Set.uIcc a (1 / 2)) := by
      rw [Set.uIcc_of_le ha.2.le]
      exact integrand_continuousOn_Icc (-1) q a (1 / 2) ha.1 (by norm_num)
    have hcontp : ContinuousOn (integrand p q) (Set.uIcc a (1 / 2)) := by
      rw [Set.uIcc_of_le ha.2.le]
      exact integrand_continuousOn_Icc p q a (1 / 2) ha.1 (by norm_num)
    apply intervalIntegral.integral_mono_on ha.2.le
      hcont1.intervalIntegrable hcontp.intervalIntegrable
    intro x hx
    exact gap14 p q x hp hq (ha.1.trans_le hx.1) hx.2
  exact tendsto_atTop_mono' L hle (gap15 q hq)

theorem gap17 (p q : ℝ) :
    (-1 < p ∧ -1 < q) ↔ IntegrableUnit p q := by
  constructor
  · rintro ⟨hp, hq⟩
    exact (gap1 p q).2 ⟨gap13 p q hp, gap5 p q hq⟩
  · intro hunit
    have hparts := (gap1 p q).1 hunit
    have hq : -1 < q := by
      by_contra hn
      have hqle : q ≤ -1 := le_of_not_gt hn
      have hint : IntervalIntegrable (integrand p q) volume (1 / 2) 1 :=
        (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)).2 hparts.2
      exact (not_tendsto_atTop_of_tendsto_nhds
        (primitive_tendsto_right (by norm_num) hint)) (gap6 p q hqle)
    have hp : -1 < p := by
      by_contra hn
      have hple : p ≤ -1 := le_of_not_gt hn
      have hint : IntervalIntegrable (integrand p q) volume 0 (1 / 2) :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).2 hparts.1
      exact (not_tendsto_atTop_of_tendsto_nhds
        (primitive_tendsto_left (by norm_num) hint)) (gap16 p q hple hq)
    exact ⟨hp, hq⟩

end
end ProofGap.Exercise2362
