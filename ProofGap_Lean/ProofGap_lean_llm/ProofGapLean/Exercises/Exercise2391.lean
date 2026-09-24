import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace ProofGap.Exercise2391
noncomputable section

open Filter Set MeasureTheory
open scoped Interval

def logInv (ξ : ℝ) : ℝ := 1 / Real.log ξ

def alpha (ξ : ℝ) : ℝ :=
  if ξ = 1 then 0
  else 1 + 2 * (Real.log ξ - (ξ - 1)) / (ξ - 1) ^ 2

def logRemainder (ξ : ℝ) : ℝ :=
  ((alpha ξ - 1) / 2) /
    (1 + (alpha ξ - 1) / 2 * (ξ - 1))

def LiExists (x : ℝ) : Prop :=
  if x < 1 then
    ∃ L : ℝ,
      Tendsto (fun ε => ∫ ξ in ε..x, logInv ξ)
        (nhdsWithin 0 (Ioi 0)) (nhds L)
  else if 1 < x then
    ∃ L : ℝ,
      Tendsto
        (fun ε =>
          (∫ ξ in ε..(1 - ε), logInv ξ) +
            ∫ ξ in (1 + ε)..x, logInv ξ)
        (nhdsWithin 0 (Ioi 0)) (nhds L)
  else False

private def logQuadraticRatio (ξ : ℝ) : ℝ :=
  (Real.log ξ - (ξ - 1)) / (ξ - 1) ^ 2

private theorem continuousAt_logInv_zero : ContinuousAt logInv 0 := by
  have hp : Tendsto logInv (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
    have h := tendsto_inv_atBot_zero.comp Real.tendsto_log_nhdsNE_zero
    apply h.congr'
    exact Filter.Eventually.of_forall (fun ξ => by simp [logInv, one_div, Function.comp_apply])
  rw [ContinuousAt, ← pure_sup_nhdsNE, tendsto_sup]
  constructor
  · exact tendsto_pure_nhds logInv 0
  · simpa [logInv] using hp

private theorem continuousAt_logInv (ξ : ℝ) (hξ : 0 < ξ) (hξ1 : ξ ≠ 1) :
    ContinuousAt logInv ξ := by
  unfold logInv
  exact continuousAt_const.div (Real.continuousAt_log hξ.ne')
    (Real.log_ne_zero_of_pos_of_ne_one hξ hξ1)

private theorem logInv_continuousOn_Icc (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b < 1) :
    ContinuousOn logInv (Icc 0 b) := by
  apply continuousOn_of_forall_continuousAt
  intro ξ hξ
  by_cases hξ0 : ξ = 0
  · simpa [hξ0] using continuousAt_logInv_zero
  · exact continuousAt_logInv ξ (lt_of_le_of_ne hξ.1 (Ne.symm hξ0)) (by linarith [hξ.2])

private theorem primitive_tendsto_right {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hint : IntervalIntegrable f volume a b) :
    Tendsto (fun x => ∫ t in a..x, f t) (nhdsWithin b (Iio b))
      (nhds (∫ t in a..b, f t)) := by
  have hu : IntegrableOn f (Set.uIcc a b) := (intervalIntegrable_iff').1 hint
  have hc := (intervalIntegral.continuousOn_primitive_interval hu) b
    (by rw [Set.uIcc_of_le hab.le]; exact ⟨hab.le, le_rfl⟩)
  have hfilter : nhdsWithin b (Iio b) ≤ nhdsWithin b (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab.le]
    exact le_inf inf_le_left (Filter.le_principal_iff.mpr (Icc_mem_nhdsLT hab))
  exact hc.tendsto.mono_left hfilter

private theorem primitive_tendsto_left {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hint : IntervalIntegrable f volume a b) :
    Tendsto (fun x => ∫ t in x..b, f t) (nhdsWithin a (Ioi a))
      (nhds (∫ t in a..b, f t)) := by
  have hu : IntegrableOn f (Set.uIcc a b) := (intervalIntegrable_iff').1 hint
  have hc := (intervalIntegral.continuousOn_primitive_interval_left hu) a
    (by rw [Set.uIcc_of_le hab.le]; exact ⟨le_rfl, hab.le⟩)
  have hfilter : nhdsWithin a (Ioi a) ≤ nhdsWithin a (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab.le]
    exact le_inf inf_le_left (Filter.le_principal_iff.mpr (Icc_mem_nhdsGT hab))
  exact hc.tendsto.mono_left hfilter

private theorem logQuadraticRatio_tendsto :
    Tendsto logQuadraticRatio (nhdsWithin 1 ({1} : Set ℝ)ᶜ) (nhds (-(1 / 2 : ℝ))) := by
  let F : ℝ → ℝ := fun ξ => Real.log ξ - (ξ - 1)
  let F' : ℝ → ℝ := fun ξ => ξ⁻¹ - 1
  let G : ℝ → ℝ := fun ξ => (ξ - 1) ^ 2
  let G' : ℝ → ℝ := fun ξ => 2 * (ξ - 1)
  have hFder : ∀ ξ ∈ Ioo (1 / 2 : ℝ) 2, HasDerivAt F (F' ξ) ξ := by
    intro ξ hξ
    unfold F F'
    convert (Real.hasDerivAt_log (by linarith [hξ.1])).sub
      ((hasDerivAt_id ξ).sub_const 1) using 1 <;> ring
  have hGder : ∀ ξ : ℝ, HasDerivAt G (G' ξ) ξ := by
    intro ξ
    simpa [G, G', id, mul_comm] using ((hasDerivAt_id ξ).sub_const 1).pow 2
  have hratioRight : Tendsto (fun ξ => F' ξ / G' ξ)
      (nhdsWithin 1 (Ioi 1)) (nhds (-(1 / 2 : ℝ))) := by
    have hcont : Tendsto (fun ξ : ℝ => -(1 / (2 * ξ)))
        (nhdsWithin 1 (Ioi 1)) (nhds (-(1 / 2 : ℝ))) := by
      have hcden : ContinuousAt (fun ξ : ℝ => 2 * ξ) 1 :=
        continuousAt_const.mul continuousAt_id
      have hc : ContinuousAt (fun ξ : ℝ => -(1 / (2 * ξ))) 1 :=
        (continuousAt_const.div hcden (by norm_num)).neg
      have h := hc.tendsto
      simpa using h.mono_left inf_le_left
    apply hcont.congr'
    filter_upwards [self_mem_nhdsWithin] with ξ hξ
    unfold F' G'
    have hξ0 : ξ ≠ 0 := (zero_lt_one.trans hξ).ne'
    have hξ1 : ξ - 1 ≠ 0 := sub_ne_zero.mpr hξ.ne'
    field_simp [hξ0, hξ1]
    ring
  have hratioLeft : Tendsto (fun ξ => F' ξ / G' ξ)
      (nhdsWithin 1 (Iio 1)) (nhds (-(1 / 2 : ℝ))) := by
    have hcont : Tendsto (fun ξ : ℝ => -(1 / (2 * ξ)))
        (nhdsWithin 1 (Iio 1)) (nhds (-(1 / 2 : ℝ))) := by
      have hcden : ContinuousAt (fun ξ : ℝ => 2 * ξ) 1 :=
        continuousAt_const.mul continuousAt_id
      have hc : ContinuousAt (fun ξ : ℝ => -(1 / (2 * ξ))) 1 :=
        (continuousAt_const.div hcden (by norm_num)).neg
      have h := hc.tendsto
      simpa using h.mono_left inf_le_left
    apply hcont.congr'
    filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsLT (by norm_num : (1 / 2 : ℝ) < 1)]
      with ξ hξ hξhalf
    unfold F' G'
    have hξ0 : ξ ≠ 0 := (by linarith [hξhalf.1] : 0 < ξ).ne'
    have hξ1 : ξ - 1 ≠ 0 := sub_ne_zero.mpr hξ.ne
    field_simp [hξ0, hξ1]
    ring
  have hFcontRight : ContinuousOn F (Ico (1 : ℝ) 2) := by
    apply continuousOn_of_forall_continuousAt
    intro ξ hξ
    unfold F
    exact (Real.continuousAt_log (by linarith [hξ.1])).sub
      (continuousAt_id.sub continuousAt_const)
  have hFcontLeft : ContinuousOn F (Ioc (1 / 2 : ℝ) 1) := by
    apply continuousOn_of_forall_continuousAt
    intro ξ hξ
    unfold F
    exact (Real.continuousAt_log (by linarith [hξ.1])).sub
      (continuousAt_id.sub continuousAt_const)
  have hGcont : Continuous G := by
    unfold G
    fun_prop
  have hright : Tendsto (fun ξ => F ξ / G ξ)
      (nhdsWithin 1 (Ioi 1)) (nhds (-(1 / 2 : ℝ))) := by
    apply HasDerivAt.lhopital_zero_right_on_Ico (b := 2) (by norm_num)
      (fun ξ hξ => hFder ξ ⟨(by linarith [hξ.1]), hξ.2⟩)
      (fun ξ _ => hGder ξ) hFcontRight hGcont.continuousOn
    · intro ξ hξ
      unfold G'
      linarith [hξ.1]
    · simp [F]
    · simp [G]
    · exact hratioRight
  have hleft : Tendsto (fun ξ => F ξ / G ξ)
      (nhdsWithin 1 (Iio 1)) (nhds (-(1 / 2 : ℝ))) := by
    apply HasDerivAt.lhopital_zero_left_on_Ioc (a := (1 / 2 : ℝ)) (by norm_num)
      (fun ξ hξ => hFder ξ ⟨hξ.1, (by linarith [hξ.2])⟩)
      (fun ξ _ => hGder ξ) hFcontLeft hGcont.continuousOn
    · intro ξ hξ
      unfold G'
      linarith [hξ.2]
    · simp [F]
    · simp [G]
    · exact hratioLeft
  unfold logQuadraticRatio
  unfold F G at hleft hright
  rw [← nhdsLT_sup_nhdsGT, tendsto_sup]
  exact ⟨hleft, hright⟩

theorem gap1 :
    Tendsto logInv (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
  have h := tendsto_inv_atBot_zero.comp Real.tendsto_log_nhdsGT_zero
  apply h.congr'
  exact Filter.Eventually.of_forall (fun ξ => by simp [logInv, one_div, Function.comp_apply])

theorem gap2 (x : ℝ) (hx₀ : 0 ≤ x) (hx₁ : x < 1) :
    ∃ L : ℝ,
      Tendsto (fun ε => ∫ ξ in ε..x, logInv ξ)
        (nhdsWithin 0 (Ioi 0)) (nhds L) := by
  let b : ℝ := (x + 1) / 2
  have hb0 : 0 < b := by unfold b; linarith
  have hxb : x < b := by unfold b; linarith
  have hb1 : b < 1 := by unfold b; linarith
  have hcont : ContinuousOn logInv (Icc 0 b) :=
    logInv_continuousOn_Icc b hb0.le hb1
  have hInt : IntervalIntegrable logInv volume 0 b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hb0.le]
    exact hcont
  have hxInt : IntervalIntegrable logInv volume x b :=
    hInt.mono_set (Set.uIcc_subset_uIcc
      (by rw [Set.uIcc_of_le hb0.le]; exact ⟨hx₀, hxb.le⟩)
      (by rw [Set.uIcc_of_le hb0.le]; exact ⟨hb0.le, le_rfl⟩))
  let L : ℝ := (∫ ξ in (0 : ℝ)..b, logInv ξ) - ∫ ξ in x..b, logInv ξ
  refine ⟨L, ?_⟩
  have hleft := primitive_tendsto_left (f := logInv) hb0 hInt
  have hlim : Tendsto
      (fun ε => (∫ ξ in ε..b, logInv ξ) - ∫ ξ in x..b, logInv ξ)
      (nhdsWithin 0 (Ioi 0)) (nhds L) := by
    have h := hleft.sub_const (∫ ξ in x..b, logInv ξ)
    simpa [L] using h
  apply hlim.congr'
  filter_upwards [Ioo_mem_nhdsGT hb0] with ε hε
  have hεx : IntervalIntegrable logInv volume ε x :=
    hInt.mono_set (Set.uIcc_subset_uIcc
      (by rw [Set.uIcc_of_le hb0.le]; exact ⟨hε.1.le, hε.2.le⟩)
      (by rw [Set.uIcc_of_le hb0.le]; exact ⟨hx₀, hxb.le⟩))
  have hadd := intervalIntegral.integral_add_adjacent_intervals hεx hxInt
  linarith

theorem gap3 (a c b : ℝ) (ha : 0 < a) (hac : a < c) (hcb : c < b) :
    Tendsto
      (fun ε =>
        (∫ x in a..(c - ε), 1 / (x - c)) +
          ∫ x in (c + ε)..b, 1 / (x - c))
      (nhdsWithin 0 (Ioi 0))
      (nhds (Real.log ((b - c) / (c - a)))) := by
  apply tendsto_const_nhds.congr'
  let d : ℝ := min (c - a) (b - c)
  have hd : 0 < d := lt_min (sub_pos.mpr hac) (sub_pos.mpr hcb)
  filter_upwards [Ioo_mem_nhdsGT hd] with ε hε
  have hεbound : ε < min (c - a) (b - c) := by simpa [d] using hε.2
  have hleftOrder : a - c < -ε := by
    linarith [hεbound.trans_le (min_le_left (c - a) (b - c))]
  have hrightOrder : ε < b - c := hεbound.trans_le (min_le_right _ _)
  have hzleft : 0 ∉ Set.uIcc (a - c) (-ε) := by
    rw [Set.uIcc_of_le hleftOrder.le]
    intro h0
    linarith [h0.2, hε.1]
  have hzright : 0 ∉ Set.uIcc ε (b - c) := by
    rw [Set.uIcc_of_le hrightOrder.le]
    intro h0
    linarith [h0.1, hε.1]
  simp only [one_div]
  rw [intervalIntegral.integral_comp_sub_right (fun y : ℝ => y⁻¹) c,
    intervalIntegral.integral_comp_sub_right (fun y : ℝ => y⁻¹) c]
  rw [show c - ε - c = -ε by ring, show c + ε - c = ε by ring,
    integral_inv hzleft, integral_inv hzright]
  have hp1 : 0 < (-ε) / (a - c) :=
    div_pos_of_neg_of_neg (neg_neg_of_pos hε.1) (sub_neg.mpr hac)
  have hp2 : 0 < (b - c) / ε := div_pos (sub_pos.mpr hcb) hε.1
  rw [← Real.log_mul hp1.ne' hp2.ne']
  congr 1
  have hca : c - a ≠ 0 := sub_ne_zero.mpr hac.ne'
  have hac' : a - c ≠ 0 := sub_ne_zero.mpr hac.ne
  have hbc : b - c ≠ 0 := sub_ne_zero.mpr hcb.ne'
  field_simp [hε.1.ne', hca, hac', hbc]
  ring

theorem gap4 (ξ : ℝ) (hξ : 0 < ξ) :
    Real.log ξ =
      ξ - 1 + (alpha ξ - 1) * (ξ - 1) ^ 2 / 2 := by
  by_cases hξ1 : ξ = 1
  · subst ξ
    simp [alpha]
  · unfold alpha
    rw [if_neg hξ1]
    have ht : ξ - 1 ≠ 0 := sub_ne_zero.mpr hξ1
    field_simp [ht]
    ring

theorem gap5 :
    Tendsto alpha (nhds 1) (nhds 0) := by
  have hp : Tendsto alpha (nhdsWithin 1 ({1} : Set ℝ)ᶜ) (nhds 0) := by
    have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) (nhdsWithin 1 ({1} : Set ℝ)ᶜ)
        (nhds 1) := tendsto_const_nhds
    have htwo : Tendsto (fun _ : ℝ => (2 : ℝ)) (nhdsWithin 1 ({1} : Set ℝ)ᶜ)
        (nhds 2) := tendsto_const_nhds
    have h := hone.add (htwo.mul logQuadraticRatio_tendsto)
    have h' : Tendsto (fun ξ => 1 + 2 * logQuadraticRatio ξ)
        (nhdsWithin 1 ({1} : Set ℝ)ᶜ) (nhds 0) := by simpa using h
    apply h'.congr'
    filter_upwards [self_mem_nhdsWithin] with ξ hξ
    unfold alpha logQuadraticRatio
    have hξ1 : ξ ≠ 1 := by simpa using hξ
    rw [if_neg hξ1]
    ring
  rw [← pure_sup_nhdsNE, tendsto_sup]
  constructor
  · simpa [alpha] using tendsto_pure_nhds alpha 1
  · exact hp

theorem gap6 (ξ : ℝ) (hξ₀ : 0 < ξ) (hξ₁ : ξ ≠ 1) :
    logInv ξ = 1 / (ξ - 1) - logRemainder ξ := by
  let t : ℝ := ξ - 1
  let a : ℝ := (alpha ξ - 1) / 2
  let u : ℝ := 1 + a * t
  have ht : t ≠ 0 := by unfold t; exact sub_ne_zero.mpr hξ₁
  have hlog : Real.log ξ ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one hξ₀ hξ₁
  have hfactor : Real.log ξ = t * u := by
    unfold t u a
    rw [gap4 ξ hξ₀]
    ring
  have hfac : u ≠ 0 := by
    intro hzero
    rw [hfactor, hzero, mul_zero] at hlog
    exact hlog rfl
  unfold logInv logRemainder
  change 1 / Real.log ξ = 1 / t - a / u
  rw [hfactor]
  field_simp [ht, hfac]
  ring

theorem gap7 :
    ∃ δ > 0, ∃ M : ℝ, ∀ ξ : ℝ,
      0 < |ξ - 1| → |ξ - 1| < δ → |logRemainder ξ| ≤ M := by
  have ha1 : Tendsto (fun ξ => (alpha ξ - 1) / 2) (nhds 1) (nhds (-(1 / 2 : ℝ))) := by
    have h := (gap5.sub_const 1).div_const 2
    convert h using 1 <;> norm_num
  have ht : Tendsto (fun ξ : ℝ => ξ - 1) (nhds 1) (nhds 0) := by
    have hc : ContinuousAt (fun ξ : ℝ => ξ - 1) 1 :=
      continuousAt_id.sub continuousAt_const
    simpa using hc.tendsto
  have hden : Tendsto (fun ξ => 1 + (alpha ξ - 1) / 2 * (ξ - 1))
      (nhds 1) (nhds 1) := by
    simpa using tendsto_const_nhds.add (ha1.mul ht)
  have hrem : Tendsto logRemainder (nhds 1) (nhds (-(1 / 2 : ℝ))) := by
    unfold logRemainder
    simpa using ha1.div hden one_ne_zero
  have hevent := (Metric.tendsto_nhds.1 hrem) 1 zero_lt_one
  obtain ⟨δ, hδ, hball⟩ := (Metric.mem_nhds_iff.1 hevent)
  refine ⟨δ, hδ, 2, ?_⟩
  intro ξ _ hξδ
  have hb := hball (by
    rw [Metric.mem_ball, Real.dist_eq]
    simpa [abs_sub_comm] using hξδ)
  change dist (logRemainder ξ) (-(1 / 2 : ℝ)) < 1 at hb
  rw [Real.dist_eq] at hb
  have hb' : |logRemainder ξ + 1 / 2| < 1 := by
    convert hb using 1 <;> ring
  have htri := abs_add_le (logRemainder ξ - (-(1 / 2 : ℝ))) (-(1 / 2 : ℝ))
  have heq : logRemainder ξ - (-(1 / 2 : ℝ)) + (-(1 / 2 : ℝ)) =
      logRemainder ξ := by ring
  rw [heq] at htri
  norm_num at htri ⊢
  linarith [hb']

private theorem logRemainder_tendsto_one :
    Tendsto logRemainder (nhds 1) (nhds (-(1 / 2 : ℝ))) := by
  have ha1 : Tendsto (fun ξ => (alpha ξ - 1) / 2) (nhds 1)
      (nhds (-(1 / 2 : ℝ))) := by
    have h := (gap5.sub_const 1).div_const 2
    convert h using 1 <;> norm_num
  have ht : Tendsto (fun ξ : ℝ => ξ - 1) (nhds 1) (nhds 0) := by
    have hc : ContinuousAt (fun ξ : ℝ => ξ - 1) 1 :=
      continuousAt_id.sub continuousAt_const
    simpa using hc.tendsto
  have hden : Tendsto (fun ξ => 1 + (alpha ξ - 1) / 2 * (ξ - 1))
      (nhds 1) (nhds 1) := by
    simpa using tendsto_const_nhds.add (ha1.mul ht)
  unfold logRemainder
  simpa using ha1.div hden one_ne_zero

private theorem continuousAt_logRemainder (ξ : ℝ) (hξ : 0 < ξ) :
    ContinuousAt logRemainder ξ := by
  by_cases hξ1 : ξ = 1
  · subst ξ
    have hv : logRemainder 1 = -(1 / 2 : ℝ) := by
      norm_num [logRemainder, alpha]
    rw [ContinuousAt, hv]
    exact logRemainder_tendsto_one
  · have hc : ContinuousAt (fun y : ℝ => 1 / (y - 1) - logInv y) ξ := by
      exact (continuousAt_const.div (continuousAt_id.sub continuousAt_const)
        (sub_ne_zero.mpr hξ1)).sub (continuousAt_logInv ξ hξ hξ1)
    rw [ContinuousAt]
    have hval : 1 / (ξ - 1) - logInv ξ = logRemainder ξ := by
      linarith [gap6 ξ hξ hξ1]
    rw [← hval]
    apply hc.tendsto.congr'
    filter_upwards [Ioi_mem_nhds hξ, eventually_ne_nhds hξ1] with y hy hy1
    have h := gap6 y hy hy1
    linarith

private theorem logRemainder_continuousOn_Icc (a b : ℝ) (ha : 0 < a) :
    ContinuousOn logRemainder (Icc a b) := by
  apply continuousOn_of_forall_continuousAt
  intro ξ hξ
  exact continuousAt_logRemainder ξ (ha.trans_le hξ.1)

private theorem logInv_continuousOn_Icc_right (a b : ℝ) (ha : 1 < a) :
    ContinuousOn logInv (Icc a b) := by
  apply continuousOn_of_forall_continuousAt
  intro ξ hξ
  exact continuousAt_logInv ξ (zero_lt_one.trans (ha.trans_le hξ.1))
    (by linarith [ha, hξ.1])

private theorem invSub_continuousOn_Icc_left (a b : ℝ) (hb : b < 1) :
    ContinuousOn (fun ξ : ℝ => 1 / (ξ - 1)) (Icc a b) := by
  apply continuousOn_of_forall_continuousAt
  intro ξ hξ
  exact continuousAt_const.div (continuousAt_id.sub continuousAt_const)
    (by linarith [hξ.2, hb])

private theorem invSub_continuousOn_Icc_right (a b : ℝ) (ha : 1 < a) :
    ContinuousOn (fun ξ : ℝ => 1 / (ξ - 1)) (Icc a b) := by
  apply continuousOn_of_forall_continuousAt
  intro ξ hξ
  exact continuousAt_const.div (continuousAt_id.sub continuousAt_const)
    (by linarith [hξ.1, ha])

theorem gap8 (x : ℝ) (hx : 1 < x) :
    LiExists x := by
  let a : ℝ := 1 / 2
  obtain ⟨L₀, hL₀⟩ := gap2 a (by norm_num) (by norm_num)
  have hsing := gap3 a 1 x (by norm_num) (by norm_num) hx
  have hremA1 : IntervalIntegrable logRemainder volume a 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : a ≤ 1)]
    exact logRemainder_continuousOn_Icc a 1 (by norm_num [a])
  have hrem1x : IntervalIntegrable logRemainder volume 1 x := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hx.le]
    exact logRemainder_continuousOn_Icc 1 x zero_lt_one
  let l := nhdsWithin (0 : ℝ) (Ioi 0)
  have heps : Tendsto (fun ε : ℝ => ε) l (nhds 0) :=
    tendsto_id.mono_left inf_le_left
  have hlmem : ∀ᶠ ε : ℝ in l, ε ∈ Ioi 0 := by
    unfold l
    exact self_mem_nhdsWithin
  have hminus : Tendsto (fun ε : ℝ => 1 - ε) l (nhdsWithin 1 (Iio 1)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using tendsto_const_nhds.sub heps
    · exact hlmem.mono (fun ε hε => by
        have hε' : 0 < ε := hε
        show 1 - ε < 1
        linarith)
  have hplus : Tendsto (fun ε : ℝ => 1 + ε) l (nhdsWithin 1 (Ioi 1)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using tendsto_const_nhds.add heps
    · exact hlmem.mono (fun ε hε => by
        have hε' : 0 < ε := hε
        show 1 < 1 + ε
        linarith)
  have hremLeft : Tendsto (fun ε => ∫ ξ in a..(1 - ε), logRemainder ξ) l
      (nhds (∫ ξ in a..1, logRemainder ξ)) :=
    (primitive_tendsto_right (by norm_num : a < 1) hremA1).comp hminus
  have hremRight : Tendsto (fun ε => ∫ ξ in (1 + ε)..x, logRemainder ξ) l
      (nhds (∫ ξ in 1..x, logRemainder ξ)) :=
    (primitive_tendsto_left hx hrem1x).comp hplus
  have hrem := hremLeft.add hremRight
  let L : ℝ := L₀ + Real.log ((x - 1) / (1 - a)) -
    ((∫ ξ in a..1, logRemainder ξ) + ∫ ξ in 1..x, logRemainder ξ)
  have hlim : Tendsto
      (fun ε =>
        (∫ ξ in ε..a, logInv ξ) +
          ((∫ ξ in a..(1 - ε), 1 / (ξ - 1)) +
            ∫ ξ in (1 + ε)..x, 1 / (ξ - 1)) -
          ((∫ ξ in a..(1 - ε), logRemainder ξ) +
            ∫ ξ in (1 + ε)..x, logRemainder ξ))
      l (nhds L) := by
    have h := (hL₀.add hsing).sub hrem
    simpa [L] using h
  unfold LiExists
  rw [if_neg (by linarith : ¬x < 1), if_pos hx]
  refine ⟨L, ?_⟩
  apply hlim.congr'
  let d : ℝ := min a (x - 1)
  have hd : 0 < d := lt_min (by norm_num [a]) (sub_pos.mpr hx)
  filter_upwards [Ioo_mem_nhdsGT hd] with ε hε
  have hεbound : ε < min a (x - 1) := by simpa [d] using hε.2
  have hεa : ε < a := hεbound.trans_le (min_le_left _ _)
  have ha0 : 0 < a := by norm_num [a]
  have h1m : a < 1 - ε := by
    dsimp [a] at hεa ⊢
    linarith
  have h1p : 1 + ε < x := by
    linarith [hεbound.trans_le (min_le_right a (x - 1))]
  have hlog0a : IntervalIntegrable logInv volume 0 a := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ a)]
    exact logInv_continuousOn_Icc a (by norm_num) (by norm_num)
  have hlogεa : IntervalIntegrable logInv volume ε a :=
    hlog0a.mono_set (Set.uIcc_subset_uIcc
      (by rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ a)]; exact ⟨hε.1.le, hεa.le⟩)
      (by rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ a)]; exact ⟨by norm_num [a], le_rfl⟩))
  have hlogLeft : IntervalIntegrable logInv volume a (1 - ε) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le h1m.le]
    exact (logInv_continuousOn_Icc (1 - ε) (by linarith [hε.1]) (by linarith [hε.1])).mono
      (Set.Icc_subset_Icc_left (by norm_num [a]))
  have hlogRight : IntervalIntegrable logInv volume (1 + ε) x := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le h1p.le]
    exact logInv_continuousOn_Icc_right (1 + ε) x (by linarith [hε.1])
  have hsingLeft : IntervalIntegrable (fun ξ : ℝ => 1 / (ξ - 1)) volume a (1 - ε) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le h1m.le]
    exact invSub_continuousOn_Icc_left a (1 - ε) (by linarith [hε.1])
  have hsingRight : IntervalIntegrable (fun ξ : ℝ => 1 / (ξ - 1)) volume (1 + ε) x := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le h1p.le]
    exact invSub_continuousOn_Icc_right (1 + ε) x (by linarith [hε.1])
  have hremLeftInt : IntervalIntegrable logRemainder volume a (1 - ε) :=
    hremA1.mono_set (Set.uIcc_subset_uIcc
      (by rw [Set.uIcc_of_le (by norm_num : a ≤ 1)]; exact ⟨le_rfl, by norm_num [a]⟩)
      (by rw [Set.uIcc_of_le (by norm_num : a ≤ 1)]; exact ⟨h1m.le, by linarith [hε.1]⟩))
  have hremRightInt : IntervalIntegrable logRemainder volume (1 + ε) x :=
    hrem1x.mono_set (Set.uIcc_subset_uIcc
      (by rw [Set.uIcc_of_le hx.le]; exact ⟨by linarith [hε.1], h1p.le⟩)
      (by rw [Set.uIcc_of_le hx.le]; exact ⟨hx.le, le_rfl⟩))
  have hadd := intervalIntegral.integral_add_adjacent_intervals hlogεa hlogLeft
  have heqLeft : (∫ ξ in a..(1 - ε), logInv ξ) =
      ∫ ξ in a..(1 - ε), (1 / (ξ - 1) - logRemainder ξ) := by
    apply intervalIntegral.integral_congr
    intro ξ hξ
    rw [Set.uIcc_of_le h1m.le] at hξ
    exact gap6 ξ (by linarith [hξ.1, ha0]) (by linarith [hξ.2, hε.1])
  have heqRight : (∫ ξ in (1 + ε)..x, logInv ξ) =
      ∫ ξ in (1 + ε)..x, (1 / (ξ - 1) - logRemainder ξ) := by
    apply intervalIntegral.integral_congr
    intro ξ hξ
    rw [Set.uIcc_of_le h1p.le] at hξ
    exact gap6 ξ (by linarith [hξ.1, hε.1]) (by linarith [hξ.1, hε.1])
  rw [← hadd, heqLeft, heqRight,
    intervalIntegral.integral_sub hsingLeft hremLeftInt,
    intervalIntegral.integral_sub hsingRight hremRightInt]
  ring

theorem gap9 (x : ℝ) (hx₀ : 0 ≤ x) (hx₁ : x ≠ 1) :
    LiExists x := by
  rcases lt_or_gt_of_ne hx₁ with hx | hx
  · unfold LiExists
    rw [if_pos hx]
    exact gap2 x hx₀ hx
  · exact gap8 x hx

theorem gap10 (x : ℝ) (hx₀ : 0 ≤ x) (hx₁ : x ≠ 1) :
    LiExists x := by
  exact gap9 x hx₀ hx₁

end
end ProofGap.Exercise2391
