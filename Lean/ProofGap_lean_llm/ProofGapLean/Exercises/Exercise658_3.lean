import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise658_3

noncomputable section

def cbrt (x : ℝ) : ℝ := Real.rpow x (1 / 3)
def target (x : ℝ) : ℝ := x / cbrt (1 - x ^ 3)
def model (x : ℝ) : ℝ := (1 / cbrt 3) * (1 / cbrt (1 - x))

/-- Exercise 658_3, gap 1; restrict to the left neighborhood of `1`. -/
theorem gap1 (x : ℝ) (hx0 : 0 < x) (hx1 : x < 1) :
    target x =
      (x / cbrt (1 - x)) * (1 / cbrt (1 + x + x ^ 2)) := by
  have hleft : 0 < 1 - x := sub_pos.mpr hx1
  have hright : 0 < 1 + x + x ^ 2 := by
    nlinarith [sq_nonneg x]
  have hfactor : 1 - x ^ 3 = (1 - x) * (1 + x + x ^ 2) := by
    ring
  have ha : Real.rpow (1 - x) (1 / 3) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hleft _)
  have hb : Real.rpow (1 + x + x ^ 2) (1 / 3) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hright _)
  have hrpow :
      Real.rpow ((1 - x) * (1 + x + x ^ 2)) (1 / 3) =
        Real.rpow (1 - x) (1 / 3) *
          Real.rpow (1 + x + x ^ 2) (1 / 3) := by
    exact Real.mul_rpow (le_of_lt hleft) (le_of_lt hright)
  unfold target cbrt
  rw [hfactor, hrpow]
  field_simp [ha, hb]

/-- Exercise 658_3, gap 2. -/
theorem gap2 :
    Filter.Tendsto (fun x : ℝ => target x / model x)
      (nhdsWithin 1 (Set.Iio 1)) (nhds 1) := by
  have hpos_nhds : ∀ᶠ x : ℝ in nhds (1 : ℝ), (0 : ℝ) < x :=
    eventually_gt_nhds (show (0 : ℝ) < 1 by norm_num)
  have hpos : ∀ᶠ x : ℝ in nhdsWithin 1 (Set.Iio 1), 0 < x :=
    hpos_nhds.filter_mono inf_le_left
  have hformula :
      (fun x : ℝ => target x / model x) =ᶠ[nhdsWithin 1 (Set.Iio 1)]
        (fun x => x * cbrt 3 / cbrt (1 + x + x ^ 2)) := by
    filter_upwards [hpos, self_mem_nhdsWithin] with x hx0 hx1
    change x < 1 at hx1
    have hA : cbrt (1 - x) ≠ 0 := by
      unfold cbrt
      exact ne_of_gt (Real.rpow_pos_of_pos (sub_pos.mpr hx1) _)
    have hq : 0 < 1 + x + x ^ 2 := by
      nlinarith [sq_nonneg x]
    have hB : cbrt (1 + x + x ^ 2) ≠ 0 := by
      unfold cbrt
      exact ne_of_gt (Real.rpow_pos_of_pos hq _)
    have hD : cbrt 3 ≠ 0 := by
      unfold cbrt
      exact ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _)
    rw [gap1 x hx0 hx1]
    unfold model
    field_simp [hA, hB, hD]
    <;> ring
  have hp : ContinuousAt (fun x : ℝ => 1 + x + x ^ 2) 1 :=
    (continuousAt_const.add continuousAt_id).add (continuousAt_id.pow 2)
  have hlogAt : ContinuousAt Real.log (1 + (1 : ℝ) + 1 ^ 2) :=
    Real.continuousAt_log (by norm_num)
  have hlog :
      ContinuousAt (fun x : ℝ => Real.log (1 + x + x ^ 2)) 1 := by
    exact ContinuousAt.comp
      (f := fun x : ℝ => 1 + x + x ^ 2) hlogAt hp
  have hexp :
      ContinuousAt
        (fun x : ℝ => Real.exp (Real.log (1 + x + x ^ 2) * (1 / 3))) 1 :=
    Real.continuous_exp.continuousAt.comp (hlog.mul continuousAt_const)
  have hqpos :
      ∀ᶠ x : ℝ in nhds (1 : ℝ), 0 < 1 + x + x ^ 2 := by
    filter_upwards [hpos_nhds] with x hx
    nlinarith [sq_nonneg x]
  have hcbrtEq :
      (fun x : ℝ => cbrt (1 + x + x ^ 2)) =ᶠ[nhds 1]
        (fun x => Real.exp (Real.log (1 + x + x ^ 2) * (1 / 3))) := by
    filter_upwards [hqpos] with x hx
    unfold cbrt
    exact Real.rpow_def_of_pos hx (1 / 3 : ℝ)
  have hthree :
      cbrt 3 = Real.exp (Real.log 3 * (1 / 3)) := by
    unfold cbrt
    exact Real.rpow_def_of_pos (by norm_num) (1 / 3 : ℝ)
  have hcbrtq :
      Filter.Tendsto (fun x : ℝ => cbrt (1 + x + x ^ 2))
        (nhds 1) (nhds (cbrt 3)) := by
    have hexpT0 :
        Filter.Tendsto
          (fun x : ℝ => Real.exp (Real.log (1 + x + x ^ 2) * (1 / 3)))
          (nhds 1) (nhds (Real.exp (Real.log 3 * (1 / 3)))) := by
      convert hexp.tendsto using 1 <;> norm_num
    have hexpT :
        Filter.Tendsto
          (fun x : ℝ => Real.exp (Real.log (1 + x + x ^ 2) * (1 / 3)))
          (nhds 1) (nhds (cbrt 3)) := by
      rw [hthree]
      exact hexpT0
    exact hexpT.congr' hcbrtEq.symm
  have hD : cbrt 3 ≠ 0 := by
    unfold cbrt
    exact ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _)
  have hid :
      Filter.Tendsto (fun x : ℝ => x) (nhds 1) (nhds 1) :=
    continuousAt_id
  have hconst :
      Filter.Tendsto (fun _ : ℝ => cbrt 3) (nhds 1) (nhds (cbrt 3)) :=
    tendsto_const_nhds
  have hquot :
      Filter.Tendsto (fun x : ℝ => x * cbrt 3 / cbrt (1 + x + x ^ 2))
        (nhds 1) (nhds ((1 : ℝ) * cbrt 3 / cbrt 3)) :=
    (hid.mul hconst).div hcbrtq hD
  have hlim :
      Filter.Tendsto (fun x : ℝ => x * cbrt 3 / cbrt (1 + x + x ^ 2))
        (nhdsWithin 1 (Set.Iio 1)) (nhds 1) := by
    have hquot' :
        Filter.Tendsto (fun x : ℝ => x * cbrt 3 / cbrt (1 + x + x ^ 2))
          (nhds 1) (nhds 1) := by
      simpa [hD] using hquot
    exact hquot'.mono_left inf_le_left
  exact hlim.congr' hformula.symm

/-- Exercise 658_3, gap 3. -/
theorem gap3 :
    Asymptotics.IsEquivalent (nhdsWithin 1 (Set.Iio 1)) target model := by
  have hmodel :
      ∀ᶠ x : ℝ in nhdsWithin 1 (Set.Iio 1), model x ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    change x < 1 at hx
    have h3 : cbrt 3 ≠ 0 := by
      unfold cbrt
      exact ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _)
    have hx' : cbrt (1 - x) ≠ 0 := by
      unfold cbrt
      exact ne_of_gt (Real.rpow_pos_of_pos (sub_pos.mpr hx) _)
    unfold model
    exact mul_ne_zero (div_ne_zero one_ne_zero h3) (div_ne_zero one_ne_zero hx')
  have hone :
      Filter.Tendsto (fun _ : ℝ => (1 : ℝ))
        (nhdsWithin 1 (Set.Iio 1)) (nhds 1) :=
    tendsto_const_nhds
  have hratio0 :
      Filter.Tendsto (fun x : ℝ => target x / model x - 1)
        (nhdsWithin 1 (Set.Iio 1)) (nhds 0) := by
    simpa using gap2.sub hone
  change Asymptotics.IsLittleO (nhdsWithin 1 (Set.Iio 1))
    (target - model) model
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have hsmall :
      ∀ᶠ x : ℝ in nhdsWithin 1 (Set.Iio 1),
        ‖target x / model x - 1‖ < c := by
    simpa using (Metric.tendsto_nhds.1 hratio0 c hc)
  filter_upwards [hmodel, hsmall] with x hmx hs
  change ‖target x - model x‖ ≤ c * ‖model x‖
  have hid :
      target x - model x = (target x / model x - 1) * model x := by
    field_simp [hmx]
    <;> ring
  rw [hid, norm_mul]
  exact mul_le_mul_of_nonneg_right (le_of_lt hs) (norm_nonneg _)

/-- Exercise 658_3, gap 4; unpack the singleton pair and preserve the one-sided domain. -/
theorem gap4 (C n : ℝ) (h : (C, n) = (1 / cbrt 3, 1 / 3)) :
    Asymptotics.IsEquivalent (nhdsWithin 1 (Set.Iio 1))
      target (fun x => C * Real.rpow (1 / (1 - x)) n) := by
  have hC : C = 1 / cbrt 3 := congrArg Prod.fst h
  have hn : n = 1 / 3 := congrArg Prod.snd h
  subst C
  subst n
  have hcomp :
      model =ᶠ[nhdsWithin 1 (Set.Iio 1)]
        (fun x : ℝ => (1 / cbrt 3) * Real.rpow (1 / (1 - x)) (1 / 3)) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    change x < 1 at hx
    have hbase : 0 ≤ 1 - x := le_of_lt (sub_pos.mpr hx)
    have hinv' :
        Real.rpow ((1 - x)⁻¹) (1 / 3) =
          (Real.rpow (1 - x) (1 / 3))⁻¹ := by
      exact Real.inv_rpow hbase (1 / 3 : ℝ)
    have hinv :
        Real.rpow (1 / (1 - x)) (1 / 3) =
          1 / Real.rpow (1 - x) (1 / 3) := by
      simpa only [one_div] using hinv'
    unfold model cbrt
    exact congrArg
      (fun z : ℝ => (1 / Real.rpow 3 (1 / 3)) * z) hinv.symm
  have ht :
      target =ᶠ[nhdsWithin 1 (Set.Iio 1)] target :=
    Filter.EventuallyEq.rfl
  have hdiff :
      target - model =ᶠ[nhdsWithin 1 (Set.Iio 1)]
        target - (fun x : ℝ => (1 / cbrt 3) * Real.rpow (1 / (1 - x)) (1 / 3)) :=
    ht.sub hcomp
  exact gap3.congr' hdiff hcomp

end

end ProofGap.Exercise658_3
