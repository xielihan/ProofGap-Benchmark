import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

namespace ProofGap.Exercise589

noncomputable section

def original (x : ℝ) : ℝ :=
  x * (Real.pi / 2 - Real.arcsin (x / Real.sqrt (x ^ 2 + 1)))
def transformed (x : ℝ) : ℝ :=
  x * Real.arcsin (1 / Real.sqrt (x ^ 2 + 1))
def normalized (x : ℝ) : ℝ :=
  (Real.arcsin (1 / Real.sqrt (x ^ 2 + 1)) /
    (1 / Real.sqrt (x ^ 2 + 1))) *
  (x / Real.sqrt (x ^ 2 + 1))
def HasLimitAtPosInfinity (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f Filter.atTop (nhds L)

/-- Source: `proof_gap/exercise_589/1.txt`. -/
private theorem eventually_pos_real :
    ∀ᶠ x : ℝ in Filter.atTop, 0 < x := by
  refine Filter.eventually_atTop.2 ?_
  exact ⟨1, by
    intro x hx
    linarith⟩

theorem gap1 (L : ℝ) :
    HasLimitAtPosInfinity original L ↔ HasLimitAtPosInfinity transformed L := by
  have hfg : original =ᶠ[Filter.atTop] transformed := by
    filter_upwards [eventually_pos_real] with x hx
    have hpos : 0 < x ^ 2 + 1 := by
      nlinarith [sq_nonneg x]
    have hspos : 0 < Real.sqrt (x ^ 2 + 1) := Real.sqrt_pos.2 hpos
    have hs_sq : (Real.sqrt (x ^ 2 + 1)) ^ 2 = x ^ 2 + 1 :=
      Real.sq_sqrt hpos.le
    have hz0 : 0 ≤ x / Real.sqrt (x ^ 2 + 1) := by
      exact div_nonneg (le_of_lt hx) (Real.sqrt_nonneg _)
    have hy0 : 0 ≤ 1 / Real.sqrt (x ^ 2 + 1) := by
      exact div_nonneg (by norm_num) (Real.sqrt_nonneg _)
    have hrad :
        1 - (x / Real.sqrt (x ^ 2 + 1)) ^ 2 =
          (1 / Real.sqrt (x ^ 2 + 1)) ^ 2 := by
      field_simp [ne_of_gt hspos]
      nlinarith [hs_sq]
    let A : ℝ := Real.pi / 2 -
      Real.arcsin (x / Real.sqrt (x ^ 2 + 1))
    have hA0 : 0 ≤ A := by
      dsimp [A]
      nlinarith [Real.arcsin_le_pi_div_two
        (x / Real.sqrt (x ^ 2 + 1))]
    have hAle : A ≤ Real.pi / 2 := by
      dsimp [A]
      nlinarith [Real.arcsin_nonneg.2 hz0]
    have hsin :
        Real.sin A = 1 / Real.sqrt (x ^ 2 + 1) := by
      dsimp [A]
      rw [Real.sin_sub, Real.sin_pi_div_two, Real.cos_pi_div_two,
        one_mul, zero_mul, sub_zero, Real.cos_arcsin, hrad,
        Real.sqrt_sq hy0]
    have hid :
        Real.arcsin (1 / Real.sqrt (x ^ 2 + 1)) = A := by
      calc
        Real.arcsin (1 / Real.sqrt (x ^ 2 + 1)) =
            Real.arcsin (Real.sin A) := by rw [hsin]
        _ = A := Real.arcsin_sin
          (by nlinarith [hA0, Real.pi_pos]) hAle
    simp only [original, transformed]
    rw [hid]
  unfold HasLimitAtPosInfinity
  exact Filter.tendsto_congr' hfg

/-- Source: `proof_gap/exercise_589/2.txt`. -/
theorem gap2 (L : ℝ) :
    HasLimitAtPosInfinity transformed L ↔ HasLimitAtPosInfinity normalized L := by
  have hfun : transformed = normalized := by
    funext x
    have hpos : 0 < x ^ 2 + 1 := by
      nlinarith [sq_nonneg x]
    have hspos : 0 < Real.sqrt (x ^ 2 + 1) := Real.sqrt_pos.2 hpos
    unfold transformed normalized
    field_simp [ne_of_gt hspos]
  rw [hfun]

/-- Source: `proof_gap/exercise_589/3.txt`. -/
theorem gap3 : HasLimitAtPosInfinity normalized 1 := by
  unfold HasLimitAtPosInfinity
  have hq :
      Filter.Tendsto (fun x : ℝ => 1 / x) Filter.atTop (nhds 0) := by
    simpa [one_div] using
      (tendsto_inv_atTop_zero :
        Filter.Tendsto (fun x : ℝ => x⁻¹) Filter.atTop (nhds 0))
  have hi :
      Filter.Tendsto (fun x : ℝ => 1 + (1 / x) ^ 2)
        Filter.atTop (nhds 1) := by
    simpa using
      ((tendsto_const_nhds :
          Filter.Tendsto (fun _ : ℝ => (1 : ℝ)) Filter.atTop (nhds 1)).add
        (hq.pow 2))
  have hs :
      Filter.Tendsto
        (fun x : ℝ => Real.sqrt (1 + (1 / x) ^ 2))
        Filter.atTop (nhds 1) := by
    simpa using Real.continuous_sqrt.continuousAt.tendsto.comp hi
  have huClean :
      Filter.Tendsto
        (fun x : ℝ => (1 / x) / Real.sqrt (1 + (1 / x) ^ 2))
        Filter.atTop (nhds 0) := by
    simpa using hq.div hs (by norm_num : (1 : ℝ) ≠ 0)
  have hwClean :
      Filter.Tendsto
        (fun x : ℝ => 1 / Real.sqrt (1 + (1 / x) ^ 2))
        Filter.atTop (nhds 1) := by
    have hone :
        Filter.Tendsto (fun _ : ℝ => (1 : ℝ))
          Filter.atTop (nhds 1) := tendsto_const_nhds
    change Filter.Tendsto
      ((fun _ : ℝ => (1 : ℝ)) /
        (fun x : ℝ => Real.sqrt (1 + (1 / x) ^ 2)))
      Filter.atTop (nhds 1)
    simpa only [div_one] using
      hone.div hs (by norm_num : (1 : ℝ) ≠ 0)
  have hscale : ∀ᶠ x : ℝ in Filter.atTop,
      Real.sqrt (x ^ 2 + 1) =
        x * Real.sqrt (1 + (1 / x) ^ 2) := by
    filter_upwards [eventually_pos_real] with x hx
    have hxne : x ≠ 0 := ne_of_gt hx
    have hleftsq :
        (Real.sqrt (x ^ 2 + 1)) ^ 2 = x ^ 2 + 1 :=
      Real.sq_sqrt (by nlinarith [sq_nonneg x])
    have hinner : 0 ≤ 1 + (1 / x) ^ 2 := by positivity
    have hrightsq :
        (x * Real.sqrt (1 + (1 / x) ^ 2)) ^ 2 = x ^ 2 + 1 := by
      rw [mul_pow, Real.sq_sqrt hinner]
      field_simp [hxne]
      <;> ring
    have hrightnonneg :
        0 ≤ x * Real.sqrt (1 + (1 / x) ^ 2) :=
      mul_nonneg (le_of_lt hx) (Real.sqrt_nonneg _)
    nlinarith [hleftsq, hrightsq, Real.sqrt_nonneg (x ^ 2 + 1)]
  have huEq :
      (fun x : ℝ => 1 / Real.sqrt (x ^ 2 + 1)) =ᶠ[Filter.atTop]
        (fun x : ℝ => (1 / x) / Real.sqrt (1 + (1 / x) ^ 2)) := by
    filter_upwards [hscale, eventually_pos_real] with x hscaleX hx
    have hxne : x ≠ 0 := ne_of_gt hx
    have hden : 0 < Real.sqrt (1 + (1 / x) ^ 2) :=
      Real.sqrt_pos.2 (by positivity)
    rw [hscaleX]
    field_simp [hxne, ne_of_gt hden]
    <;> ring
  have hwEq :
      (fun x : ℝ => x / Real.sqrt (x ^ 2 + 1)) =ᶠ[Filter.atTop]
        (fun x : ℝ => 1 / Real.sqrt (1 + (1 / x) ^ 2)) := by
    filter_upwards [hscale, eventually_pos_real] with x hscaleX hx
    have hxne : x ≠ 0 := ne_of_gt hx
    have hden : 0 < Real.sqrt (1 + (1 / x) ^ 2) :=
      Real.sqrt_pos.2 (by positivity)
    rw [hscaleX]
    field_simp [hxne, ne_of_gt hden]
    <;> ring
  have hu :
      Filter.Tendsto
        (fun x : ℝ => 1 / Real.sqrt (x ^ 2 + 1))
        Filter.atTop (nhds 0) :=
    (Filter.tendsto_congr' huEq).2 huClean
  have hw :
      Filter.Tendsto
        (fun x : ℝ => x / Real.sqrt (x ^ 2 + 1))
        Filter.atTop (nhds 1) :=
    (Filter.tendsto_congr' hwEq).2 hwClean
  have hA :
      Filter.Tendsto
        (fun x : ℝ => Real.arcsin (1 / Real.sqrt (x ^ 2 + 1)))
        Filter.atTop (nhds 0) := by
    simpa using Real.continuous_arcsin.continuousAt.tendsto.comp hu
  have hAPunctured :
      Filter.Tendsto
        (fun x : ℝ => Real.arcsin (1 / Real.sqrt (x ^ 2 + 1)))
        Filter.atTop (nhdsWithin 0 ({0}ᶜ : Set ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hA, ?_⟩
    filter_upwards with x
    have hspos : 0 < Real.sqrt (x ^ 2 + 1) :=
      Real.sqrt_pos.2 (by nlinarith [sq_nonneg x])
    have hup : 0 < 1 / Real.sqrt (x ^ 2 + 1) := one_div_pos.2 hspos
    simpa using (ne_of_gt (Real.arcsin_pos.2 hup) :
      Real.arcsin (1 / Real.sqrt (x ^ 2 + 1)) ≠ 0)
  have hsinRatioZero :
      Filter.Tendsto (fun y : ℝ => Real.sin y / y)
        (nhdsWithin 0 ({0}ᶜ : Set ℝ)) (nhds 1) := by
    have hder := (Real.hasDerivAt_sin 0).tendsto_slope
    have heq :
        slope Real.sin 0 =ᶠ[nhdsWithin 0 ({0}ᶜ : Set ℝ)]
          (fun y : ℝ => Real.sin y / y) := by
      filter_upwards with y
      simp [slope, div_eq_mul_inv, mul_comm]
    have hder' :
        Filter.Tendsto (slope Real.sin 0)
          (nhdsWithin 0 ({0}ᶜ : Set ℝ)) (nhds 1) := by
      simpa using hder
    exact (Filter.tendsto_congr' heq).1 hder'
  have hsinRatio :
      Filter.Tendsto
        (fun x : ℝ =>
          Real.sin (Real.arcsin (1 / Real.sqrt (x ^ 2 + 1))) /
            Real.arcsin (1 / Real.sqrt (x ^ 2 + 1)))
        Filter.atTop (nhds 1) := by
    exact hsinRatioZero.comp hAPunctured
  have hratioInv :
      Filter.Tendsto
        (fun x : ℝ =>
          1 / (Real.sin (Real.arcsin (1 / Real.sqrt (x ^ 2 + 1))) /
            Real.arcsin (1 / Real.sqrt (x ^ 2 + 1))))
        Filter.atTop (nhds 1) := by
    have hone :
        Filter.Tendsto (fun _ : ℝ => (1 : ℝ))
          Filter.atTop (nhds 1) := tendsto_const_nhds
    change Filter.Tendsto
      ((fun _ : ℝ => (1 : ℝ)) /
        (fun x : ℝ =>
          Real.sin (Real.arcsin (1 / Real.sqrt (x ^ 2 + 1))) /
            Real.arcsin (1 / Real.sqrt (x ^ 2 + 1))))
      Filter.atTop (nhds 1)
    simpa only [div_one] using
      hone.div hsinRatio (by norm_num : (1 : ℝ) ≠ 0)
  have hratioEq :
      (fun x : ℝ =>
        Real.arcsin (1 / Real.sqrt (x ^ 2 + 1)) /
          (1 / Real.sqrt (x ^ 2 + 1))) =ᶠ[Filter.atTop]
      (fun x : ℝ =>
        1 / (Real.sin (Real.arcsin (1 / Real.sqrt (x ^ 2 + 1))) /
          Real.arcsin (1 / Real.sqrt (x ^ 2 + 1)))) := by
    filter_upwards with x
    have hbase : 0 < x ^ 2 + 1 := by
      nlinarith [sq_nonneg x]
    have hspos : 0 < Real.sqrt (x ^ 2 + 1) := Real.sqrt_pos.2 hbase
    have hssq : (Real.sqrt (x ^ 2 + 1)) ^ 2 = x ^ 2 + 1 :=
      Real.sq_sqrt hbase.le
    have hsge : 1 ≤ Real.sqrt (x ^ 2 + 1) := by
      nlinarith [hssq, Real.sqrt_nonneg (x ^ 2 + 1), sq_nonneg x]
    have hup : 0 < 1 / Real.sqrt (x ^ 2 + 1) := one_div_pos.2 hspos
    have hule : 1 / Real.sqrt (x ^ 2 + 1) ≤ 1 := by
      rw [div_le_iff₀ hspos]
      simpa using hsge
    have huge : -1 ≤ 1 / Real.sqrt (x ^ 2 + 1) := by linarith
    have hapos :
        0 < Real.arcsin (1 / Real.sqrt (x ^ 2 + 1)) :=
      Real.arcsin_pos.2 hup
    have hsin :
        Real.sin (Real.arcsin (1 / Real.sqrt (x ^ 2 + 1))) =
          1 / Real.sqrt (x ^ 2 + 1) :=
      Real.sin_arcsin huge hule
    rw [hsin]
    field_simp [ne_of_gt hup, ne_of_gt hapos]
  have hratio :
      Filter.Tendsto
        (fun x : ℝ =>
          Real.arcsin (1 / Real.sqrt (x ^ 2 + 1)) /
            (1 / Real.sqrt (x ^ 2 + 1)))
        Filter.atTop (nhds 1) :=
    (Filter.tendsto_congr' hratioEq).2 hratioInv
  change Filter.Tendsto
    (fun x : ℝ =>
      (Real.arcsin (1 / Real.sqrt (x ^ 2 + 1)) /
        (1 / Real.sqrt (x ^ 2 + 1))) *
      (x / Real.sqrt (x ^ 2 + 1)))
    Filter.atTop (nhds 1)
  simpa only [one_mul] using hratio.mul hw

/-- Source: `proof_gap/exercise_589/4.txt`. -/
theorem gap4 : HasLimitAtPosInfinity original 1 := by
  exact (gap1 1).2 ((gap2 1).2 gap3)

end

end ProofGap.Exercise589
