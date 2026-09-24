import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod

namespace ProofGap.Exercise4168

noncomputable section

open Filter MeasureTheory
open scoped Interval

abbrev Point := ℝ × ℝ

def kernel (x y : ℝ) : ℝ :=
  (x ^ 2 - y ^ 2) / (x ^ 2 + y ^ 2) ^ 2

def quadrant : Set Point :=
  {z | 1 ≤ z.1 ∧ 1 ≤ z.2}

def triangle (n : ℝ) : Set Point :=
  {z | 1 ≤ z.1 ∧ z.1 ≤ n ∧ 1 ≤ z.2 ∧ z.2 ≤ z.1}

def firstYThenX : ℝ :=
  ∫ x in Set.Ici (1 : ℝ),
    ∫ y in Set.Ici (1 : ℝ), kernel x y

def firstXThenY : ℝ :=
  ∫ y in Set.Ici (1 : ℝ),
    ∫ x in Set.Ici (1 : ℝ), kernel x y

def triangleAreaIntegral (n : ℝ) : ℝ :=
  ∫ z in triangle n, kernel z.1 z.2

def triangleIteratedIntegral (n : ℝ) : ℝ :=
  ∫ x in (1 : ℝ)..n, ∫ y in (1 : ℝ)..x, kernel x y

def reducedTriangleIntegral (n : ℝ) : ℝ :=
  ∫ x in (1 : ℝ)..n, (-1 / (x ^ 2 + 1) + 1 / (2 * x))

private theorem ae_ne_real (a : ℝ) :
    ∀ᵐ x : ℝ ∂volume, x ≠ a := by
  rw [ae_iff]
  simp

private theorem kernel_swap (x y : ℝ) :
    kernel x y = -kernel y x := by
  unfold kernel
  ring

private theorem kernel_integrable_Ici (x : ℝ) :
    IntegrableOn (fun y : ℝ => kernel x y) (Set.Ici (1 : ℝ)) := by
  have hpow : IntegrableOn (fun y : ℝ => y ^ (-2 : ℝ))
      (Set.Ioi (1 : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one
  have hpow' : IntegrableOn (fun y : ℝ => y ^ (-2 : ℝ))
      (Set.Ici (1 : ℝ)) :=
    hpow.congr_set_ae Ioi_ae_eq_Ici.symm
  refine hpow'.mono'
    (by
      have hc : ContinuousOn (fun y : ℝ => kernel x y)
          (Set.Ici (1 : ℝ)) := by
        unfold kernel
        apply ContinuousOn.div (by fun_prop) (by fun_prop)
        intro y hy
        have hy0 : 0 < y := zero_lt_one.trans_le hy
        have hpos : 0 < x ^ 2 + y ^ 2 := by
          nlinarith [sq_nonneg x, sq_pos_of_pos hy0]
        exact pow_ne_zero _ (ne_of_gt hpos)
      exact hc.aestronglyMeasurable measurableSet_Ici) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ici] with y hy
  have hy0 : 0 < y := zero_lt_one.trans_le hy
  have hden : 0 < x ^ 2 + y ^ 2 := by
    nlinarith [sq_nonneg x, sq_nonneg y]
  have hnum : |x ^ 2 - y ^ 2| ≤ x ^ 2 + y ^ 2 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg x, sq_nonneg y]
  have hk :
      |kernel x y| ≤ 1 / (x ^ 2 + y ^ 2) := by
    unfold kernel
    rw [abs_div, abs_of_pos (sq_pos_of_pos hden)]
    rw [div_le_iff₀ (sq_pos_of_pos hden),
      div_eq_mul_inv, one_mul]
    calc
      |x ^ 2 - y ^ 2| ≤ x ^ 2 + y ^ 2 := hnum
      _ = (x ^ 2 + y ^ 2) ^ 2 *
          (x ^ 2 + y ^ 2)⁻¹ := by
        field_simp [ne_of_gt hden]
      _ = (x ^ 2 + y ^ 2)⁻¹ *
          (x ^ 2 + y ^ 2) ^ 2 := by ring
  have hxy : 1 / (x ^ 2 + y ^ 2) ≤ 1 / y ^ 2 := by
    exact one_div_le_one_div_of_le (sq_pos_of_pos hy0)
      (le_add_of_nonneg_left (sq_nonneg x))
  rw [Real.norm_eq_abs]
  calc
    |kernel x y| ≤ 1 / (x ^ 2 + y ^ 2) := hk
    _ ≤ 1 / y ^ 2 := hxy
    _ = y ^ (-2 : ℝ) := by
      rw [Real.rpow_neg (le_of_lt hy0)]
      norm_num [Real.rpow_two]

private theorem inner_tail (x : ℝ) :
    (∫ y in Set.Ici (1 : ℝ), kernel x y) =
      -1 / (x ^ 2 + 1) := by
  let F : ℝ → ℝ := fun y => y / (x ^ 2 + y ^ 2)
  have hder (y : ℝ) (hy : y ∈ Set.Ici (1 : ℝ)) :
      HasDerivAt F (kernel x y) y := by
    have hden : x ^ 2 + y ^ 2 ≠ 0 := by
      have hy0 : 0 < y := zero_lt_one.trans_le hy
      have : 0 < x ^ 2 + y ^ 2 := by
        nlinarith [sq_nonneg x, sq_pos_of_pos hy0]
      exact ne_of_gt this
    unfold F kernel
    convert (hasDerivAt_id y).div
      ((hasDerivAt_const y (x ^ 2)).add ((hasDerivAt_id y).pow 2))
      hden using 1 <;>
      simp only [id_eq, Pi.add_apply, Pi.pow_apply] <;>
      field_simp [hden] <;> ring
  have ht : Tendsto F atTop (nhds 0) := by
    unfold F
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' ?_ ?_ tendsto_inv_atTop_zero
    · filter_upwards with y
      exact norm_nonneg _
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
      have hy0 : 0 < y := zero_lt_one.trans_le hy
      have hden : 0 < x ^ 2 + y ^ 2 := by
        nlinarith [sq_nonneg x, sq_nonneg y]
      rw [Real.norm_eq_abs, abs_div,
        abs_of_nonneg (zero_le_one.trans hy),
        abs_of_pos hden]
      rw [div_le_iff₀ hden]
      rw [show y⁻¹ * (x ^ 2 + y ^ 2) =
          (x ^ 2 + y ^ 2) / y by ring]
      rw [le_div_iff₀ hy0]
      nlinarith [sq_nonneg x]
  have hIoi :
      (∫ y in Set.Ioi (1 : ℝ), kernel x y) =
        0 - F 1 := by
    exact integral_Ioi_of_hasDerivAt_of_tendsto'
      (fun y hy => hder y hy)
      (by
        simpa using
          (kernel_integrable_Ici x).mono_set Set.Ioi_subset_Ici_self)
      ht
  rw [← setIntegral_congr_set Ioi_ae_eq_Ici]
  rw [hIoi]
  unfold F
  ring

private theorem inverse_one_add_sq_Ici :
    (∫ x in Set.Ici (1 : ℝ), 1 / (x ^ 2 + 1)) =
      Real.pi / 4 := by
  rw [← setIntegral_congr_set Ioi_ae_eq_Ici]
  have h :=
    (integral_Ioi_inv_one_add_sq (i := (1 : ℝ)))
  change
    (∫ x in Set.Ioi (1 : ℝ), (1 + x ^ 2)⁻¹) =
      Real.pi / 2 - Real.arctan 1 at h
  have hfun :
      (fun x : ℝ => 1 / (x ^ 2 + 1)) =
        fun x => (1 + x ^ 2)⁻¹ := by
    funext x
    rw [one_div, add_comm]
  rw [hfun, h, Real.arctan_one]
  ring

private theorem firstYThenX_value :
    firstYThenX = -Real.pi / 4 := by
  unfold firstYThenX
  simp_rw [inner_tail]
  rw [show
      (fun x : ℝ => -1 / (x ^ 2 + 1)) =
        fun x => -(1 / (x ^ 2 + 1)) by
      funext x
      ring]
  rw [integral_neg]
  rw [inverse_one_add_sq_Ici]
  ring

private theorem firstXThenY_value :
    firstXThenY = Real.pi / 4 := by
  have hinner (y : ℝ) :
      (∫ x in Set.Ici (1 : ℝ), kernel x y) =
        1 / (y ^ 2 + 1) := by
    calc
      (∫ x in Set.Ici (1 : ℝ), kernel x y) =
          ∫ x in Set.Ici (1 : ℝ), -kernel y x := by
        apply setIntegral_congr_fun measurableSet_Ici
        intro x hx
        exact kernel_swap x y
      _ = -(∫ x in Set.Ici (1 : ℝ), kernel y x) := by
        rw [integral_neg]
      _ = 1 / (y ^ 2 + 1) := by rw [inner_tail]; ring
  unfold firstXThenY
  simp_rw [hinner]
  exact inverse_one_add_sq_Ici

private theorem triangle_measurable (n : ℝ) :
    MeasurableSet (triangle n) := by
  unfold triangle
  measurability

private theorem triangle_integrable (n : ℝ) (hn : 1 ≤ n) :
    IntegrableOn (fun z : Point => kernel z.1 z.2) (triangle n) := by
  let box : Set Point :=
    Set.Icc (1 : ℝ) n ×ˢ Set.Icc (1 : ℝ) n
  have hcompact : IsCompact box :=
    isCompact_Icc.prod isCompact_Icc
  have hcont : ContinuousOn (fun z : Point => kernel z.1 z.2) box := by
    unfold kernel
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro z hz
    have hz0 : 0 < z.1 := zero_lt_one.trans_le hz.1.1
    have hpos : 0 < z.1 ^ 2 + z.2 ^ 2 := by
      nlinarith [sq_pos_of_pos hz0, sq_nonneg z.2]
    exact pow_ne_zero _ (ne_of_gt hpos)
  have hi : IntegrableOn (fun z : Point => kernel z.1 z.2) box :=
    hcont.integrableOn_compact hcompact
  refine hi.mono_set ?_
  intro z hz
  exact
    ⟨⟨hz.1, hz.2.1⟩,
      ⟨hz.2.2.1, hz.2.2.2.trans hz.2.1⟩⟩

private theorem triangle_fubini (n : ℝ) (hn : 1 ≤ n) :
    triangleAreaIntegral n = triangleIteratedIntegral n := by
  have htri := triangle_measurable n
  have hi := triangle_integrable n hn
  have hind :
      Integrable
        ((triangle n).indicator
          (fun z : Point => kernel z.1 z.2)) := by
    exact (integrable_indicator_iff htri).2 hi
  unfold triangleAreaIntegral triangleIteratedIntegral
  rw [intervalIntegral.integral_of_le hn]
  rw [Measure.volume_eq_prod]
  rw [← integral_indicator htri]
  rw [integral_prod _ hind]
  rw [← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards [ae_ne_real 1] with x hxne
  by_cases hx : x ∈ Set.Ioc (1 : ℝ) n
  · rw [Set.indicator_of_mem hx]
    rw [intervalIntegral.integral_of_le hx.1.le]
    rw [← integral_indicator measurableSet_Ioc]
    apply integral_congr_ae
    filter_upwards [ae_ne_real 1] with y hyne
    by_cases hy : y ∈ Set.Ioc (1 : ℝ) x
    · rw [Set.indicator_of_mem hy]
      have hz : (x, y) ∈ triangle n :=
        ⟨hx.1.le, hx.2, hy.1.le, hy.2⟩
      rw [Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hy]
      have hz : (x, y) ∉ triangle n := by
        intro hz
        apply hy
        exact ⟨lt_of_le_of_ne hz.2.2.1 (Ne.symm hyne), hz.2.2.2⟩
      rw [Set.indicator_of_notMem hz]
  · rw [Set.indicator_of_notMem hx]
    have hzero :
        (fun y : ℝ =>
          (triangle n).indicator
            (fun z : Point => kernel z.1 z.2) (x, y)) =
          fun _ => 0 := by
      funext y
      rw [Set.indicator_of_notMem]
      intro hz
      apply hx
      exact ⟨lt_of_le_of_ne hz.1 (Ne.symm hxne), hz.2.1⟩
    rw [hzero, integral_zero]

private theorem finite_inner (x : ℝ) (hx : 1 ≤ x) :
    (∫ y in (1 : ℝ)..x, kernel x y) =
      -1 / (x ^ 2 + 1) + 1 / (2 * x) := by
  let F : ℝ → ℝ := fun y => y / (x ^ 2 + y ^ 2)
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hcont : ContinuousOn F (Set.Icc (1 : ℝ) x) := by
    unfold F
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro y hy
    have : 0 < x ^ 2 + y ^ 2 := by
      nlinarith [sq_nonneg x, sq_nonneg y]
    exact ne_of_gt this
  have hder : ∀ y ∈ Set.Ioo (1 : ℝ) x,
      HasDerivAt F (kernel x y) y := by
    intro y hy
    have hden : x ^ 2 + y ^ 2 ≠ 0 := by
      have : 0 < x ^ 2 + y ^ 2 := by
        nlinarith [sq_nonneg x, sq_nonneg y]
      exact ne_of_gt this
    unfold F kernel
    convert (hasDerivAt_id y).div
      ((hasDerivAt_const y (x ^ 2)).add ((hasDerivAt_id y).pow 2))
      hden using 1 <;>
      simp only [id_eq, Pi.add_apply, Pi.pow_apply] <;>
      field_simp [hden] <;> ring
  have hi : IntervalIntegrable (fun y : ℝ => kernel x y) volume 1 x := by
    have hc : ContinuousOn (fun y : ℝ => kernel x y)
        (Set.Icc (1 : ℝ) x) := by
      unfold kernel
      apply ContinuousOn.div (by fun_prop) (by fun_prop)
      intro y hy
      have : 0 < x ^ 2 + y ^ 2 := by
        nlinarith [sq_nonneg x, sq_nonneg y]
      exact pow_ne_zero _ (ne_of_gt this)
    exact hc.intervalIntegrable_of_Icc hx
  have hFTC :
      (∫ y in (1 : ℝ)..x, kernel x y) = F x - F 1 := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      hx hcont hder hi
  rw [hFTC]
  unfold F
  field_simp [ne_of_gt hx0]
  ring

private theorem triangle_reduced (n : ℝ) (hn : 1 ≤ n) :
    triangleAreaIntegral n = reducedTriangleIntegral n := by
  rw [triangle_fubini n hn]
  unfold triangleIteratedIntegral reducedTriangleIntegral
  apply intervalIntegral.integral_congr
  intro x hx
  rw [Set.uIcc_of_le hn] at hx
  exact finite_inner x hx.1

private theorem reduced_value (n : ℝ) (hn : 1 ≤ n) :
    reducedTriangleIntegral n =
      Real.pi / 4 - Real.arctan n +
        (1 / 2 : ℝ) * Real.log n := by
  let F : ℝ → ℝ := fun x =>
    -Real.arctan x + (1 / 2 : ℝ) * Real.log x
  have hcont : ContinuousOn F (Set.Icc (1 : ℝ) n) := by
    unfold F
    apply ContinuousOn.add Real.continuous_arctan.continuousOn.neg
    apply ContinuousOn.mul continuousOn_const
    intro x hx
    exact (Real.continuousAt_log
      (ne_of_gt (zero_lt_one.trans_le hx.1))).continuousWithinAt
  have hder : ∀ x ∈ Set.Ioo (1 : ℝ) n,
      HasDerivAt F (-1 / (x ^ 2 + 1) + 1 / (2 * x)) x := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx.1)
    unfold F
    convert (Real.hasDerivAt_arctan x).neg.add
      ((hasDerivAt_const x (1 / 2 : ℝ)).mul
        (Real.hasDerivAt_log hx0)) using 1 <;>
      field_simp [hx0] <;> ring
  have hi :
      IntervalIntegrable
        (fun x : ℝ => -1 / (x ^ 2 + 1) + 1 / (2 * x))
        volume 1 n := by
    have hc : ContinuousOn
        (fun x : ℝ => -1 / (x ^ 2 + 1) + 1 / (2 * x))
        (Set.Icc (1 : ℝ) n) := by
      apply ContinuousOn.add
      · have hglobal : Continuous
            (fun x : ℝ => -1 / (x ^ 2 + 1)) := by
          apply Continuous.div continuous_const
            ((continuous_id.pow 2).add continuous_const)
          intro x
          exact ne_of_gt (by nlinarith [sq_nonneg x] :
            0 < x ^ 2 + 1)
        exact hglobal.continuousOn
      · apply ContinuousOn.div continuousOn_const
          (continuousOn_const.mul continuousOn_id)
        intro x hx
        exact mul_ne_zero (by norm_num)
          (ne_of_gt (zero_lt_one.trans_le hx.1))
    exact hc.intervalIntegrable_of_Icc hn
  unfold reducedTriangleIntegral
  have hFTC :
      (∫ x in (1 : ℝ)..n,
          (-1 / (x ^ 2 + 1) + 1 / (2 * x))) =
        F n - F 1 := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      hn hcont hder hi
  rw [hFTC]
  norm_num [F, Real.arctan_one]
  ring

private theorem triangle_value (n : ℝ) (hn : 1 ≤ n) :
    triangleAreaIntegral n =
      Real.pi / 4 - Real.arctan n +
        (1 / 2 : ℝ) * Real.log n := by
  rw [triangle_reduced n hn, reduced_value n hn]

private theorem triangle_tendsto :
    Tendsto triangleAreaIntegral atTop atTop := by
  have hfinite :
      Tendsto
        (fun n : ℝ => Real.pi / 4 - Real.arctan n)
        atTop (nhds (Real.pi / 4 - Real.pi / 2)) :=
    tendsto_const_nhds.sub
      (tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop)
  have hlog :
      Tendsto (fun n : ℝ => (1 / 2 : ℝ) * Real.log n)
        atTop atTop :=
    Real.tendsto_log_atTop.const_mul_atTop (by norm_num)
  have hsum :
      Tendsto
        (fun n : ℝ =>
          (Real.pi / 4 - Real.arctan n) +
            (1 / 2 : ℝ) * Real.log n)
        atTop atTop :=
    hfinite.add_atTop hlog
  apply Tendsto.congr' _ hsum
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with n hn
  exact (triangle_value n hn).symm

private theorem quadrant_nonintegrable :
    ¬ IntegrableOn (fun z : Point => kernel z.1 z.2) quadrant := by
  intro hi
  let C : ℝ :=
    ∫ z in quadrant, ‖kernel z.1 z.2‖
  have hbound : ∀ n : ℝ, 1 ≤ n →
      |triangleAreaIntegral n| ≤ C := by
    intro n hn
    have hsubset : triangle n ⊆ quadrant := by
      intro z hz
      exact ⟨hz.1, hz.2.2.1⟩
    calc
      |triangleAreaIntegral n| =
          ‖∫ z in triangle n, kernel z.1 z.2‖ := by
        rw [Real.norm_eq_abs]
        rfl
      _ ≤ ∫ z in triangle n, ‖kernel z.1 z.2‖ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ z in quadrant, ‖kernel z.1 z.2‖ := by
        apply setIntegral_mono_set hi.norm
        · filter_upwards with z
          exact norm_nonneg _
        · exact ae_of_all _ hsubset
  have hev : ∀ᶠ n : ℝ in atTop,
      C + 1 ≤ triangleAreaIntegral n :=
    (tendsto_atTop.1 triangle_tendsto (C + 1))
  obtain ⟨n, hlarge, hn⟩ :=
    (hev.and (eventually_ge_atTop (1 : ℝ))).exists
  have hb := hbound n hn
  have : triangleAreaIntegral n ≤ C :=
    le_trans (le_abs_self _) hb
  linarith

theorem gap1 (x : ℝ) :
    (∫ y in Set.Ici (1 : ℝ), kernel x y) =
      -1 / (x ^ 2 + 1) := by
  exact inner_tail x

theorem gap2 :
    firstYThenX =
      -(∫ x in Set.Ici (1 : ℝ), 1 / (x ^ 2 + 1)) := by
  unfold firstYThenX
  simp_rw [inner_tail]
  rw [show
      (fun x : ℝ => -1 / (x ^ 2 + 1)) =
        fun x => -(1 / (x ^ 2 + 1)) by
      funext x
      ring]
  rw [integral_neg]

theorem gap3 :
    -(∫ x in Set.Ici (1 : ℝ), 1 / (x ^ 2 + 1)) =
      -Real.pi / 4 := by
  rw [inverse_one_add_sq_Ici]
  ring

theorem gap4 :
    firstYThenX = -Real.pi / 4 := by
  exact firstYThenX_value

theorem gap5 :
    firstXThenY = Real.pi / 4 := by
  exact firstXThenY_value

theorem gap6 (n : ℝ) (hn : 1 ≤ n) :
    triangleAreaIntegral n = triangleIteratedIntegral n := by
  exact triangle_fubini n hn

theorem gap7 (x : ℝ) (hx : 1 ≤ x) :
    (∫ y in (1 : ℝ)..x, kernel x y) =
      -1 / (x ^ 2 + 1) + 1 / (2 * x) := by
  exact finite_inner x hx

theorem gap8 (n : ℝ) (hn : 1 ≤ n) :
    triangleAreaIntegral n = reducedTriangleIntegral n := by
  exact triangle_reduced n hn

theorem gap9 (n : ℝ) (hn : 1 ≤ n) :
    reducedTriangleIntegral n =
      Real.pi / 4 - Real.arctan n + (1 / 2 : ℝ) * Real.log n := by
  exact reduced_value n hn

theorem gap10 (n : ℝ) (hn : 1 ≤ n) :
    triangleAreaIntegral n =
      Real.pi / 4 - Real.arctan n + (1 / 2 : ℝ) * Real.log n := by
  exact triangle_value n hn

theorem gap11 :
    Tendsto triangleAreaIntegral atTop atTop := by
  exact triangle_tendsto

theorem gap12 :
    ¬ IntegrableOn (fun z : Point => kernel z.1 z.2) quadrant := by
  exact quadrant_nonintegrable

theorem gap13 :
    firstYThenX = -Real.pi / 4 ∧
      firstXThenY = Real.pi / 4 ∧
        ¬ IntegrableOn (fun z : Point => kernel z.1 z.2) quadrant := by
  exact ⟨firstYThenX_value, firstXThenY_value, quadrant_nonintegrable⟩

end

end ProofGap.Exercise4168
