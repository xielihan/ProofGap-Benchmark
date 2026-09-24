import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3994

noncomputable section

open MeasureTheory
open scoped Interval


def region (a b h k : ℝ) : Set (ℝ × ℝ) :=
  {p |
    0 < p.1 ∧ 0 < p.2 ∧
      (p.1 / a + p.2 / b) ^ 4 ≤
        p.1 ^ 2 / h ^ 2 - p.2 ^ 2 / k ^ 2}

def regionArea (a b h k : ℝ) : ℝ :=
  ∫ _p in region a b h k, (1 : ℝ)

def radialSquared (a b h k φ : ℝ) : ℝ :=
  ((a / h) ^ 2 * Real.cos φ ^ 2 -
      (b / k) ^ 2 * Real.sin φ ^ 2) /
    (Real.cos φ + Real.sin φ) ^ 4

def cutoff (a b h k : ℝ) : ℝ :=
  Real.arctan (a * k / (b * h))

def validAngle (a b h k : ℝ) : Set ℝ :=
  Set.Icc 0 (cutoff a b h k)

private noncomputable def diagCLM (a b : ℝ) :
    (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (a • ContinuousLinearMap.fst ℝ ℝ ℝ).prod
    (b • ContinuousLinearMap.snd ℝ ℝ ℝ)

private lemma diagCLM_det (a b : ℝ) :
    LinearMap.det (diagCLM a b).toLinearMap = a * b := by
  rw [show
      (diagCLM a b).toLinearMap =
        LinearMap.prodMap
          (a • LinearMap.id)
          (b • LinearMap.id) by
    ext p <;> rfl,
    LinearMap.det_prodMap,
    LinearMap.det_smul,
    LinearMap.det_smul]
  norm_num

private noncomputable def scaleHomeomorph
    (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (ℝ × ℝ) ≃ₜ (ℝ × ℝ) :=
  (Homeomorph.mulLeft₀ a ha).prodCongr
    (Homeomorph.mulLeft₀ b hb)

private noncomputable def scaleOPH
    (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ) :=
  (scaleHomeomorph a b ha hb).toOpenPartialHomeomorph

private lemma hasFDerivAt_scaleOPH
    (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (q : ℝ × ℝ) :
    HasFDerivAt (scaleOPH a b ha hb)
      (diagCLM a b) q := by
  simpa [scaleOPH, scaleHomeomorph, diagCLM] using
    ((hasFDerivAt_fst.const_mul a).prodMk
      (hasFDerivAt_snd.const_mul b))

private lemma integral_scale
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (f : ℝ × ℝ → ℝ) :
    (∫ p, f p) =
      ∫ q : ℝ × ℝ,
        (a * b) • f (a * q.1, b * q.2) := by
  have hcov :=
    integral_target_eq_integral_abs_det_fderiv_smul
      (μ := volume)
      (f := scaleOPH a b ha.ne' hb.ne')
      (f' := fun _ => diagCLM a b)
      (fun q _ => hasFDerivAt_scaleOPH
        a b ha.ne' hb.ne' q) f
  simpa [scaleOPH, scaleHomeomorph,
    diagCLM_det, abs_of_pos (mul_pos ha hb)] using hcov

private def scaledRegion (a b h k : ℝ) :
    Set (ℝ × ℝ) :=
  {p |
    0 < p.1 ∧ 0 < p.2 ∧
      (p.1 + p.2) ^ 4 ≤
        (a / h) ^ 2 * p.1 ^ 2 -
          (b / k) ^ 2 * p.2 ^ 2}

private lemma region_measurable
    (a b h k : ℝ) :
    MeasurableSet (region a b h k) := by
  unfold region
  exact
    (measurableSet_lt measurable_const measurable_fst).inter <|
      (measurableSet_lt measurable_const measurable_snd).inter <|
        measurableSet_le
          (show Measurable
            (fun p : ℝ × ℝ =>
              (p.1 / a + p.2 / b) ^ 4) by
            fun_prop)
          (show Measurable
            (fun p : ℝ × ℝ =>
              p.1 ^ 2 / h ^ 2 -
                p.2 ^ 2 / k ^ 2) by
            fun_prop)

private lemma scaledRegion_measurable
    (a b h k : ℝ) :
    MeasurableSet (scaledRegion a b h k) := by
  unfold scaledRegion
  exact
    (measurableSet_lt measurable_const measurable_fst).inter <|
      (measurableSet_lt measurable_const measurable_snd).inter <|
        measurableSet_le
          (show Measurable
            (fun p : ℝ × ℝ => (p.1 + p.2) ^ 4) by
            fun_prop)
          (show Measurable
            (fun p : ℝ × ℝ =>
              (a / h) ^ 2 * p.1 ^ 2 -
                (b / k) ^ 2 * p.2 ^ 2) by
            fun_prop)

private lemma scale_mem_region_iff
    (a b h k : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hh : 0 < h) (hk : 0 < k)
    (q : ℝ × ℝ) :
    (a * q.1, b * q.2) ∈ region a b h k ↔
      q ∈ scaledRegion a b h k := by
  unfold region scaledRegion
  simp only [Set.mem_setOf_eq]
  have ha0 := ha.ne'
  have hb0 := hb.ne'
  have hh0 := hh.ne'
  have hk0 := hk.ne'
  constructor
  · rintro ⟨hx, hy, hineq⟩
    have hx' : 0 < q.1 := by
      rcases (mul_pos_iff.mp hx) with hpos | hneg
      · exact hpos.2
      · exfalso
        linarith
    have hy' : 0 < q.2 := by
      rcases (mul_pos_iff.mp hy) with hpos | hneg
      · exact hpos.2
      · exfalso
        linarith
    refine ⟨hx', hy', ?_⟩
    convert hineq using 1 <;>
      field_simp [ha0, hb0, hh0, hk0] <;> ring
  · rintro ⟨hx, hy, hineq⟩
    refine ⟨mul_pos ha hx, mul_pos hb hy, ?_⟩
    convert hineq using 1 <;>
      field_simp [ha0, hb0, hh0, hk0] <;> ring

private lemma regionArea_eq_scaled
    (a b h k : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hh : 0 < h) (hk : 0 < k) :
    regionArea a b h k =
      a * b * (∫ _q in scaledRegion a b h k, (1 : ℝ)) := by
  rw [regionArea,
    ← MeasureTheory.integral_indicator
      (region_measurable a b h k),
    integral_scale a b ha hb]
  calc
    (∫ q : ℝ × ℝ,
        (a * b) •
          (region a b h k).indicator
            (fun _ => (1 : ℝ)) (a * q.1, b * q.2)) =
        ∫ q : ℝ × ℝ,
          (a * b) *
            (scaledRegion a b h k).indicator
              (fun _ => (1 : ℝ)) q := by
      apply integral_congr_ae
      filter_upwards with q
      rw [smul_eq_mul]
      by_cases hq : q ∈ scaledRegion a b h k
      · rw [Set.indicator_of_mem hq,
          Set.indicator_of_mem
            ((scale_mem_region_iff
              a b h k ha hb hh hk q).2 hq)]
      · rw [Set.indicator_of_notMem hq,
          Set.indicator_of_notMem]
        intro hreg
        exact hq
          ((scale_mem_region_iff
            a b h k ha hb hh hk q).1 hreg)
    _ =
        a * b *
          ∫ q : ℝ × ℝ,
            (scaledRegion a b h k).indicator
              (fun _ => (1 : ℝ)) q := by
      rw [MeasureTheory.integral_const_mul]
    _ =
        a * b *
          (∫ _q in scaledRegion a b h k,
            (1 : ℝ)) := by
      rw [MeasureTheory.integral_indicator
        (scaledRegion_measurable a b h k)]

theorem gap1 (a b h k φ : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hh : 0 < h) (hk : 0 < k) :
    radialSquared a b h k φ =
      ((a / h) ^ 2 * Real.cos φ ^ 2 -
          (b / k) ^ 2 * Real.sin φ ^ 2) /
        (Real.cos φ + Real.sin φ) ^ 4 := by
  rfl

theorem gap3 (a b h k φ : ℝ)
    (hφ : φ ∈ validAngle a b h k) :
    0 ≤ φ := by
  exact hφ.1

theorem gap4 (a b h k φ : ℝ)
    (hφ : φ ∈ validAngle a b h k) :
    φ ≤ Real.arctan (a * k / (b * h)) := by
  exact hφ.2

theorem gap5 (a b h k : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hh : 0 < h) (hk : 0 < k) :
    0 ≤ Real.arctan (a * k / (b * h)) := by
  rw [Real.arctan_nonneg]
  positivity

theorem gap2 (a b h k φ : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hh : 0 < h) (hk : 0 < k)
    (hφ : φ ∈ validAngle a b h k) :
    0 ≤ (a / h) ^ 2 * Real.cos φ ^ 2 -
      (b / k) ^ 2 * Real.sin φ ^ 2 := by
  have hq : 0 < a * k / (b * h) := by
    positivity
  change
    0 ≤ φ ∧
      φ ≤ Real.arctan (a * k / (b * h)) at hφ
  have hcut0 :
      0 < Real.arctan (a * k / (b * h)) :=
    (Real.arctan_pos).2 hq
  have hcutHalf :
      Real.arctan (a * k / (b * h)) <
        Real.pi / 2 :=
    Real.arctan_lt_pi_div_two _
  have hφmem :
      φ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by
      linarith [Real.pi_pos], hφ.2.trans_lt hcutHalf⟩
  have hcutmem :
      Real.arctan (a * k / (b * h)) ∈
        Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith [hcut0, Real.pi_pos], hcutHalf⟩
  have htan :
      Real.tan φ ≤ a * k / (b * h) := by
    have hmono :=
      Real.strictMonoOn_tan.monotoneOn
        hφmem hcutmem hφ.2
    rwa [Real.tan_arctan] at hmono
  have hcos : 0 < Real.cos φ :=
    Real.cos_pos_of_mem_Ioo hφmem
  rw [Real.tan_eq_sin_div_cos] at htan
  have hlin :
      (b / k) * Real.sin φ ≤
        (a / h) * Real.cos φ := by
    have hsinBound :=
      (div_le_iff₀ hcos).1 htan
    have hscaled :=
      mul_le_mul_of_nonneg_left hsinBound
        (mul_pos hb hh).le
    rw [← mul_le_mul_iff_left₀ (mul_pos hh hk)]
    convert hscaled using 1 <;>
      field_simp [hb.ne', hh.ne', hk.ne'] <;> ring
  have hleft :
      0 ≤ (b / k) * Real.sin φ := by
    have hsin :
        0 ≤ Real.sin φ :=
      Real.sin_nonneg_of_nonneg_of_le_pi hφ.1
        (by linarith [hφ.2, hcutHalf, Real.pi_pos])
    exact mul_nonneg (div_nonneg hb.le hk.le) hsin
  nlinarith [sq_nonneg
    ((a / h) * Real.cos φ -
      (b / k) * Real.sin φ),
    mul_self_le_mul_self hleft hlin]

private lemma cutoff_nonneg
    (a b h k : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hh : 0 < h) (hk : 0 < k) :
    0 ≤ cutoff a b h k := by
  unfold cutoff
  rw [Real.arctan_nonneg]
  positivity

private lemma cutoff_lt_half
    (a b h k : ℝ) :
    cutoff a b h k < Real.pi / 2 := by
  unfold cutoff
  exact Real.arctan_lt_pi_div_two _

private lemma denominator_pos_on_valid
    (a b h k φ : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hh : 0 < h) (hk : 0 < k)
    (hφ : φ ∈ Set.Icc (0 : ℝ) (cutoff a b h k)) :
    0 < Real.cos φ + Real.sin φ := by
  have hhalf := cutoff_lt_half a b h k
  have hcos : 0 < Real.cos φ :=
    Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_pos, hφ.1],
        hφ.2.trans_lt hhalf⟩
  have hsin :
      0 ≤ Real.sin φ :=
    Real.sin_nonneg_of_nonneg_of_le_pi
      hφ.1 (by linarith [hφ.2, hhalf, Real.pi_pos])
  linarith

private lemma cosRatio_valid_integrable
    (a b h k : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hh : 0 < h) (hk : 0 < k) :
    IntervalIntegrable
      (fun φ : ℝ =>
        Real.cos φ ^ 2 /
          (Real.cos φ + Real.sin φ) ^ 4)
      volume 0 (cutoff a b h k) := by
  apply ContinuousOn.intervalIntegrable
  intro φ hφ
  rw [Set.uIcc_of_le
    (cutoff_nonneg a b h k ha hb hh hk)] at hφ
  apply ContinuousAt.continuousWithinAt
  exact
    (Real.continuous_cos.continuousAt.pow 2).div
      ((Real.continuous_cos.continuousAt.add
        Real.continuous_sin.continuousAt).pow 4)
      (pow_ne_zero 4
        (denominator_pos_on_valid
          a b h k φ ha hb hh hk hφ).ne')

private lemma sinRatio_valid_integrable
    (a b h k : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hh : 0 < h) (hk : 0 < k) :
    IntervalIntegrable
      (fun φ : ℝ =>
        Real.sin φ ^ 2 /
          (Real.cos φ + Real.sin φ) ^ 4)
      volume 0 (cutoff a b h k) := by
  apply ContinuousOn.intervalIntegrable
  intro φ hφ
  rw [Set.uIcc_of_le
    (cutoff_nonneg a b h k ha hb hh hk)] at hφ
  apply ContinuousAt.continuousWithinAt
  exact
    (Real.continuous_sin.continuousAt.pow 2).div
      ((Real.continuous_cos.continuousAt.add
        Real.continuous_sin.continuousAt).pow 4)
      (pow_ne_zero 4
        (denominator_pos_on_valid
          a b h k φ ha hb hh hk hφ).ne')

private lemma cos_ratio_change_variable
    (φ : ℝ) (hφ0 : 0 ≤ φ)
    (hφ1 : φ < Real.pi / 2) :
    Real.cos φ ^ 2 /
        (Real.cos φ + Real.sin φ) ^ 4 =
      1 / (1 + Real.tan φ) ^ 4 *
        deriv Real.tan φ := by
  have hcos : Real.cos φ ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_pos], hφ1⟩)
  simp only [Real.deriv_tan, Real.tan_eq_sin_div_cos]
  field_simp [hcos]

private lemma cos_outer_hasDerivAt
    (t : ℝ) (ht : t ≠ -1) :
    HasDerivAt
      (fun z : ℝ => -1 / (3 * (1 + z) ^ 3))
      (1 / (1 + t) ^ 4) t := by
  have hbase :
      HasDerivAt (fun z : ℝ => 1 + z) 1 t := by
    convert
      (hasDerivAt_const t 1).add (hasDerivAt_id t)
      using 1 <;> norm_num
  have h1 : 1 + t ≠ 0 := by
    intro hzero
    apply ht
    linarith
  have hne : 3 * (1 + t) ^ 3 ≠ 0 := by
    apply mul_ne_zero
    · norm_num
    · exact pow_ne_zero 3 h1
  have h := (((hbase.pow 3).const_mul 3).inv hne).neg
  simp only [Pi.pow_apply] at h
  convert h using 1
  · funext z
    simp [div_eq_mul_inv, add_comm, mul_comm]
  · field_simp [h1]
    ring

private lemma cosPrimitive_hasDerivAt
    (φ : ℝ) (hφ0 : 0 ≤ φ)
    (hφ1 : φ < Real.pi / 2) :
    HasDerivAt
      (fun θ : ℝ =>
        -1 / (3 * (1 + Real.tan θ) ^ 3))
      (Real.cos φ ^ 2 /
        (Real.cos φ + Real.sin φ) ^ 4) φ := by
  have hmem :
      φ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], hφ1⟩
  have htan0 : 0 ≤ Real.tan φ :=
    Real.tan_nonneg_of_nonneg_of_le_pi_div_two
      hφ0 hφ1.le
  have ht : Real.tan φ ≠ -1 := by
    linarith
  have hcomp :=
    (cos_outer_hasDerivAt (Real.tan φ) ht).comp φ
      (Real.hasDerivAt_tan_of_mem_Ioo hmem)
  convert hcomp using 1
  rw [← Real.deriv_tan]
  exact cos_ratio_change_variable φ hφ0 hφ1

private lemma sinPrimitive_hasDerivAt
    (φ : ℝ) (hφ0 : 0 ≤ φ)
    (hφ1 : φ < Real.pi / 2) :
    HasDerivAt
      (fun θ : ℝ =>
        -1 / (1 + Real.tan θ) +
          1 / (1 + Real.tan θ) ^ 2 -
          1 / (3 * (1 + Real.tan θ) ^ 3))
      (Real.sin φ ^ 2 /
        (Real.cos φ + Real.sin φ) ^ 4) φ := by
  have hmem :
      φ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], hφ1⟩
  have htan0 : 0 ≤ Real.tan φ :=
    Real.tan_nonneg_of_nonneg_of_le_pi_div_two
      hφ0 hφ1.le
  have ht1 : 1 + Real.tan φ ≠ 0 := by
    linarith
  let H : ℝ → ℝ := fun z =>
    -1 / (1 + z) + 1 / (1 + z) ^ 2 -
      1 / (3 * (1 + z) ^ 3)
  have hbase :
      HasDerivAt (fun z : ℝ => 1 + z) 1
        (Real.tan φ) := by
    convert
      (hasDerivAt_const (Real.tan φ) 1).add
        (hasDerivAt_id (Real.tan φ))
      using 1 <;> norm_num
  have houter :
      HasDerivAt H
        (Real.tan φ ^ 2 /
          (1 + Real.tan φ) ^ 4)
        (Real.tan φ) := by
    have h1 := (hbase.inv ht1).neg
    have h2 :=
      ((hbase.pow 2).inv (pow_ne_zero 2 ht1))
    have h3 :=
      ((((hbase.pow 3).const_mul 3).inv
        (mul_ne_zero (by norm_num)
          (pow_ne_zero 3 ht1))).neg)
    have hsum := (h1.add h2).add h3
    simp only [Pi.pow_apply, Pi.inv_apply, Pi.neg_apply,
      Pi.add_apply] at hsum
    dsimp [H]
    convert hsum using 1
    · funext z
      simp [div_eq_mul_inv, add_comm]
      ring
    · field_simp [ht1]
      ring
  have hcomp :=
    houter.comp φ
      (Real.hasDerivAt_tan_of_mem_Ioo hmem)
  convert hcomp using 1
  simp only [Real.tan_eq_sin_div_cos]
  have hcos : Real.cos φ ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo hmem).ne'
  field_simp [hcos]

private lemma firstQuadrant_angle_iff
    (r θ : ℝ) (hr : 0 < r)
    (hθ : -Real.pi < θ ∧ θ < Real.pi) :
    (0 < r * Real.cos θ ∧
        0 < r * Real.sin θ) ↔
      0 < θ ∧ θ < Real.pi / 2 := by
  constructor
  · rintro ⟨hx, hy⟩
    have hcos : 0 < Real.cos θ := by
      rcases (mul_pos_iff.mp hx) with hpos | hneg
      · exact hpos.2
      · exfalso
        linarith
    have hsin : 0 < Real.sin θ := by
      rcases (mul_pos_iff.mp hy) with hpos | hneg
      · exact hpos.2
      · exfalso
        linarith
    have hθ0 : 0 < θ := by
      by_contra hnot
      have hsnon :
          Real.sin θ ≤ 0 :=
        Real.sin_nonpos_of_nonpos_of_neg_pi_le
          (le_of_not_gt hnot) hθ.1.le
      linarith
    have hθhalf : θ < Real.pi / 2 := by
      by_contra hnot
      have hcnon :
          Real.cos θ ≤ 0 :=
        Real.cos_nonpos_of_pi_div_two_le_of_le
          (le_of_not_gt hnot)
          (by linarith [hθ.2, Real.pi_pos])
      linarith
    exact ⟨hθ0, hθhalf⟩
  · rintro ⟨hθ0, hθhalf⟩
    have hcos :
        0 < Real.cos θ :=
      Real.cos_pos_of_mem_Ioo
        ⟨by linarith [Real.pi_pos], hθhalf⟩
    have hsin :
        0 < Real.sin θ :=
      Real.sin_pos_of_pos_of_lt_pi
        hθ0 (by linarith [hθhalf, Real.pi_pos])
    exact ⟨mul_pos hr hcos, mul_pos hr hsin⟩

private lemma numerator_pos_iff_angle_lt_cutoff
    (a b h k θ : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hh : 0 < h) (hk : 0 < k)
    (hθ0 : 0 ≤ θ) (hθhalf : θ < Real.pi / 2) :
    0 <
        (a / h) ^ 2 * Real.cos θ ^ 2 -
          (b / k) ^ 2 * Real.sin θ ^ 2 ↔
      θ < cutoff a b h k := by
  have hcos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_pos], hθhalf⟩
  have hsin : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi
      hθ0 (by linarith [hθhalf, Real.pi_pos])
  have hcutPos :
      0 < cutoff a b h k := by
    unfold cutoff
    rw [Real.arctan_pos]
    positivity
  have hcutHalf := cutoff_lt_half a b h k
  have hθmem :
      θ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos, hθ0], hθhalf⟩
  have hcutmem :
      cutoff a b h k ∈
        Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos, hcutPos], hcutHalf⟩
  have htanCut :
      Real.tan (cutoff a b h k) =
        a * k / (b * h) := by
    unfold cutoff
    exact Real.tan_arctan _
  have hcoeffA : 0 < a / h := div_pos ha hh
  have hcoeffB : 0 < b / k := div_pos hb hk
  constructor
  · intro hnum
    have hxy :
        (b / k) * Real.sin θ <
          (a / h) * Real.cos θ := by
      have hx : 0 < (a / h) * Real.cos θ :=
        mul_pos hcoeffA hcos
      have hy : 0 ≤ (b / k) * Real.sin θ :=
        mul_nonneg hcoeffB.le hsin
      nlinarith [sq_nonneg
        ((a / h) * Real.cos θ +
          (b / k) * Real.sin θ)]
    have hscaled :=
      mul_lt_mul_of_pos_left hxy (mul_pos hh hk)
    have htan :
        Real.tan θ < a * k / (b * h) := by
      rw [Real.tan_eq_sin_div_cos]
      apply (div_lt_iff₀ hcos).2
      rw [← mul_lt_mul_iff_left₀ (mul_pos hb hh)]
      convert hscaled using 1 <;>
        field_simp [ha.ne', hb.ne', hh.ne', hk.ne'] <;>
          ring
    by_contra hnot
    have hle : cutoff a b h k ≤ θ :=
      le_of_not_gt hnot
    have hmono :=
      Real.strictMonoOn_tan.monotoneOn
        hcutmem hθmem hle
    rw [htanCut] at hmono
    linarith
  · intro hangle
    have htan :
        Real.tan θ <
          Real.tan (cutoff a b h k) :=
      Real.strictMonoOn_tan hθmem hcutmem hangle
    rw [htanCut, Real.tan_eq_sin_div_cos] at htan
    have hraw :=
      (div_lt_iff₀ hcos).1 htan
    have hrawScaled :=
      mul_lt_mul_of_pos_left hraw (mul_pos hb hh)
    have hxy :
        (b / k) * Real.sin θ <
          (a / h) * Real.cos θ := by
      rw [← mul_lt_mul_iff_left₀ (mul_pos hh hk)]
      convert hrawScaled using 1 <;>
        field_simp [ha.ne', hb.ne', hh.ne', hk.ne'] <;>
          ring
    have hx : 0 < (a / h) * Real.cos θ :=
      mul_pos hcoeffA hcos
    have hy : 0 ≤ (b / k) * Real.sin θ :=
      mul_nonneg hcoeffB.le hsin
    nlinarith [sq_nonneg
      ((a / h) * Real.cos θ +
        (b / k) * Real.sin θ)]

private def scaledPolarDomain (a b h k : ℝ) :
    Set (ℝ × ℝ) :=
  {q |
    0 < q.1 ∧ 0 < q.2 ∧
      q.2 < cutoff a b h k ∧
      q.1 ^ 2 ≤ radialSquared a b h k q.2}

private noncomputable def scaledPolarDensity
    (a b h k : ℝ) (q : ℝ × ℝ) : ℝ :=
  (scaledPolarDomain a b h k).indicator
    (fun p => p.1) q

private lemma polar_mem_scaledRegion_iff
    (a b h k : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hh : 0 < h) (hk : 0 < k)
    (q : ℝ × ℝ)
    (hq : q ∈ polarCoord.target) :
    polarCoord.symm q ∈ scaledRegion a b h k ↔
      q ∈ scaledPolarDomain a b h k := by
  rcases hq with ⟨hr, hθl, hθu⟩
  simp only [polarCoord_symm_apply]
  unfold scaledRegion scaledPolarDomain
  simp only [Set.mem_setOf_eq]
  have hangle :=
    firstQuadrant_angle_iff q.1 q.2 hr
      ⟨hθl, hθu⟩
  constructor
  · rintro ⟨hx, hy, hineq⟩
    have hang :
        0 < q.2 ∧ q.2 < Real.pi / 2 :=
      hangle.1 ⟨hx, hy⟩
    have hsum :
        0 < Real.cos q.2 + Real.sin q.2 := by
      have hc := Real.cos_pos_of_mem_Ioo
        ⟨by linarith [Real.pi_pos], hang.2⟩
      have hs := Real.sin_pos_of_pos_of_lt_pi
        hang.1 (by linarith [hang.2, Real.pi_pos])
      linarith
    have hD :
        0 < (Real.cos q.2 + Real.sin q.2) ^ 4 :=
      pow_pos hsum 4
    have hr2 : 0 < q.1 ^ 2 := sq_pos_of_pos hr
    have hfact :
        q.1 ^ 2 *
            (q.1 ^ 2 *
              (Real.cos q.2 + Real.sin q.2) ^ 4) ≤
          q.1 ^ 2 *
            ((a / h) ^ 2 * Real.cos q.2 ^ 2 -
              (b / k) ^ 2 * Real.sin q.2 ^ 2) := by
      convert hineq using 1 <;> ring
    have hcancel :
        q.1 ^ 2 *
            (Real.cos q.2 + Real.sin q.2) ^ 4 ≤
          (a / h) ^ 2 * Real.cos q.2 ^ 2 -
            (b / k) ^ 2 * Real.sin q.2 ^ 2 := by
      apply (mul_le_mul_iff_left₀ hr2).mp
      simpa [mul_comm, mul_left_comm, mul_assoc] using hfact
    have hnum :
        0 <
          (a / h) ^ 2 * Real.cos q.2 ^ 2 -
            (b / k) ^ 2 * Real.sin q.2 ^ 2 := by
      have hleft :
          0 <
            q.1 ^ 2 *
              (Real.cos q.2 + Real.sin q.2) ^ 4 :=
        mul_pos hr2 hD
      exact hleft.trans_le hcancel
    have hcut :
        q.2 < cutoff a b h k :=
      (numerator_pos_iff_angle_lt_cutoff
        a b h k q.2 ha hb hh hk hang.1.le hang.2).1 hnum
    refine ⟨hr, hang.1, hcut, ?_⟩
    unfold radialSquared
    exact (le_div_iff₀ hD).2 hcancel
  · rintro ⟨hr', hθ0, hθcut, hrad⟩
    have hθhalf :
        q.2 < Real.pi / 2 :=
      hθcut.trans (cutoff_lt_half a b h k)
    have hxy :=
      hangle.2 ⟨hθ0, hθhalf⟩
    refine ⟨hxy.1, hxy.2, ?_⟩
    have hsum :
        0 < Real.cos q.2 + Real.sin q.2 := by
      have hc := Real.cos_pos_of_mem_Ioo
        ⟨by linarith [Real.pi_pos], hθhalf⟩
      have hs := Real.sin_pos_of_pos_of_lt_pi
        hθ0 (by linarith [hθhalf, Real.pi_pos])
      linarith
    have hD :
        0 < (Real.cos q.2 + Real.sin q.2) ^ 4 :=
      pow_pos hsum 4
    unfold radialSquared at hrad
    have hmul :
        q.1 ^ 2 *
            (Real.cos q.2 + Real.sin q.2) ^ 4 ≤
          (a / h) ^ 2 * Real.cos q.2 ^ 2 -
            (b / k) ^ 2 * Real.sin q.2 ^ 2 :=
      (le_div_iff₀ hD).1 hrad
    have hr2 : 0 < q.1 ^ 2 := sq_pos_of_pos hr
    have hfact :=
      (mul_le_mul_iff_left₀ hr2).2 hmul
    convert hfact using 1 <;> ring

private lemma scaled_integral_eq_density
    (a b h k : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hh : 0 < h) (hk : 0 < k) :
    (∫ _p in scaledRegion a b h k, (1 : ℝ)) =
      ∫ q, scaledPolarDensity a b h k q := by
  classical
  have hpolar :=
    integral_comp_polarCoord_symm
      ((scaledRegion a b h k).indicator
        (fun _ : ℝ × ℝ => (1 : ℝ)))
  rw [← MeasureTheory.integral_indicator
    (scaledRegion_measurable a b h k)]
  rw [← hpolar]
  have hrestrict :
      (∫ q, scaledPolarDensity a b h k q) =
        ∫ q in polarCoord.target,
          scaledPolarDensity a b h k q := by
    rw [← MeasureTheory.integral_indicator
      polarCoord.open_target.measurableSet]
    apply integral_congr_ae
    filter_upwards with q
    by_cases hD : q ∈ scaledPolarDomain a b h k
    · have ht : q ∈ polarCoord.target := by
        rcases hD with ⟨hr, hθ0, hθcut, _⟩
        have hθhalf :=
          hθcut.trans (cutoff_lt_half a b h k)
        exact
          ⟨hr, by linarith [hθ0, Real.pi_pos],
            by linarith [hθhalf, Real.pi_pos]⟩
      exact
        (Set.indicator_of_mem ht
          (scaledPolarDensity a b h k)).symm
    · rw [scaledPolarDensity,
        Set.indicator_of_notMem hD]
      by_cases ht : q ∈ polarCoord.target
      · rw [Set.indicator_of_mem ht]
        unfold scaledPolarDensity
        rw [Set.indicator_of_notMem hD]
      · rw [Set.indicator_of_notMem ht]
  rw [hrestrict]
  apply setIntegral_congr_fun
    polarCoord.open_target.measurableSet
  intro q hq
  have hq' :
      q ∈ scaledPolarDomain a b h k ↔
        polarCoord.symm q ∈ scaledRegion a b h k :=
    (polar_mem_scaledRegion_iff
      a b h k ha hb hh hk q hq).symm
  unfold scaledPolarDensity
  by_cases hD : q ∈ scaledPolarDomain a b h k
  · have hR :
        polarCoord.symm q ∈ scaledRegion a b h k :=
      hq'.1 hD
    change
      q.1 •
          (scaledRegion a b h k).indicator
            (fun _ : ℝ × ℝ => (1 : ℝ))
            (polarCoord.symm q) =
        (scaledPolarDomain a b h k).indicator
          (fun p => p.1) q
    rw [Set.indicator_of_mem hD,
      Set.indicator_of_mem hR]
    simp [smul_eq_mul]
  · have hR :
        polarCoord.symm q ∉ scaledRegion a b h k := by
      intro h
      exact hD (hq'.2 h)
    change
      q.1 •
          (scaledRegion a b h k).indicator
            (fun _ : ℝ × ℝ => (1 : ℝ))
            (polarCoord.symm q) =
        (scaledPolarDomain a b h k).indicator
          (fun p => p.1) q
    rw [Set.indicator_of_notMem hD,
      Set.indicator_of_notMem hR]
    simp

private lemma scaledPolarDomain_measurable
    (a b h k : ℝ) :
    MeasurableSet (scaledPolarDomain a b h k) := by
  unfold scaledPolarDomain
  exact
    (measurableSet_lt measurable_const measurable_fst).inter <|
      (measurableSet_lt measurable_const measurable_snd).inter <|
        (measurableSet_lt measurable_snd measurable_const).inter <|
          measurableSet_le
            (show Measurable
              (fun q : ℝ × ℝ => q.1 ^ 2) by
              fun_prop)
            (show Measurable
              (fun q : ℝ × ℝ =>
                radialSquared a b h k q.2) by
              unfold radialSquared
              fun_prop)

private lemma radialSquared_nonneg_on_cutoff
    (a b h k θ : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hh : 0 < h) (hk : 0 < k)
    (hθ0 : 0 ≤ θ)
    (hθcut : θ ≤ cutoff a b h k) :
    0 ≤ radialSquared a b h k θ := by
  unfold radialSquared
  exact div_nonneg
    (gap2 a b h k θ ha hb hh hk ⟨hθ0, hθcut⟩)
    (by positivity)

private lemma radialSquared_le_A
    (a b h k θ : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hh : 0 < h) (hk : 0 < k)
    (hθ0 : 0 ≤ θ)
    (hθcut : θ ≤ cutoff a b h k) :
    radialSquared a b h k θ ≤ (a / h) ^ 2 := by
  have hhalf :
      θ < Real.pi / 2 :=
    hθcut.trans_lt (cutoff_lt_half a b h k)
  have hc : 0 ≤ Real.cos θ :=
    (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_pos, hθ0], hhalf⟩).le
  have hs : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi
      hθ0 (by linarith [hhalf, Real.pi_pos])
  have hsum : 0 < Real.cos θ + Real.sin θ := by
    have hcpos : 0 < Real.cos θ :=
      Real.cos_pos_of_mem_Ioo
        ⟨by linarith [Real.pi_pos, hθ0], hhalf⟩
    linarith
  let A : ℝ := (a / h) ^ 2
  let B : ℝ := (b / k) ^ 2
  let N : ℝ :=
    A * Real.cos θ ^ 2 - B * Real.sin θ ^ 2
  let D : ℝ := (Real.cos θ + Real.sin θ) ^ 4
  have hA : 0 ≤ A := sq_nonneg _
  have hB : 0 ≤ B := sq_nonneg _
  have hN : 0 ≤ N := by
    dsimp [N, A, B]
    exact gap2 a b h k θ ha hb hh hk ⟨hθ0, hθcut⟩
  have hcSq : Real.cos θ ^ 2 ≤ 1 :=
    Real.cos_sq_le_one θ
  have hNle : N ≤ A := by
    dsimp [N]
    nlinarith [
      mul_nonneg hA (sub_nonneg.2 hcSq),
      mul_nonneg hB (sq_nonneg (Real.sin θ))]
  have hcsSq :
      (Real.cos θ + Real.sin θ) ^ 2 =
        1 + 2 * Real.cos θ * Real.sin θ := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have hD1 : 1 ≤ D := by
    dsimp [D]
    have hcs2 :
        1 ≤ (Real.cos θ + Real.sin θ) ^ 2 := by
      rw [hcsSq]
      nlinarith [mul_nonneg hc hs]
    nlinarith [sq_nonneg
      ((Real.cos θ + Real.sin θ) ^ 2 - 1)]
  have hDpos : 0 < D :=
    lt_of_lt_of_le zero_lt_one hD1
  have hdiv : N / D ≤ N := by
    apply (div_le_iff₀ hDpos).2
    nlinarith [mul_nonneg hN (sub_nonneg.2 hD1)]
  unfold radialSquared
  change N / D ≤ A
  exact hdiv.trans hNle

private lemma scaledPolarDensity_integrable
    (a b h k : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hh : 0 < h) (hk : 0 < k) :
    Integrable (scaledPolarDensity a b h k) := by
  let M : ℝ := (a / h) ^ 2
  have hM : 0 ≤ M := sq_nonneg _
  have hsubset :
      scaledPolarDomain a b h k ⊆
        Set.Icc (0 : ℝ) (Real.sqrt M) ×ˢ
          Set.Icc (0 : ℝ) (Real.pi / 2) := by
    intro q hq
    rcases hq with ⟨hr, hθ0, hθcut, hrad⟩
    have hRle :
        radialSquared a b h k q.2 ≤ M := by
      dsimp [M]
      exact radialSquared_le_A
        a b h k q.2 ha hb hh hk hθ0.le hθcut.le
    have hrsq : q.1 ^ 2 ≤ M := hrad.trans hRle
    have hsqrtSq : Real.sqrt M ^ 2 = M :=
      Real.sq_sqrt hM
    have hrle : q.1 ≤ Real.sqrt M := by
      nlinarith [Real.sqrt_nonneg M]
    have hθhalf :
        q.2 < Real.pi / 2 :=
      hθcut.trans (cutoff_lt_half a b h k)
    exact
      ⟨⟨hr.le, hrle⟩, ⟨hθ0.le, hθhalf.le⟩⟩
  have hcompact :
      IsCompact
        (Set.Icc (0 : ℝ) (Real.sqrt M) ×ˢ
          Set.Icc (0 : ℝ) (Real.pi / 2)) :=
    isCompact_Icc.prod isCompact_Icc
  have hrect :
      IntegrableOn (fun q : ℝ × ℝ => q.1)
        (Set.Icc (0 : ℝ) (Real.sqrt M) ×ˢ
          Set.Icc (0 : ℝ) (Real.pi / 2)) :=
    continuous_fst.continuousOn.integrableOn_compact
      hcompact
  unfold scaledPolarDensity
  rw [integrable_indicator_iff
    (scaledPolarDomain_measurable a b h k)]
  exact hrect.mono_set hsubset

private lemma scaledPolarDensity_fubini
    (a b h k : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hh : 0 < h) (hk : 0 < k) :
    (∫ q, scaledPolarDensity a b h k q) =
      ∫ θ : ℝ,
        ∫ r : ℝ, scaledPolarDensity a b h k (r, θ) := by
  simpa only [Measure.volume_eq_prod] using
    (MeasureTheory.integral_prod_symm
      (scaledPolarDensity a b h k)
      (scaledPolarDensity_integrable
        a b h k ha hb hh hk))

private noncomputable def scaledAngularDensity
    (a b h k θ : ℝ) : ℝ :=
  if 0 < θ ∧ θ < cutoff a b h k then
    radialSquared a b h k θ / 2
  else
    0

private lemma scaledPolarDensity_inner
    (a b h k θ : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hh : 0 < h) (hk : 0 < k) :
    (∫ r : ℝ, scaledPolarDensity a b h k (r, θ)) =
      scaledAngularDensity a b h k θ := by
  by_cases hθ : 0 < θ ∧ θ < cutoff a b h k
  · rw [scaledAngularDensity, if_pos hθ]
    have hR :
        0 ≤ radialSquared a b h k θ :=
      radialSquared_nonneg_on_cutoff
        a b h k θ ha hb hh hk hθ.1.le hθ.2.le
    have hfun :
        (fun r : ℝ =>
          scaledPolarDensity a b h k (r, θ)) =
        (Set.Ioc (0 : ℝ)
          (Real.sqrt (radialSquared a b h k θ))).indicator
            (fun r => r) := by
      funext r
      unfold scaledPolarDensity scaledPolarDomain
      by_cases hr :
          0 < r ∧
            r ≤ Real.sqrt (radialSquared a b h k θ)
      · have hrsq :
            r ^ 2 ≤ radialSquared a b h k θ := by
          nlinarith [Real.sq_sqrt hR,
            Real.sqrt_nonneg
              (radialSquared a b h k θ)]
        have hD :
            (r, θ) ∈
              {q |
                0 < q.1 ∧ 0 < q.2 ∧
                  q.2 < cutoff a b h k ∧
                  q.1 ^ 2 ≤
                    radialSquared a b h k q.2} :=
          ⟨hr.1, hθ.1, hθ.2, hrsq⟩
        have hI :
            r ∈ Set.Ioc (0 : ℝ)
              (Real.sqrt
                (radialSquared a b h k θ)) := hr
        rw [Set.indicator_of_mem hD,
          Set.indicator_of_mem hI]
      · have hD :
            (r, θ) ∉
              {q |
                0 < q.1 ∧ 0 < q.2 ∧
                  q.2 < cutoff a b h k ∧
                  q.1 ^ 2 ≤
                    radialSquared a b h k q.2} := by
          intro hD
          apply hr
          refine ⟨hD.1, ?_⟩
          apply
            (sq_le_sq₀ hD.1.le
              (Real.sqrt_nonneg
                (radialSquared a b h k θ))).mp
          rw [Real.sq_sqrt hR]
          exact hD.2.2.2
        have hI :
            r ∉ Set.Ioc (0 : ℝ)
              (Real.sqrt
                (radialSquared a b h k θ)) := hr
        rw [Set.indicator_of_notMem hD,
          Set.indicator_of_notMem hI]
    rw [hfun,
      MeasureTheory.integral_indicator measurableSet_Ioc,
      ← intervalIntegral.integral_of_le
        (Real.sqrt_nonneg _),
      integral_id, Real.sq_sqrt hR]
    ring
  · rw [scaledAngularDensity, if_neg hθ]
    have hzero :
        (fun r : ℝ =>
          scaledPolarDensity a b h k (r, θ)) =
            fun _ => (0 : ℝ) := by
      funext r
      unfold scaledPolarDensity
      rw [Set.indicator_of_notMem]
      intro hD
      exact hθ ⟨hD.2.1, hD.2.2.1⟩
    rw [hzero, integral_zero]

private lemma scaledAngularDensity_integral
    (a b h k : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hh : 0 < h) (hk : 0 < k) :
    (∫ θ : ℝ, scaledAngularDensity a b h k θ) =
      1 / 2 *
        ∫ θ in (0 : ℝ)..cutoff a b h k,
          radialSquared a b h k θ := by
  have hfun :
      scaledAngularDensity a b h k =
        (Set.Ioo (0 : ℝ) (cutoff a b h k)).indicator
          (fun θ =>
            radialSquared a b h k θ / 2) := by
    funext θ
    by_cases hθ :
        θ ∈ Set.Ioo (0 : ℝ) (cutoff a b h k)
    · change
        (if 0 < θ ∧ θ < cutoff a b h k then
            radialSquared a b h k θ / 2
          else 0) =
          (Set.Ioo (0 : ℝ)
            (cutoff a b h k)).indicator
              (fun θ =>
                radialSquared a b h k θ / 2) θ
      rw [if_pos
        (show 0 < θ ∧ θ < cutoff a b h k from hθ),
        Set.indicator_of_mem hθ]
    · have hcond :
          ¬(0 < θ ∧ θ < cutoff a b h k) := hθ
      rw [scaledAngularDensity, if_neg hcond,
        Set.indicator_of_notMem hθ]
  rw [hfun,
    MeasureTheory.integral_indicator measurableSet_Ioo,
    ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le
      (cutoff_nonneg a b h k ha hb hh hk)]
  simp only [intervalIntegral.integral_div]
  ring

private lemma scaled_area_polar
    (a b h k : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hh : 0 < h) (hk : 0 < k) :
    (∫ _p in scaledRegion a b h k, (1 : ℝ)) =
      1 / 2 *
        ∫ θ in (0 : ℝ)..cutoff a b h k,
          radialSquared a b h k θ := by
  rw [scaled_integral_eq_density
      a b h k ha hb hh hk,
    scaledPolarDensity_fubini
      a b h k ha hb hh hk]
  simp_rw [scaledPolarDensity_inner
    a b h k _ ha hb hh hk]
  exact scaledAngularDensity_integral
    a b h k ha hb hh hk

theorem gap6 (a b h k : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hh : 0 < h) (hk : 0 < k) :
    regionArea a b h k =
      a * b / 2 *
        ∫ φ in (0 : ℝ)..Real.arctan (a * k / (b * h)),
          radialSquared a b h k φ := by
  rw [regionArea_eq_scaled a b h k ha hb hh hk,
    scaled_area_polar a b h k ha hb hh hk]
  unfold cutoff
  ring

theorem gap7 (a b h k : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hh : 0 < h) (hk : 0 < k) :
    regionArea a b h k =
      a * b / 2 * (a / h) ^ 2 *
          (∫ φ in (0 : ℝ)..Real.arctan (a * k / (b * h)),
            Real.cos φ ^ 2 /
              (Real.cos φ + Real.sin φ) ^ 4) -
        a * b / 2 * (b / k) ^ 2 *
          (∫ φ in (0 : ℝ)..Real.arctan (a * k / (b * h)),
            Real.sin φ ^ 2 /
              (Real.cos φ + Real.sin φ) ^ 4) := by
  rw [gap6 a b h k ha hb hh hk]
  unfold radialSquared
  rw [show
      (∫ φ in (0 : ℝ)..Real.arctan (a * k / (b * h)),
        ((a / h) ^ 2 * Real.cos φ ^ 2 -
          (b / k) ^ 2 * Real.sin φ ^ 2) /
            (Real.cos φ + Real.sin φ) ^ 4) =
        (a / h) ^ 2 *
            (∫ φ in (0 : ℝ)..Real.arctan (a * k / (b * h)),
              Real.cos φ ^ 2 /
                (Real.cos φ + Real.sin φ) ^ 4) -
          (b / k) ^ 2 *
            (∫ φ in (0 : ℝ)..Real.arctan (a * k / (b * h)),
              Real.sin φ ^ 2 /
                (Real.cos φ + Real.sin φ) ^ 4) by
    calc
      (∫ φ in (0 : ℝ)..Real.arctan (a * k / (b * h)),
        ((a / h) ^ 2 * Real.cos φ ^ 2 -
          (b / k) ^ 2 * Real.sin φ ^ 2) /
            (Real.cos φ + Real.sin φ) ^ 4) =
          ∫ φ in (0 : ℝ)..Real.arctan (a * k / (b * h)),
            (a / h) ^ 2 *
                (Real.cos φ ^ 2 /
                  (Real.cos φ + Real.sin φ) ^ 4) -
              (b / k) ^ 2 *
                (Real.sin φ ^ 2 /
                  (Real.cos φ + Real.sin φ) ^ 4) := by
        apply intervalIntegral.integral_congr
        intro φ _
        ring
      _ =
          (∫ φ in (0 : ℝ)..Real.arctan (a * k / (b * h)),
            (a / h) ^ 2 *
              (Real.cos φ ^ 2 /
                (Real.cos φ + Real.sin φ) ^ 4)) -
          ∫ φ in (0 : ℝ)..Real.arctan (a * k / (b * h)),
            (b / k) ^ 2 *
              (Real.sin φ ^ 2 /
                (Real.cos φ + Real.sin φ) ^ 4) := by
        exact intervalIntegral.integral_sub
          (cosRatio_valid_integrable
            a b h k ha hb hh hk |>.const_mul _)
          (sinRatio_valid_integrable
            a b h k ha hb hh hk |>.const_mul _)
      _ = _ := by
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul]
    ]
  ring

theorem gap8 (a b h k : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hh : 0 < h) (hk : 0 < k) :
    regionArea a b h k =
      a ^ 4 * b * k * (a * k + 2 * b * h) /
        (6 * h ^ 2 * (a * k + b * h) ^ 2) := by
  have hcut0 :=
    cutoff_nonneg a b h k ha hb hh hk
  have hcutHalf := cutoff_lt_half a b h k
  have hcosIntegral :
      (∫ φ in (0 : ℝ)..cutoff a b h k,
        Real.cos φ ^ 2 /
          (Real.cos φ + Real.sin φ) ^ 4) =
        1 / 3 -
          1 / (3 * (1 + a * k / (b * h)) ^ 3) := by
    have hfund :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun θ : ℝ =>
          -1 / (3 * (1 + Real.tan θ) ^ 3))
        (f' := fun φ : ℝ =>
          Real.cos φ ^ 2 /
            (Real.cos φ + Real.sin φ) ^ 4)
        (fun φ hφ => by
          rw [Set.uIcc_of_le hcut0] at hφ
          exact cosPrimitive_hasDerivAt
            φ hφ.1 (hφ.2.trans_lt hcutHalf))
        (cosRatio_valid_integrable
          a b h k ha hb hh hk)
    rw [hfund]
    unfold cutoff
    simp only [Real.tan_arctan, Real.tan_zero, add_zero,
      one_pow, mul_one]
    ring
  have hsinIntegral :
      (∫ φ in (0 : ℝ)..cutoff a b h k,
        Real.sin φ ^ 2 /
          (Real.cos φ + Real.sin φ) ^ 4) =
        -1 / (1 + a * k / (b * h)) +
          1 / (1 + a * k / (b * h)) ^ 2 -
          1 / (3 * (1 + a * k / (b * h)) ^ 3) +
          1 / 3 := by
    have hfund :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun θ : ℝ =>
          -1 / (1 + Real.tan θ) +
            1 / (1 + Real.tan θ) ^ 2 -
            1 / (3 * (1 + Real.tan θ) ^ 3))
        (f' := fun φ : ℝ =>
          Real.sin φ ^ 2 /
            (Real.cos φ + Real.sin φ) ^ 4)
        (fun φ hφ => by
          rw [Set.uIcc_of_le hcut0] at hφ
          exact sinPrimitive_hasDerivAt
            φ hφ.1 (hφ.2.trans_lt hcutHalf))
        (sinRatio_valid_integrable
          a b h k ha hb hh hk)
    rw [hfund]
    unfold cutoff
    simp only [Real.tan_arctan, Real.tan_zero]
    norm_num
  rw [gap7 a b h k ha hb hh hk]
  change
    a * b / 2 * (a / h) ^ 2 *
        (∫ φ in (0 : ℝ)..cutoff a b h k,
          Real.cos φ ^ 2 /
            (Real.cos φ + Real.sin φ) ^ 4) -
      a * b / 2 * (b / k) ^ 2 *
        (∫ φ in (0 : ℝ)..cutoff a b h k,
          Real.sin φ ^ 2 /
            (Real.cos φ + Real.sin φ) ^ 4) =
      a ^ 4 * b * k * (a * k + 2 * b * h) /
        (6 * h ^ 2 * (a * k + b * h) ^ 2)
  rw [hcosIntegral, hsinIntegral]
  have habhk : b * h ≠ 0 :=
    mul_ne_zero hb.ne' hh.ne'
  have hsum : a * k + b * h ≠ 0 := by
    positivity
  field_simp [ha.ne', hb.ne', hh.ne', hk.ne',
    habhk, hsum]
  ring

end

end ProofGap.Exercise3994
