import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3992

noncomputable section

open MeasureTheory
open scoped Interval

def region (a b h k : ℝ) : Set (ℝ × ℝ) :=
  {p |
    0 ≤ p.1 ∧ 0 ≤ p.2 ∧
      p.1 ^ 3 / a ^ 3 + p.2 ^ 3 / b ^ 3 ≤
        p.1 ^ 2 / h ^ 2 + p.2 ^ 2 / k ^ 2}

def regionArea (a b h k : ℝ) : ℝ :=
  ∫ _p in region a b h k, (1 : ℝ)

def radial (a b h k φ : ℝ) : ℝ :=
  ((a / h) ^ 2 * Real.cos φ ^ 2 +
      (b / k) ^ 2 * Real.sin φ ^ 2) /
    (Real.cos φ ^ 3 + Real.sin φ ^ 3)

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
    0 ≤ p.1 ∧ 0 ≤ p.2 ∧
      p.1 ^ 3 + p.2 ^ 3 ≤
        (a / h) ^ 2 * p.1 ^ 2 +
          (b / k) ^ 2 * p.2 ^ 2}

private lemma region_measurable
    (a b h k : ℝ) :
    MeasurableSet (region a b h k) := by
  unfold region
  exact
    (measurableSet_le measurable_const measurable_fst).inter <|
      (measurableSet_le measurable_const measurable_snd).inter <|
        measurableSet_le
          (show Measurable
            (fun p : ℝ × ℝ =>
              p.1 ^ 3 / a ^ 3 + p.2 ^ 3 / b ^ 3) by
            fun_prop)
          (show Measurable
            (fun p : ℝ × ℝ =>
              p.1 ^ 2 / h ^ 2 +
                p.2 ^ 2 / k ^ 2) by
            fun_prop)

private lemma scaledRegion_measurable
    (a b h k : ℝ) :
    MeasurableSet (scaledRegion a b h k) := by
  unfold scaledRegion
  exact
    (measurableSet_le measurable_const measurable_fst).inter <|
      (measurableSet_le measurable_const measurable_snd).inter <|
        measurableSet_le
          (show Measurable
            (fun p : ℝ × ℝ => p.1 ^ 3 + p.2 ^ 3) by
            fun_prop)
          (show Measurable
            (fun p : ℝ × ℝ =>
              (a / h) ^ 2 * p.1 ^ 2 +
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
    have hx' : 0 ≤ q.1 := by
      exact (mul_nonneg_iff_of_pos_left ha).mp hx
    have hy' : 0 ≤ q.2 := by
      exact (mul_nonneg_iff_of_pos_left hb).mp hy
    refine ⟨hx', hy', ?_⟩
    convert hineq using 1 <;>
      field_simp [ha0, hb0, hh0, hk0] <;> ring
  · rintro ⟨hx, hy, hineq⟩
    refine ⟨mul_nonneg ha.le hx, mul_nonneg hb.le hy, ?_⟩
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
    radial a b h k φ =
      ((a / h) ^ 2 * Real.cos φ ^ 2 +
          (b / k) ^ 2 * Real.sin φ ^ 2) /
        (Real.cos φ ^ 3 + Real.sin φ ^ 3) := by
  rfl

private def scaledPolarDomain (a b h k : ℝ) :
    Set (ℝ × ℝ) :=
  {q |
    0 < q.1 ∧ 0 ≤ q.2 ∧ q.2 ≤ Real.pi / 2 ∧
      q.1 ≤ radial a b h k q.2}

private noncomputable def scaledPolarDensity
    (a b h k : ℝ) (q : ℝ × ℝ) : ℝ :=
  (scaledPolarDomain a b h k).indicator
    (fun p => p.1) q

private lemma firstQuadrant_nonneg_angle_iff
    (r θ : ℝ) (hr : 0 < r)
    (hθ : -Real.pi < θ ∧ θ < Real.pi) :
    (0 ≤ r * Real.cos θ ∧
        0 ≤ r * Real.sin θ) ↔
      0 ≤ θ ∧ θ ≤ Real.pi / 2 := by
  constructor
  · rintro ⟨hx, hy⟩
    have hcos : 0 ≤ Real.cos θ := by
      exact (mul_nonneg_iff_of_pos_left hr).mp hx
    have hsin : 0 ≤ Real.sin θ := by
      exact (mul_nonneg_iff_of_pos_left hr).mp hy
    have hθ0 : 0 ≤ θ := by
      by_contra hnot
      have hsneg :
          Real.sin θ < 0 :=
        Real.sin_neg_of_neg_of_neg_pi_lt
          (lt_of_not_ge hnot) hθ.1
      linarith
    have hθhalf : θ ≤ Real.pi / 2 := by
      by_contra hnot
      have hcneg :
          Real.cos θ < 0 :=
        Real.cos_neg_of_pi_div_two_lt_of_lt
          (lt_of_not_ge hnot)
          (by linarith [hθ.2, Real.pi_pos])
      linarith
    exact ⟨hθ0, hθhalf⟩
  · rintro ⟨hθ0, hθhalf⟩
    have hcos :
        0 ≤ Real.cos θ :=
      Real.cos_nonneg_of_mem_Icc
        ⟨by linarith [Real.pi_pos, hθ0], hθhalf⟩
    have hsin :
        0 ≤ Real.sin θ :=
      Real.sin_nonneg_of_nonneg_of_le_pi
        hθ0 (by linarith [hθhalf, Real.pi_pos])
    exact
      ⟨mul_nonneg hr.le hcos,
        mul_nonneg hr.le hsin⟩

private lemma polar_mem_scaledRegion_iff
    (a b h k : ℝ) (q : ℝ × ℝ)
    (hq : q ∈ polarCoord.target) :
    polarCoord.symm q ∈ scaledRegion a b h k ↔
      q ∈ scaledPolarDomain a b h k := by
  rcases hq with ⟨hr, hθl, hθu⟩
  simp only [polarCoord_symm_apply]
  unfold scaledRegion scaledPolarDomain
  simp only [Set.mem_setOf_eq]
  have hangle :=
    firstQuadrant_nonneg_angle_iff q.1 q.2 hr
      ⟨hθl, hθu⟩
  constructor
  · rintro ⟨hx, hy, hineq⟩
    have hang :
        0 ≤ q.2 ∧ q.2 ≤ Real.pi / 2 :=
      hangle.1 ⟨hx, hy⟩
    refine ⟨hr, hang.1, hang.2, ?_⟩
    have hc :
        0 ≤ Real.cos q.2 :=
      Real.cos_nonneg_of_mem_Icc
        ⟨by linarith [Real.pi_pos, hang.1], hang.2⟩
    have hs :
        0 ≤ Real.sin q.2 :=
      Real.sin_nonneg_of_nonneg_of_le_pi
        hang.1 (by linarith [hang.2, Real.pi_pos])
    have hden :
        0 < Real.cos q.2 ^ 3 + Real.sin q.2 ^ 3 := by
      have hsq := Real.sin_sq_add_cos_sq q.2
      by_cases hc0 : Real.cos q.2 = 0
      · have hspos : 0 < Real.sin q.2 := by
          nlinarith
        positivity
      · have hcpos : 0 < Real.cos q.2 :=
          lt_of_le_of_ne hc (Ne.symm hc0)
        positivity
    have hr2 : 0 < q.1 ^ 2 := sq_pos_of_pos hr
    have hfact :
        q.1 ^ 2 *
            (q.1 *
              (Real.cos q.2 ^ 3 + Real.sin q.2 ^ 3)) ≤
          q.1 ^ 2 *
            ((a / h) ^ 2 * Real.cos q.2 ^ 2 +
              (b / k) ^ 2 * Real.sin q.2 ^ 2) := by
      convert hineq using 1 <;> ring
    have hcancel :
        q.1 *
            (Real.cos q.2 ^ 3 + Real.sin q.2 ^ 3) ≤
          (a / h) ^ 2 * Real.cos q.2 ^ 2 +
            (b / k) ^ 2 * Real.sin q.2 ^ 2 := by
      apply (mul_le_mul_iff_left₀ hr2).mp
      simpa [mul_comm, mul_left_comm, mul_assoc] using hfact
    unfold radial
    exact (le_div_iff₀ hden).2 hcancel
  · rintro ⟨hr', hθ0, hθhalf, hrad⟩
    have hxy := hangle.2 ⟨hθ0, hθhalf⟩
    refine ⟨hxy.1, hxy.2, ?_⟩
    have hc :
        0 ≤ Real.cos q.2 :=
      Real.cos_nonneg_of_mem_Icc
        ⟨by linarith [Real.pi_pos, hθ0], hθhalf⟩
    have hs :
        0 ≤ Real.sin q.2 :=
      Real.sin_nonneg_of_nonneg_of_le_pi
        hθ0 (by linarith [hθhalf, Real.pi_pos])
    have hden :
        0 < Real.cos q.2 ^ 3 + Real.sin q.2 ^ 3 := by
      have hsq := Real.sin_sq_add_cos_sq q.2
      by_cases hc0 : Real.cos q.2 = 0
      · have hspos : 0 < Real.sin q.2 := by
          nlinarith
        positivity
      · have hcpos : 0 < Real.cos q.2 :=
          lt_of_le_of_ne hc (Ne.symm hc0)
        positivity
    unfold radial at hrad
    have hmul :
        q.1 *
            (Real.cos q.2 ^ 3 + Real.sin q.2 ^ 3) ≤
          (a / h) ^ 2 * Real.cos q.2 ^ 2 +
            (b / k) ^ 2 * Real.sin q.2 ^ 2 :=
      (le_div_iff₀ hden).1 hrad
    have hr2 : 0 < q.1 ^ 2 := sq_pos_of_pos hr
    have hfact :=
      (mul_le_mul_iff_left₀ hr2).2 hmul
    convert hfact using 1 <;> ring

private lemma scaled_integral_eq_density
    (a b h k : ℝ) :
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
        rcases hD with ⟨hr, hθ0, hθhalf, _⟩
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
    (polar_mem_scaledRegion_iff a b h k q hq).symm
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
      (measurableSet_le measurable_const measurable_snd).inter <|
        (measurableSet_le measurable_snd measurable_const).inter <|
          measurableSet_le
            measurable_fst
            (show Measurable
              (fun q : ℝ × ℝ =>
                radial a b h k q.2) by
              unfold radial
              fun_prop)

private lemma radial_nonneg
    (a b h k θ : ℝ)
    (hθ0 : 0 ≤ θ) (hθhalf : θ ≤ Real.pi / 2) :
    0 ≤ radial a b h k θ := by
  have hc :
      0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [Real.pi_pos, hθ0], hθhalf⟩
  have hs :
      0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi
      hθ0 (by linarith [hθhalf, Real.pi_pos])
  have hden :
      0 < Real.cos θ ^ 3 + Real.sin θ ^ 3 := by
    have hsq := Real.sin_sq_add_cos_sq θ
    by_cases hc0 : Real.cos θ = 0
    · have hspos : 0 < Real.sin θ := by
        nlinarith
      positivity
    · have hcpos : 0 < Real.cos θ :=
        lt_of_le_of_ne hc (Ne.symm hc0)
      positivity
  unfold radial
  exact div_nonneg
    (add_nonneg
      (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (mul_nonneg (sq_nonneg _) (sq_nonneg _)))
    hden.le

private lemma radial_le_bound
    (a b h k θ : ℝ)
    (hθ0 : 0 ≤ θ) (hθhalf : θ ≤ Real.pi / 2) :
    radial a b h k θ ≤
      2 * ((a / h) ^ 2 + (b / k) ^ 2) := by
  have hc :
      0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [Real.pi_pos, hθ0], hθhalf⟩
  have hs :
      0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi
      hθ0 (by linarith [hθhalf, Real.pi_pos])
  let A : ℝ := (a / h) ^ 2
  let B : ℝ := (b / k) ^ 2
  let N : ℝ :=
    A * Real.cos θ ^ 2 + B * Real.sin θ ^ 2
  let D : ℝ := Real.cos θ ^ 3 + Real.sin θ ^ 3
  have hA : 0 ≤ A := sq_nonneg _
  have hB : 0 ≤ B := sq_nonneg _
  have hAB : 0 ≤ A + B := add_nonneg hA hB
  have hN : 0 ≤ N := by
    dsimp [N]
    exact add_nonneg
      (mul_nonneg hA (sq_nonneg _))
      (mul_nonneg hB (sq_nonneg _))
  have hcSq : Real.cos θ ^ 2 ≤ 1 :=
    Real.cos_sq_le_one θ
  have hsSq : Real.sin θ ^ 2 ≤ 1 :=
    Real.sin_sq_le_one θ
  have hNle : N ≤ A + B := by
    dsimp [N]
    nlinarith [
      mul_nonneg hA (sub_nonneg.2 hcSq),
      mul_nonneg hB (sub_nonneg.2 hsSq)]
  have hprod : Real.cos θ * Real.sin θ ≤ 1 / 2 := by
    nlinarith [Real.sin_sq_add_cos_sq θ,
      sq_nonneg (Real.cos θ - Real.sin θ)]
  have hsumSq :
      (Real.cos θ + Real.sin θ) ^ 2 =
        1 + 2 * (Real.cos θ * Real.sin θ) := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  have hsum1 : 1 ≤ Real.cos θ + Real.sin θ := by
    have hsum0 : 0 ≤ Real.cos θ + Real.sin θ :=
      add_nonneg hc hs
    nlinarith [hsumSq,
      sq_nonneg (Real.cos θ + Real.sin θ - 1)]
  have hfactor : 1 / 2 ≤ 1 - Real.cos θ * Real.sin θ := by
    linarith
  have hDhalf : 1 / 2 ≤ D := by
    calc
      (1 / 2 : ℝ) ≤
          1 * (1 - Real.cos θ * Real.sin θ) := by
        simpa using hfactor
      _ ≤
          (Real.cos θ + Real.sin θ) *
            (1 - Real.cos θ * Real.sin θ) := by
        exact mul_le_mul_of_nonneg_right hsum1
          (by linarith)
      _ = D := by
        dsimp [D]
        nlinarith [Real.sin_sq_add_cos_sq θ]
  have hDpos : 0 < D :=
    lt_of_lt_of_le (by norm_num) hDhalf
  unfold radial
  change N / D ≤ 2 * (A + B)
  apply (div_le_iff₀ hDpos).2
  calc
    N ≤ A + B := hNle
    _ ≤ 2 * (A + B) * D := by
      nlinarith [mul_nonneg hAB
        (sub_nonneg.2 hDhalf)]

private lemma scaledPolarDensity_integrable
    (a b h k : ℝ) :
    Integrable (scaledPolarDensity a b h k) := by
  let M : ℝ :=
    2 * ((a / h) ^ 2 + (b / k) ^ 2)
  have hM : 0 ≤ M := by
    dsimp [M]
    positivity
  have hsubset :
      scaledPolarDomain a b h k ⊆
        Set.Icc (0 : ℝ) M ×ˢ
          Set.Icc (0 : ℝ) (Real.pi / 2) := by
    intro q hq
    rcases hq with ⟨hr, hθ0, hθhalf, hrad⟩
    have hRle :
        radial a b h k q.2 ≤ M := by
      dsimp [M]
      exact radial_le_bound
        a b h k q.2 hθ0 hθhalf
    exact
      ⟨⟨hr.le, hrad.trans hRle⟩, ⟨hθ0, hθhalf⟩⟩
  have hcompact :
      IsCompact
        (Set.Icc (0 : ℝ) M ×ˢ
          Set.Icc (0 : ℝ) (Real.pi / 2)) :=
    isCompact_Icc.prod isCompact_Icc
  have hrect :
      IntegrableOn (fun q : ℝ × ℝ => q.1)
        (Set.Icc (0 : ℝ) M ×ˢ
          Set.Icc (0 : ℝ) (Real.pi / 2)) :=
    continuous_fst.continuousOn.integrableOn_compact
      hcompact
  unfold scaledPolarDensity
  rw [integrable_indicator_iff
    (scaledPolarDomain_measurable a b h k)]
  exact hrect.mono_set hsubset

private lemma scaledPolarDensity_fubini
    (a b h k : ℝ) :
    (∫ q, scaledPolarDensity a b h k q) =
      ∫ θ : ℝ,
        ∫ r : ℝ, scaledPolarDensity a b h k (r, θ) := by
  simpa only [Measure.volume_eq_prod] using
    (MeasureTheory.integral_prod_symm
      (scaledPolarDensity a b h k)
      (scaledPolarDensity_integrable a b h k))

private noncomputable def scaledAngularDensity
    (a b h k θ : ℝ) : ℝ :=
  if 0 ≤ θ ∧ θ ≤ Real.pi / 2 then
    radial a b h k θ ^ 2 / 2
  else
    0

private lemma scaledPolarDensity_inner
    (a b h k θ : ℝ) :
    (∫ r : ℝ, scaledPolarDensity a b h k (r, θ)) =
      scaledAngularDensity a b h k θ := by
  by_cases hθ : 0 ≤ θ ∧ θ ≤ Real.pi / 2
  · rw [scaledAngularDensity, if_pos hθ]
    have hR : 0 ≤ radial a b h k θ :=
      radial_nonneg a b h k θ hθ.1 hθ.2
    have hfun :
        (fun r : ℝ =>
          scaledPolarDensity a b h k (r, θ)) =
        (Set.Ioc (0 : ℝ) (radial a b h k θ)).indicator
          (fun r => r) := by
      funext r
      unfold scaledPolarDensity scaledPolarDomain
      by_cases hr :
          0 < r ∧ r ≤ radial a b h k θ
      · have hD :
            (r, θ) ∈
              {q |
                0 < q.1 ∧ 0 ≤ q.2 ∧
                  q.2 ≤ Real.pi / 2 ∧
                  q.1 ≤ radial a b h k q.2} :=
          ⟨hr.1, hθ.1, hθ.2, hr.2⟩
        have hI :
            r ∈ Set.Ioc (0 : ℝ)
              (radial a b h k θ) := hr
        rw [Set.indicator_of_mem hD,
          Set.indicator_of_mem hI]
      · have hD :
            (r, θ) ∉
              {q |
                0 < q.1 ∧ 0 ≤ q.2 ∧
                  q.2 ≤ Real.pi / 2 ∧
                  q.1 ≤ radial a b h k q.2} := by
          intro hD
          exact hr ⟨hD.1, hD.2.2.2⟩
        have hI :
            r ∉ Set.Ioc (0 : ℝ)
              (radial a b h k θ) := hr
        rw [Set.indicator_of_notMem hD,
          Set.indicator_of_notMem hI]
    rw [hfun,
      MeasureTheory.integral_indicator measurableSet_Ioc,
      ← intervalIntegral.integral_of_le hR,
      integral_id]
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
    (a b h k : ℝ) :
    (∫ θ : ℝ, scaledAngularDensity a b h k θ) =
      1 / 2 *
        ∫ θ in (0 : ℝ)..Real.pi / 2,
          radial a b h k θ ^ 2 := by
  have hfun :
      scaledAngularDensity a b h k =
        (Set.Icc (0 : ℝ) (Real.pi / 2)).indicator
          (fun θ => radial a b h k θ ^ 2 / 2) := by
    funext θ
    by_cases hθ :
        θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2)
    · change
        (if 0 ≤ θ ∧ θ ≤ Real.pi / 2 then
            radial a b h k θ ^ 2 / 2
          else 0) =
          (Set.Icc (0 : ℝ)
            (Real.pi / 2)).indicator
              (fun θ =>
                radial a b h k θ ^ 2 / 2) θ
      rw [if_pos
        (show 0 ≤ θ ∧ θ ≤ Real.pi / 2 from hθ),
        Set.indicator_of_mem hθ]
    · have hcond :
          ¬(0 ≤ θ ∧ θ ≤ Real.pi / 2) := hθ
      rw [scaledAngularDensity, if_neg hcond,
        Set.indicator_of_notMem hθ]
  rw [hfun,
    MeasureTheory.integral_indicator measurableSet_Icc,
    integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le
      (by linarith [Real.pi_pos])]
  simp only [intervalIntegral.integral_div]
  ring

private lemma scaled_area_polar
    (a b h k : ℝ) :
    (∫ _p in scaledRegion a b h k, (1 : ℝ)) =
      1 / 2 *
        ∫ θ in (0 : ℝ)..Real.pi / 2,
          radial a b h k θ ^ 2 := by
  rw [scaled_integral_eq_density,
    scaledPolarDensity_fubini]
  simp_rw [scaledPolarDensity_inner]
  exact scaledAngularDensity_integral a b h k

theorem gap2 (a b h k : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hh : 0 < h) (hk : 0 < k) :
    regionArea a b h k =
      a * b / 2 *
        ∫ φ in (0 : ℝ)..Real.pi / 2,
          radial a b h k φ ^ 2 := by
  rw [regionArea_eq_scaled a b h k ha hb hh hk,
    scaled_area_polar]
  ring

theorem gap3 (a b h k : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hh : 0 < h) (hk : 0 < k) :
    regionArea a b h k =
      a * b / 2 *
        ∫ φ in (0 : ℝ)..Real.pi / 2,
          ((a / h) ^ 4 * Real.cos φ ^ 4 +
              (b / k) ^ 4 * Real.sin φ ^ 4 +
              2 * (a / h) ^ 2 * (b / k) ^ 2 *
                Real.cos φ ^ 2 * Real.sin φ ^ 2) /
            (Real.cos φ ^ 3 + Real.sin φ ^ 3) ^ 2 := by
  rw [gap2 a b h k ha hb hh hk]
  refine congrArg (fun z : ℝ => a * b / 2 * z) ?_
  apply intervalIntegral.integral_congr
  intro φ hφ
  rw [Set.uIcc_of_le (by linarith [Real.pi_pos])] at hφ
  have hc :
      0 ≤ Real.cos φ :=
    Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [Real.pi_pos, hφ.1], hφ.2⟩
  have hs :
      0 ≤ Real.sin φ :=
    Real.sin_nonneg_of_nonneg_of_le_pi
      hφ.1 (by linarith [hφ.2, Real.pi_pos])
  have hden :
      Real.cos φ ^ 3 + Real.sin φ ^ 3 ≠ 0 := by
    have hsq := Real.sin_sq_add_cos_sq φ
    by_cases hc0 : Real.cos φ = 0
    · have hspos : 0 < Real.sin φ := by
        nlinarith
      positivity
    · have hcpos : 0 < Real.cos φ :=
        lt_of_le_of_ne hc (Ne.symm hc0)
      positivity
  unfold radial
  field_simp [hden]
  ring

theorem gap8 (a b h k : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hh : 0 < h) (hk : 0 < k) :
    2 * Real.pi * a * b / (9 * Real.sqrt 3) * (a / h) ^ 4 +
          2 * Real.pi * a * b / (9 * Real.sqrt 3) * (b / k) ^ 4 +
          a * b / 3 * (a / h) ^ 2 * (b / k) ^ 2 =
      a * b / 3 *
        (2 * Real.pi / (3 * Real.sqrt 3) *
            (a ^ 4 / h ^ 4 + b ^ 4 / k ^ 4) +
          a ^ 2 * b ^ 2 / (h ^ 2 * k ^ 2)) := by
  have hsqrt : Real.sqrt 3 ≠ 0 :=
    (Real.sqrt_pos.2 (by norm_num)).ne'
  field_simp [ha.ne', hb.ne', hh.ne', hk.ne', hsqrt]
  ring

private noncomputable def rationalPrimitive (t : ℝ) : ℝ :=
  -2 / (9 * (t + 1)) +
    (2 - t) / (9 * (t ^ 2 - t + 1)) +
    4 / (3 * Real.sqrt 3) *
      Real.arctan ((2 * t - 1) / Real.sqrt 3)

private lemma rationalPrimitive_hasDerivAt
    (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt rationalPrimitive
      ((1 + t ^ 4) / (1 + t ^ 3) ^ 2) t := by
  have hsqrtpos : 0 < Real.sqrt 3 :=
    Real.sqrt_pos.2 (by norm_num)
  have hsqrt0 : Real.sqrt 3 ≠ 0 := hsqrtpos.ne'
  have hsqrtSq : Real.sqrt 3 ^ 2 = 3 :=
    Real.sq_sqrt (by norm_num)
  have ht1 : t + 1 ≠ 0 := by
    linarith
  have hqpos : 0 < t ^ 2 - t + 1 := by
    nlinarith [sq_nonneg (t - 1 / 2)]
  have hq0 : t ^ 2 - t + 1 ≠ 0 := hqpos.ne'
  have hcubic :
      1 + t ^ 3 =
        (t + 1) * (t ^ 2 - t + 1) := by
    ring
  have hcubic0 : 1 + t ^ 3 ≠ 0 := by
    rw [hcubic]
    exact mul_ne_zero ht1 hq0
  have hq :
      HasDerivAt
        (fun z : ℝ => z ^ 2 - z + 1)
        (2 * t - 1) t := by
    convert
      (((hasDerivAt_id t).pow 2).sub
        (hasDerivAt_id t)).const_add 1
      using 1 <;> simp [id_eq, Function.comp_def] <;> ring
  have hden1 :
      HasDerivAt (fun z : ℝ => 9 * (z + 1)) 9 t := by
    convert
      ((hasDerivAt_id t).const_add 1).const_mul 9
      using 1 <;> simp [id_eq, Function.comp_def] <;> ring
  have hterm1 :=
    (hasDerivAt_const t (-2 : ℝ)).div hden1
      (mul_ne_zero (by norm_num) ht1)
  have hnum2 :
      HasDerivAt (fun z : ℝ => 2 - z) (-1) t := by
    convert
      (hasDerivAt_const t 2).sub (hasDerivAt_id t)
      using 1 <;> ring
  have hden2 :
      HasDerivAt
        (fun z : ℝ => 9 * (z ^ 2 - z + 1))
        (9 * (2 * t - 1)) t := by
    exact hq.const_mul 9
  have hterm2 :=
    hnum2.div hden2
      (mul_ne_zero (by norm_num) hq0)
  have hz :
      HasDerivAt
        (fun z : ℝ => (2 * z - 1) / Real.sqrt 3)
        (2 / Real.sqrt 3) t := by
    convert
      (((hasDerivAt_id t).const_mul 2).sub_const 1).div_const
        (Real.sqrt 3)
      using 1 <;> ring
  have hatan :=
    (Real.hasDerivAt_arctan
      ((2 * t - 1) / Real.sqrt 3)).comp t hz
  have hterm3 :=
    hatan.const_mul (4 / (3 * Real.sqrt 3))
  have hsum := (hterm1.add hterm2).add hterm3
  have harcden :
      Real.sqrt 3 ^ 2 + (2 * t - 1) ^ 2 ≠ 0 := by
    positivity
  have harctanDen :
      1 + ((2 * t - 1) / Real.sqrt 3) ^ 2 =
        (4 / 3) * (t ^ 2 - t + 1) := by
    field_simp [hsqrt0]
    nlinarith [hsqrtSq]
  have hqReordered : 1 - t + t ^ 2 ≠ 0 := by
    convert hq0 using 1 <;> ring
  have hqReorderedEq :
      1 - t + t ^ 2 = t ^ 2 - t + 1 := by
    ring
  have hqExpandedSq :
      1 - 2 * t + 3 * t ^ 2 - 2 * t ^ 3 + t ^ 4 ≠ 0 := by
    rw [show
      1 - 2 * t + 3 * t ^ 2 - 2 * t ^ 3 + t ^ 4 =
        (t ^ 2 - t + 1) ^ 2 by ring]
    exact pow_ne_zero 2 hq0
  have hqExpandedSq' :
      1 - t * 2 + (t ^ 2 * 3 - t ^ 3 * 2) + t ^ 4 ≠ 0 := by
    convert hqExpandedSq using 1 <;> ring
  have hqExpandedSqEq :
      1 - t * 2 + (t ^ 2 * 3 - t ^ 3 * 2) + t ^ 4 =
        (t ^ 2 - t + 1) ^ 2 := by
    ring
  have hqExpandedSq'' :
      1 - t * 2 + t ^ 2 * (3 - t * 2) + t ^ 4 ≠ 0 := by
    convert hqExpandedSq using 1 <;> ring
  have hqFactoredEq :
      t * (t - 1) + 1 = t ^ 2 - t + 1 := by
    ring
  have hqFactored0 : t * (t - 1) + 1 ≠ 0 := by
    rw [hqFactoredEq]
    exact hq0
  have htarget :
      (1 + t ^ 4) / (1 + t ^ 3) ^ 2 =
        2 / (9 * (t + 1) ^ 2) +
          (7 * t ^ 2 - 10 * t + 7) /
            (9 * (t ^ 2 - t + 1) ^ 2) := by
    rw [hcubic]
    field_simp [ht1, hq0, hqFactored0, hqExpandedSq,
      hqExpandedSq', hqExpandedSq'']
    ring
  have hraw :
      (0 * (9 * (t + 1)) - (-2) * 9) /
            (9 * (t + 1)) ^ 2 +
          ((-1) * (9 * (t ^ 2 - t + 1)) -
              (2 - t) * (9 * (2 * t - 1))) /
            (9 * (t ^ 2 - t + 1)) ^ 2 +
          4 / (3 * Real.sqrt 3) *
            (1 / (1 + ((2 * t - 1) / Real.sqrt 3) ^ 2) *
              (2 / Real.sqrt 3)) =
        2 / (9 * (t + 1) ^ 2) +
          (7 * t ^ 2 - 10 * t + 7) /
            (9 * (t ^ 2 - t + 1) ^ 2) := by
    rw [harctanDen]
    field_simp [ht1, hq0, hqFactored0, hqReordered,
      hqExpandedSq, hqExpandedSq', hqExpandedSq'', hsqrt0]
    rw [hsqrtSq]
    ring
  unfold rationalPrimitive
  convert hsum using 1
  exact htarget.trans hraw.symm

private noncomputable def cosTerm (φ : ℝ) : ℝ :=
  Real.cos φ ^ 4 /
    (Real.cos φ ^ 3 + Real.sin φ ^ 3) ^ 2

private noncomputable def sinTerm (φ : ℝ) : ℝ :=
  Real.sin φ ^ 4 /
    (Real.cos φ ^ 3 + Real.sin φ ^ 3) ^ 2

private noncomputable def crossTerm (φ : ℝ) : ℝ :=
  2 * Real.cos φ ^ 2 * Real.sin φ ^ 2 /
    (Real.cos φ ^ 3 + Real.sin φ ^ 3) ^ 2

private lemma cubicDen_pos_on_Icc
    (φ : ℝ)
    (hφ : φ ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    0 < Real.cos φ ^ 3 + Real.sin φ ^ 3 := by
  have hc : 0 ≤ Real.cos φ :=
    Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [Real.pi_pos, hφ.1], hφ.2⟩
  have hs : 0 ≤ Real.sin φ :=
    Real.sin_nonneg_of_nonneg_of_le_pi
      hφ.1 (by linarith [Real.pi_pos, hφ.2])
  have hsq := Real.sin_sq_add_cos_sq φ
  by_cases hc0 : Real.cos φ = 0
  · have hspos : 0 < Real.sin φ := by
      nlinarith
    positivity
  · have hcpos : 0 < Real.cos φ :=
      lt_of_le_of_ne hc (Ne.symm hc0)
    positivity

private lemma cosTerm_intervalIntegrable :
    IntervalIntegrable cosTerm volume 0 (Real.pi / 2) := by
  apply ContinuousOn.intervalIntegrable
  intro φ hφ
  rw [Set.uIcc_of_le
    (by linarith [Real.pi_pos])] at hφ
  apply ContinuousAt.continuousWithinAt
  unfold cosTerm
  exact
    (Real.continuous_cos.continuousAt.pow 4).div
      (((Real.continuous_cos.continuousAt.pow 3).add
        (Real.continuous_sin.continuousAt.pow 3)).pow 2)
      (pow_ne_zero 2
        (cubicDen_pos_on_Icc φ hφ).ne')

private lemma sinTerm_intervalIntegrable :
    IntervalIntegrable sinTerm volume 0 (Real.pi / 2) := by
  apply ContinuousOn.intervalIntegrable
  intro φ hφ
  rw [Set.uIcc_of_le
    (by linarith [Real.pi_pos])] at hφ
  apply ContinuousAt.continuousWithinAt
  unfold sinTerm
  exact
    (Real.continuous_sin.continuousAt.pow 4).div
      (((Real.continuous_cos.continuousAt.pow 3).add
        (Real.continuous_sin.continuousAt.pow 3)).pow 2)
      (pow_ne_zero 2
        (cubicDen_pos_on_Icc φ hφ).ne')

private lemma crossTerm_intervalIntegrable :
    IntervalIntegrable crossTerm volume 0 (Real.pi / 2) := by
  apply ContinuousOn.intervalIntegrable
  intro φ hφ
  rw [Set.uIcc_of_le
    (by linarith [Real.pi_pos])] at hφ
  apply ContinuousAt.continuousWithinAt
  unfold crossTerm
  exact
    (((continuousAt_const.mul
        (Real.continuous_cos.continuousAt.pow 2)).mul
          (Real.continuous_sin.continuousAt.pow 2)).div
      (((Real.continuous_cos.continuousAt.pow 3).add
        (Real.continuous_sin.continuousAt.pow 3)).pow 2)
      (pow_ne_zero 2
        (cubicDen_pos_on_Icc φ hφ).ne'))

private lemma half_sum_hasDerivAt
    (φ : ℝ) (hφ0 : 0 ≤ φ)
    (hφ1 : φ ≤ Real.pi / 4) :
    HasDerivAt
      (fun θ : ℝ =>
        rationalPrimitive (Real.tan θ))
      (cosTerm φ + sinTerm φ) φ := by
  have hhalf : φ < Real.pi / 2 := by
    linarith [Real.pi_pos]
  have hmem :
      φ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], hhalf⟩
  have htan0 : 0 ≤ Real.tan φ :=
    Real.tan_nonneg_of_nonneg_of_le_pi_div_two
      hφ0 hhalf.le
  have hcomp :=
    (rationalPrimitive_hasDerivAt
      (Real.tan φ) htan0).comp φ
      (Real.hasDerivAt_tan_of_mem_Ioo hmem)
  convert hcomp using 1
  unfold cosTerm sinTerm
  have hcos : Real.cos φ ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo hmem).ne'
  rw [Real.tan_eq_sin_div_cos]
  field_simp [hcos]

private lemma rationalPrimitive_one_sub_zero :
    rationalPrimitive 1 - rationalPrimitive 0 =
      4 * Real.pi / (9 * Real.sqrt 3) := by
  have hsqrt0 : Real.sqrt 3 ≠ 0 :=
    (Real.sqrt_pos.2 (by norm_num)).ne'
  have hsqrtSq : Real.sqrt 3 ^ 2 = 3 :=
    Real.sq_sqrt (by norm_num)
  unfold rationalPrimitive
  rw [show (2 * (1 : ℝ) - 1) / Real.sqrt 3 =
      (Real.sqrt 3)⁻¹ by
    norm_num [one_div],
    Real.arctan_inv_sqrt_three,
    show (2 * (0 : ℝ) - 1) / Real.sqrt 3 =
      -(Real.sqrt 3)⁻¹ by
    norm_num [div_eq_mul_inv],
    Real.arctan_neg,
    Real.arctan_inv_sqrt_three]
  field_simp [hsqrt0]
  ring

private lemma half_sum_intervalIntegrable :
    IntervalIntegrable
      (fun φ : ℝ => cosTerm φ + sinTerm φ)
      volume 0 (Real.pi / 4) := by
  apply ContinuousOn.intervalIntegrable
  intro φ hφ
  rw [Set.uIcc_of_le
    (by linarith [Real.pi_pos])] at hφ
  have hφFull :
      φ ∈ Set.Icc (0 : ℝ) (Real.pi / 2) :=
    ⟨hφ.1, by linarith [hφ.2, Real.pi_pos]⟩
  have hne := (cubicDen_pos_on_Icc φ hφFull).ne'
  apply ContinuousAt.continuousWithinAt
  unfold cosTerm sinTerm
  exact
    ((Real.continuous_cos.continuousAt.pow 4).div
        (((Real.continuous_cos.continuousAt.pow 3).add
          (Real.continuous_sin.continuousAt.pow 3)).pow 2)
        (pow_ne_zero 2 hne)).add
      ((Real.continuous_sin.continuousAt.pow 4).div
        (((Real.continuous_cos.continuousAt.pow 3).add
          (Real.continuous_sin.continuousAt.pow 3)).pow 2)
        (pow_ne_zero 2 hne))

private lemma half_sum_integral :
    (∫ φ in (0 : ℝ)..Real.pi / 4,
        cosTerm φ + sinTerm φ) =
      4 * Real.pi / (9 * Real.sqrt 3) := by
  have hderiv :
      ∀ φ ∈ Set.uIcc (0 : ℝ) (Real.pi / 4),
        HasDerivAt
          (fun θ : ℝ =>
            rationalPrimitive (Real.tan θ))
          (cosTerm φ + sinTerm φ) φ := by
    intro φ hφ
    rw [Set.uIcc_of_le
      (by linarith [Real.pi_pos])] at hφ
    exact half_sum_hasDerivAt φ hφ.1 hφ.2
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    hderiv half_sum_intervalIntegrable,
    Real.tan_pi_div_four]
  norm_num [rationalPrimitive_one_sub_zero]

private lemma cosTerm_integral :
    (∫ φ in (0 : ℝ)..Real.pi / 2, cosTerm φ) =
      4 * Real.pi / (9 * Real.sqrt 3) := by
  have hhalfSub :
      Set.uIcc (0 : ℝ) (Real.pi / 4) ⊆
        Set.uIcc (0 : ℝ) (Real.pi / 2) := by
    rw [Set.uIcc_of_le (by linarith [Real.pi_pos]),
      Set.uIcc_of_le (by linarith [Real.pi_pos])]
    intro x hx
    exact ⟨hx.1, by linarith [hx.2, Real.pi_pos]⟩
  have hupperSub :
      Set.uIcc (Real.pi / 4) (Real.pi / 2) ⊆
        Set.uIcc (0 : ℝ) (Real.pi / 2) := by
    rw [Set.uIcc_of_le (by linarith [Real.pi_pos]),
      Set.uIcc_of_le (by linarith [Real.pi_pos])]
    intro x hx
    exact ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩
  have hcHalf :
      IntervalIntegrable cosTerm volume 0
        (Real.pi / 4) :=
    cosTerm_intervalIntegrable.mono_set hhalfSub
  have hsHalf :
      IntervalIntegrable sinTerm volume 0
        (Real.pi / 4) :=
    sinTerm_intervalIntegrable.mono_set hhalfSub
  have hcUpper :
      IntervalIntegrable cosTerm volume
        (Real.pi / 4) (Real.pi / 2) :=
    cosTerm_intervalIntegrable.mono_set hupperSub
  have hsub :=
    intervalIntegral.integral_comp_sub_left
      (f := cosTerm) (a := (0 : ℝ))
      (b := Real.pi / 4) (Real.pi / 2)
  have hupper :
      (∫ φ in Real.pi / 4..Real.pi / 2,
          cosTerm φ) =
        ∫ φ in (0 : ℝ)..Real.pi / 4,
          sinTerm φ := by
    calc
      (∫ φ in Real.pi / 4..Real.pi / 2,
          cosTerm φ) =
          ∫ φ in (0 : ℝ)..Real.pi / 4,
            cosTerm (Real.pi / 2 - φ) := by
        convert hsub.symm using 1 <;> ring
      _ =
          ∫ φ in (0 : ℝ)..Real.pi / 4,
            sinTerm φ := by
        apply intervalIntegral.integral_congr
        intro φ _
        unfold cosTerm sinTerm
        change
          Real.cos (Real.pi / 2 - φ) ^ 4 /
                (Real.cos (Real.pi / 2 - φ) ^ 3 +
                  Real.sin (Real.pi / 2 - φ) ^ 3) ^ 2 =
            Real.sin φ ^ 4 /
                (Real.cos φ ^ 3 + Real.sin φ ^ 3) ^ 2
        rw [Real.cos_pi_div_two_sub,
          Real.sin_pi_div_two_sub]
        ring
  rw [← intervalIntegral.integral_add_adjacent_intervals
      hcHalf hcUpper,
    hupper,
    ← intervalIntegral.integral_add hcHalf hsHalf,
    half_sum_integral]

private noncomputable def crossPrimitive (t : ℝ) : ℝ :=
  (2 / 3) * t ^ 3 / (1 + t ^ 3)

private lemma crossPrimitive_hasDerivAt
    (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt crossPrimitive
      (2 * t ^ 2 / (1 + t ^ 3) ^ 2) t := by
  have hpow :
      HasDerivAt (fun z : ℝ => z ^ 3) (3 * t ^ 2) t := by
    convert (hasDerivAt_id t).pow 3 using 1 <;>
      simp [id_eq] <;> ring
  have hden :
      HasDerivAt (fun z : ℝ => 1 + z ^ 3)
        (3 * t ^ 2) t := by
    convert (hasDerivAt_const t 1).add hpow using 1 <;>
      simp
  have hden0 : 1 + t ^ 3 ≠ 0 := by
    positivity
  have hraw :=
    (hpow.const_mul (2 / 3)).div hden hden0
  unfold crossPrimitive
  convert hraw using 1
  field_simp [hden0]
  ring

private lemma half_cross_hasDerivAt
    (φ : ℝ) (hφ0 : 0 ≤ φ)
    (hφ1 : φ ≤ Real.pi / 4) :
    HasDerivAt
      (fun θ : ℝ =>
        crossPrimitive (Real.tan θ))
      (crossTerm φ) φ := by
  have hhalf : φ < Real.pi / 2 := by
    linarith [Real.pi_pos]
  have hmem :
      φ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith [Real.pi_pos], hhalf⟩
  have htan0 : 0 ≤ Real.tan φ :=
    Real.tan_nonneg_of_nonneg_of_le_pi_div_two
      hφ0 hhalf.le
  have hcomp :=
    (crossPrimitive_hasDerivAt
      (Real.tan φ) htan0).comp φ
      (Real.hasDerivAt_tan_of_mem_Ioo hmem)
  convert hcomp using 1
  unfold crossTerm
  have hcos : Real.cos φ ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo hmem).ne'
  rw [Real.tan_eq_sin_div_cos]
  field_simp [hcos]

private lemma half_cross_intervalIntegrable :
    IntervalIntegrable crossTerm volume 0 (Real.pi / 4) := by
  apply crossTerm_intervalIntegrable.mono_set
  rw [Set.uIcc_of_le (by linarith [Real.pi_pos]),
    Set.uIcc_of_le (by linarith [Real.pi_pos])]
  intro x hx
  exact ⟨hx.1, by linarith [hx.2, Real.pi_pos]⟩

private lemma half_cross_integral :
    (∫ φ in (0 : ℝ)..Real.pi / 4, crossTerm φ) =
      1 / 3 := by
  have hderiv :
      ∀ φ ∈ Set.uIcc (0 : ℝ) (Real.pi / 4),
        HasDerivAt
          (fun θ : ℝ =>
            crossPrimitive (Real.tan θ))
          (crossTerm φ) φ := by
    intro φ hφ
    rw [Set.uIcc_of_le
      (by linarith [Real.pi_pos])] at hφ
    exact half_cross_hasDerivAt φ hφ.1 hφ.2
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    hderiv half_cross_intervalIntegrable,
    Real.tan_pi_div_four]
  norm_num [crossPrimitive]

private lemma crossTerm_integral :
    (∫ φ in (0 : ℝ)..Real.pi / 2, crossTerm φ) =
      2 / 3 := by
  have hupperSub :
      Set.uIcc (Real.pi / 4) (Real.pi / 2) ⊆
        Set.uIcc (0 : ℝ) (Real.pi / 2) := by
    rw [Set.uIcc_of_le (by linarith [Real.pi_pos]),
      Set.uIcc_of_le (by linarith [Real.pi_pos])]
    intro x hx
    exact ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩
  have hupperInt :
      IntervalIntegrable crossTerm volume
        (Real.pi / 4) (Real.pi / 2) :=
    crossTerm_intervalIntegrable.mono_set hupperSub
  have hsub :=
    intervalIntegral.integral_comp_sub_left
      (f := crossTerm) (a := (0 : ℝ))
      (b := Real.pi / 4) (Real.pi / 2)
  have hupper :
      (∫ φ in Real.pi / 4..Real.pi / 2,
          crossTerm φ) =
        ∫ φ in (0 : ℝ)..Real.pi / 4,
          crossTerm φ := by
    calc
      (∫ φ in Real.pi / 4..Real.pi / 2,
          crossTerm φ) =
          ∫ φ in (0 : ℝ)..Real.pi / 4,
            crossTerm (Real.pi / 2 - φ) := by
        convert hsub.symm using 1 <;> ring
      _ =
          ∫ φ in (0 : ℝ)..Real.pi / 4,
            crossTerm φ := by
        apply intervalIntegral.integral_congr
        intro φ _
        unfold crossTerm
        change
          2 * Real.cos (Real.pi / 2 - φ) ^ 2 *
                  Real.sin (Real.pi / 2 - φ) ^ 2 /
                (Real.cos (Real.pi / 2 - φ) ^ 3 +
                  Real.sin (Real.pi / 2 - φ) ^ 3) ^ 2 =
            2 * Real.cos φ ^ 2 * Real.sin φ ^ 2 /
                (Real.cos φ ^ 3 + Real.sin φ ^ 3) ^ 2
        rw [Real.cos_pi_div_two_sub,
          Real.sin_pi_div_two_sub]
        ring
  rw [← intervalIntegral.integral_add_adjacent_intervals
      half_cross_intervalIntegrable hupperInt,
    hupper, half_cross_integral]
  norm_num

private lemma sinTerm_integral :
    (∫ φ in (0 : ℝ)..Real.pi / 2, sinTerm φ) =
      4 * Real.pi / (9 * Real.sqrt 3) := by
  have hsub :=
    intervalIntegral.integral_comp_sub_left
      (f := cosTerm) (a := (0 : ℝ))
      (b := Real.pi / 2) (Real.pi / 2)
  calc
    (∫ φ in (0 : ℝ)..Real.pi / 2,
        sinTerm φ) =
        ∫ φ in (0 : ℝ)..Real.pi / 2,
          cosTerm (Real.pi / 2 - φ) := by
      apply intervalIntegral.integral_congr
      intro φ _
      unfold cosTerm sinTerm
      change
        Real.sin φ ^ 4 /
              (Real.cos φ ^ 3 + Real.sin φ ^ 3) ^ 2 =
          Real.cos (Real.pi / 2 - φ) ^ 4 /
              (Real.cos (Real.pi / 2 - φ) ^ 3 +
                Real.sin (Real.pi / 2 - φ) ^ 3) ^ 2
      rw [Real.cos_pi_div_two_sub,
        Real.sin_pi_div_two_sub]
      ring
    _ =
        ∫ φ in Real.pi / 2 - Real.pi / 2..
          Real.pi / 2 - 0, cosTerm φ := hsub
    _ =
        ∫ φ in (0 : ℝ)..Real.pi / 2,
          cosTerm φ := by
      ring_nf
    _ = 4 * Real.pi / (9 * Real.sqrt 3) :=
      cosTerm_integral

theorem gap4 (a b h k : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hh : 0 < h) (hk : 0 < k) :
    a * b / 2 *
        (∫ φ in (0 : ℝ)..Real.pi / 2,
          ((a / h) ^ 4 * Real.cos φ ^ 4) /
            (Real.cos φ ^ 3 + Real.sin φ ^ 3) ^ 2) =
      2 * Real.pi * a * b / (9 * Real.sqrt 3) *
        (a / h) ^ 4 := by
  have hint :
      (∫ φ in (0 : ℝ)..Real.pi / 2,
          ((a / h) ^ 4 * Real.cos φ ^ 4) /
            (Real.cos φ ^ 3 + Real.sin φ ^ 3) ^ 2) =
        (a / h) ^ 4 *
          ∫ φ in (0 : ℝ)..Real.pi / 2,
            cosTerm φ := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro φ _
    unfold cosTerm
    ring
  rw [hint, cosTerm_integral]
  ring

theorem gap5 (a b h k : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hh : 0 < h) (hk : 0 < k) :
    a * b / 2 *
        (∫ φ in (0 : ℝ)..Real.pi / 2,
          ((b / k) ^ 4 * Real.sin φ ^ 4) /
            (Real.cos φ ^ 3 + Real.sin φ ^ 3) ^ 2) =
      2 * Real.pi * a * b / (9 * Real.sqrt 3) *
        (b / k) ^ 4 := by
  have hint :
      (∫ φ in (0 : ℝ)..Real.pi / 2,
          ((b / k) ^ 4 * Real.sin φ ^ 4) /
            (Real.cos φ ^ 3 + Real.sin φ ^ 3) ^ 2) =
        (b / k) ^ 4 *
          ∫ φ in (0 : ℝ)..Real.pi / 2,
            sinTerm φ := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro φ _
    unfold sinTerm
    ring
  rw [hint, sinTerm_integral]
  ring

theorem gap6 (a b h k : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hh : 0 < h) (hk : 0 < k) :
    a * b / 2 *
        (∫ φ in (0 : ℝ)..Real.pi / 2,
          (2 * (a / h) ^ 2 * (b / k) ^ 2 *
              Real.cos φ ^ 2 * Real.sin φ ^ 2) /
            (Real.cos φ ^ 3 + Real.sin φ ^ 3) ^ 2) =
      a * b / 3 * (a / h) ^ 2 * (b / k) ^ 2 := by
  have hint :
      (∫ φ in (0 : ℝ)..Real.pi / 2,
          (2 * (a / h) ^ 2 * (b / k) ^ 2 *
              Real.cos φ ^ 2 * Real.sin φ ^ 2) /
            (Real.cos φ ^ 3 + Real.sin φ ^ 3) ^ 2) =
        (a / h) ^ 2 * (b / k) ^ 2 *
          ∫ φ in (0 : ℝ)..Real.pi / 2,
            crossTerm φ := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro φ _
    unfold crossTerm
    ring
  rw [hint, crossTerm_integral]
  ring

private lemma expanded_integral
    (a b h k : ℝ) :
    (∫ φ in (0 : ℝ)..Real.pi / 2,
        ((a / h) ^ 4 * Real.cos φ ^ 4 +
            (b / k) ^ 4 * Real.sin φ ^ 4 +
            2 * (a / h) ^ 2 * (b / k) ^ 2 *
              Real.cos φ ^ 2 * Real.sin φ ^ 2) /
          (Real.cos φ ^ 3 + Real.sin φ ^ 3) ^ 2) =
      (a / h) ^ 4 *
          (∫ φ in (0 : ℝ)..Real.pi / 2, cosTerm φ) +
        (b / k) ^ 4 *
          (∫ φ in (0 : ℝ)..Real.pi / 2, sinTerm φ) +
        (a / h) ^ 2 * (b / k) ^ 2 *
          (∫ φ in (0 : ℝ)..Real.pi / 2, crossTerm φ) := by
  have hc :=
    cosTerm_intervalIntegrable.const_mul ((a / h) ^ 4)
  have hs :=
    sinTerm_intervalIntegrable.const_mul ((b / k) ^ 4)
  have hx :=
    crossTerm_intervalIntegrable.const_mul
      ((a / h) ^ 2 * (b / k) ^ 2)
  calc
    (∫ φ in (0 : ℝ)..Real.pi / 2,
        ((a / h) ^ 4 * Real.cos φ ^ 4 +
            (b / k) ^ 4 * Real.sin φ ^ 4 +
            2 * (a / h) ^ 2 * (b / k) ^ 2 *
              Real.cos φ ^ 2 * Real.sin φ ^ 2) /
          (Real.cos φ ^ 3 + Real.sin φ ^ 3) ^ 2) =
        ∫ φ in (0 : ℝ)..Real.pi / 2,
          (a / h) ^ 4 * cosTerm φ +
            ((b / k) ^ 4 * sinTerm φ +
              (a / h) ^ 2 * (b / k) ^ 2 *
                crossTerm φ) := by
      apply intervalIntegral.integral_congr
      intro φ _
      unfold cosTerm sinTerm crossTerm
      ring
    _ =
        (∫ φ in (0 : ℝ)..Real.pi / 2,
            (a / h) ^ 4 * cosTerm φ) +
          ((∫ φ in (0 : ℝ)..Real.pi / 2,
              (b / k) ^ 4 * sinTerm φ) +
            ∫ φ in (0 : ℝ)..Real.pi / 2,
              (a / h) ^ 2 * (b / k) ^ 2 *
                crossTerm φ) := by
      rw [intervalIntegral.integral_add hc (hs.add hx),
        intervalIntegral.integral_add hs hx]
    _ =
        (a / h) ^ 4 *
            (∫ φ in (0 : ℝ)..Real.pi / 2, cosTerm φ) +
          (b / k) ^ 4 *
            (∫ φ in (0 : ℝ)..Real.pi / 2, sinTerm φ) +
          (a / h) ^ 2 * (b / k) ^ 2 *
            (∫ φ in (0 : ℝ)..Real.pi / 2,
              crossTerm φ) := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]
      ring

theorem gap7 (a b h k : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hh : 0 < h) (hk : 0 < k) :
    regionArea a b h k =
      2 * Real.pi * a * b / (9 * Real.sqrt 3) *
          (a / h) ^ 4 +
        2 * Real.pi * a * b / (9 * Real.sqrt 3) *
          (b / k) ^ 4 +
        a * b / 3 * (a / h) ^ 2 * (b / k) ^ 2 := by
  rw [gap3 a b h k ha hb hh hk,
    expanded_integral,
    cosTerm_integral, sinTerm_integral,
    crossTerm_integral]
  ring

theorem gap9 (a b h k : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hh : 0 < h) (hk : 0 < k) :
    regionArea a b h k =
      a * b / 3 *
        (2 * Real.pi / (3 * Real.sqrt 3) *
            (a ^ 4 / h ^ 4 + b ^ 4 / k ^ 4) +
          a ^ 2 * b ^ 2 / (h ^ 2 * k ^ 2)) := by
  rw [gap7 a b h k ha hb hh hk,
    gap8 a b h k ha hb hh hk]

end

end ProofGap.Exercise3992
