import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3993

noncomputable section

open MeasureTheory
open scoped Interval

def region (a b h k : ℝ) : Set (ℝ × ℝ) :=
  {p |
    0 < p.1 ∧ 0 < p.2 ∧
      (p.1 / a + p.2 / b) ^ 4 ≤
        p.1 ^ 2 / h ^ 2 + p.2 ^ 2 / k ^ 2}

def regionArea (a b h k : ℝ) : ℝ :=
  ∫ _p in region a b h k, (1 : ℝ)

def radialSquaredAB (a b h k φ : ℝ) : ℝ :=
  ((a / h) ^ 2 * Real.cos φ ^ 2 +
      (b / k) ^ 2 * Real.sin φ ^ 2) /
    (Real.cos φ + Real.sin φ) ^ 4

def radialSquaredHK (a b h k φ : ℝ) : ℝ :=
  1 /
    ((h / a) * Real.cos φ + (k / b) * Real.sin φ) ^ 4

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
        (a / h) ^ 2 * p.1 ^ 2 +
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
              p.1 ^ 2 / h ^ 2 +
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

private def scaledPolarDomain (a b h k : ℝ) :
    Set (ℝ × ℝ) :=
  {q |
    0 < q.1 ∧ 0 < q.2 ∧ q.2 < Real.pi / 2 ∧
      q.1 ^ 2 ≤ radialSquaredAB a b h k q.2}

private noncomputable def scaledPolarDensity
    (a b h k : ℝ) (q : ℝ × ℝ) : ℝ :=
  (scaledPolarDomain a b h k).indicator
    (fun p => p.1) q

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
    firstQuadrant_angle_iff q.1 q.2 hr
      ⟨hθl, hθu⟩
  constructor
  · rintro ⟨hx, hy, hineq⟩
    have hang : 0 < q.2 ∧ q.2 < Real.pi / 2 :=
      hangle.1 ⟨hx, hy⟩
    refine ⟨hr, hang.1, hang.2, ?_⟩
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
            ((a / h) ^ 2 * Real.cos q.2 ^ 2 +
              (b / k) ^ 2 * Real.sin q.2 ^ 2) := by
      convert hineq using 1 <;> ring
    have hcancel :
        q.1 ^ 2 *
            (Real.cos q.2 + Real.sin q.2) ^ 4 ≤
          (a / h) ^ 2 * Real.cos q.2 ^ 2 +
            (b / k) ^ 2 * Real.sin q.2 ^ 2 := by
      apply (mul_le_mul_iff_left₀ hr2).mp
      simpa [mul_comm, mul_left_comm, mul_assoc] using hfact
    unfold radialSquaredAB
    exact (le_div_iff₀ hD).2 hcancel
  · rintro ⟨hr', hθ0, hθhalf, hrad⟩
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
    unfold radialSquaredAB at hrad
    have hmul :
        q.1 ^ 2 *
            (Real.cos q.2 + Real.sin q.2) ^ 4 ≤
          (a / h) ^ 2 * Real.cos q.2 ^ 2 +
            (b / k) ^ 2 * Real.sin q.2 ^ 2 :=
      (le_div_iff₀ hD).1 hrad
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
      (measurableSet_lt measurable_const measurable_snd).inter <|
        (measurableSet_lt measurable_snd measurable_const).inter <|
          measurableSet_le
            (show Measurable
              (fun q : ℝ × ℝ => q.1 ^ 2) by
              fun_prop)
            (show Measurable
              (fun q : ℝ × ℝ =>
                radialSquaredAB a b h k q.2) by
              unfold radialSquaredAB
              fun_prop)

private lemma radialSquaredAB_nonneg
    (a b h k θ : ℝ)
    (hθ0 : 0 ≤ θ) (hθhalf : θ ≤ Real.pi / 2) :
    0 ≤ radialSquaredAB a b h k θ := by
  have hc :
      0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [Real.pi_pos, hθ0], hθhalf⟩
  have hs :
      0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi
      hθ0 (by linarith [hθhalf, Real.pi_pos])
  have hsum : 0 < Real.cos θ + Real.sin θ := by
    by_cases hθz : θ = 0
    · subst θ
      norm_num
    · have hspos :
          0 < Real.sin θ :=
        Real.sin_pos_of_pos_of_lt_pi
          (lt_of_le_of_ne hθ0 (Ne.symm hθz))
          (by linarith [hθhalf, Real.pi_pos])
      linarith
  unfold radialSquaredAB
  exact div_nonneg
    (add_nonneg
      (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (mul_nonneg (sq_nonneg _) (sq_nonneg _)))
    (pow_nonneg hsum.le 4)

private lemma radialSquaredAB_le_sum
    (a b h k θ : ℝ)
    (hθ0 : 0 ≤ θ) (hθhalf : θ ≤ Real.pi / 2) :
    radialSquaredAB a b h k θ ≤
      (a / h) ^ 2 + (b / k) ^ 2 := by
  have hc :
      0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [Real.pi_pos, hθ0], hθhalf⟩
  have hs :
      0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi
      hθ0 (by linarith [hθhalf, Real.pi_pos])
  have hsum : 0 < Real.cos θ + Real.sin θ := by
    by_cases hθz : θ = 0
    · subst θ
      norm_num
    · have hspos :
          0 < Real.sin θ :=
        Real.sin_pos_of_pos_of_lt_pi
          (lt_of_le_of_ne hθ0 (Ne.symm hθz))
          (by linarith [hθhalf, Real.pi_pos])
      linarith
  let A : ℝ := (a / h) ^ 2
  let B : ℝ := (b / k) ^ 2
  let N : ℝ :=
    A * Real.cos θ ^ 2 + B * Real.sin θ ^ 2
  let D : ℝ := (Real.cos θ + Real.sin θ) ^ 4
  have hA : 0 ≤ A := sq_nonneg _
  have hB : 0 ≤ B := sq_nonneg _
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
    nlinarith [mul_nonneg hA (sub_nonneg.2 hcSq),
      mul_nonneg hB (sub_nonneg.2 hsSq)]
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
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD1
  have hdiv : N / D ≤ N := by
    apply (div_le_iff₀ hDpos).2
    nlinarith [mul_nonneg hN (sub_nonneg.2 hD1)]
  unfold radialSquaredAB
  change N / D ≤ A + B
  exact hdiv.trans hNle

private lemma scaledPolarDensity_integrable
    (a b h k : ℝ) :
    Integrable (scaledPolarDensity a b h k) := by
  let M : ℝ := (a / h) ^ 2 + (b / k) ^ 2
  have hM : 0 ≤ M :=
    add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hsubset :
      scaledPolarDomain a b h k ⊆
        Set.Icc (0 : ℝ) (Real.sqrt M) ×ˢ
          Set.Icc (0 : ℝ) (Real.pi / 2) := by
    intro q hq
    rcases hq with ⟨hr, hθ0, hθhalf, hrad⟩
    have hRle :
        radialSquaredAB a b h k q.2 ≤ M := by
      dsimp [M]
      exact radialSquaredAB_le_sum
        a b h k q.2 hθ0.le hθhalf.le
    have hrsq : q.1 ^ 2 ≤ M := hrad.trans hRle
    have hsqrtSq : Real.sqrt M ^ 2 = M :=
      Real.sq_sqrt hM
    have hrle : q.1 ≤ Real.sqrt M := by
      nlinarith [Real.sqrt_nonneg M]
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
  if 0 < θ ∧ θ < Real.pi / 2 then
    radialSquaredAB a b h k θ / 2
  else
    0

private lemma scaledPolarDensity_inner
    (a b h k θ : ℝ) :
    (∫ r : ℝ, scaledPolarDensity a b h k (r, θ)) =
      scaledAngularDensity a b h k θ := by
  by_cases hθ : 0 < θ ∧ θ < Real.pi / 2
  · rw [scaledAngularDensity, if_pos hθ]
    have hR :
        0 ≤ radialSquaredAB a b h k θ :=
      radialSquaredAB_nonneg a b h k θ
        hθ.1.le hθ.2.le
    have hfun :
        (fun r : ℝ =>
          scaledPolarDensity a b h k (r, θ)) =
        (Set.Ioc (0 : ℝ)
          (Real.sqrt (radialSquaredAB a b h k θ))).indicator
            (fun r => r) := by
      funext r
      unfold scaledPolarDensity scaledPolarDomain
      by_cases hr :
          0 < r ∧
            r ≤ Real.sqrt (radialSquaredAB a b h k θ)
      · have hrsq :
            r ^ 2 ≤ radialSquaredAB a b h k θ := by
          nlinarith [Real.sq_sqrt hR,
            Real.sqrt_nonneg
              (radialSquaredAB a b h k θ)]
        have hD :
            (r, θ) ∈
              {q |
                0 < q.1 ∧ 0 < q.2 ∧
                  q.2 < Real.pi / 2 ∧
                  q.1 ^ 2 ≤
                    radialSquaredAB a b h k q.2} :=
          ⟨hr.1, hθ.1, hθ.2, hrsq⟩
        have hI :
            r ∈ Set.Ioc (0 : ℝ)
              (Real.sqrt
                (radialSquaredAB a b h k θ)) := hr
        rw [Set.indicator_of_mem hD,
          Set.indicator_of_mem hI]
      · have hD :
            (r, θ) ∉
              {q |
                0 < q.1 ∧ 0 < q.2 ∧
                  q.2 < Real.pi / 2 ∧
                  q.1 ^ 2 ≤
                    radialSquaredAB a b h k q.2} := by
          intro hD
          apply hr
          refine ⟨hD.1, ?_⟩
          apply
            (sq_le_sq₀ hD.1.le
              (Real.sqrt_nonneg
                (radialSquaredAB a b h k θ))).mp
          rw [Real.sq_sqrt hR]
          exact hD.2.2.2
        have hI :
            r ∉ Set.Ioc (0 : ℝ)
              (Real.sqrt
                (radialSquaredAB a b h k θ)) := hr
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
    (a b h k : ℝ) :
    (∫ θ : ℝ, scaledAngularDensity a b h k θ) =
      1 / 2 *
        ∫ θ in (0 : ℝ)..Real.pi / 2,
          radialSquaredAB a b h k θ := by
  have hfun :
      scaledAngularDensity a b h k =
        (Set.Ioo (0 : ℝ) (Real.pi / 2)).indicator
          (fun θ =>
            radialSquaredAB a b h k θ / 2) := by
    funext θ
    by_cases hθ :
        θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)
    · change
        (if 0 < θ ∧ θ < Real.pi / 2 then
            radialSquaredAB a b h k θ / 2
          else 0) =
          (Set.Ioo (0 : ℝ)
            (Real.pi / 2)).indicator
              (fun θ =>
                radialSquaredAB a b h k θ / 2) θ
      rw [if_pos
        (show 0 < θ ∧ θ < Real.pi / 2 from hθ),
        Set.indicator_of_mem hθ]
    · have hcond :
          ¬(0 < θ ∧ θ < Real.pi / 2) := hθ
      rw [scaledAngularDensity, if_neg hcond,
        Set.indicator_of_notMem hθ]
  rw [hfun,
    MeasureTheory.integral_indicator measurableSet_Ioo,
    ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le
      (by linarith [Real.pi_pos])]
  simp only [intervalIntegral.integral_div]
  ring

private lemma scaled_area_polar
    (a b h k : ℝ) :
    (∫ _p in scaledRegion a b h k, (1 : ℝ)) =
      1 / 2 *
        ∫ θ in (0 : ℝ)..Real.pi / 2,
          radialSquaredAB a b h k θ := by
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
          radialSquaredAB a b h k φ := by
  rw [regionArea_eq_scaled a b h k ha hb hh hk,
    scaled_area_polar]
  ring

theorem gap1 (a b h k φ : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hh : 0 < h) (hk : 0 < k) :
    radialSquaredAB a b h k φ =
      ((a / h) ^ 2 * Real.cos φ ^ 2 +
          (b / k) ^ 2 * Real.sin φ ^ 2) /
        (Real.cos φ + Real.sin φ) ^ 4 := by
  rfl

theorem gap3 (φ : ℝ) (hφ0 : 0 ≤ φ)
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

theorem gap4 (t C : ℝ) (ht : t ≠ -1) :
    HasDerivAt
      (fun z : ℝ => -1 / (3 * (1 + z) ^ 3) + C)
      (1 / (1 + t) ^ 4) t := by
  have hbase :
      HasDerivAt (fun z : ℝ => 1 + z) 1 t :=
    by
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
  have h :=
    (((hbase.pow 3).const_mul 3).inv hne).neg.const_add C
  simp only [Pi.pow_apply] at h
  convert h using 1
  · funext z
    simp [div_eq_mul_inv, add_comm, mul_comm]
  · field_simp [h1]
    ring

theorem gap5 (φ C : ℝ) (hφ0 : 0 ≤ φ)
    (hφ1 : φ < Real.pi / 2) :
    HasDerivAt
      (fun θ : ℝ =>
        -1 / (3 * (1 + Real.tan θ) ^ 3) + C)
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
    (gap4 (Real.tan φ) C ht).comp φ
      (Real.hasDerivAt_tan_of_mem_Ioo hmem)
  convert hcomp using 1
  rw [← Real.deriv_tan]
  exact gap3 φ hφ0 hφ1

theorem gap6 (φ C : ℝ) (hφ0 : 0 ≤ φ)
    (hφ1 : φ < Real.pi / 2) :
    HasDerivAt
      (fun θ : ℝ =>
        -1 / (1 + Real.tan θ) +
          1 / (1 + Real.tan θ) ^ 2 -
          1 / (3 * (1 + Real.tan θ) ^ 3) + C)
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
      1 / (3 * (1 + z) ^ 3) + C
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
    have h1 :=
      (hbase.inv ht1).neg
    have h2 :=
      ((hbase.pow 2).inv (pow_ne_zero 2 ht1))
    have h3 :=
      ((((hbase.pow 3).const_mul 3).inv
        (mul_ne_zero (by norm_num)
          (pow_ne_zero 3 ht1))).neg)
    have hsum := ((h1.add h2).add h3).const_add C
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

private noncomputable def totalPrimitive (φ : ℝ) : ℝ :=
  1 / 4 *
    (Real.tan (φ - Real.pi / 4) +
      Real.tan (φ - Real.pi / 4) ^ 3 / 3)

private lemma cos_add_sin_eq_sqrtTwo_mul (φ : ℝ) :
    Real.cos φ + Real.sin φ =
      Real.sqrt 2 * Real.cos (φ - Real.pi / 4) := by
  rw [Real.cos_sub, Real.cos_pi_div_four,
    Real.sin_pi_div_four]
  have hsqrt : Real.sqrt 2 * Real.sqrt 2 = 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    Real.cos φ + Real.sin φ =
        (Real.sqrt 2 * Real.sqrt 2) / 2 *
          (Real.cos φ + Real.sin φ) := by
      rw [hsqrt]
      ring
    _ =
        Real.sqrt 2 *
          (Real.cos φ * (Real.sqrt 2 / 2) +
            Real.sin φ * (Real.sqrt 2 / 2)) := by
      ring

private lemma totalPrimitive_hasDerivAt
    (φ : ℝ) (hφ0 : 0 ≤ φ)
    (hφ1 : φ ≤ Real.pi / 2) :
    HasDerivAt totalPrimitive
      (1 / (Real.cos φ + Real.sin φ) ^ 4) φ := by
  have hu :
      φ - Real.pi / 4 ∈
        Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [Real.pi_pos]
  have ht :=
    (Real.hasDerivAt_tan_of_mem_Ioo hu).comp φ
      ((hasDerivAt_id φ).sub_const (Real.pi / 4))
  have hraw :=
    (ht.add ((ht.pow 3).div_const 3)).const_mul (1 / 4)
  unfold totalPrimitive
  convert hraw using 1
  rw [cos_add_sin_eq_sqrtTwo_mul]
  have hcos : Real.cos (φ - Real.pi / 4) ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo hu).ne'
  have hsqrt : Real.sqrt 2 ≠ 0 :=
    (Real.sqrt_pos.2 (by norm_num)).ne'
  simp only [Function.comp_apply, id_eq, Nat.cast_ofNat,
    Nat.reduceSub]
  have hsqrt4 : Real.sqrt 2 ^ 4 = 4 := by
    nlinarith [Real.sq_sqrt
      (by norm_num : (0 : ℝ) ≤ 2)]
  have htan :
      1 + Real.tan (φ - Real.pi / 4) ^ 2 =
        1 / Real.cos (φ - Real.pi / 4) ^ 2 := by
    calc
      1 + Real.tan (φ - Real.pi / 4) ^ 2 =
          ((1 +
            Real.tan (φ - Real.pi / 4) ^ 2)⁻¹)⁻¹ := by
        rw [inv_inv]
      _ = (Real.cos (φ - Real.pi / 4) ^ 2)⁻¹ := by
        rw [Real.inv_one_add_tan_sq hcos]
      _ = 1 / Real.cos (φ - Real.pi / 4) ^ 2 := by
        rw [one_div]
  rw [mul_pow, hsqrt4]
  rw [show
    (1 / 4 : ℝ) *
        (1 / Real.cos (φ - Real.pi / 4) ^ 2 * 1 +
          3 * Real.tan (φ - Real.pi / 4) ^ 2 *
              (1 / Real.cos (φ - Real.pi / 4) ^ 2 * 1) /
            3) =
      1 / 4 *
        ((1 + Real.tan (φ - Real.pi / 4) ^ 2) *
          (1 / Real.cos (φ - Real.pi / 4) ^ 2)) by ring,
    htan]
  field_simp [hcos]

private lemma total_integral :
    (∫ φ in (0 : ℝ)..Real.pi / 2,
        1 / (Real.cos φ + Real.sin φ) ^ 4) =
      2 / 3 := by
  have hderiv :
      ∀ φ ∈ Set.uIcc (0 : ℝ) (Real.pi / 2),
        HasDerivAt totalPrimitive
          (1 / (Real.cos φ + Real.sin φ) ^ 4) φ := by
    intro φ hφ
    rw [Set.uIcc_of_le
      (by linarith [Real.pi_pos])] at hφ
    exact totalPrimitive_hasDerivAt φ hφ.1 hφ.2
  have hint :
      IntervalIntegrable
        (fun φ : ℝ =>
          1 / (Real.cos φ + Real.sin φ) ^ 4)
        volume 0 (Real.pi / 2) := by
    apply ContinuousOn.intervalIntegrable
    intro φ hφ
    rw [Set.uIcc_of_le
      (by linarith [Real.pi_pos])] at hφ
    have hpos :
        0 < Real.cos φ + Real.sin φ := by
      have hcos := Real.cos_nonneg_of_mem_Icc
        ⟨by linarith [Real.pi_pos, hφ.1], hφ.2⟩
      have hsin := Real.sin_nonneg_of_nonneg_of_le_pi
        hφ.1 (by linarith [Real.pi_pos, hφ.2])
      by_cases hφ0 : φ = 0
      · subst φ
        norm_num
      · have hsinpos : 0 < Real.sin φ :=
          Real.sin_pos_of_pos_of_lt_pi
            (lt_of_le_of_ne hφ.1 (Ne.symm hφ0))
            (by linarith [Real.pi_pos, hφ.2])
        linarith
    apply ContinuousAt.continuousWithinAt
    exact continuousAt_const.div
      (by fun_prop) (pow_ne_zero 4 hpos.ne')
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    hderiv hint]
  unfold totalPrimitive
  rw [show (0 : ℝ) - Real.pi / 4 =
      -(Real.pi / 4) by ring,
    Real.tan_neg, Real.tan_pi_div_four,
    show Real.pi / 2 - Real.pi / 4 =
      Real.pi / 4 by ring,
    Real.tan_pi_div_four]
  ring

private lemma cos_add_sin_pos_on_Icc
    (φ : ℝ) (hφ : φ ∈ Set.Icc (0 : ℝ) (Real.pi / 2)) :
    0 < Real.cos φ + Real.sin φ := by
  have hcos := Real.cos_nonneg_of_mem_Icc
    ⟨by linarith [Real.pi_pos, hφ.1], hφ.2⟩
  have hsin := Real.sin_nonneg_of_nonneg_of_le_pi
    hφ.1 (by linarith [Real.pi_pos, hφ.2])
  by_cases hφ0 : φ = 0
  · subst φ
    norm_num
  · have hsinpos : 0 < Real.sin φ :=
      Real.sin_pos_of_pos_of_lt_pi
        (lt_of_le_of_ne hφ.1 (Ne.symm hφ0))
        (by linarith [Real.pi_pos, hφ.2])
    linarith

private lemma cosRatio_intervalIntegrable :
    IntervalIntegrable
      (fun φ : ℝ =>
        Real.cos φ ^ 2 /
          (Real.cos φ + Real.sin φ) ^ 4)
      volume 0 (Real.pi / 2) := by
  apply ContinuousOn.intervalIntegrable
  intro φ hφ
  rw [Set.uIcc_of_le
    (by linarith [Real.pi_pos])] at hφ
  apply ContinuousAt.continuousWithinAt
  exact
    (Real.continuous_cos.continuousAt.pow 2).div
      ((Real.continuous_cos.continuousAt.add
        Real.continuous_sin.continuousAt).pow 4)
      (pow_ne_zero 4
        (cos_add_sin_pos_on_Icc φ hφ).ne')

private lemma sinRatio_intervalIntegrable :
    IntervalIntegrable
      (fun φ : ℝ =>
        Real.sin φ ^ 2 /
          (Real.cos φ + Real.sin φ) ^ 4)
      volume 0 (Real.pi / 2) := by
  apply ContinuousOn.intervalIntegrable
  intro φ hφ
  rw [Set.uIcc_of_le
    (by linarith [Real.pi_pos])] at hφ
  apply ContinuousAt.continuousWithinAt
  exact
    (Real.continuous_sin.continuousAt.pow 2).div
      ((Real.continuous_cos.continuousAt.add
        Real.continuous_sin.continuousAt).pow 4)
      (pow_ne_zero 4
        (cos_add_sin_pos_on_Icc φ hφ).ne')

private lemma cosRatio_integral :
    (∫ φ in (0 : ℝ)..Real.pi / 2,
        Real.cos φ ^ 2 /
          (Real.cos φ + Real.sin φ) ^ 4) =
      1 / 3 := by
  let fc : ℝ → ℝ := fun φ =>
    Real.cos φ ^ 2 /
      (Real.cos φ + Real.sin φ) ^ 4
  let fs : ℝ → ℝ := fun φ =>
    Real.sin φ ^ 2 /
      (Real.cos φ + Real.sin φ) ^ 4
  have hsym :
      (∫ φ in (0 : ℝ)..Real.pi / 2, fs φ) =
        ∫ φ in (0 : ℝ)..Real.pi / 2, fc φ := by
    have hsub :=
      intervalIntegral.integral_comp_sub_left
        (f := fc) (a := (0 : ℝ))
        (b := Real.pi / 2) (Real.pi / 2)
    calc
      (∫ φ in (0 : ℝ)..Real.pi / 2, fs φ) =
          ∫ φ in (0 : ℝ)..Real.pi / 2,
            fc (Real.pi / 2 - φ) := by
        apply intervalIntegral.integral_congr
        intro φ _
        dsimp [fc, fs]
        rw [Real.cos_pi_div_two_sub,
          Real.sin_pi_div_two_sub]
        ring
      _ = ∫ φ in Real.pi / 2 - Real.pi / 2..
          Real.pi / 2 - 0, fc φ := hsub
      _ = ∫ φ in (0 : ℝ)..Real.pi / 2, fc φ := by
        ring_nf
  have hsum :
      (∫ φ in (0 : ℝ)..Real.pi / 2, fc φ) +
          (∫ φ in (0 : ℝ)..Real.pi / 2, fs φ) =
        2 / 3 := by
    rw [← intervalIntegral.integral_add
      cosRatio_intervalIntegrable
      sinRatio_intervalIntegrable]
    calc
      (∫ φ in (0 : ℝ)..Real.pi / 2,
          fc φ + fs φ) =
          ∫ φ in (0 : ℝ)..Real.pi / 2,
            1 /
              (Real.cos φ + Real.sin φ) ^ 4 := by
        apply intervalIntegral.integral_congr
        intro φ hφ
        rw [Set.uIcc_of_le
          (by linarith [Real.pi_pos])] at hφ
        dsimp [fc, fs]
        have hne :=
          (cos_add_sin_pos_on_Icc φ hφ).ne'
        field_simp [hne]
        nlinarith [Real.sin_sq_add_cos_sq φ]
      _ = 2 / 3 := total_integral
  dsimp [fc, fs] at hsym hsum ⊢
  rw [hsym] at hsum
  linarith

private lemma sinRatio_integral :
    (∫ φ in (0 : ℝ)..Real.pi / 2,
        Real.sin φ ^ 2 /
          (Real.cos φ + Real.sin φ) ^ 4) =
      1 / 3 := by
  have hsub :=
    intervalIntegral.integral_comp_sub_left
      (f := fun φ : ℝ =>
        Real.cos φ ^ 2 /
          (Real.cos φ + Real.sin φ) ^ 4)
      (a := (0 : ℝ)) (b := Real.pi / 2)
      (Real.pi / 2)
  calc
    (∫ φ in (0 : ℝ)..Real.pi / 2,
        Real.sin φ ^ 2 /
          (Real.cos φ + Real.sin φ) ^ 4) =
        ∫ φ in (0 : ℝ)..Real.pi / 2,
          Real.cos (Real.pi / 2 - φ) ^ 2 /
            (Real.cos (Real.pi / 2 - φ) +
              Real.sin (Real.pi / 2 - φ)) ^ 4 := by
      apply intervalIntegral.integral_congr
      intro φ _
      change
        Real.sin φ ^ 2 /
            (Real.cos φ + Real.sin φ) ^ 4 =
          Real.cos (Real.pi / 2 - φ) ^ 2 /
            (Real.cos (Real.pi / 2 - φ) +
              Real.sin (Real.pi / 2 - φ)) ^ 4
      rw [Real.cos_pi_div_two_sub,
        Real.sin_pi_div_two_sub]
      ring
    _ =
        ∫ φ in Real.pi / 2 - Real.pi / 2..
          Real.pi / 2 - 0,
          Real.cos φ ^ 2 /
            (Real.cos φ + Real.sin φ) ^ 4 := hsub
    _ =
        ∫ φ in (0 : ℝ)..Real.pi / 2,
          Real.cos φ ^ 2 /
            (Real.cos φ + Real.sin φ) ^ 4 := by
      ring_nf
    _ = 1 / 3 := cosRatio_integral

theorem gap7 (a b h k : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hh : 0 < h) (hk : 0 < k) :
    regionArea a b h k =
      a * b / 6 *
        (a ^ 2 / h ^ 2 + b ^ 2 / k ^ 2) := by
  rw [gap2 a b h k ha hb hh hk]
  have hrad :
      (∫ φ in (0 : ℝ)..Real.pi / 2,
          radialSquaredAB a b h k φ) =
        (a / h) ^ 2 * (1 / 3) +
          (b / k) ^ 2 * (1 / 3) := by
    calc
      (∫ φ in (0 : ℝ)..Real.pi / 2,
          radialSquaredAB a b h k φ) =
          ∫ φ in (0 : ℝ)..Real.pi / 2,
            (a / h) ^ 2 *
                (Real.cos φ ^ 2 /
                  (Real.cos φ + Real.sin φ) ^ 4) +
              (b / k) ^ 2 *
                (Real.sin φ ^ 2 /
                  (Real.cos φ + Real.sin φ) ^ 4) := by
        apply intervalIntegral.integral_congr
        intro φ _
        unfold radialSquaredAB
        ring
      _ =
          (a / h) ^ 2 *
              (∫ φ in (0 : ℝ)..Real.pi / 2,
                Real.cos φ ^ 2 /
                  (Real.cos φ + Real.sin φ) ^ 4) +
            (b / k) ^ 2 *
              (∫ φ in (0 : ℝ)..Real.pi / 2,
                Real.sin φ ^ 2 /
                  (Real.cos φ + Real.sin φ) ^ 4) := by
        rw [intervalIntegral.integral_add
            (cosRatio_intervalIntegrable.const_mul _)
            (sinRatio_intervalIntegrable.const_mul _),
          intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul]
      _ = (a / h) ^ 2 * (1 / 3) +
          (b / k) ^ 2 * (1 / 3) := by
        rw [cosRatio_integral, sinRatio_integral]
  rw [hrad]
  field_simp [hh.ne', hk.ne']
  ring

theorem gap8 (a b h k φ : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hh : 0 < h) (hk : 0 < k) :
    radialSquaredHK a b h k φ =
      1 /
        ((h / a) * Real.cos φ +
          (k / b) * Real.sin φ) ^ 4 := by
  rfl

theorem gap9 (a b h k : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hh : 0 < h) (hk : 0 < k) :
    regionArea a b h k =
      a * b / 6 *
        (a ^ 2 / h ^ 2 + b ^ 2 / k ^ 2) := by
  exact gap7 a b h k ha hb hh hk


end

end ProofGap.Exercise3993

