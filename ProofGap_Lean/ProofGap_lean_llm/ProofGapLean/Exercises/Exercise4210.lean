import Mathlib.Tactic.Measurability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4210

noncomputable section

open MeasureTheory Set

private abbrev BaseVec (d : ℕ) := Fin (d + 1) → ℝ

private def baseCone (d : ℕ) (a : BaseVec d) : Set (BaseVec d) :=
  {x | 0 ≤ x (Fin.last d) ∧ x (Fin.last d) ≤ a (Fin.last d) ∧
    (∑ i : Fin d,
      x (Fin.castSucc i) ^ 2 / a (Fin.castSucc i) ^ 2) ≤
        x (Fin.last d) ^ 2 / a (Fin.last d) ^ 2}

private def baseConeVolume (d : ℕ) (a : BaseVec d) : ℝ :=
  (MeasureTheory.volume (baseCone d a)).toReal

private def crossSection (d : ℕ) (a : BaseVec d) (z : ℝ) :
    Set (Fin d → ℝ) :=
  {y |
    (∑ i : Fin d, y i ^ 2 / a i.castSucc ^ 2) ≤
      z ^ 2 / a (Fin.last d) ^ 2}

private def splitLast (d : ℕ) :
    BaseVec d ≃ᵐ ℝ × (Fin d → ℝ) :=
  MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (d + 1) => ℝ) (Fin.last d)

private def baseSplitRegion (d : ℕ) (a : BaseVec d) :
    Set (ℝ × (Fin d → ℝ)) :=
  {p |
    p.1 ∈ Set.Icc 0 (a (Fin.last d)) ∧
    p.2 ∈ crossSection d a p.1}

private theorem splitLast_apply (d : ℕ) (x : BaseVec d) :
    splitLast d x =
      (x (Fin.last d), fun i : Fin d => x i.castSucc) := by
  simp [splitLast, MeasurableEquiv.piFinSuccAbove_apply]
  funext i
  rfl

private theorem coneRegion_preimage (d : ℕ) (a : BaseVec d) :
    splitLast d ⁻¹' baseSplitRegion d a = baseCone d a := by
  ext x
  simp only [Set.mem_preimage, baseSplitRegion, Set.mem_setOf_eq,
    Set.mem_Icc, crossSection, baseCone, splitLast_apply]
  tauto

private theorem splitLast_measurePreserving (d : ℕ) :
    MeasurePreserving (splitLast d)
      (volume : Measure (BaseVec d))
      ((volume : Measure ℝ).prod
        (volume : Measure (Fin d → ℝ))) := by
  exact volume_preserving_piFinSuccAbove
    (fun _ : Fin (d + 1) => ℝ) (Fin.last d)

private def ballFin (d : ℕ) (r : ℝ) :
    Set (Fin d → ℝ) :=
  {u | ∑ i, u i ^ 2 ≤ r ^ 2}

private def normalizeMatrix (d : ℕ) (a : BaseVec d) :
    Matrix (Fin d) (Fin d) ℝ :=
  Matrix.diagonal fun i => (a i.castSucc)⁻¹

private def normalize (d : ℕ) (a : BaseVec d) :
    (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ) :=
  Matrix.toLin' (normalizeMatrix d a)

private theorem normalize_apply (d : ℕ) (a : BaseVec d)
    (y : Fin d → ℝ) (i : Fin d) :
    normalize d a y i = y i / a i.castSucc := by
  simp [normalize, normalizeMatrix, Matrix.toLin'_apply,
    Matrix.mulVec_diagonal, div_eq_mul_inv, mul_comm]

private theorem normalize_det (d : ℕ) (a : BaseVec d) :
    LinearMap.det (normalize d a) =
      ∏ i : Fin d, (a i.castSucc)⁻¹ := by
  rw [normalize, LinearMap.det_toLin', normalizeMatrix,
    Matrix.det_diagonal]

private theorem crossSection_preimage_ball
    (d : ℕ) (a : BaseVec d) (z : ℝ) :
    crossSection d a z =
      normalize d a ⁻¹'
        ballFin d (z / a (Fin.last d)) := by
  ext y
  simp only [crossSection, ballFin, Set.mem_setOf_eq,
    Set.mem_preimage]
  simp_rw [normalize_apply, div_pow]

private theorem ballFin_volume_real
    (d : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    (volume (ballFin d r)).toReal =
      r ^ d *
        (Real.rpow Real.pi ((d : ℝ) / 2) /
          Real.Gamma (((d : ℝ) + 2) / 2)) := by
  by_cases hd : d = 0
  · subst d
    letI : ∀ i : Fin 0, IsProbabilityMeasure
        (volume : Measure ℝ) := fun i => Fin.elim0 i
    letI : IsProbabilityMeasure
        (volume : Measure (Fin 0 → ℝ)) := inferInstance
    have hball : ballFin 0 r = Set.univ := by
      ext u
      simp [ballFin, sq_nonneg r]
    rw [hball]
    simp
  · haveI : Nonempty (Fin d) :=
      Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hd)
    have hball :
        ballFin d r =
          (@WithLp.toLp 2 (Fin d → ℝ)) ⁻¹'
            Metric.closedBall
              (0 : EuclideanSpace ℝ (Fin d)) r := by
      ext u
      simp only [ballFin, Set.mem_setOf_eq, Set.mem_preimage,
        Metric.mem_closedBall, dist_zero_right]
      rw [← sq_le_sq₀
        (norm_nonneg (@WithLp.toLp 2 (Fin d → ℝ) u)) hr]
      rw [EuclideanSpace.real_norm_sq_eq]
    rw [hball]
    rw [(PiLp.volume_preserving_toLp (Fin d)).measure_preimage
      measurableSet_closedBall.nullMeasurableSet]
    rw [EuclideanSpace.volume_closedBall]
    simp only [Fintype.card_fin, ENNReal.toReal_mul,
      ENNReal.toReal_pow, ENNReal.toReal_ofReal hr]
    have hgamma :
        0 ≤ Real.sqrt Real.pi ^ d /
          Real.Gamma ((d : ℝ) / 2 + 1) := by
      positivity
    rw [ENNReal.toReal_ofReal hgamma]
    have hpi :
        Real.sqrt Real.pi ^ d =
          Real.rpow Real.pi ((d : ℝ) / 2) := by
      have h :=
        Real.rpow_div_two_eq_sqrt (d : ℝ) Real.pi_nonneg
      rw [Real.rpow_natCast] at h
      exact h.symm
    rw [hpi]
    rw [show (d : ℝ) / 2 + 1 =
      ((d : ℝ) + 2) / 2 by ring]

private theorem crossSection_volume_real
    (d : ℕ) (a : BaseVec d)
    (ha : ∀ i, 0 < a i) (z : ℝ) (hz : 0 ≤ z) :
    (volume (crossSection d a z)).toReal =
      (∏ i : Fin d, a i.castSucc) *
        (z / a (Fin.last d)) ^ d *
        (Real.rpow Real.pi ((d : ℝ) / 2) /
          Real.Gamma (((d : ℝ) + 2) / 2)) := by
  have hdet :
      LinearMap.det (normalize d a) ≠ 0 := by
    rw [normalize_det]
    exact Finset.prod_ne_zero_iff.mpr fun i _ =>
      inv_ne_zero (ne_of_gt (ha i.castSucc))
  have hr : 0 ≤ z / a (Fin.last d) :=
    div_nonneg hz (ha (Fin.last d)).le
  rw [crossSection_preimage_ball]
  rw [Measure.addHaar_preimage_linearMap volume hdet]
  rw [ENNReal.toReal_mul]
  rw [ballFin_volume_real d _ hr]
  have hdet_value :
      |(LinearMap.det (normalize d a))⁻¹| =
        ∏ i : Fin d, a i.castSucc := by
    rw [normalize_det, Finset.prod_inv_distrib, inv_inv]
    rw [abs_of_pos]
    exact Finset.prod_pos fun i _ => ha i.castSucc
  rw [hdet_value, ENNReal.toReal_ofReal
    (Finset.prod_nonneg fun i _ => (ha i.castSucc).le)]
  ring

private theorem measurableSet_crossSection
    (d : ℕ) (a : BaseVec d) (z : ℝ) :
    MeasurableSet (crossSection d a z) := by
  unfold crossSection
  measurability

private theorem isClosed_coneRegion
    (d : ℕ) (a : BaseVec d) :
    IsClosed (baseSplitRegion d a) := by
  have hsum :
      Continuous
        (fun p : ℝ × (Fin d → ℝ) =>
          ∑ i : Fin d,
            p.2 i ^ 2 / a i.castSucc ^ 2) := by
    apply continuous_finset_sum Finset.univ
    intro i _
    have hi :
        Continuous
          (fun p : ℝ × (Fin d → ℝ) => p.2 i) :=
      (continuous_apply i).comp continuous_snd
    exact (hi.pow 2).div_const (a i.castSucc ^ 2)
  have hheight :
      Continuous
        (fun p : ℝ × (Fin d → ℝ) =>
          p.1 ^ 2 / a (Fin.last d) ^ 2) :=
    (continuous_fst.pow 2).div_const
      (a (Fin.last d) ^ 2)
  have hzero :
      IsClosed {p : ℝ × (Fin d → ℝ) | 0 ≤ p.1} :=
    isClosed_le continuous_const continuous_fst
  have htop :
      IsClosed
        {p : ℝ × (Fin d → ℝ) |
          p.1 ≤ a (Fin.last d)} :=
    isClosed_le continuous_fst continuous_const
  have hcross :
      IsClosed
        {p : ℝ × (Fin d → ℝ) |
          (∑ i : Fin d,
            p.2 i ^ 2 / a i.castSucc ^ 2) ≤
              p.1 ^ 2 / a (Fin.last d) ^ 2} :=
    isClosed_le hsum hheight
  change IsClosed
    ({p : ℝ × (Fin d → ℝ) | 0 ≤ p.1} ∩
      {p | p.1 ≤ a (Fin.last d)} ∩
      {p |
        (∑ i : Fin d,
          p.2 i ^ 2 / a i.castSucc ^ 2) ≤
            p.1 ^ 2 / a (Fin.last d) ^ 2})
  exact (hzero.inter htop).inter hcross

private theorem coneRegion_isCompact
    (d : ℕ) (a : BaseVec d) (ha : ∀ i, 0 < a i) :
    IsCompact (baseSplitRegion d a) := by
  let lower : Fin d → ℝ := fun i => -a i.castSucc
  let upper : Fin d → ℝ := fun i => a i.castSucc
  let box : Set (ℝ × (Fin d → ℝ)) :=
    Set.Icc (0 : ℝ) (a (Fin.last d)) ×ˢ
      Set.Icc lower upper
  have hbox : IsCompact box :=
    isCompact_Icc.prod isCompact_Icc
  apply IsCompact.of_isClosed_subset hbox
    (isClosed_coneRegion d a)
  intro p hp
  rcases hp with ⟨hz, hcross⟩
  refine ⟨hz, ?_⟩
  constructor
  · intro i
    have hterm :
        p.2 i ^ 2 / a i.castSucc ^ 2 ≤
          ∑ j : Fin d,
            p.2 j ^ 2 / a j.castSucc ^ 2 := by
      calc
        p.2 i ^ 2 / a i.castSucc ^ 2 =
            ∑ j ∈ ({i} : Finset (Fin d)),
              p.2 j ^ 2 / a j.castSucc ^ 2 := by simp
        _ ≤ ∑ j ∈ Finset.univ,
              p.2 j ^ 2 / a j.castSucc ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (by simp)
            (fun j _ _ =>
              div_nonneg (sq_nonneg _) (sq_nonneg _))
    have hzsq :
        p.1 ^ 2 ≤ a (Fin.last d) ^ 2 := by
      nlinarith [hz.1, hz.2, ha (Fin.last d)]
    have hratio :
        p.1 ^ 2 / a (Fin.last d) ^ 2 ≤ 1 :=
      (div_le_one (sq_pos_of_pos (ha (Fin.last d)))).2 hzsq
    have hi :
        p.2 i ^ 2 / a i.castSucc ^ 2 ≤ 1 :=
      hterm.trans (hcross.trans hratio)
    have hisq :
        p.2 i ^ 2 ≤ a i.castSucc ^ 2 :=
      (div_le_one (sq_pos_of_pos (ha i.castSucc))).mp hi
    change -a i.castSucc ≤ p.2 i
    nlinarith [ha i.castSucc]
  · intro i
    have hterm :
        p.2 i ^ 2 / a i.castSucc ^ 2 ≤
          ∑ j : Fin d,
            p.2 j ^ 2 / a j.castSucc ^ 2 := by
      calc
        p.2 i ^ 2 / a i.castSucc ^ 2 =
            ∑ j ∈ ({i} : Finset (Fin d)),
              p.2 j ^ 2 / a j.castSucc ^ 2 := by simp
        _ ≤ ∑ j ∈ Finset.univ,
              p.2 j ^ 2 / a j.castSucc ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (by simp)
            (fun j _ _ =>
              div_nonneg (sq_nonneg _) (sq_nonneg _))
    have hzsq :
        p.1 ^ 2 ≤ a (Fin.last d) ^ 2 := by
      nlinarith [hz.1, hz.2, ha (Fin.last d)]
    have hratio :
        p.1 ^ 2 / a (Fin.last d) ^ 2 ≤ 1 :=
      (div_le_one (sq_pos_of_pos (ha (Fin.last d)))).2 hzsq
    have hi :
        p.2 i ^ 2 / a i.castSucc ^ 2 ≤ 1 :=
      hterm.trans (hcross.trans hratio)
    have hisq :
        p.2 i ^ 2 ≤ a i.castSucc ^ 2 :=
      (div_le_one (sq_pos_of_pos (ha i.castSucc))).mp hi
    change p.2 i ≤ a i.castSucc
    nlinarith [ha i.castSucc]

private theorem coneVolume_eq_region_integral_one
    (d : ℕ) (a : BaseVec d) :
    baseConeVolume d a =
      ∫ p in baseSplitRegion d a, (1 : ℝ) := by
  have hchange :=
    (splitLast_measurePreserving d).setIntegral_preimage_emb
      (splitLast d).measurableEmbedding
      (fun _ : ℝ × (Fin d → ℝ) => (1 : ℝ))
      (baseSplitRegion d a)
  rw [coneRegion_preimage] at hchange
  change
    (volume (baseCone d a)).toReal =
      ∫ p in baseSplitRegion d a, (1 : ℝ)
  calc
    (volume (baseCone d a)).toReal =
        ∫ x in baseCone d a, (1 : ℝ) := by
      simp [MeasureTheory.integral_const, measureReal_def]
    _ = ∫ p in baseSplitRegion d a, (1 : ℝ) := hchange

private theorem coneRegion_integral_one
    (d : ℕ) (a : BaseVec d) (ha : ∀ i, 0 < a i) :
    (∫ p in baseSplitRegion d a, (1 : ℝ)) =
      ∫ z in (0 : ℝ)..a (Fin.last d),
        (volume (crossSection d a z)).toReal := by
  have hregion :
      MeasurableSet (baseSplitRegion d a) :=
    (isClosed_coneRegion d a).measurableSet
  have hint :
      IntegrableOn (fun _ : ℝ × (Fin d → ℝ) => (1 : ℝ))
        (baseSplitRegion d a) :=
    continuous_const.continuousOn.integrableOn_compact
      (coneRegion_isCompact d a ha)
  have hindicator :
      Integrable
        ((baseSplitRegion d a).indicator
          (fun _ : ℝ × (Fin d → ℝ) => (1 : ℝ)))
        ((volume : Measure ℝ).prod
          (volume : Measure (Fin d → ℝ))) :=
    (integrable_indicator_iff hregion).mpr hint
  have hinner (z : ℝ) :
      (∫ y : Fin d → ℝ,
        (baseSplitRegion d a).indicator
          (fun _ => (1 : ℝ)) (z, y)) =
        (Set.Icc 0 (a (Fin.last d))).indicator
          (fun w =>
            (volume (crossSection d a w)).toReal) z := by
    by_cases hz : z ∈ Set.Icc (0 : ℝ) (a (Fin.last d))
    · rw [Set.indicator_of_mem hz]
      have hfun :
          (fun y : Fin d → ℝ =>
            (baseSplitRegion d a).indicator
              (fun _ => (1 : ℝ)) (z, y)) =
            (crossSection d a z).indicator
              (fun _ => (1 : ℝ)) := by
        funext y
        by_cases hy : y ∈ crossSection d a z
        · simp [baseSplitRegion, hz.1, hz.2, hy]
        · simp [baseSplitRegion, hz.1, hz.2, hy]
      rw [hfun]
      rw [MeasureTheory.integral_indicator
        (measurableSet_crossSection d a z)]
      simp [MeasureTheory.integral_const, measureReal_def]
    · rw [Set.indicator_of_notMem hz]
      have hzero :
          (fun y : Fin d → ℝ =>
            (baseSplitRegion d a).indicator
              (fun _ => (1 : ℝ)) (z, y)) = 0 := by
        funext y
        apply Set.indicator_of_notMem
        intro hmem
        exact hz hmem.1
      rw [hzero]
      simp
  calc
    (∫ p in baseSplitRegion d a, (1 : ℝ)) =
        ∫ p : ℝ × (Fin d → ℝ),
          (baseSplitRegion d a).indicator
            (fun _ => (1 : ℝ)) p := by
      rw [MeasureTheory.integral_indicator hregion]
    _ = ∫ z : ℝ,
        ∫ y : Fin d → ℝ,
          (baseSplitRegion d a).indicator
            (fun _ => (1 : ℝ)) (z, y) := by
      exact MeasureTheory.integral_prod _ hindicator
    _ = ∫ z : ℝ,
        (Set.Icc 0 (a (Fin.last d))).indicator
          (fun w =>
            (volume (crossSection d a w)).toReal) z := by
      exact integral_congr_ae
        (Filter.Eventually.of_forall hinner)
    _ = ∫ z in Set.Icc (0 : ℝ) (a (Fin.last d)),
        (volume (crossSection d a z)).toReal := by
      rw [MeasureTheory.integral_indicator measurableSet_Icc]
    _ = ∫ z in (0 : ℝ)..a (Fin.last d),
        (volume (crossSection d a z)).toReal := by
      symm
      simp only [intervalIntegral.integral_of_le
          (ha (Fin.last d)).le,
        setIntegral_congr_set
          (Ioc_ae_eq_Icc (α := ℝ) (μ := volume))]

private theorem integral_div_pow
    (d : ℕ) (A : ℝ) (hA : 0 < A) :
    (∫ z in (0 : ℝ)..A, (z / A) ^ d) =
      A / (d + 1 : ℕ) := by
  simp_rw [div_pow]
  rw [intervalIntegral.integral_div]
  rw [integral_pow]
  simp
  have hA0 : A ≠ 0 := ne_of_gt hA
  have hd1 : ((d + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp [hA0, hd1]
  ring

private theorem coneVolume_closedForm
    (d : ℕ) (a : BaseVec d) (ha : ∀ i, 0 < a i) :
    baseConeVolume d a =
      (∏ i : Fin d, a i.castSucc) *
        (a (Fin.last d) / (d + 1 : ℕ)) *
        (Real.rpow Real.pi ((d : ℝ) / 2) /
          Real.Gamma (((d : ℝ) + 2) / 2)) := by
  rw [coneVolume_eq_region_integral_one]
  rw [coneRegion_integral_one d a ha]
  calc
    (∫ z in (0 : ℝ)..a (Fin.last d),
        (volume (crossSection d a z)).toReal) =
        ∫ z in (0 : ℝ)..a (Fin.last d),
          (∏ i : Fin d, a i.castSucc) *
            (z / a (Fin.last d)) ^ d *
            (Real.rpow Real.pi ((d : ℝ) / 2) /
              Real.Gamma (((d : ℝ) + 2) / 2)) := by
      apply intervalIntegral.integral_congr
      intro z hz
      have hz0 : 0 ≤ z := by
        have hmem :
            z ∈ Set.Icc (0 : ℝ) (a (Fin.last d)) := by
          simpa [Set.uIcc_of_le
            (ha (Fin.last d)).le] using hz
        exact hmem.1
      change
        (volume (crossSection d a z)).toReal =
          (∏ i : Fin d, a i.castSucc) *
            (z / a (Fin.last d)) ^ d *
            (Real.rpow Real.pi ((d : ℝ) / 2) /
              Real.Gamma (((d : ℝ) + 2) / 2))
      rw [crossSection_volume_real d a ha z hz0]
    _ = (∏ i : Fin d, a i.castSucc) *
        (∫ z in (0 : ℝ)..a (Fin.last d),
          (z / a (Fin.last d)) ^ d) *
        (Real.rpow Real.pi ((d : ℝ) / 2) /
          Real.Gamma (((d : ℝ) + 2) / 2)) := by
      rw [intervalIntegral.integral_mul_const]
      rw [intervalIntegral.integral_const_mul]
    _ = (∏ i : Fin d, a i.castSucc) *
        (a (Fin.last d) / (d + 1 : ℕ)) *
        (Real.rpow Real.pi ((d : ℝ) / 2) /
          Real.Gamma (((d : ℝ) + 2) / 2)) := by
      rw [integral_div_pow d _ (ha (Fin.last d))]

/-! Exercise 4210. -/

private theorem baseConeFormula
    (d : ℕ) (hd : 0 < d) (a : BaseVec d)
    (ha : ∀ i, 0 < a i) :
    baseConeVolume d a =
      Real.rpow Real.pi ((d : ℝ) / 2) /
          ((d + 1 : ℕ) *
            Real.Gamma (((d : ℝ) + 2) / 2)) *
        (∏ i, a i) := by
  rw [coneVolume_closedForm d a ha]
  rw [Fin.prod_univ_castSucc]
  have hd1 : (((d + 1 : ℕ) : ℕ) : ℝ) ≠ 0 := by
    positivity
  have harg : 0 < ((d : ℝ) + 2) / 2 := by
    positivity
  have hgamma :
      Real.Gamma (((d : ℝ) + 2) / 2) ≠ 0 :=
    ne_of_gt (Real.Gamma_pos_of_pos harg)
  field_simp [hd1, hgamma]

def normalizedCone (d : ℕ) : Set (Fin (d + 1) → ℝ) :=
  {u |
    0 ≤ u (Fin.last d) ∧
      u (Fin.last d) ≤ 1 ∧
      (∑ i : Fin d, (u i.castSucc) ^ 2) ≤ (u (Fin.last d)) ^ 2}

def coneRegion
    (d : ℕ) (a : Fin (d + 1) → ℝ) :
    Set (Fin (d + 1) → ℝ) :=
  {x |
    0 ≤ x (Fin.last d) ∧
      x (Fin.last d) ≤ a (Fin.last d) ∧
      (∑ i : Fin d,
        (x i.castSucc / a i.castSucc) ^ 2) ≤
        (x (Fin.last d) / a (Fin.last d)) ^ 2}

def scaleMap
    {d : ℕ} (a : Fin (d + 1) → ℝ)
    (u : Fin (d + 1) → ℝ) : Fin (d + 1) → ℝ :=
  fun i => a i * u i

def coneVolume
    (d : ℕ) (a : Fin (d + 1) → ℝ) : ℝ :=
  ∫ _x in coneRegion d a, (1 : ℝ)

def normalizedConeVolume (d : ℕ) : ℝ :=
  ∫ _u in normalizedCone d, (1 : ℝ)

def angularSineChain (d : ℕ) : ℝ :=
  ∏ q ∈ Finset.range (d - 2),
    ∫ φ in (0 : ℝ)..Real.pi, (Real.sin φ) ^ (q + 1)

def betaValue (x y : ℝ) : ℝ :=
  Real.Gamma x * Real.Gamma y / Real.Gamma (x + y)

def angularBetaChain (d : ℕ) : ℝ :=
  ∏ q ∈ Finset.range (d - 2),
    betaValue (((q : ℝ) + 2) / 2) (1 / 2)

theorem gap1
    (d : ℕ) (a : Fin (d + 1) → ℝ) (ha : ∀ i, 0 < a i) :
    coneRegion d a = scaleMap a '' normalizedCone d := by
  ext x
  constructor
  · intro hx
    refine ⟨fun i => x i / a i, ?_, ?_⟩
    · unfold normalizedCone
      exact
        ⟨div_nonneg hx.1 (ha (Fin.last d)).le,
          (div_le_one (ha (Fin.last d))).2 hx.2.1,
          hx.2.2⟩
    · funext i
      unfold scaleMap
      field_simp [(ha i).ne']
  · rintro ⟨u, hu, rfl⟩
    unfold coneRegion normalizedCone scaleMap at *
    refine ⟨mul_nonneg (ha (Fin.last d)).le hu.1,
      ?_, ?_⟩
    · nlinarith [ha (Fin.last d), hu.2.1]
    · simpa [ne_of_gt (ha _)] using hu.2.2

theorem gap2
    (d : ℕ) (a : Fin (d + 1) → ℝ) (ha : ∀ i, 0 < a i) :
    |(Matrix.diagonal a).det| = ∏ i, a i := by
  rw [Matrix.det_diagonal, abs_of_pos]
  exact Finset.prod_pos fun i _ => ha i

private theorem coneRegion_eq_baseCone
    (d : ℕ) (a : Fin (d + 1) → ℝ) :
    coneRegion d a = baseCone d a := by
  ext x
  simp only [coneRegion, baseCone, Set.mem_setOf_eq]
  simp_rw [div_pow]

private theorem coneVolume_eq_base
    (d : ℕ) (a : Fin (d + 1) → ℝ) :
    coneVolume d a = baseConeVolume d a := by
  rw [coneVolume, coneRegion_eq_baseCone]
  simp [baseConeVolume, MeasureTheory.integral_const,
    measureReal_def]

private theorem publicCone_formula
    (d : ℕ) (hd : 0 < d)
    (a : Fin (d + 1) → ℝ) (ha : ∀ i, 0 < a i) :
    coneVolume d a =
      Real.rpow Real.pi ((d : ℝ) / 2) /
          ((d + 1 : ℕ) *
            Real.Gamma (((d : ℝ) + 2) / 2)) *
        (∏ i, a i) := by
  rw [coneVolume_eq_base]
  exact baseConeFormula d hd a ha

private theorem normalizedCone_as_region (d : ℕ) :
    normalizedCone d =
      coneRegion d (fun _ : Fin (d + 1) => (1 : ℝ)) := by
  ext u
  simp [normalizedCone, coneRegion]

private theorem normalizedCone_formula
    (d : ℕ) (hd : 0 < d) :
    normalizedConeVolume d =
      Real.rpow Real.pi ((d : ℝ) / 2) /
        ((d + 1 : ℕ) *
          Real.Gamma (((d : ℝ) + 2) / 2)) := by
  unfold normalizedConeVolume
  rw [normalizedCone_as_region]
  change coneVolume d (fun _ : Fin (d + 1) => (1 : ℝ)) = _
  rw [publicCone_formula d hd
    (fun _ : Fin (d + 1) => (1 : ℝ))
    (by intro i; norm_num)]
  simp

theorem gap3
    (d : ℕ) (a : Fin (d + 1) → ℝ) (ha : ∀ i, 0 < a i) :
    coneVolume d a = (∏ i, a i) * normalizedConeVolume d := by
  rw [coneVolume_eq_base, coneVolume_closedForm d a ha]
  unfold normalizedConeVolume
  rw [normalizedCone_as_region]
  change
    (∏ i : Fin d, a i.castSucc) *
          (a (Fin.last d) / (d + 1 : ℕ)) *
          (Real.rpow Real.pi ((d : ℝ) / 2) /
            Real.Gamma (((d : ℝ) + 2) / 2)) =
      (∏ i, a i) *
        coneVolume d (fun _ : Fin (d + 1) => (1 : ℝ))
  rw [coneVolume_eq_base,
    coneVolume_closedForm d
      (fun _ : Fin (d + 1) => (1 : ℝ))
      (by intro i; norm_num)]
  simp
  rw [Fin.prod_univ_castSucc]
  ring

private theorem betaValue_two_step (q : ℕ) :
    betaValue ((((q + 2 : ℕ) : ℝ) + 2) / 2) (1 / 2) =
      ((q : ℝ) + 2) / ((q : ℝ) + 3) *
        betaValue (((q : ℝ) + 2) / 2) (1 / 2) := by
  have hx : ((q : ℝ) + 2) / 2 ≠ 0 := by positivity
  have hd : ((q : ℝ) + 3) / 2 ≠ 0 := by positivity
  have hg :
      Real.Gamma (((q : ℝ) + 3) / 2) ≠ 0 := by
    exact (Real.Gamma_pos_of_pos (by positivity)).ne'
  unfold betaValue
  rw [show ((((q + 2 : ℕ) : ℝ) + 2) / 2) =
      ((q : ℝ) + 2) / 2 + 1 by push_cast; ring]
  rw [Real.Gamma_add_one hx]
  rw [show ((q : ℝ) + 2) / 2 + 1 + 1 / 2 =
      ((q : ℝ) + 3) / 2 + 1 by ring]
  rw [Real.Gamma_add_one hd]
  field_simp [hg]
  <;> ring

private theorem sineIntegral_eq_beta (q : ℕ) :
    (∫ φ in (0 : ℝ)..Real.pi,
      (Real.sin φ) ^ (q + 1)) =
      betaValue (((q : ℝ) + 2) / 2) (1 / 2) := by
  induction q using Nat.twoStepInduction with
  | zero =>
      unfold betaValue
      norm_num
      rw [Real.Gamma_one_half_eq]
      rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by ring,
        Real.Gamma_add_one
          (by norm_num : (1 / 2 : ℝ) ≠ 0)]
      norm_num
      rw [Real.Gamma_one_half_eq]
      have hsqrt : Real.sqrt Real.pi ≠ 0 := by positivity
      field_simp
  | one =>
      unfold betaValue
      have hi :
          (∫ φ in (0 : ℝ)..Real.pi,
            (Real.sin φ) ^ 2) =
              Real.pi / 2 := by
        rw [integral_sin_sq]
        simp
      rw [hi]
      norm_num [Real.Gamma_one, Real.Gamma_one_half_eq]
      rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by ring,
        Real.Gamma_add_one
          (by norm_num : (1 / 2 : ℝ) ≠ 0),
        Real.Gamma_one_half_eq]
      nlinarith [Real.sq_sqrt Real.pi_pos.le]
  | more q ih _ =>
      calc
        (∫ φ in (0 : ℝ)..Real.pi,
            (Real.sin φ) ^ (q + 2 + 1)) =
            ((q : ℝ) + 2) / ((q : ℝ) + 3) *
              ∫ φ in (0 : ℝ)..Real.pi,
                (Real.sin φ) ^ (q + 1) := by
          rw [show q + 2 + 1 = (q + 1) + 2 by omega,
            integral_sin_pow]
          have hne : q + 1 + 1 ≠ 0 := by omega
          simp only [Real.sin_zero, Real.sin_pi,
            zero_pow hne, zero_mul, sub_self, zero_div,
            zero_add]
          push_cast
          ring
        _ =
            ((q : ℝ) + 2) / ((q : ℝ) + 3) *
              betaValue (((q : ℝ) + 2) / 2) (1 / 2) := by
          rw [ih]
        _ =
            betaValue ((((q + 2 : ℕ) : ℝ) + 2) / 2)
              (1 / 2) := (betaValue_two_step q).symm

private theorem betaChain_range_formula (m : ℕ) :
    (∏ q ∈ Finset.range m,
      betaValue (((q : ℝ) + 2) / 2) (1 / 2)) =
      Real.rpow Real.pi ((m : ℝ) / 2) /
        Real.Gamma (((m : ℝ) + 2) / 2) := by
  induction m with
  | zero =>
      simp [Real.Gamma_one]
  | succ m ih =>
      rw [Finset.prod_range_succ, ih]
      unfold betaValue
      rw [Real.Gamma_one_half_eq, Real.sqrt_eq_rpow]
      have hg :
          Real.Gamma (((m : ℝ) + 2) / 2) ≠ 0 := by
        exact (Real.Gamma_pos_of_pos (by positivity)).ne'
      have hgd :
          Real.Gamma (((m : ℝ) + 3) / 2) ≠ 0 := by
        exact (Real.Gamma_pos_of_pos (by positivity)).ne'
      have harg :
          ((m : ℝ) + 2) / 2 + 1 / 2 =
            ((m : ℝ) + 3) / 2 := by ring
      have hcast :
          (((m + 1 : ℕ) : ℝ) + 2) / 2 =
            ((m : ℝ) + 3) / 2 := by
        push_cast
        ring
      rw [harg, hcast]
      rw [show ((m + 1 : ℕ) : ℝ) / 2 =
        (m : ℝ) / 2 + 1 / 2 by push_cast; ring]
      rw [← Real.rpow_eq_pow]
      have hpow :
          Real.rpow Real.pi ((m : ℝ) / 2 + 1 / 2) =
            Real.rpow Real.pi ((m : ℝ) / 2) *
              Real.rpow Real.pi (1 / 2) := by
        simpa only [Real.rpow_eq_pow] using
          (Real.rpow_add Real.pi_pos
            ((m : ℝ) / 2) (1 / 2))
      rw [hpow]
      field_simp [hg, hgd]
      <;> ring

private theorem angularSine_eq_beta (d : ℕ) :
    angularSineChain d = angularBetaChain d := by
  unfold angularSineChain angularBetaChain
  apply Finset.prod_congr rfl
  intro q hq
  exact sineIntegral_eq_beta q

private theorem angularBeta_formula (d : ℕ) (hd : 2 ≤ d) :
    angularBetaChain d =
      Real.rpow Real.pi (((d : ℝ) - 2) / 2) /
        Real.Gamma ((d : ℝ) / 2) := by
  unfold angularBetaChain
  rw [betaChain_range_formula (d - 2)]
  have hcast :
      ((d - 2 : ℕ) : ℝ) = (d : ℝ) - 2 := by
    exact Nat.cast_sub hd
  rw [hcast]
  congr 2
  ring

private theorem angularSine_formula (d : ℕ) (hd : 2 ≤ d) :
    angularSineChain d =
      Real.rpow Real.pi (((d : ℝ) - 2) / 2) /
        Real.Gamma ((d : ℝ) / 2) := by
  rw [angularSine_eq_beta, angularBeta_formula d hd]

theorem gap4 (d : ℕ) (hd : 2 ≤ d) :
    normalizedConeVolume d =
      2 * Real.pi / ((d : ℝ) * ((d : ℝ) + 1)) *
        angularSineChain d := by
  rw [normalizedCone_formula d (by omega),
    angularSine_formula d hd]
  have hdpos : 0 < (d : ℝ) := by positivity
  have hdne : (d : ℝ) ≠ 0 := hdpos.ne'
  have hd1ne : (d : ℝ) + 1 ≠ 0 := by positivity
  have hg :
      Real.Gamma ((d : ℝ) / 2) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by positivity)).ne'
  rw [show ((d : ℝ) + 2) / 2 =
      (d : ℝ) / 2 + 1 by ring,
    Real.Gamma_add_one (by positivity : (d : ℝ) / 2 ≠ 0)]
  have hpow :
      Real.rpow Real.pi ((d : ℝ) / 2) =
        Real.pi *
          Real.rpow Real.pi (((d : ℝ) - 2) / 2) := by
    calc
      Real.rpow Real.pi ((d : ℝ) / 2) =
          Real.rpow Real.pi
            (1 + (((d : ℝ) - 2) / 2)) := by
        congr 1
        ring
      _ =
          Real.rpow Real.pi 1 *
            Real.rpow Real.pi (((d : ℝ) - 2) / 2) := by
        simpa only [Real.rpow_eq_pow] using
          (Real.rpow_add Real.pi_pos
            1 (((d : ℝ) - 2) / 2))
      _ = _ := by
        have hone : Real.rpow Real.pi 1 = Real.pi := by
          norm_num [Real.rpow_one]
        rw [hone]
  rw [hpow]
  push_cast
  field_simp [hdne, hd1ne, hg]
  <;> ring

theorem gap5 (d : ℕ) (hd : 2 ≤ d) :
    angularSineChain d = angularBetaChain d := by
  exact angularSine_eq_beta d

theorem gap6
    (d : ℕ) (hd : 2 ≤ d)
    (a : Fin (d + 1) → ℝ) (ha : ∀ i, 0 < a i) :
    coneVolume d a =
      2 * Real.pi * (∏ i, a i) /
          (((d : ℝ) + 1) * (d : ℝ)) *
        (Real.rpow Real.pi (((d : ℝ) - 2) / 2) /
          Real.Gamma ((d : ℝ) / 2)) := by
  rw [publicCone_formula d (by omega) a ha]
  have hdpos : 0 < (d : ℝ) := by positivity
  have hdne : (d : ℝ) ≠ 0 := hdpos.ne'
  have hd1ne : (d : ℝ) + 1 ≠ 0 := by positivity
  have hg :
      Real.Gamma ((d : ℝ) / 2) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by positivity)).ne'
  push_cast
  rw [show ((d : ℝ) + 2) / 2 =
      (d : ℝ) / 2 + 1 by ring,
    Real.Gamma_add_one (by positivity : (d : ℝ) / 2 ≠ 0)]
  have hpow :
      Real.rpow Real.pi ((d : ℝ) / 2) =
        Real.pi *
          Real.rpow Real.pi (((d : ℝ) - 2) / 2) := by
    calc
      Real.rpow Real.pi ((d : ℝ) / 2) =
          Real.rpow Real.pi
            (1 + (((d : ℝ) - 2) / 2)) := by
        congr 1
        ring
      _ =
          Real.rpow Real.pi 1 *
            Real.rpow Real.pi (((d : ℝ) - 2) / 2) := by
        simpa only [Real.rpow_eq_pow] using
          (Real.rpow_add Real.pi_pos
            1 (((d : ℝ) - 2) / 2))
      _ = _ := by
        have hone : Real.rpow Real.pi 1 = Real.pi := by
          norm_num [Real.rpow_one]
        rw [hone]
  rw [hpow]
  field_simp [hdne, hd1ne, hg]
  <;> ring

theorem gap7
    (d : ℕ) (hd : 2 ≤ d)
    (a : Fin (d + 1) → ℝ) (ha : ∀ i, 0 < a i) :
    coneVolume d a =
      Real.rpow Real.pi ((d : ℝ) / 2) /
          (((d : ℝ) + 1) * Real.Gamma ((d : ℝ) / 2 + 1)) *
        (∏ i, a i) := by
  rw [publicCone_formula d (by omega) a ha]
  push_cast
  congr 3 <;> ring

end

end ProofGap.Exercise4210
