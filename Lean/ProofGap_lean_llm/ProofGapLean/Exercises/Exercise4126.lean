import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4126

noncomputable section

open MeasureTheory Set
open scoped Interval

abbrev Point3 := Fin 3 → ℝ

def solid (a : ℝ) : Set Point3 :=
  {p |
    p 0 ^ 2 + p 1 ^ 2 ≤ a * p 2 ∧
      p 2 ≤ 2 * a - Real.sqrt (p 0 ^ 2 + p 1 ^ 2)}

def boundarySurface (a : ℝ) : Set Point3 :=
  {p |
    (p 0 ^ 2 + p 1 ^ 2 = a * p 2 ∧
      p 2 ≤ 2 * a - Real.sqrt (p 0 ^ 2 + p 1 ^ 2)) ∨
    (p 2 = 2 * a - Real.sqrt (p 0 ^ 2 + p 1 ^ 2) ∧
      p 0 ^ 2 + p 1 ^ 2 ≤ a * p 2)}

def volumeReal (V : Set Point3) : ℝ :=
  (MeasureTheory.volume V).toReal

private def paraboloidSurfaceArea (a : ℝ) : ℝ :=
  ∫ φ in (0 : ℝ)..2 * Real.pi,
    ∫ r in (0 : ℝ)..1,
      Real.sqrt (1 + 4 * r ^ 2) * a ^ 2 * r

private def coneSurfaceArea (a : ℝ) : ℝ :=
  Real.sqrt 2 * Real.pi * a ^ 2

def surfaceArea (a : ℝ) : ℝ :=
  paraboloidSurfaceArea a + coneSurfaceArea a

def paraboloidHeight (a x y : ℝ) : ℝ :=
  (x ^ 2 + y ^ 2) / a

def coneHeight (a x y : ℝ) : ℝ :=
  2 * a - Real.sqrt (x ^ 2 + y ^ 2)

private theorem intervalIntegral_eq_sub_of_hasDerivAt
    {f F : ℝ → ℝ} (hF : ∀ x, HasDerivAt F (f x) x)
    (hf : Continuous f) (l u : ℝ) :
    intervalIntegral f l u volume = F u - F l := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _hx => hF x) (hf.intervalIntegrable (μ := volume) l u)

private theorem integral_poly2
    (c₀ c₁ c₂ l u : ℝ) :
    (∫ x in l..u, c₀ + c₁ * x + c₂ * x ^ 2) =
      c₀ * (u - l) +
        c₁ / 2 * (u ^ 2 - l ^ 2) +
        c₂ / 3 * (u ^ 3 - l ^ 3) := by
  let F : ℝ → ℝ := fun x =>
    c₀ * x + c₁ / 2 * x ^ 2 + c₂ / 3 * x ^ 3
  have hderiv (x : ℝ) :
      HasDerivAt F (c₀ + c₁ * x + c₂ * x ^ 2) x := by
    dsimp [F]
    convert
      (((hasDerivAt_id x).const_mul c₀).add
        (((hasDerivAt_id x).pow 2).const_mul (c₁ / 2))).add
        (((hasDerivAt_id x).pow 3).const_mul (c₂ / 3))
      using 1 <;> norm_num <;> ring
  rw [intervalIntegral_eq_sub_of_hasDerivAt hderiv (by fun_prop)]
  dsimp only [F]
  ring

private abbrev PlainPoint3 := Fin 3 → ℝ

private def splitZ : PlainPoint3 ≃ᵐ ((ℝ × ℝ) × ℝ) :=
  (MeasurableEquiv.piFinSuccAbove
      (fun _i : Fin 3 => ℝ) (2 : Fin 3)).trans
    ((MeasurableEquiv.prodCongr
      (MeasurableEquiv.refl ℝ)
      (MeasurableEquiv.piFinTwo (fun _i : Fin 2 => ℝ))).trans
      (MeasurableEquiv.prodComm :
        ℝ × (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) × ℝ))

@[simp] private theorem splitZ_apply (p : PlainPoint3) :
    splitZ p = ((p 0, p 1), p 2) := by
  rfl

private theorem splitZ_measurePreserving :
    MeasurePreserving splitZ volume volume := by
  have h₁ :
      MeasurePreserving
        (MeasurableEquiv.piFinSuccAbove
          (fun _i : Fin 3 => ℝ) (2 : Fin 3)) volume volume :=
    volume_preserving_piFinSuccAbove (fun _i : Fin 3 => ℝ) (2 : Fin 3)
  have h₂ :
      MeasurePreserving
        (MeasurableEquiv.prodCongr
          (MeasurableEquiv.refl ℝ)
          (MeasurableEquiv.piFinTwo (fun _i : Fin 2 => ℝ)))
        volume volume := by
    exact (MeasurePreserving.id (volume : Measure ℝ)).prod
      (volume_preserving_piFinTwo (fun _i : Fin 2 => ℝ))
  have h₃ :
      MeasurePreserving
        (MeasurableEquiv.prodComm :
          ℝ × (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) × ℝ)
        volume volume :=
    Measure.measurePreserving_swap
  exact h₃.comp (h₂.comp h₁)

private def plainSolid (a : ℝ) : Set PlainPoint3 :=
  {p |
    p 0 ^ 2 + p 1 ^ 2 ≤ a * p 2 ∧
      p 2 ≤ 2 * a - Real.sqrt (p 0 ^ 2 + p 1 ^ 2)}

private def baseDisk (a : ℝ) : Set (ℝ × ℝ) :=
  {q | q.1 ^ 2 + q.2 ^ 2 ≤ a ^ 2}

private def sectionLower (a : ℝ) (q : ℝ × ℝ) : ℝ :=
  (q.1 ^ 2 + q.2 ^ 2) / a

private def sectionUpper (a : ℝ) (q : ℝ × ℝ) : ℝ :=
  2 * a - Real.sqrt (q.1 ^ 2 + q.2 ^ 2)

private def closedRegion (a : ℝ) : Set ((ℝ × ℝ) × ℝ) :=
  {p |
    p.1 ∈ baseDisk a ∧
      sectionLower a p.1 ≤ p.2 ∧ p.2 ≤ sectionUpper a p.1}

private theorem solid_closed (a : ℝ) : IsClosed (solid a) := by
  have hx : Continuous (fun p : Point3 => p 0) := by fun_prop
  have hy : Continuous (fun p : Point3 => p 1) := by fun_prop
  have hz : Continuous (fun p : Point3 => p 2) := by fun_prop
  have hr : Continuous (fun p : Point3 => p 0 ^ 2 + p 1 ^ 2) :=
    (hx.pow 2).add (hy.pow 2)
  have hsqrt : Continuous
      (fun p : Point3 => Real.sqrt (p 0 ^ 2 + p 1 ^ 2)) :=
    Real.continuous_sqrt.comp hr
  unfold solid
  simpa only [Set.setOf_and] using
    (isClosed_le hr (continuous_const.mul hz)).inter
      (isClosed_le hz (continuous_const.sub hsqrt))

private theorem plainSolid_eq_preimage (a : ℝ) :
    plainSolid a = solid a := by
  rfl

private theorem volume_solid_eq_plain (a : ℝ) :
    volume (solid a) = volume (plainSolid a) := by
  rw [plainSolid_eq_preimage]

private theorem baseDisk_closed (a : ℝ) : IsClosed (baseDisk a) := by
  unfold baseDisk
  exact isClosed_le
    ((continuous_fst.pow 2).add (continuous_snd.pow 2))
    continuous_const

private theorem sectionLower_continuous (a : ℝ) :
    Continuous (sectionLower a) := by
  unfold sectionLower
  fun_prop

private theorem sectionUpper_continuous (a : ℝ) :
    Continuous (sectionUpper a) := by
  unfold sectionUpper
  fun_prop

private theorem closedRegion_measurable (a : ℝ) :
    MeasurableSet (closedRegion a) := by
  unfold closedRegion
  exact measurableSet_region_between_cc
    (sectionLower_continuous a).measurable
    (sectionUpper_continuous a).measurable
    (baseDisk_closed a).measurableSet

private theorem splitZ_preimage_closedRegion
    (a : ℝ) (ha : 0 < a) :
    splitZ ⁻¹' closedRegion a = plainSolid a := by
  ext p
  simp only [Set.mem_preimage, splitZ_apply]
  change
    ((p 0) ^ 2 + (p 1) ^ 2 ≤ a ^ 2 ∧
        ((p 0) ^ 2 + (p 1) ^ 2) / a ≤ p 2 ∧
          p 2 ≤ 2 * a - Real.sqrt ((p 0) ^ 2 + (p 1) ^ 2)) ↔
      ((p 0) ^ 2 + (p 1) ^ 2 ≤ a * p 2 ∧
        p 2 ≤ 2 * a - Real.sqrt ((p 0) ^ 2 + (p 1) ^ 2))
  constructor
  · rintro ⟨hbase, hlo, hhi⟩
    exact ⟨by
      simpa only [mul_comm] using (div_le_iff₀ ha).1 hlo, hhi⟩
  · rintro ⟨hlo, hhi⟩
    let s := (p 0) ^ 2 + (p 1) ^ 2
    let t := Real.sqrt s
    have hs : 0 ≤ s := by
      dsimp only [s]
      positivity
    have ht : 0 ≤ t := by
      dsimp only [t]
      exact Real.sqrt_nonneg _
    have ht2 : t ^ 2 = s := by
      dsimp only [t]
      exact Real.sq_sqrt hs
    have hbound : s ≤ 2 * a ^ 2 - a * t := by
      dsimp only [s, t] at hhi ⊢
      nlinarith
    have hta : t ≤ a := by
      nlinarith [sq_nonneg (t - a)]
    have hbase : s ≤ a ^ 2 := by nlinarith
    refine ⟨hbase, ?_, hhi⟩
    apply (div_le_iff₀ ha).2
    simpa only [mul_comm] using hlo

private theorem volume_plain_eq_closedRegion
    (a : ℝ) (ha : 0 < a) :
    volume (plainSolid a) = volume (closedRegion a) := by
  rw [← splitZ_preimage_closedRegion a ha]
  exact splitZ_measurePreserving.measure_preimage
    (closedRegion_measurable a).nullMeasurableSet

private theorem closedRegion_measure_eq_open (a : ℝ) :
    volume (closedRegion a) =
      volume (regionBetween (sectionLower a) (sectionUpper a)
        (baseDisk a)) := by
  change
    ((volume : Measure (ℝ × ℝ)).prod (volume : Measure ℝ))
        (closedRegion a) =
      ((volume : Measure (ℝ × ℝ)).prod (volume : Measure ℝ))
        (regionBetween (sectionLower a) (sectionUpper a)
          (baseDisk a))
  rw [MeasureTheory.Measure.prod_apply (closedRegion_measurable a),
    MeasureTheory.Measure.prod_apply
      (measurableSet_regionBetween
        (sectionLower_continuous a).measurable
        (sectionUpper_continuous a).measurable
        (baseDisk_closed a).measurableSet)]
  apply lintegral_congr
  intro q
  change
    volume
        {z : ℝ |
          q ∈ baseDisk a ∧
            sectionLower a q ≤ z ∧ z ≤ sectionUpper a q} =
      volume
        {z : ℝ |
          q ∈ baseDisk a ∧
            z ∈ Set.Ioo (sectionLower a q) (sectionUpper a q)}
  by_cases hq : q ∈ baseDisk a
  · rw [show
      {z : ℝ |
        q ∈ baseDisk a ∧
          sectionLower a q ≤ z ∧ z ≤ sectionUpper a q} =
          Set.Icc (sectionLower a q) (sectionUpper a q) by
        ext z
        simp [hq],
      show
      {z : ℝ |
        q ∈ baseDisk a ∧
          z ∈ Set.Ioo (sectionLower a q) (sectionUpper a q)} =
          Set.Ioo (sectionLower a q) (sectionUpper a q) by
        ext z
        simp [hq],
      Real.volume_Icc, Real.volume_Ioo]
  · have hleft :
        {z : ℝ |
          q ∈ baseDisk a ∧
            sectionLower a q ≤ z ∧ z ≤ sectionUpper a q} = ∅ := by
      ext z
      simp [hq]
    have hright :
        {z : ℝ |
          q ∈ baseDisk a ∧
            z ∈ Set.Ioo (sectionLower a q) (sectionUpper a q)} = ∅ := by
      ext z
      simp [hq]
    rw [hleft, hright]

private theorem baseDisk_compact (a : ℝ) (ha : 0 < a) :
    IsCompact (baseDisk a) := by
  apply (isCompact_Icc :
    IsCompact (Set.Icc ((-a, -a) : ℝ × ℝ) (a, a))).of_isClosed_subset
      (baseDisk_closed a)
  intro q hq
  change q.1 ^ 2 + q.2 ^ 2 ≤ a ^ 2 at hq
  have hx2 : q.1 ^ 2 ≤ a ^ 2 := by
    nlinarith [sq_nonneg q.2]
  have hy2 : q.2 ^ 2 ≤ a ^ 2 := by
    nlinarith [sq_nonneg q.1]
  exact
    ⟨⟨by nlinarith [sq_nonneg (q.1 + a)],
        by nlinarith [sq_nonneg (q.2 + a)]⟩,
      ⟨by nlinarith [sq_nonneg (q.1 - a)],
        by nlinarith [sq_nonneg (q.2 - a)]⟩⟩

private theorem section_order
    (a : ℝ) (ha : 0 < a) (q : ℝ × ℝ)
    (hq : q ∈ baseDisk a) :
    sectionLower a q ≤ sectionUpper a q := by
  let s := q.1 ^ 2 + q.2 ^ 2
  have hs : 0 ≤ s := by
    dsimp only [s]
    positivity
  have hsa : s ≤ a ^ 2 := hq
  have hsqrt : Real.sqrt s ≤ a := by
    rw [Real.sqrt_le_iff]
    exact ⟨ha.le, hsa⟩
  have hdiv : s / a ≤ a := by
    apply (div_le_iff₀ ha).2
    nlinarith
  unfold sectionLower sectionUpper
  dsimp only [s] at hdiv hsqrt
  linarith

private theorem closedRegion_volumeReal_as_base
    (a : ℝ) (ha : 0 < a) :
    (volume (closedRegion a)).toReal =
      ∫ q in baseDisk a, sectionUpper a q - sectionLower a q := by
  rw [closedRegion_measure_eq_open]
  have hlo : IntegrableOn (sectionLower a) (baseDisk a) volume :=
    (sectionLower_continuous a).continuousOn.integrableOn_compact
      (baseDisk_compact a ha)
  have hhi : IntegrableOn (sectionUpper a) (baseDisk a) volume :=
    (sectionUpper_continuous a).continuousOn.integrableOn_compact
      (baseDisk_compact a ha)
  change
    (((volume : Measure (ℝ × ℝ)).prod (volume : Measure ℝ))
      (regionBetween (sectionLower a) (sectionUpper a)
        (baseDisk a))).toReal =
      ∫ q in baseDisk a,
        (sectionUpper a - sectionLower a) q
  rw [volume_regionBetween_eq_integral hlo hhi
    (baseDisk_closed a).measurableSet (section_order a ha)]
  rw [ENNReal.toReal_ofReal]
  exact MeasureTheory.setIntegral_nonneg
    (baseDisk_closed a).measurableSet
    (fun q hq => sub_nonneg.2 (section_order a ha q hq))

private theorem angular_full :
    (∫ θ in Set.Ioo (-Real.pi) Real.pi, (1 : ℝ)) =
      2 * Real.pi := by
  calc
    _ = ∫ θ in Set.Ioc (-Real.pi) Real.pi, (1 : ℝ) :=
      (integral_Ioc_eq_integral_Ioo
        (f := fun _ : ℝ => (1 : ℝ))).symm
    _ = ∫ θ in -Real.pi..Real.pi, (1 : ℝ) := by
      rw [intervalIntegral.integral_of_le]
      exact neg_le_self Real.pi_nonneg
    _ = 2 * Real.pi := by
      simp only [intervalIntegral.integral_const, smul_eq_mul]
      ring

private theorem radial_polar_pointwise
    (a : ℝ) (ha : 0 < a) (F : ℝ → ℝ)
    (p : ℝ × ℝ) (hp : p ∈ polarCoord.target) :
    p.1 • (baseDisk a).indicator
        (fun q : ℝ × ℝ =>
          F (Real.sqrt (q.1 ^ 2 + q.2 ^ 2)))
        (polarCoord.symm p) =
      (Set.Iic a).indicator (fun r => r * F r) p.1 *
        (1 : ℝ) := by
  rcases p with ⟨r, θ⟩
  have hr : 0 < r := hp.1
  have htrig :
      (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 = r ^ 2 := by
    calc
      _ = r ^ 2 * (Real.cos θ ^ 2 + Real.sin θ ^ 2) := by ring
      _ = r ^ 2 := by rw [Real.cos_sq_add_sin_sq]; ring
  have hmem :
      polarCoord.symm (r, θ) ∈ baseDisk a ↔ r ≤ a := by
    rw [polarCoord_symm_apply]
    simp only [baseDisk, Set.mem_setOf_eq, htrig]
    exact sq_le_sq₀ hr.le ha.le
  simp only [Set.indicator, hmem, Set.mem_Iic, smul_eq_mul]
  by_cases h : r ≤ a
  · simp only [h, if_true]
    rw [polarCoord_symm_apply, htrig, Real.sqrt_sq_eq_abs,
      abs_of_pos hr]
    ring
  · simp [h]

private theorem radial_set_to_interval
    (a : ℝ) (ha : 0 < a) (F : ℝ → ℝ) :
    (∫ r in Set.Ioi (0 : ℝ),
        (Set.Iic a).indicator (fun r => r * F r) r) =
      ∫ r in (0 : ℝ)..a, r * F r := by
  rw [setIntegral_indicator measurableSet_Iic]
  have hinter :
      Set.Ioi (0 : ℝ) ∩ Set.Iic a = Set.Ioc (0 : ℝ) a := by
    ext r
    simp
  rw [hinter, intervalIntegral.integral_of_le ha.le]

private theorem radial_disk_integral
    (a : ℝ) (ha : 0 < a) (F : ℝ → ℝ) :
    (∫ q in baseDisk a,
        F (Real.sqrt (q.1 ^ 2 + q.2 ^ 2))) =
      2 * Real.pi * ∫ r in (0 : ℝ)..a, r * F r := by
  have hp := integral_comp_polarCoord_symm
    ((baseDisk a).indicator
      (fun q : ℝ × ℝ =>
        F (Real.sqrt (q.1 ^ 2 + q.2 ^ 2))))
  rw [integral_indicator (baseDisk_closed a).measurableSet] at hp
  have hprod :
      (∫ p in polarCoord.target,
          p.1 • (baseDisk a).indicator
            (fun q : ℝ × ℝ =>
              F (Real.sqrt (q.1 ^ 2 + q.2 ^ 2)))
            (polarCoord.symm p)) =
        (∫ r in Set.Ioi (0 : ℝ),
            (Set.Iic a).indicator (fun r => r * F r) r) *
          ∫ θ in Set.Ioo (-Real.pi) Real.pi, (1 : ℝ) := by
    rw [polarCoord_target]
    calc
      _ = ∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
          (Set.Iic a).indicator (fun r => r * F r) p.1 *
            (1 : ℝ) := by
        apply setIntegral_congr_fun
          (measurableSet_Ioi.prod measurableSet_Ioo)
        intro p hp'
        exact radial_polar_pointwise a ha F p hp'
      _ = _ := by
        exact setIntegral_prod_mul
          (fun r : ℝ => (Set.Iic a).indicator (fun r => r * F r) r)
          (fun _ : ℝ => (1 : ℝ))
          (Set.Ioi (0 : ℝ)) (Set.Ioo (-Real.pi) Real.pi)
  rw [hprod, radial_set_to_interval a ha F, angular_full] at hp
  rw [← hp]
  ring

private def heightRadial (a r : ℝ) : ℝ :=
  2 * a - r - r ^ 2 / a

private theorem base_height_radial (a : ℝ) :
    (∫ q in baseDisk a, sectionUpper a q - sectionLower a q) =
      ∫ q in baseDisk a,
        heightRadial a (Real.sqrt (q.1 ^ 2 + q.2 ^ 2)) := by
  apply MeasureTheory.setIntegral_congr_fun
    (baseDisk_closed a).measurableSet
  intro q hq
  have hs : 0 ≤ q.1 ^ 2 + q.2 ^ 2 := by positivity
  change
    sectionUpper a q - sectionLower a q =
      heightRadial a (Real.sqrt (q.1 ^ 2 + q.2 ^ 2))
  unfold sectionUpper sectionLower heightRadial
  rw [Real.sq_sqrt hs]

private theorem radial_height_value (a : ℝ) (ha : 0 < a) :
    (∫ r in (0 : ℝ)..a, r * heightRadial a r) =
      5 * a ^ 3 / 12 := by
  have ha0 : a ≠ 0 := ha.ne'
  calc
    _ = ∫ r in (0 : ℝ)..a,
        0 + (2 * a) * r + (-1) * r ^ 2 +
          (-1 / a) * r ^ 3 := by
      apply intervalIntegral.integral_congr
      intro r hr
      unfold heightRadial
      field_simp [ha0]
      <;> ring
    _ = 5 * a ^ 3 / 12 := by
      let F : ℝ → ℝ := fun r =>
        a * r ^ 2 - r ^ 3 / 3 - r ^ 4 / (4 * a)
      have hF (r : ℝ) :
          HasDerivAt F
            (0 + (2 * a) * r + (-1) * r ^ 2 +
              (-1 / a) * r ^ 3) r := by
        dsimp only [F]
        convert
          ((((hasDerivAt_id r).pow 2).const_mul a).sub
            (((hasDerivAt_id r).pow 3).const_mul (1 / 3))).sub
            (((hasDerivAt_id r).pow 4).const_mul (1 / (4 * a)))
          using 1 <;> norm_num <;> try ring
        exact funext (fun x => by
          simp [sub_eq_add_neg, div_eq_mul_inv, add_assoc, mul_comm])
      rw [intervalIntegral_eq_sub_of_hasDerivAt hF (by fun_prop)]
      dsimp only [F]
      field_simp [ha0]
      <;> ring

private theorem base_height_value (a : ℝ) (ha : 0 < a) :
    (∫ q in baseDisk a, sectionUpper a q - sectionLower a q) =
      5 * Real.pi * a ^ 3 / 6 := by
  rw [base_height_radial a, radial_disk_integral a ha (heightRadial a),
    radial_height_value a ha]
  ring

private theorem volume_value (a : ℝ) (ha : 0 < a) :
    volumeReal (solid a) = 5 * Real.pi * a ^ 3 / 6 := by
  unfold volumeReal
  rw [volume_solid_eq_plain a, volume_plain_eq_closedRegion a ha,
    closedRegion_volumeReal_as_base a ha, base_height_value a ha]

private def surfaceRadialPrimitive (a r : ℝ) : ℝ :=
  a ^ 2 / 12 * Real.rpow (1 + 4 * r ^ 2) (3 / 2 : ℝ)

private theorem surfaceRadialPrimitive_hasDerivAt (a r : ℝ) :
    HasDerivAt (surfaceRadialPrimitive a)
      (Real.sqrt (1 + 4 * r ^ 2) * a ^ 2 * r) r := by
  have hu : 0 < 1 + 4 * r ^ 2 := by positivity
  have hinner :
      HasDerivAt (fun x : ℝ => 1 + 4 * x ^ 2) (8 * r) r := by
    convert (hasDerivAt_const r 1).add
      (((hasDerivAt_id r).pow 2).const_mul 4)
      using 1 <;> simp only [id_eq] <;> ring
  have hpow := (Real.hasDerivAt_rpow_const
    (p := (3 / 2 : ℝ)) (Or.inl hu.ne')).comp r hinner
  unfold surfaceRadialPrimitive
  convert hpow.const_mul (a ^ 2 / 12) using 1
  norm_num [Real.sqrt_eq_rpow]
  ring

private theorem surface_radial_value (a : ℝ) :
    (∫ r in (0 : ℝ)..1,
        Real.sqrt (1 + 4 * r ^ 2) * a ^ 2 * r) =
      a ^ 2 * (5 * Real.sqrt 5 - 1) / 12 := by
  rw [intervalIntegral_eq_sub_of_hasDerivAt
    (surfaceRadialPrimitive_hasDerivAt a) (by fun_prop)]
  unfold surfaceRadialPrimitive
  have hfive :
      Real.rpow 5 (3 / 2 : ℝ) = 5 * Real.sqrt 5 := by
    calc
      Real.rpow 5 (3 / 2 : ℝ) =
          Real.rpow 5 (1 + 1 / 2 : ℝ) := by norm_num
      _ = Real.rpow 5 1 * Real.rpow 5 (1 / 2 : ℝ) :=
        Real.rpow_add (by norm_num) 1 (1 / 2)
      _ = 5 * Real.rpow 5 (1 / 2 : ℝ) :=
        congrArg (fun t : ℝ => t * Real.rpow 5 (1 / 2 : ℝ))
          (Real.rpow_one 5)
      _ = 5 * Real.sqrt 5 :=
        congrArg (fun t : ℝ => 5 * t) (Real.sqrt_eq_rpow 5).symm
  have hbase1 : (1 + 4 * (1 : ℝ) ^ 2) = 5 := by norm_num
  have hbase0 : (1 + 4 * (0 : ℝ) ^ 2) = 1 := by norm_num
  rw [hbase1, hbase0, hfive]
  have hone : Real.rpow 1 (3 / 2 : ℝ) = 1 :=
    Real.one_rpow _
  rw [hone]
  ring

private theorem surface_expression_value (a : ℝ) :
    (∫ φ in (0 : ℝ)..2 * Real.pi,
        ∫ r in (0 : ℝ)..1,
          Real.sqrt (1 + 4 * r ^ 2) * a ^ 2 * r) +
        Real.sqrt 2 * Real.pi * a ^ 2 =
      Real.pi * a ^ 2 / 6 *
        (6 * Real.sqrt 2 + 5 * Real.sqrt 5 - 1) := by
  simp_rw [surface_radial_value]
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  ring

theorem gap1 (a x y z : ℝ) (ha : 0 < a)
    (hparaboloid : x ^ 2 + y ^ 2 = a * z)
    (hcone : z = 2 * a - Real.sqrt (x ^ 2 + y ^ 2)) :
    x ^ 2 + y ^ 2 = a ^ 2 := by
  have hs : 0 ≤ x ^ 2 + y ^ 2 :=
    add_nonneg (sq_nonneg x) (sq_nonneg y)
  have hsqrt : Real.sqrt (x ^ 2 + y ^ 2) ^ 2 =
      x ^ 2 + y ^ 2 :=
    Real.sq_sqrt hs
  have hsqrtnonneg : 0 ≤ Real.sqrt (x ^ 2 + y ^ 2) :=
    Real.sqrt_nonneg _
  rw [hcone] at hparaboloid
  nlinarith

theorem gap2 (a x y z : ℝ) (ha : 0 < a)
    (hparaboloid : x ^ 2 + y ^ 2 = a * z)
    (hcone : z = 2 * a - Real.sqrt (x ^ 2 + y ^ 2)) :
    z = a := by
  have hs := gap1 a x y z ha hparaboloid hcone
  rw [hs, Real.sqrt_sq_eq_abs, abs_of_pos ha] at hcone
  linarith

theorem gap4 (a : ℝ) (ha : 0 < a) :
    (∫ z in (0 : ℝ)..a, Real.pi * a * z) +
        (∫ z in a..2 * a, Real.pi * (2 * a - z) ^ 2) =
      Real.pi * a ^ 3 / 2 + Real.pi * a ^ 3 / 3 := by
  have hfirst :
      (∫ z in (0 : ℝ)..a, Real.pi * a * z) =
        Real.pi * a ^ 3 / 2 := by
    calc
      _ = ∫ z in (0 : ℝ)..a,
          0 + (Real.pi * a) * z + 0 * z ^ 2 := by
        apply intervalIntegral.integral_congr
        intro z hz
        ring
      _ = Real.pi * a ^ 3 / 2 := by
        rw [integral_poly2]
        ring
  have hsecond :
      (∫ z in a..2 * a, Real.pi * (2 * a - z) ^ 2) =
        Real.pi * a ^ 3 / 3 := by
    calc
      _ = ∫ z in a..2 * a,
          (4 * Real.pi * a ^ 2) +
            (-4 * Real.pi * a) * z + Real.pi * z ^ 2 := by
        apply intervalIntegral.integral_congr
        intro z hz
        ring
      _ = Real.pi * a ^ 3 / 3 := by
        rw [integral_poly2]
        ring
  rw [hfirst, hsecond]

theorem gap5 (a : ℝ) :
    Real.pi * a ^ 3 / 2 + Real.pi * a ^ 3 / 3 =
      5 * Real.pi * a ^ 3 / 6 := by
  ring

theorem gap3 (a : ℝ) (ha : 0 < a) :
    volumeReal (solid a) =
      (∫ z in (0 : ℝ)..a, Real.pi * a * z) +
        ∫ z in a..2 * a, Real.pi * (2 * a - z) ^ 2 := by
  calc
    volumeReal (solid a) = 5 * Real.pi * a ^ 3 / 6 :=
      volume_value a ha
    _ = (∫ z in (0 : ℝ)..a, Real.pi * a * z) +
        ∫ z in a..2 * a, Real.pi * (2 * a - z) ^ 2 :=
      ((gap4 a ha).trans (gap5 a)).symm

theorem gap6 (a : ℝ) (ha : 0 < a) :
    volumeReal (solid a) = 5 * Real.pi * a ^ 3 / 6 := by
  exact volume_value a ha

theorem gap7 (a x y : ℝ) (ha : 0 < a) :
    deriv (fun t => paraboloidHeight a t y) x = 2 * x / a := by
  have h :
      HasDerivAt (fun t => paraboloidHeight a t y)
        (2 * x / a) x := by
    unfold paraboloidHeight
    convert (((hasDerivAt_id x).pow 2).add_const (y ^ 2)).div_const a
      using 1 <;> simp only [id_eq] <;> ring
  exact h.deriv

theorem gap8 (a x y : ℝ) (ha : 0 < a) :
    deriv (fun t => paraboloidHeight a x t) y = 2 * y / a := by
  have h :
      HasDerivAt (fun t => paraboloidHeight a x t)
        (2 * y / a) y := by
    unfold paraboloidHeight
    convert ((hasDerivAt_const y (x ^ 2)).add
      ((hasDerivAt_id y).pow 2)).div_const a
      using 1 <;> simp only [id_eq] <;> ring
  exact h.deriv

theorem gap9 (a x y : ℝ) (ha : 0 < a) :
    Real.sqrt
        (1 +
          deriv (fun t => paraboloidHeight a t y) x ^ 2 +
          deriv (fun t => paraboloidHeight a x t) y ^ 2) =
      1 / a * Real.sqrt (a ^ 2 + 4 * x ^ 2 + 4 * y ^ 2) := by
  rw [gap7 a x y ha, gap8 a x y ha]
  have ha0 : a ≠ 0 := ha.ne'
  have hleft :
      0 ≤ 1 + (2 * x / a) ^ 2 + (2 * y / a) ^ 2 := by
    positivity
  have hright :
      0 ≤ a ^ 2 + 4 * x ^ 2 + 4 * y ^ 2 := by
    positivity
  have hsquare :
      (Real.sqrt
          (1 + (2 * x / a) ^ 2 + (2 * y / a) ^ 2)) ^ 2 =
        (1 / a *
          Real.sqrt (a ^ 2 + 4 * x ^ 2 + 4 * y ^ 2)) ^ 2 := by
    rw [Real.sq_sqrt hleft, mul_pow, Real.sq_sqrt hright]
    field_simp [ha0]
    <;> ring
  exact (sq_eq_sq₀ (Real.sqrt_nonneg _)
    (mul_nonneg (by positivity) (Real.sqrt_nonneg _))).mp hsquare

theorem gap10 (a x y : ℝ) (hr : 0 < x ^ 2 + y ^ 2) :
    deriv (fun t => coneHeight a t y) x =
      -x / Real.sqrt (x ^ 2 + y ^ 2) := by
  have hquad :
      HasDerivAt (fun t : ℝ => t ^ 2 + y ^ 2) (2 * x) x := by
    convert ((hasDerivAt_id x).pow 2).add_const (y ^ 2)
      using 1 <;> simp only [id_eq] <;> ring
  have hsqrt :
      HasDerivAt (fun t : ℝ => Real.sqrt (t ^ 2 + y ^ 2))
        ((2 * x) / (2 * Real.sqrt (x ^ 2 + y ^ 2))) x :=
    hquad.sqrt hr.ne'
  have h :
      HasDerivAt (fun t : ℝ => coneHeight a t y)
        (-x / Real.sqrt (x ^ 2 + y ^ 2)) x := by
    unfold coneHeight
    convert (hasDerivAt_const x (2 * a)).sub hsqrt using 1 <;> ring
  exact h.deriv

theorem gap11 (a x y : ℝ) (hr : 0 < x ^ 2 + y ^ 2) :
    deriv (fun t => coneHeight a x t) y =
      -y / Real.sqrt (x ^ 2 + y ^ 2) := by
  have hquad :
      HasDerivAt (fun t : ℝ => x ^ 2 + t ^ 2) (2 * y) y := by
    convert (hasDerivAt_const y (x ^ 2)).add
      ((hasDerivAt_id y).pow 2)
      using 1 <;> simp only [id_eq] <;> ring
  have hsqrt :
      HasDerivAt (fun t : ℝ => Real.sqrt (x ^ 2 + t ^ 2))
        ((2 * y) / (2 * Real.sqrt (x ^ 2 + y ^ 2))) y :=
    hquad.sqrt hr.ne'
  have h :
      HasDerivAt (fun t : ℝ => coneHeight a x t)
        (-y / Real.sqrt (x ^ 2 + y ^ 2)) y := by
    unfold coneHeight
    convert (hasDerivAt_const y (2 * a)).sub hsqrt using 1 <;> ring
  exact h.deriv

theorem gap12 (a x y : ℝ) (hr : 0 < x ^ 2 + y ^ 2) :
    Real.sqrt
        (1 +
          deriv (fun t => coneHeight a t y) x ^ 2 +
          deriv (fun t => coneHeight a x t) y ^ 2) =
      Real.sqrt 2 := by
  rw [gap10 a x y hr, gap11 a x y hr]
  congr 1
  have hr0 : x ^ 2 + y ^ 2 ≠ 0 := hr.ne'
  have hsqrt0 : Real.sqrt (x ^ 2 + y ^ 2) ≠ 0 :=
    (Real.sqrt_pos.2 hr).ne'
  have hsqrt_sq :
      Real.sqrt (x ^ 2 + y ^ 2) ^ 2 = x ^ 2 + y ^ 2 :=
    Real.sq_sqrt hr.le
  field_simp [hsqrt0, hr0]
  nlinarith

theorem gap13 (a : ℝ) (ha : 0 < a) :
    surfaceArea a =
      (∫ φ in (0 : ℝ)..2 * Real.pi,
        ∫ r in (0 : ℝ)..1,
          Real.sqrt (1 + 4 * r ^ 2) * a ^ 2 * r) +
        Real.sqrt 2 * Real.pi * a ^ 2 := by
  rfl

theorem gap14 (a : ℝ) (ha : 0 < a) :
    surfaceArea a =
      Real.pi * a ^ 2 / 6 *
        (6 * Real.sqrt 2 + 5 * Real.sqrt 5 - 1) := by
  exact (gap13 a ha).trans (surface_expression_value a)

end

end ProofGap.Exercise4126
