import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4148

noncomputable section

open MeasureTheory
open scoped Interval

abbrev Point3 := ℝ × ℝ × ℝ

def solid : Set Point3 :=
  {p |
    -1 ≤ p.1 + p.2.1 ∧ p.1 + p.2.1 ≤ 1 ∧
      -1 ≤ p.1 - p.2.1 ∧ p.1 - p.2.1 ≤ 1 ∧
        0 ≤ p.2.2 ∧ p.2.2 ≤ p.1 ^ 2 + p.2.1 ^ 2}

def inertiaZ : ℝ :=
  ∫ p in solid, p.1 ^ 2 + p.2.1 ^ 2

def inertiaZX : ℝ :=
  ∫ p in solid, p.2.1 ^ 2

def inertiaZY : ℝ :=
  ∫ p in solid, p.1 ^ 2

def xyJacobian : ℝ :=
  |(1 / 2 : ℝ) * (-(1 / 2)) - (1 / 2) * (1 / 2)|

private def transformedSolid : Set Point3 :=
  {p |
    -1 ≤ p.1 ∧ p.1 ≤ 1 ∧
      -1 ≤ p.2.1 ∧ p.2.1 ≤ 1 ∧
        0 ≤ p.2.2 ∧ p.2.2 ≤ (p.1 ^ 2 + p.2.1 ^ 2) / 2}

private def coordinateEquiv :
    Point3 ≃ₗ[ℝ] (Fin 3 → ℝ) :=
  { toFun := fun p => ![p.1, p.2.1, p.2.2]
    invFun := fun x => (x 0, x 1, x 2)
    left_inv := by
      intro p
      ext <;> simp
    right_inv := by
      intro x
      funext i
      fin_cases i <;> simp
    map_add' := by
      intro p q
      funext i
      fin_cases i <;> simp
    map_smul' := by
      intro r p
      funext i
      fin_cases i <;> simp }

private def forwardMap (p : Point3) : Point3 :=
  (p.1 + p.2.1, p.1 - p.2.1, p.2.2)

private def inverseMap (p : Point3) : Point3 :=
  ((p.1 + p.2.1) / 2, (p.1 - p.2.1) / 2, p.2.2)

private def forwardLinear : Point3 →ₗ[ℝ] Point3 :=
  let A : Matrix (Fin 3) (Fin 3) ℝ :=
    ![![(1 : ℝ), 1, 0], ![1, (-1 : ℝ), 0], ![0, 0, 1] ]
  (coordinateEquiv.symm : (Fin 3 → ℝ) →ₗ[ℝ] Point3) ∘ₗ
    Matrix.toLin' A ∘ₗ
      (coordinateEquiv : Point3 →ₗ[ℝ] (Fin 3 → ℝ))

@[simp] private theorem forwardLinear_apply (p : Point3) :
    forwardLinear p = forwardMap p := by
  ext <;>
    simp [forwardLinear, coordinateEquiv, forwardMap,
      Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ] <;>
    ring

private theorem forwardLinear_det :
    LinearMap.det forwardLinear = -2 := by
  let A : Matrix (Fin 3) (Fin 3) ℝ :=
    ![![(1 : ℝ), 1, 0], ![1, (-1 : ℝ), 0], ![0, 0, 1] ]
  change
    LinearMap.det
        ((coordinateEquiv.symm :
            (Fin 3 → ℝ) →ₗ[ℝ] Point3) ∘ₗ
          Matrix.toLin' A ∘ₗ
            (coordinateEquiv :
              Point3 →ₗ[ℝ] (Fin 3 → ℝ))) =
      -2
  have hconj :
      LinearMap.det
          ((coordinateEquiv.symm :
              (Fin 3 → ℝ) →ₗ[ℝ] Point3) ∘ₗ
            Matrix.toLin' A ∘ₗ
              (coordinateEquiv :
                Point3 →ₗ[ℝ] (Fin 3 → ℝ))) =
        LinearMap.det (Matrix.toLin' A) := by
    simpa only [LinearEquiv.symm_symm] using
      (LinearMap.det_conj (Matrix.toLin' A) coordinateEquiv.symm)
  rw [hconj]
  simp only [LinearMap.det_toLin']
  rw [Matrix.det_fin_three]
  simp [A]
  norm_num

private theorem inverse_forward (p : Point3) :
    inverseMap (forwardMap p) = p := by
  rcases p with ⟨x, y, z⟩
  ext <;> simp [inverseMap, forwardMap] <;> ring

private theorem transformed_iff (p : Point3) :
    forwardMap p ∈ transformedSolid ↔ p ∈ solid := by
  rcases p with ⟨x, y, z⟩
  change
    (-1 ≤ x + y ∧ x + y ≤ 1 ∧
        -1 ≤ x - y ∧ x - y ≤ 1 ∧
          0 ≤ z ∧ z ≤ ((x + y) ^ 2 + (x - y) ^ 2) / 2) ↔
      (-1 ≤ x + y ∧ x + y ≤ 1 ∧
        -1 ≤ x - y ∧ x - y ≤ 1 ∧
          0 ≤ z ∧ z ≤ x ^ 2 + y ^ 2)
  constructor
  · rintro ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩
    refine ⟨h₁, h₂, h₃, h₄, h₅, ?_⟩
    convert h₆ using 1 <;> ring
  · rintro ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩
    refine ⟨h₁, h₂, h₃, h₄, h₅, ?_⟩
    convert h₆ using 1 <;> ring

private theorem solid_measurable : MeasurableSet solid := by
  unfold solid
  measurability

private theorem transformed_measurable : MeasurableSet transformedSolid := by
  unfold transformedSolid
  measurability

private theorem continuous_inverseMap : Continuous inverseMap := by
  unfold inverseMap
  fun_prop

private theorem integral_solid_eq_half_transformed
    (f : Point3 → ℝ) (hf : Continuous f) :
    (∫ p in solid, f p) =
      (1 / 2 : ℝ) * ∫ q in transformedSolid, f (inverseMap q) := by
  letI : Measure.IsAddHaarMeasure
      (MeasureTheory.volume : Measure (ℝ × ℝ)) := by
    rw [Measure.volume_eq_prod]
    infer_instance
  letI : Measure.IsAddHaarMeasure
      (MeasureTheory.volume : Measure Point3) := by
    rw [Measure.volume_eq_prod]
    infer_instance
  let g : Point3 → ℝ :=
    transformedSolid.indicator (fun q => f (inverseMap q))
  have hgmeas : StronglyMeasurable g := by
    exact
      ((hf.comp continuous_inverseMap).stronglyMeasurable.indicator
        transformed_measurable)
  have hmap :
      Measure.map forwardLinear MeasureTheory.volume =
        ENNReal.ofReal |(LinearMap.det forwardLinear)⁻¹| •
          (MeasureTheory.volume : Measure Point3) :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar
      (MeasureTheory.volume : Measure Point3)
      (by rw [forwardLinear_det]; norm_num)
  rw [forwardLinear_det] at hmap
  norm_num at hmap
  have hchange :=
    MeasureTheory.integral_map
      (forwardLinear.continuous_of_finiteDimensional.measurable.aemeasurable)
      (hgmeas.aestronglyMeasurable
        (μ := Measure.map forwardLinear MeasureTheory.volume))
  change
    (∫ q : Point3, g q ∂Measure.map forwardLinear MeasureTheory.volume) =
      ∫ p : Point3, g (forwardLinear p) at hchange
  rw [hmap, MeasureTheory.integral_smul_measure] at hchange
  norm_num at hchange
  have hpoint (p : Point3) :
      g (forwardLinear p) = solid.indicator f p := by
    simp only [g, forwardLinear_apply]
    by_cases hp : p ∈ solid
    · have ht : forwardMap p ∈ transformedSolid :=
        (transformed_iff p).2 hp
      rw [Set.indicator_of_mem ht, Set.indicator_of_mem hp,
        inverse_forward]
    · have ht : forwardMap p ∉ transformedSolid := by
        simpa [transformed_iff p] using hp
      rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem hp]
  calc
    (∫ p in solid, f p) =
        ∫ p : Point3, solid.indicator f p := by
      rw [MeasureTheory.integral_indicator solid_measurable]
    _ = ∫ p : Point3, g (forwardLinear p) := by
      apply integral_congr_ae
      filter_upwards with p
      exact (hpoint p).symm
    _ = (1 / 2 : ℝ) * ∫ q : Point3, g q := by
      simpa only [forwardLinear_apply] using hchange.symm
    _ = (1 / 2 : ℝ) * ∫ q in transformedSolid, f (inverseMap q) := by
      rw [MeasureTheory.integral_indicator transformed_measurable]

private theorem transformed_subset_box :
    transformedSolid ⊆
      Set.Icc (-1 : ℝ) 1 ×ˢ
        (Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) := by
  intro q hq
  rcases hq with ⟨hu₀, hu₁, hv₀, hv₁, hz₀, hz₁⟩
  have hu_sq : q.1 ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (q.1 + 1), sq_nonneg (q.1 - 1)]
  have hv_sq : q.2.1 ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (q.2.1 + 1), sq_nonneg (q.2.1 - 1)]
  have hz_le : q.2.2 ≤ 1 := by
    nlinarith
  exact ⟨⟨hu₀, hu₁⟩, ⟨⟨hv₀, hv₁⟩, hz₀, hz_le⟩⟩

private theorem transformed_box_compact :
    IsCompact
      (Set.Icc (-1 : ℝ) 1 ×ˢ
        (Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)) :=
  isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)

private theorem integral_transformed_eq_iterated
    (f : Point3 → ℝ) (hf : Continuous f) :
    (∫ q in transformedSolid, f q) =
      ∫ u in (-1 : ℝ)..1,
        ∫ v in (-1 : ℝ)..1,
          ∫ z in (0 : ℝ)..(u ^ 2 + v ^ 2) / 2,
            f (u, v, z) := by
  classical
  have hbox :
      IntegrableOn f
        (Set.Icc (-1 : ℝ) 1 ×ˢ
          (Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1))
        volume :=
    hf.continuousOn.integrableOn_compact transformed_box_compact
  have hfi : IntegrableOn f transformedSolid volume :=
    hbox.mono_set transformed_subset_box
  have hind : Integrable (transformedSolid.indicator f) volume :=
    (integrable_indicator_iff transformed_measurable).2 hfi
  change Integrable (transformedSolid.indicator f)
    (volume.prod (volume.prod volume)) at hind
  have hprod :
      (∫ q : Point3, transformedSolid.indicator f q
          ∂volume.prod (volume.prod volume)) =
        ∫ u : ℝ, ∫ v : ℝ, ∫ z : ℝ,
          transformedSolid.indicator f (u, v, z) := by
    rw [MeasureTheory.integral_prod _ hind]
    apply integral_congr_ae
    filter_upwards [hind.prod_right_ae] with u hu
    change
      (∫ vz : ℝ × ℝ, transformedSolid.indicator f (u, vz)
          ∂volume.prod volume) =
        ∫ v : ℝ, ∫ z : ℝ, transformedSolid.indicator f (u, v, z)
    rw [MeasureTheory.integral_prod _ hu]
  have hsections :
      (∫ u : ℝ, ∫ v : ℝ, ∫ z : ℝ,
        transformedSolid.indicator f (u, v, z)) =
        ∫ u in Set.Icc (-1 : ℝ) 1,
          ∫ v in Set.Icc (-1 : ℝ) 1,
            ∫ z in Set.Icc (0 : ℝ) ((u ^ 2 + v ^ 2) / 2),
              f (u, v, z) := by
    rw [← MeasureTheory.integral_indicator measurableSet_Icc]
    apply integral_congr_ae
    filter_upwards with u
    by_cases hu : u ∈ Set.Icc (-1 : ℝ) 1
    · rw [Set.indicator_of_mem hu]
      rw [← MeasureTheory.integral_indicator measurableSet_Icc]
      apply integral_congr_ae
      filter_upwards with v
      by_cases hv : v ∈ Set.Icc (-1 : ℝ) 1
      · rw [Set.indicator_of_mem hv]
        rw [← MeasureTheory.integral_indicator measurableSet_Icc]
        apply integral_congr_ae
        filter_upwards with z
        by_cases hz : z ∈ Set.Icc (0 : ℝ) ((u ^ 2 + v ^ 2) / 2)
        · have hsolid : (u, v, z) ∈ transformedSolid :=
            ⟨hu.1, hu.2, hv.1, hv.2, hz.1, hz.2⟩
          simp only [Set.indicator_of_mem hz,
            Set.indicator_of_mem hsolid]
        · have hnsolid : (u, v, z) ∉ transformedSolid := by
            intro hq
            exact hz ⟨hq.2.2.2.2.1, hq.2.2.2.2.2⟩
          simp [Set.indicator, hz, hnsolid]
      · have hvr :
            (Set.Icc (-1 : ℝ) 1).indicator
              (fun v =>
                ∫ z in Set.Icc (0 : ℝ) ((u ^ 2 + v ^ 2) / 2),
                  f (u, v, z)) v = 0 := by
          simp [Set.indicator, hv]
        rw [hvr, ← integral_zero]
        apply integral_congr_ae
        filter_upwards with z
        have hnsolid : (u, v, z) ∉ transformedSolid := by
          intro hq
          exact hv ⟨hq.2.2.1, hq.2.2.2.1⟩
        simp [Set.indicator, hnsolid]
    · have hur :
          (Set.Icc (-1 : ℝ) 1).indicator
            (fun u =>
              ∫ v in Set.Icc (-1 : ℝ) 1,
                ∫ z in Set.Icc (0 : ℝ) ((u ^ 2 + v ^ 2) / 2),
                  f (u, v, z)) u = 0 := by
        simp [Set.indicator, hu]
      rw [hur, ← integral_zero]
      apply integral_congr_ae
      filter_upwards with v
      rw [← integral_zero]
      apply integral_congr_ae
      filter_upwards with z
      have hnsolid : (u, v, z) ∉ transformedSolid := by
        intro hq
        exact hu ⟨hq.1, hq.2.1⟩
      simp [Set.indicator, hnsolid]
  calc
    (∫ q in transformedSolid, f q) =
        ∫ q : Point3, transformedSolid.indicator f q := by
      rw [MeasureTheory.integral_indicator transformed_measurable]
    _ = ∫ u : ℝ, ∫ v : ℝ, ∫ z : ℝ,
          transformedSolid.indicator f (u, v, z) := hprod
    _ = ∫ u in Set.Icc (-1 : ℝ) 1,
          ∫ v in Set.Icc (-1 : ℝ) 1,
            ∫ z in Set.Icc (0 : ℝ) ((u ^ 2 + v ^ 2) / 2),
              f (u, v, z) := hsections
    _ = ∫ u in (-1 : ℝ)..1,
          ∫ v in (-1 : ℝ)..1,
            ∫ z in (0 : ℝ)..(u ^ 2 + v ^ 2) / 2,
              f (u, v, z) := by
      rw [intervalIntegral.integral_of_le
        (by norm_num : (-1 : ℝ) ≤ 1)]
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
      intro u hu
      dsimp only
      rw [intervalIntegral.integral_of_le
        (by norm_num : (-1 : ℝ) ≤ 1)]
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
      intro v hv
      dsimp only
      have hzorder : 0 ≤ (u ^ 2 + v ^ 2) / 2 := by positivity
      rw [intervalIntegral.integral_of_le hzorder]
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc]

private theorem solid_subset_box :
    solid ⊆
      Set.Icc (-1 : ℝ) 1 ×ˢ
        (Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 2) := by
  intro p hp
  rcases hp with ⟨hs₀, hs₁, hd₀, hd₁, hz₀, hz₁⟩
  have hx₀ : -1 ≤ p.1 := by linarith
  have hx₁ : p.1 ≤ 1 := by linarith
  have hy₀ : -1 ≤ p.2.1 := by linarith
  have hy₁ : p.2.1 ≤ 1 := by linarith
  have hx_sq : p.1 ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (p.1 + 1), sq_nonneg (p.1 - 1)]
  have hy_sq : p.2.1 ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (p.2.1 + 1), sq_nonneg (p.2.1 - 1)]
  exact ⟨⟨hx₀, hx₁⟩, ⟨⟨hy₀, hy₁⟩, hz₀, hz₁.trans (by nlinarith)⟩⟩

private theorem solid_box_compact :
    IsCompact
      (Set.Icc (-1 : ℝ) 1 ×ˢ
        (Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 2)) :=
  isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)

private theorem coordinate_integrableOn_solid :
    IntegrableOn (fun p : Point3 => p.1 ^ 2) solid ∧
      IntegrableOn (fun p : Point3 => p.2.1 ^ 2) solid := by
  have hxcont : Continuous (fun p : Point3 => p.1 ^ 2) :=
    continuous_fst.pow 2
  have hycont : Continuous (fun p : Point3 => p.2.1 ^ 2) :=
    (continuous_fst.comp continuous_snd).pow 2
  constructor
  · exact
      (hxcont.continuousOn.integrableOn_compact solid_box_compact).mono_set
        solid_subset_box
  · exact
      (hycont.continuousOn.integrableOn_compact solid_box_compact).mono_set
        solid_subset_box

private theorem integral_poly4
    (c₀ c₁ c₂ c₃ c₄ a b : ℝ) :
    (∫ x in a..b,
        c₀ + c₁ * x + c₂ * x ^ 2 + c₃ * x ^ 3 + c₄ * x ^ 4) =
      c₀ * (b - a) +
        c₁ / 2 * (b ^ 2 - a ^ 2) +
        c₂ / 3 * (b ^ 3 - a ^ 3) +
        c₃ / 4 * (b ^ 4 - a ^ 4) +
        c₄ / 5 * (b ^ 5 - a ^ 5) := by
  let F : ℝ → ℝ := fun x =>
    c₀ * x + c₁ / 2 * x ^ 2 + c₂ / 3 * x ^ 3 +
      c₃ / 4 * x ^ 4 + c₄ / 5 * x ^ 5
  have hderiv (x : ℝ) :
      HasDerivAt F
        (c₀ + c₁ * x + c₂ * x ^ 2 + c₃ * x ^ 3 + c₄ * x ^ 4) x := by
    dsimp [F]
    convert
      (((((hasDerivAt_id x).const_mul c₀).add
          (((hasDerivAt_id x).pow 2).const_mul (c₁ / 2))).add
          (((hasDerivAt_id x).pow 3).const_mul (c₂ / 3))).add
          (((hasDerivAt_id x).pow 4).const_mul (c₃ / 4))).add
          (((hasDerivAt_id x).pow 5).const_mul (c₄ / 5))
      using 1 <;> norm_num <;> ring
  have hcont : Continuous (fun x : ℝ =>
      c₀ + c₁ * x + c₂ * x ^ 2 + c₃ * x ^ 3 + c₄ * x ^ 4) := by
    fun_prop
  calc
    (∫ x in a..b,
        c₀ + c₁ * x + c₂ * x ^ 2 + c₃ * x ^ 3 + c₄ * x ^ 4) =
        F b - F a :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x _hx => hderiv x)
        (hcont.intervalIntegrable a b)
    _ = _ := by
      dsimp [F]
      ring

theorem gap1 :
    inertiaZ = inertiaZX + inertiaZY := by
  unfold inertiaZ inertiaZX inertiaZY
  rw [add_comm]
  exact integral_add coordinate_integrableOn_solid.1
    coordinate_integrableOn_solid.2

theorem gap2 (x y u v : ℝ)
    (hu : u = x + y) (hv : v = x - y) :
    x = (u + v) / 2 := by
  linarith

theorem gap3 (x y u v : ℝ)
    (hu : u = x + y) (hv : v = x - y) :
    y = (u - v) / 2 := by
  linarith

theorem gap4 (x y z u v : ℝ)
    (hu : u = x + y) (hv : v = x - y)
    (hz : z = x ^ 2 + y ^ 2) :
    z = (u ^ 2 + v ^ 2) / 2 := by
  rw [hu, hv]
  rw [hz]
  ring

theorem gap5 :
    xyJacobian = (1 : ℝ) / 2 := by
  norm_num [xyJacobian, abs_of_nonneg]

theorem gap6 :
    inertiaZ =
      ∫ u in (-1 : ℝ)..1,
        ∫ v in (-1 : ℝ)..1,
          ∫ z in (0 : ℝ)..(u ^ 2 + v ^ 2) / 2,
            1 / 2 * (((u - v) / 2) ^ 2 + ((u + v) / 2) ^ 2) := by
  have hf : Continuous (fun p : Point3 => p.1 ^ 2 + p.2.1 ^ 2) := by
    fun_prop
  unfold inertiaZ
  rw [integral_solid_eq_half_transformed _ hf]
  rw [integral_transformed_eq_iterated]
  · rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u hu
    change
      1 / 2 *
          (∫ v in (-1 : ℝ)..1,
            ∫ z in (0 : ℝ)..(u ^ 2 + v ^ 2) / 2,
              (inverseMap (u, v, z)).1 ^ 2 +
                (inverseMap (u, v, z)).2.1 ^ 2) =
        ∫ v in (-1 : ℝ)..1,
          ∫ z in (0 : ℝ)..(u ^ 2 + v ^ 2) / 2,
            1 / 2 * (((u - v) / 2) ^ 2 + ((u + v) / 2) ^ 2)
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro v hv
    change
      1 / 2 *
          (∫ z in (0 : ℝ)..(u ^ 2 + v ^ 2) / 2,
            (inverseMap (u, v, z)).1 ^ 2 +
              (inverseMap (u, v, z)).2.1 ^ 2) =
        ∫ z in (0 : ℝ)..(u ^ 2 + v ^ 2) / 2,
          1 / 2 * (((u - v) / 2) ^ 2 + ((u + v) / 2) ^ 2)
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro z hz
    simp only [inverseMap]
    ring
  · exact hf.comp continuous_inverseMap

theorem gap7 :
    (∫ u in (-1 : ℝ)..1,
        ∫ v in (-1 : ℝ)..1,
          ∫ z in (0 : ℝ)..(u ^ 2 + v ^ 2) / 2,
            1 / 2 * (((u - v) / 2) ^ 2 + ((u + v) / 2) ^ 2)) =
      ∫ u in (-1 : ℝ)..1,
        ∫ v in (-1 : ℝ)..1, (u ^ 2 + v ^ 2) ^ 2 / 8 := by
  apply intervalIntegral.integral_congr
  intro u hu
  apply intervalIntegral.integral_congr
  intro v hv
  change
    (∫ _z in (0 : ℝ)..(u ^ 2 + v ^ 2) / 2,
      1 / 2 * (((u - v) / 2) ^ 2 + ((u + v) / 2) ^ 2)) =
      (u ^ 2 + v ^ 2) ^ 2 / 8
  rw [intervalIntegral.integral_const]
  simp only [smul_eq_mul, sub_zero]
  ring

theorem gap8 :
    (∫ u in (-1 : ℝ)..1,
        ∫ v in (-1 : ℝ)..1, (u ^ 2 + v ^ 2) ^ 2 / 8) =
      (14 : ℝ) / 45 := by
  have hv (u : ℝ) :
      (∫ v in (-1 : ℝ)..1, (u ^ 2 + v ^ 2) ^ 2 / 8) =
        u ^ 4 / 4 + u ^ 2 / 6 + 1 / 20 := by
    calc
      (∫ v in (-1 : ℝ)..1, (u ^ 2 + v ^ 2) ^ 2 / 8) =
          ∫ v in (-1 : ℝ)..1,
            u ^ 4 / 8 + 0 * v + (u ^ 2 / 4) * v ^ 2 +
              0 * v ^ 3 + (1 / 8) * v ^ 4 := by
        apply intervalIntegral.integral_congr
        intro v hv'
        ring
      _ = u ^ 4 / 4 + u ^ 2 / 6 + 1 / 20 := by
        rw [integral_poly4]
        norm_num
        ring
  calc
    (∫ u in (-1 : ℝ)..1,
        ∫ v in (-1 : ℝ)..1, (u ^ 2 + v ^ 2) ^ 2 / 8) =
        ∫ u in (-1 : ℝ)..1,
          u ^ 4 / 4 + u ^ 2 / 6 + 1 / 20 := by
      apply intervalIntegral.integral_congr
      intro u hu
      exact hv u
    _ = (14 : ℝ) / 45 := by
      convert
        integral_poly4 (1 / 20) 0 (1 / 6) 0 (1 / 4) (-1) 1
        using 1 <;> norm_num <;> ring

theorem gap9 :
    inertiaZ = (14 : ℝ) / 45 := by
  rw [gap6, gap7, gap8]

end

end ProofGap.Exercise4148
