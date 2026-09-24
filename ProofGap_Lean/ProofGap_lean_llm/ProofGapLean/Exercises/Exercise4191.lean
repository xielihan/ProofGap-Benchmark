import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4191

noncomputable section

open MeasureTheory Set

private abbrev Point3 := ℝ × ℝ × ℝ

def exterior : Set (ℝ × ℝ × ℝ) :=
  {z | 1 < z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2}

def radiusSquared (z : ℝ × ℝ × ℝ) : ℝ :=
  z.1 ^ 2 + z.2.1 ^ 2 + z.2.2 ^ 2

def modelWeight (p : ℝ) (z : ℝ × ℝ × ℝ) : ℝ :=
  1 / Real.rpow (radiusSquared z) p

def weightedIntegrand (phi : ℝ × ℝ × ℝ → ℝ) (p : ℝ)
    (z : ℝ × ℝ × ℝ) : ℝ :=
  phi z / Real.rpow (radiusSquared z) p

def modelIntegral (p : ℝ) : ℝ :=
  ∫ z in exterior, modelWeight p z

def absoluteWeightedIntegral
    (phi : ℝ × ℝ × ℝ → ℝ) (p : ℝ) : ℝ :=
  ∫ z in exterior, |phi z| / Real.rpow (radiusSquared z) p

def radialWeight (p r : ℝ) : ℝ :=
  1 / Real.rpow r (2 * p - 2)

private def model (p : ℝ) (q : Point3) : ℝ :=
  1 / Real.rpow (radiusSquared q) p

private def modelLIntegral (p : ℝ) : ENNReal :=
  ∫⁻ q in exterior, ENNReal.ofReal (model p q)

private def cylindricalSet : Set (ℝ × ℝ) :=
  {v | 0 < v.2 ∧ 1 < v.1 ^ 2 + v.2 ^ 2}

private def cylindricalKernel (p : ℝ) (v : ℝ × ℝ) : ENNReal :=
  ENNReal.ofReal
    (v.2 * (1 / Real.rpow (v.1 ^ 2 + v.2 ^ 2) p))

private def cylindricalLIntegral (p : ℝ) : ENNReal :=
  ∫⁻ v in cylindricalSet, cylindricalKernel p v

private def radialLIntegral (p : ℝ) : ENNReal :=
  ∫⁻ R in Ioi (1 : ℝ), ENNReal.ofReal (R ^ (2 - 2 * p : ℝ))

private theorem volume_point3 :
    (volume : Measure Point3) =
      (volume : Measure ℝ).prod
        ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
  rw [Measure.volume_eq_prod, Measure.volume_eq_prod]

private theorem exterior_measurable : MeasurableSet exterior := by
  unfold exterior
  measurability

private theorem cylindricalSet_measurable :
    MeasurableSet cylindricalSet := by
  unfold cylindricalSet
  measurability

private theorem model_measurable (p : ℝ) :
    Measurable (model p) := by
  have hrpow : Measurable (fun t : ℝ => Real.rpow t p) := by
    apply measurable_of_continuousOn_compl_singleton 0
    exact continuousOn_id.rpow_const
      (fun t ht => Or.inl (by simpa using ht))
  unfold model radiusSquared
  exact measurable_const.div
    (hrpow.comp
      (((measurable_fst.pow_const 2).add
        (measurable_snd.fst.pow_const 2)).add
          (measurable_snd.snd.pow_const 2)))

private theorem cylindricalKernel_measurable (p : ℝ) :
    Measurable (cylindricalKernel p) := by
  apply ENNReal.measurable_ofReal.comp
  have hrpow : Measurable (fun t : ℝ => Real.rpow t p) := by
    apply measurable_of_continuousOn_compl_singleton 0
    exact continuousOn_id.rpow_const
      (fun t ht => Or.inl (by simpa using ht))
  exact measurable_snd.mul
    (measurable_const.div
      (hrpow.comp
        ((measurable_fst.pow_const 2).add
          (measurable_snd.pow_const 2))))

private theorem model_nonneg (p : ℝ) (q : Point3) :
    0 ≤ model p q := by
  unfold model
  exact one_div_nonneg.mpr
    (Real.rpow_nonneg
      (by
        unfold radiusSquared
        positivity) p)

private theorem cylindricalKernel_nonneg_real
    (p : ℝ) {v : ℝ × ℝ} (hv : 0 ≤ v.2) :
    0 ≤ v.2 * (1 / Real.rpow (v.1 ^ 2 + v.2 ^ 2) p) := by
  exact mul_nonneg hv
    (one_div_nonneg.mpr
      (Real.rpow_nonneg
        (add_nonneg (sq_nonneg v.1) (sq_nonneg v.2)) p))

private theorem yz_radius (x : ℝ) (u : ℝ × ℝ) :
    radiusSquared (x, polarCoord.symm u) =
      x ^ 2 + u.1 ^ 2 := by
  unfold radiusSquared
  simp only [polarCoord_symm_apply]
  nlinarith [Real.sin_sq_add_cos_sq u.2]

private theorem theta_measure :
    (volume : Measure ℝ) (Ioo (-Real.pi) Real.pi) =
      ENNReal.ofReal (2 * Real.pi) := by
  rw [Real.volume_Ioo]
  apply congrArg ENNReal.ofReal
  ring

private theorem first_polar_section (p x : ℝ) :
    (∫⁻ yz : ℝ × ℝ,
        exterior.indicator
          (fun q : Point3 => ENNReal.ofReal (model p q))
          (x, yz)) =
      (∫⁻ ρ in Ioi (0 : ℝ),
          cylindricalSet.indicator (cylindricalKernel p) (x, ρ)) *
        ENNReal.ofReal (2 * Real.pi) := by
  let k : ℝ × ℝ → ENNReal := fun yz =>
    exterior.indicator
      (fun q : Point3 => ENNReal.ofReal (model p q)) (x, yz)
  calc
    (∫⁻ yz : ℝ × ℝ, k yz) =
        ∫⁻ u in polarCoord.target,
          ENNReal.ofReal u.1 • k (polarCoord.symm u) :=
      (lintegral_comp_polarCoord_symm k).symm
    _ =
        ∫⁻ u in
            Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
          cylindricalSet.indicator (cylindricalKernel p)
            (x, u.1) := by
      apply setLIntegral_congr_fun polarCoord.open_target.measurableSet
      intro u hu
      have hρ : 0 < u.1 := hu.1
      have hmem :
          polarCoord.symm u |> fun yz => (x, yz) ∈ exterior ↔
            (x, u.1) ∈ cylindricalSet := by
        change
          1 < radiusSquared (x, polarCoord.symm u) ↔
            0 < u.1 ∧ 1 < x ^ 2 + u.1 ^ 2
        rw [yz_radius]
        simp only [hρ, true_and]
      change
        ENNReal.ofReal u.1 •
            exterior.indicator
              (fun q : Point3 => ENNReal.ofReal (model p q))
              (x, polarCoord.symm u) =
          cylindricalSet.indicator (cylindricalKernel p)
            (x, u.1)
      by_cases hext : (x, polarCoord.symm u) ∈ exterior
      · have hcyl : (x, u.1) ∈ cylindricalSet := hmem.mp hext
        rw [indicator_of_mem hext, indicator_of_mem hcyl]
        simp only [smul_eq_mul]
        rw [← ENNReal.ofReal_mul hρ.le]
        apply congrArg ENNReal.ofReal
        change
          u.1 * model p (x, polarCoord.symm u) =
            u.1 * (1 / Real.rpow (x ^ 2 + u.1 ^ 2) p)
        unfold model
        rw [yz_radius]
      · have hcyl : (x, u.1) ∉ cylindricalSet := by
          intro h
          exact hext (hmem.mpr h)
        rw [indicator_of_notMem hext, indicator_of_notMem hcyl]
        simp
    _ =
        (∫⁻ ρ in Ioi (0 : ℝ),
            cylindricalSet.indicator (cylindricalKernel p) (x, ρ)) *
          (volume : Measure ℝ) (Ioo (-Real.pi) Real.pi) := by
      rw [Measure.volume_eq_prod]
      rw [MeasureTheory.setLIntegral_prod]
      · simp_rw [setLIntegral_const]
        rw [theta_measure]
        apply lintegral_mul_const'
        exact ENNReal.ofReal_ne_top
      · exact
          ((cylindricalKernel_measurable p).indicator
            cylindricalSet_measurable).comp
              (measurable_const.prodMk measurable_fst)
              |>.aemeasurable
    _ =
        (∫⁻ ρ in Ioi (0 : ℝ),
            cylindricalSet.indicator (cylindricalKernel p) (x, ρ)) *
          ENNReal.ofReal (2 * Real.pi) := by
      rw [theta_measure]

private theorem modelLIntegral_eq_cylindrical (p : ℝ) :
    modelLIntegral p =
      cylindricalLIntegral p * ENNReal.ofReal (2 * Real.pi) := by
  let K : Point3 → ENNReal := fun q => ENNReal.ofReal (model p q)
  unfold modelLIntegral
  change (∫⁻ q in exterior, K q) = _
  rw [← lintegral_indicator exterior_measurable]
  rw [volume_point3]
  rw [lintegral_prod]
  · dsimp [K]
    simp_rw [← Measure.volume_eq_prod ℝ ℝ]
    simp_rw [first_polar_section p]
    rw [lintegral_mul_const'
      (ENNReal.ofReal (2 * Real.pi))
      (fun x : ℝ =>
        ∫⁻ ρ in Ioi (0 : ℝ),
          cylindricalSet.indicator (cylindricalKernel p) (x, ρ))]
    · apply congrArg
        (fun t : ENNReal =>
          t * ENNReal.ofReal (2 * Real.pi))
      unfold cylindricalLIntegral
      rw [← lintegral_indicator cylindricalSet_measurable]
      rw [Measure.volume_eq_prod]
      rw [lintegral_prod _ <|
        ((cylindricalKernel_measurable p).indicator
          cylindricalSet_measurable).aemeasurable]
      apply lintegral_congr
      intro x
      rw [← lintegral_indicator measurableSet_Ioi]
      apply lintegral_congr
      intro ρ
      by_cases hcyl : (x, ρ) ∈ cylindricalSet
      · have hρ : ρ ∈ Ioi (0 : ℝ) := hcyl.1
        simp [hcyl, hρ]
      · simp [hcyl]
    · exact ENNReal.ofReal_ne_top
  · exact
      ((model_measurable p).ennreal_ofReal.indicator
        exterior_measurable).aemeasurable

private theorem polar_rpow_identity (p R : ℝ) (hR : 0 < R) :
    R * (1 / Real.rpow (R ^ 2) p) =
      R ^ (1 - 2 * p : ℝ) := by
  have hsq :
      Real.rpow (R ^ 2) p = R ^ (2 * p : ℝ) := by
    calc
      Real.rpow (R ^ 2) p =
          Real.rpow (Real.rpow R (2 : ℝ)) p := by
        exact congrArg (fun t : ℝ => Real.rpow t p)
          (Real.rpow_natCast R 2).symm
      _ = Real.rpow R ((2 : ℝ) * p) :=
        (Real.rpow_mul hR.le 2 p).symm
  rw [hsq, one_div, ← Real.rpow_neg hR.le]
  calc
    R * R ^ (-(2 * p) : ℝ) =
        R ^ (1 : ℝ) * R ^ (-(2 * p) : ℝ) := by
      rw [Real.rpow_one]
    _ = R ^ ((1 : ℝ) + -(2 * p)) := by
      rw [Real.rpow_add hR]
    _ = R ^ (1 - 2 * p : ℝ) := by ring

private theorem spherical_rpow_identity
    (p R α : ℝ) (hR : 0 < R) :
    R * (R * Real.sin α *
        (1 / Real.rpow (R ^ 2) p)) =
      R ^ (2 - 2 * p : ℝ) * Real.sin α := by
  rw [show
    R * (R * Real.sin α *
        (1 / Real.rpow (R ^ 2) p)) =
      R * (R * (1 / Real.rpow (R ^ 2) p)) *
        Real.sin α by ring]
  rw [polar_rpow_identity p R hR]
  calc
    R * R ^ (1 - 2 * p : ℝ) * Real.sin α =
        R ^ (1 : ℝ) * R ^ (1 - 2 * p : ℝ) *
          Real.sin α := by rw [Real.rpow_one]
    _ = R ^ ((1 : ℝ) + (1 - 2 * p)) *
          Real.sin α := by rw [Real.rpow_add hR]
    _ = R ^ (2 - 2 * p : ℝ) * Real.sin α := by ring

private theorem sin_pos_iff_angle
    {α : ℝ} (hα : α ∈ Ioo (-Real.pi) Real.pi) :
    0 < Real.sin α ↔ α ∈ Ioo (0 : ℝ) Real.pi := by
  constructor
  · intro hs
    constructor
    · by_contra h
      have hnonpos : α ≤ 0 := le_of_not_gt h
      have :=
        Real.sin_nonpos_of_nonpos_of_neg_pi_le
          hnonpos hα.1.le
      linarith
    · exact hα.2
  · exact Real.sin_pos_of_mem_Ioo

private theorem cylindrical_polar_mem
    (u : ℝ × ℝ) (hu : u ∈ polarCoord.target) :
    polarCoord.symm u ∈ cylindricalSet ↔
      u ∈ Ioi (1 : ℝ) ×ˢ Ioo (0 : ℝ) Real.pi := by
  have hR : 0 < u.1 := hu.1
  have htrig :
      (polarCoord.symm u).1 ^ 2 +
          (polarCoord.symm u).2 ^ 2 = u.1 ^ 2 := by
    simp only [polarCoord_symm_apply]
    nlinarith [Real.sin_sq_add_cos_sq u.2]
  have hrho :
      0 < (polarCoord.symm u).2 ↔
        u.2 ∈ Ioo (0 : ℝ) Real.pi := by
    simp only [polarCoord_symm_apply]
    rw [mul_pos_iff_of_pos_left hR]
    exact sin_pos_iff_angle hu.2
  have hradial : 1 < u.1 ^ 2 ↔ 1 < u.1 := by
    constructor <;> intro h <;>
      nlinarith [sq_nonneg (u.1 - 1)]
  unfold cylindricalSet
  simp only [mem_setOf_eq, mem_prod, mem_Ioi]
  rw [hrho, htrig, hradial]
  tauto

private theorem sin_lintegral :
    (∫⁻ α in Ioo (0 : ℝ) Real.pi,
        ENNReal.ofReal (Real.sin α)) = ENNReal.ofReal 2 := by
  have hint :
      IntegrableOn Real.sin (Ioo (0 : ℝ) Real.pi) volume := by
    have hinterval :
        IntervalIntegrable Real.sin volume (0 : ℝ) Real.pi :=
      Real.continuous_sin.intervalIntegrable 0 Real.pi
    exact
      (intervalIntegrable_iff_integrableOn_Ioo_of_le
        Real.pi_pos.le).mp hinterval
  have hnonneg :
      0 ≤ᵐ[(volume : Measure ℝ).restrict
        (Ioo (0 : ℝ) Real.pi)] Real.sin := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with α hα
    exact (Real.sin_pos_of_mem_Ioo hα).le
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnonneg]
  apply congrArg ENNReal.ofReal
  calc
    (∫ α in Ioo (0 : ℝ) Real.pi, Real.sin α) =
        ∫ α in Ioc (0 : ℝ) Real.pi, Real.sin α :=
      setIntegral_congr_set Ioo_ae_eq_Ioc
    _ = ∫ α in (0 : ℝ)..Real.pi, Real.sin α :=
      (intervalIntegral.integral_of_le Real.pi_pos.le).symm
    _ = 2 := by
      rw [integral_sin, Real.cos_zero, Real.cos_pi]
      norm_num

private theorem cylindricalLIntegral_eq_radial (p : ℝ) :
    cylindricalLIntegral p =
      radialLIntegral p * ENNReal.ofReal 2 := by
  let P : Set (ℝ × ℝ) :=
    Ioi (1 : ℝ) ×ˢ Ioo (0 : ℝ) Real.pi
  have hP : MeasurableSet P :=
    measurableSet_Ioi.prod measurableSet_Ioo
  unfold cylindricalLIntegral
  rw [← lintegral_indicator cylindricalSet_measurable]
  rw [← lintegral_comp_polarCoord_symm]
  have hrewrite :
      (∫⁻ u in polarCoord.target,
          ENNReal.ofReal u.1 •
            cylindricalSet.indicator (cylindricalKernel p)
              (polarCoord.symm u)) =
        ∫⁻ u in polarCoord.target,
          P.indicator
            (fun v =>
              ENNReal.ofReal (v.1 ^ (2 - 2 * p : ℝ)) *
                ENNReal.ofReal (Real.sin v.2)) u := by
    apply setLIntegral_congr_fun polarCoord.open_target.measurableSet
    intro u hu
    have hR : 0 < u.1 := hu.1
    have hmem :=
      cylindrical_polar_mem u hu
    by_cases hcyl : polarCoord.symm u ∈ cylindricalSet
    · have hparam : u ∈ P := hmem.mp hcyl
      change
        ENNReal.ofReal u.1 •
            cylindricalSet.indicator (cylindricalKernel p)
              (polarCoord.symm u) =
          P.indicator
            (fun v =>
              ENNReal.ofReal (v.1 ^ (2 - 2 * p : ℝ)) *
                ENNReal.ofReal (Real.sin v.2)) u
      rw [indicator_of_mem hcyl, indicator_of_mem hparam]
      simp only [smul_eq_mul]
      have hsin : 0 ≤ Real.sin u.2 :=
        (Real.sin_pos_of_mem_Ioo hparam.2).le
      change
        ENNReal.ofReal u.1 *
            ENNReal.ofReal
              ((polarCoord.symm u).2 *
                (1 / Real.rpow
                  ((polarCoord.symm u).1 ^ 2 +
                    (polarCoord.symm u).2 ^ 2) p)) =
          ENNReal.ofReal (u.1 ^ (2 - 2 * p : ℝ)) *
            ENNReal.ofReal (Real.sin u.2)
      rw [← ENNReal.ofReal_mul hR.le]
      rw [← ENNReal.ofReal_mul
        (Real.rpow_nonneg hR.le (2 - 2 * p : ℝ))]
      apply congrArg ENNReal.ofReal
      have htrig :
          (polarCoord.symm u).1 ^ 2 +
              (polarCoord.symm u).2 ^ 2 = u.1 ^ 2 := by
        simp only [polarCoord_symm_apply]
        nlinarith [Real.sin_sq_add_cos_sq u.2]
      rw [htrig]
      simp only [polarCoord_symm_apply]
      exact spherical_rpow_identity p u.1 u.2 hR
    · have hparam : u ∉ P := by
        intro h
        exact hcyl (hmem.mpr h)
      change
        ENNReal.ofReal u.1 •
            cylindricalSet.indicator (cylindricalKernel p)
              (polarCoord.symm u) =
          P.indicator
            (fun v =>
              ENNReal.ofReal (v.1 ^ (2 - 2 * p : ℝ)) *
                ENNReal.ofReal (Real.sin v.2)) u
      rw [indicator_of_notMem hcyl, indicator_of_notMem hparam]
      simp
  rw [hrewrite, setLIntegral_indicator hP]
  have hsubset : P ⊆ polarCoord.target := by
    rintro u ⟨hR, hα⟩
    constructor
    · change 0 < u.1
      exact zero_lt_one.trans hR
    · exact ⟨by linarith [hα.1, Real.pi_pos], hα.2⟩
  rw [inter_eq_left.mpr hsubset]
  change
    (∫⁻ u in
        Ioi (1 : ℝ) ×ˢ Ioo (0 : ℝ) Real.pi,
      ENNReal.ofReal (u.1 ^ (2 - 2 * p : ℝ)) *
        ENNReal.ofReal (Real.sin u.2)) =
      radialLIntegral p * ENNReal.ofReal 2
  rw [Measure.volume_eq_prod]
  have hpowMeas :
      Measurable (fun R : ℝ => R ^ (2 - 2 * p : ℝ)) := by
    apply measurable_of_continuousOn_compl_singleton 0
    exact continuousOn_id.rpow_const
      (fun R hR => Or.inl (by simpa using hR))
  rw [MeasureTheory.setLIntegral_prod]
  · have hsinMeas :
        AEMeasurable (fun α : ℝ =>
          ENNReal.ofReal (Real.sin α))
          ((volume : Measure ℝ).restrict
            (Ioo (0 : ℝ) Real.pi)) :=
      (ENNReal.measurable_ofReal.comp
        Real.continuous_sin.measurable).aemeasurable
    have hinner (R : ℝ) :
        (∫⁻ α in Ioo (0 : ℝ) Real.pi,
            ENNReal.ofReal (R ^ (2 - 2 * p : ℝ)) *
              ENNReal.ofReal (Real.sin α)) =
          ENNReal.ofReal (R ^ (2 - 2 * p : ℝ)) *
            ENNReal.ofReal 2 := by
      rw [lintegral_const_mul''
        (ENNReal.ofReal (R ^ (2 - 2 * p : ℝ))) hsinMeas,
        sin_lintegral]
    simp_rw [hinner]
    have hradMeas :
        AEMeasurable
          (fun R : ℝ =>
            ENNReal.ofReal (R ^ (2 - 2 * p : ℝ)))
          ((volume : Measure ℝ).restrict (Ioi (1 : ℝ))) := by
      apply AEMeasurable.restrict
      exact
        (ENNReal.measurable_ofReal.comp hpowMeas).aemeasurable
    rw [lintegral_mul_const'' (ENNReal.ofReal 2) hradMeas]
    rfl
  · exact
      (((ENNReal.measurable_ofReal.comp hpowMeas).comp
                measurable_fst).mul
        (ENNReal.measurable_ofReal.comp
          (Real.continuous_sin.measurable.comp measurable_snd))).aemeasurable

private theorem radialLIntegral_ne_top_iff (p : ℝ) :
    radialLIntegral p ≠ ⊤ ↔ 3 / 2 < p := by
  unfold radialLIntegral
  have hmeas :
      AEStronglyMeasurable
        (fun R : ℝ => R ^ (2 - 2 * p : ℝ))
        (volume.restrict (Ioi (1 : ℝ))) := by
    exact
      (continuousOn_id.rpow_const
        (fun R hR =>
          Or.inl (ne_of_gt (zero_lt_one.trans hR)))).aestronglyMeasurable
        measurableSet_Ioi
  have hnonneg :
      0 ≤ᵐ[volume.restrict (Ioi (1 : ℝ))]
        (fun R : ℝ => R ^ (2 - 2 * p : ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with R hR
    exact Real.rpow_nonneg (zero_lt_one.trans hR).le _
  rw [lintegral_ofReal_ne_top_iff_integrable hmeas hnonneg]
  change
    IntegrableOn (fun R : ℝ => R ^ (2 - 2 * p : ℝ))
      (Ioi (1 : ℝ)) volume ↔ 3 / 2 < p
  rw [integrableOn_Ioi_rpow_iff zero_lt_one]
  constructor <;> intro h <;> linarith

private theorem modelLIntegral_ne_top_iff (p : ℝ) :
    modelLIntegral p ≠ ⊤ ↔ 3 / 2 < p := by
  rw [modelLIntegral_eq_cylindrical,
    cylindricalLIntegral_eq_radial]
  have htwo0 : ENNReal.ofReal (2 : ℝ) ≠ 0 := by norm_num
  have htwoTop : ENNReal.ofReal (2 : ℝ) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have hangle0 :
      ENNReal.ofReal (2 * Real.pi) ≠ 0 := by
    exact ENNReal.ofReal_ne_zero_iff.mpr
      (mul_pos (by norm_num) Real.pi_pos)
  have hangleTop :
      ENNReal.ofReal (2 * Real.pi) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  constructor
  · intro h
    apply (radialLIntegral_ne_top_iff p).mp
    intro htop
    apply h
    apply ENNReal.mul_eq_top.mpr
    exact Or.inr
      ⟨ENNReal.mul_eq_top.mpr (Or.inr ⟨htop, htwo0⟩),
        hangle0⟩
  · intro hp
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        ((radialLIntegral_ne_top_iff p).mpr hp) htwoTop)
      hangleTop

private theorem model_integrable_iff (p : ℝ) :
    IntegrableOn (model p) exterior volume ↔ 3 / 2 < p := by
  have hnonneg :
      0 ≤ᵐ[volume.restrict exterior] model p := by
    exact Filter.Eventually.of_forall (model_nonneg p)
  rw [← modelLIntegral_ne_top_iff p]
  unfold modelLIntegral
  exact
    (lintegral_ofReal_ne_top_iff_integrable
      (model_measurable p).aestronglyMeasurable hnonneg).symm

private theorem integrand_measurable
    (φ : Point3 → ℝ) (p : ℝ) (hφ : Measurable φ) :
    Measurable (weightedIntegrand φ p) := by
  have hrpow : Measurable (fun t : ℝ => Real.rpow t p) := by
    apply measurable_of_continuousOn_compl_singleton 0
    exact continuousOn_id.rpow_const
      (fun t ht => Or.inl (by simpa using ht))
  unfold weightedIntegrand radiusSquared
  exact hφ.div
    (hrpow.comp
      (((measurable_fst.pow_const 2).add
        (measurable_snd.fst.pow_const 2)).add
          (measurable_snd.snd.pow_const 2)))

private theorem integrand_norm_eq
    (φ : Point3 → ℝ) (p : ℝ) {q : Point3} (hq : q ∈ exterior) :
    ‖weightedIntegrand φ p q‖ = |φ q| * model p q := by
  have hradius : 0 < radiusSquared q := by
    change 1 < radiusSquared q at hq
    linarith
  have hpow : 0 < Real.rpow (radiusSquared q) p :=
    Real.rpow_pos_of_pos hradius p
  unfold weightedIntegrand model
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hpow]
  ring

private theorem weighted_integrable_iff_bounds
    (φ : Point3 → ℝ) (p m M : ℝ)
    (hφ : Measurable φ)
    (hm : 0 < m) (hM : 0 < M)
    (hbound : ∀ q ∈ exterior, m ≤ |φ q| ∧ |φ q| ≤ M) :
    IntegrableOn (weightedIntegrand φ p) exterior MeasureTheory.volume ↔ 3 / 2 < p := by
  constructor
  · intro hint
    have hmodel : IntegrableOn (model p) exterior volume := by
      have hscaled :
          IntegrableOn
            (fun q : Point3 => (1 / m) * weightedIntegrand φ p q)
            exterior volume :=
        hint.const_mul (1 / m)
      apply Integrable.mono hscaled
        (model_measurable p).aestronglyMeasurable
      filter_upwards [ae_restrict_mem exterior_measurable] with q hq
      have hmodel0 := model_nonneg p q
      have hlower := (hbound q hq).1
      have hmle :
          model p q ≤ (1 / m) * (|φ q| * model p q) := by
        have hscale : 1 ≤ (1 / m) * |φ q| := by
          have hdiv : 1 ≤ |φ q| / m :=
            (le_div_iff₀ hm).mpr (by simpa using hlower)
          simpa [div_eq_mul_inv, one_div, mul_comm] using hdiv
        nlinarith
      rw [Real.norm_eq_abs, abs_of_nonneg hmodel0]
      rw [norm_mul, Real.norm_eq_abs,
        abs_of_pos (one_div_pos.mpr hm)]
      rw [integrand_norm_eq φ p hq]
      simpa [mul_assoc] using hmle
    exact (model_integrable_iff p).mp hmodel
  · intro hp
    have hmodel :
        IntegrableOn (model p) exterior volume :=
      (model_integrable_iff p).mpr hp
    have hscaled :
        IntegrableOn (fun q : Point3 => M * model p q)
          exterior volume :=
      hmodel.const_mul M
    apply Integrable.mono hscaled
      (integrand_measurable φ p hφ).aestronglyMeasurable
    filter_upwards [ae_restrict_mem exterior_measurable] with q hq
    rw [integrand_norm_eq φ p hq]
    have hmodel0 := model_nonneg p q
    have hupper := (hbound q hq).2
    calc
      |φ q| * model p q ≤ M * model p q :=
        mul_le_mul_of_nonneg_right hupper hmodel0
      _ = ‖M * model p q‖ := by
        rw [norm_mul, Real.norm_eq_abs, abs_of_pos hM,
          Real.norm_eq_abs, abs_of_nonneg hmodel0]

private theorem radiusSquared_pos {z : Point3} (hz : z ∈ exterior) :
    0 < radiusSquared z := by
  change 1 < radiusSquared z at hz
  linarith

private theorem absolute_weighted_integrable
    (phi : Point3 → ℝ) (M p : ℝ)
    (hp : (3 / 2 : ℝ) < p)
    (hphi : Measurable phi)
    (hM : ∀ z, |phi z| ≤ M) :
    IntegrableOn
      (fun z => |phi z| / Real.rpow (radiusSquared z) p)
      exterior := by
  have hM0 : 0 ≤ M :=
    (abs_nonneg (phi (0, 0, 0))).trans (hM (0, 0, 0))
  have hmodel : IntegrableOn (model p) exterior :=
    (model_integrable_iff p).2 hp
  have hscaled :
      IntegrableOn (fun z : Point3 => M * model p z) exterior :=
    hmodel.const_mul M
  apply Integrable.mono hscaled
    (integrand_measurable (fun z => |phi z|) p
      (continuous_abs.measurable.comp hphi)).aestronglyMeasurable
  filter_upwards [ae_restrict_mem exterior_measurable] with z hz
  rw [integrand_norm_eq (fun z => |phi z|) p hz, abs_abs]
  have hmodel0 := model_nonneg p z
  calc
    |phi z| * model p z ≤ M * model p z :=
      mul_le_mul_of_nonneg_right (hM z) hmodel0
    _ = ‖M * model p z‖ := by
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hM0,
        Real.norm_eq_abs, abs_of_nonneg hmodel0]

private theorem radialWeight_eq_rpow
    (p r : ℝ) (hr : 0 < r) :
    radialWeight p r = r ^ (2 - 2 * p : ℝ) := by
  unfold radialWeight
  rw [one_div]
  calc
    (Real.rpow r (2 * p - 2))⁻¹ =
        Real.rpow r (-(2 * p - 2)) :=
      (Real.rpow_neg hr.le (2 * p - 2)).symm
    _ = Real.rpow r (2 - 2 * p) := by
      congr 1
      ring

private theorem publicRadialIntegral_toReal (p : ℝ) :
    (∫ r in Ici (1 : ℝ), radialWeight p r) =
      (radialLIntegral p).toReal := by
  have hnonneg :
      0 ≤ᵐ[(volume : Measure ℝ).restrict (Ici (1 : ℝ))]
        radialWeight p := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with r hr
    rw [radialWeight_eq_rpow p r (zero_lt_one.trans_le hr)]
    exact Real.rpow_nonneg (zero_lt_one.trans_le hr).le _
  have hmeas :
      AEStronglyMeasurable (radialWeight p)
        ((volume : Measure ℝ).restrict (Ici (1 : ℝ))) := by
    have hrpow :
        Measurable (fun r : ℝ => Real.rpow r (2 * p - 2)) := by
      apply measurable_of_continuousOn_compl_singleton 0
      exact continuousOn_id.rpow_const
        (fun r hr => Or.inl (by simpa using hr))
    unfold radialWeight
    exact (measurable_const.div hrpow).aestronglyMeasurable
  calc
    (∫ r in Ici (1 : ℝ), radialWeight p r) =
        ENNReal.toReal
          (∫⁻ r in Ici (1 : ℝ),
            ENNReal.ofReal (radialWeight p r)) :=
      integral_eq_lintegral_of_nonneg_ae hnonneg hmeas
    _ = ENNReal.toReal
          (∫⁻ r in Ioi (1 : ℝ),
            ENNReal.ofReal (radialWeight p r)) := by
      congr 1
      exact setLIntegral_congr Ioi_ae_eq_Ici.symm
    _ = ENNReal.toReal
          (∫⁻ r in Ioi (1 : ℝ),
            ENNReal.ofReal (r ^ (2 - 2 * p : ℝ))) := by
      congr 1
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro r hr
      dsimp only
      rw [radialWeight_eq_rpow p r (zero_lt_one.trans hr)]
    _ = (radialLIntegral p).toReal := rfl

private theorem publicModelIntegral_toReal (p : ℝ) :
    modelIntegral p = (modelLIntegral p).toReal := by
  change
    (∫ z in exterior, model p z) =
      (modelLIntegral p).toReal
  exact integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (model_nonneg p))
    (model_measurable p).aestronglyMeasurable

private theorem modelIntegral_eq_radial (p : ℝ) :
    modelIntegral p =
      4 * Real.pi *
        ∫ r in Ici (1 : ℝ), radialWeight p r := by
  rw [publicModelIntegral_toReal,
    modelLIntegral_eq_cylindrical,
    cylindricalLIntegral_eq_radial,
    ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 2),
    ENNReal.toReal_ofReal
      (mul_nonneg (by norm_num) Real.pi_pos.le),
    ← publicRadialIntegral_toReal]
  ring

private theorem angularIntegral_eq (p : ℝ) :
    (∫ azimuth in (0 : ℝ)..2 * Real.pi,
        ∫ latitude in (-Real.pi / 2)..Real.pi / 2,
          (∫ r in Set.Ici (1 : ℝ), radialWeight p r) *
            Real.cos latitude) =
      4 * Real.pi *
        ∫ r in Set.Ici (1 : ℝ), radialWeight p r := by
  let A : ℝ := ∫ r in Ici (1 : ℝ), radialWeight p r
  have hlat :
      (∫ latitude in (-Real.pi / 2)..Real.pi / 2,
          A * Real.cos latitude) = 2 * A := by
    rw [intervalIntegral.integral_const_mul,
      integral_cos]
    rw [Real.sin_pi_div_two,
      show -Real.pi / 2 = -(Real.pi / 2) by ring,
      Real.sin_neg, Real.sin_pi_div_two]
    ring
  change
    (∫ azimuth in (0 : ℝ)..2 * Real.pi,
      ∫ latitude in (-Real.pi / 2)..Real.pi / 2,
        A * Real.cos latitude) =
      4 * Real.pi * A
  rw [hlat]
  rw [intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

theorem gap1 (phi : ℝ × ℝ × ℝ → ℝ) (m p : ℝ)
    (z : ℝ × ℝ × ℝ) (hz : z ∈ exterior)
    (hm : ∀ w, m ≤ |phi w|) :
    m / Real.rpow (radiusSquared z) p ≤
      |phi z| / Real.rpow (radiusSquared z) p := by
  apply (div_le_div_iff_of_pos_right
    (Real.rpow_pos_of_pos (radiusSquared_pos hz) p)).2
  exact hm z

theorem gap2 (phi : ℝ × ℝ × ℝ → ℝ) (M p : ℝ)
    (z : ℝ × ℝ × ℝ) (hz : z ∈ exterior)
    (hM : ∀ w, |phi w| ≤ M) :
    |phi z| / Real.rpow (radiusSquared z) p ≤
      M / Real.rpow (radiusSquared z) p := by
  apply (div_le_div_iff_of_pos_right
    (Real.rpow_pos_of_pos (radiusSquared_pos hz) p)).2
  exact hM z

theorem gap3 (phi : ℝ × ℝ × ℝ → ℝ) (m M p : ℝ)
    (z : ℝ × ℝ × ℝ) (hz : z ∈ exterior)
    (hm : ∀ w, m ≤ |phi w|)
    (hM : ∀ w, |phi w| ≤ M) :
    m / Real.rpow (radiusSquared z) p ≤
      M / Real.rpow (radiusSquared z) p :=
  (gap1 phi m p z hz hm).trans (gap2 phi M p z hz hM)

theorem gap4 (phi : ℝ × ℝ × ℝ → ℝ) (m p : ℝ)
    (hp : (3 / 2 : ℝ) < p) (hm0 : 0 < m)
    (hphi : Measurable phi)
    (hm : ∀ z, m ≤ |phi z|)
    (habs : IntegrableOn
      (fun z => |phi z| /
        Real.rpow (radiusSquared z) p) exterior) :
    m * modelIntegral p ≤ absoluteWeightedIntegral phi p := by
  have hmodel :
      IntegrableOn (modelWeight p) exterior := by
    change IntegrableOn (model p) exterior
    exact (model_integrable_iff p).2 hp
  unfold modelIntegral absoluteWeightedIntegral
  rw [← integral_const_mul]
  apply setIntegral_mono_on (hmodel.const_mul m) habs
    exterior_measurable
  intro z hz
  simpa [modelWeight, div_eq_mul_inv] using
    gap1 phi m p z hz hm

theorem gap5 (phi : ℝ × ℝ × ℝ → ℝ) (M p : ℝ)
    (hp : (3 / 2 : ℝ) < p)
    (hphi : Measurable phi)
    (hM : ∀ z, |phi z| ≤ M) :
    absoluteWeightedIntegral phi p ≤ M * modelIntegral p := by
  have hmodel :
      IntegrableOn (modelWeight p) exterior := by
    change IntegrableOn (model p) exterior
    exact (model_integrable_iff p).2 hp
  have habs :=
    absolute_weighted_integrable phi M p hp hphi hM
  unfold modelIntegral absoluteWeightedIntegral
  rw [← integral_const_mul]
  apply setIntegral_mono_on habs (hmodel.const_mul M)
    exterior_measurable
  intro z hz
  simpa [modelWeight, div_eq_mul_inv] using
    gap2 phi M p z hz hM

theorem gap6 (phi : ℝ × ℝ × ℝ → ℝ) (m M p : ℝ)
    (hp : (3 / 2 : ℝ) < p) (hm0 : 0 < m)
    (hm : ∀ z, m ≤ |phi z|)
    (hM : ∀ z, |phi z| ≤ M) :
    m * modelIntegral p ≤ M * modelIntegral p := by
  have hmM : m ≤ M :=
    (hm (0, 0, 0)).trans (hM (0, 0, 0))
  have hmodel0 : 0 ≤ modelIntegral p := by
    unfold modelIntegral
    apply setIntegral_nonneg exterior_measurable
    intro z hz
    unfold modelWeight
    exact one_div_nonneg.mpr
      (Real.rpow_nonneg (by
        unfold radiusSquared
        positivity) p)
  exact mul_le_mul_of_nonneg_right hmM hmodel0

theorem gap7 (p : ℝ) (hp : (3 / 2 : ℝ) < p) :
    modelIntegral p =
      ∫ azimuth in (0 : ℝ)..2 * Real.pi,
        ∫ latitude in (-Real.pi / 2)..Real.pi / 2,
          (∫ r in Set.Ici (1 : ℝ), radialWeight p r) *
            Real.cos latitude := by
  rw [modelIntegral_eq_radial p]
  symm
  exact angularIntegral_eq p

theorem gap8 (p : ℝ) (hp : (3 / 2 : ℝ) < p) :
    (∫ azimuth in (0 : ℝ)..2 * Real.pi,
        ∫ latitude in (-Real.pi / 2)..Real.pi / 2,
          (∫ r in Set.Ici (1 : ℝ), radialWeight p r) *
            Real.cos latitude) =
      4 * Real.pi *
        ∫ r in Set.Ici (1 : ℝ), radialWeight p r := by
  exact angularIntegral_eq p

theorem gap9 (p : ℝ) (hp : (3 / 2 : ℝ) < p) :
    modelIntegral p =
      4 * Real.pi *
        ∫ r in Set.Ici (1 : ℝ), radialWeight p r :=
  modelIntegral_eq_radial p

theorem gap10 (phi : ℝ × ℝ × ℝ → ℝ) (m M p : ℝ)
    (hm0 : 0 < m)
    (hphi : Measurable phi)
    (hm : ∀ z, m ≤ |phi z|)
    (hM : ∀ z, |phi z| ≤ M) :
    IntegrableOn (weightedIntegrand phi p) exterior ↔
      (3 / 2 : ℝ) < p := by
  have hM0 : 0 < M :=
    hm0.trans_le ((hm (0, 0, 0)).trans (hM (0, 0, 0)))
  exact weighted_integrable_iff_bounds phi p m M hphi hm0 hM0
    (fun z hz => ⟨hm z, hM z⟩)

end

end ProofGap.Exercise4191
