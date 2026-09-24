import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Prod

namespace ProofGap.Exercise4172

noncomputable section

open Filter MeasureTheory
open scoped ENNReal

abbrev Point := ℝ × ℝ

def exterior : Set Point :=
  {z | 1 ≤ z.1 ^ 2 + z.2 ^ 2}

def surfaceIntegral (p : ℝ) : ℝ≥0∞ :=
  ∫⁻ z in exterior,
    ENNReal.ofReal (1 / Real.rpow (z.1 ^ 2 + z.2 ^ 2) p)

def polarIntegral (p : ℝ) : ℝ≥0∞ :=
  ∫⁻ _θ in Set.Icc (0 : ℝ) (2 * Real.pi),
    ∫⁻ r in Set.Ici (1 : ℝ),
      ENNReal.ofReal (1 / Real.rpow r (2 * p - 1))

private def radial (p r : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (1 / Real.rpow r (2 * p - 1))

private def radialIntegral (p : ℝ) : ℝ≥0∞ :=
  ∫⁻ r in Set.Ici (1 : ℝ), radial p r

private theorem exterior_measurable : MeasurableSet exterior := by
  unfold exterior
  measurability

private theorem measurable_rpow (s : ℝ) :
    Measurable (fun r : ℝ => Real.rpow r s) := by
  apply measurable_of_continuousOn_compl_singleton 0
  exact continuousOn_id.rpow_const
    (fun x hx => Or.inl (by simpa using hx))

private theorem radial_measurable (p : ℝ) :
    Measurable (radial p) := by
  unfold radial
  exact (measurable_const.div (measurable_rpow _)).ennreal_ofReal

private theorem radial_eq_rpow (p r : ℝ) (hr : 1 ≤ r) :
    radial p r = ENNReal.ofReal (Real.rpow r (1 - 2 * p)) := by
  unfold radial
  congr 1
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  calc
    1 / Real.rpow r (2 * p - 1) =
        Real.rpow r (-(2 * p - 1)) := by
      simpa [one_div] using (Real.rpow_neg hr0.le (2 * p - 1)).symm
    _ = Real.rpow r (1 - 2 * p) := by congr 1 <;> ring

private theorem polarIntegral_factor (p : ℝ) :
    polarIntegral p =
      ENNReal.ofReal (2 * Real.pi) * radialIntegral p := by
  unfold polarIntegral radialIntegral radial
  rw [setLIntegral_const, Real.volume_Icc]
  simp only [sub_zero]
  rw [mul_comm]

private theorem surfaceIntegral_factor (p : ℝ) :
    surfaceIntegral p =
      ENNReal.ofReal (2 * Real.pi) * radialIntegral p := by
  let f : ℝ × ℝ → ℝ≥0∞ := fun z =>
    exterior.indicator
      (fun w =>
        ENNReal.ofReal
          (1 / Real.rpow (w.1 ^ 2 + w.2 ^ 2) p)) z
  have hf : surfaceIntegral p = ∫⁻ z : ℝ × ℝ, f z := by
    unfold surfaceIntegral
    rw [← lintegral_indicator exterior_measurable]
  rw [hf, ← lintegral_comp_polarCoord_symm]
  let rect : Set (ℝ × ℝ) :=
    Set.Ici (1 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi
  have htarget : MeasurableSet polarCoord.target :=
    polarCoord.open_target.measurableSet
  have hrect : MeasurableSet rect :=
    measurableSet_Ici.prod measurableSet_Ioo
  have hrestrict :
      (∫⁻ u in polarCoord.target,
          ENNReal.ofReal u.1 • f (polarCoord.symm u)) =
        ∫⁻ u in rect, radial p u.1 := by
    rw [← lintegral_indicator htarget, ← lintegral_indicator hrect]
    apply lintegral_congr
    intro u
    by_cases hu : u ∈ polarCoord.target
    · rw [Set.indicator_of_mem hu]
      have hrpos : 0 < u.1 := hu.1
      have hsq :
          (polarCoord.symm u).1 ^ 2 +
              (polarCoord.symm u).2 ^ 2 = u.1 ^ 2 := by
        simp only [polarCoord_symm_apply]
        nlinarith [Real.sin_sq_add_cos_sq u.2]
      have hrpow :
          Real.rpow (u.1 ^ 2) p =
            Real.rpow u.1 (2 * p) := by
        have h := Real.rpow_mul hrpos.le (2 : ℝ) p
        simpa only [Real.rpow_eq_pow, Real.rpow_two] using h.symm
      by_cases hr : 1 ≤ u.1
      · have hur : u ∈ rect := ⟨hr, hu.2⟩
        have hext : polarCoord.symm u ∈ exterior := by
          change 1 ≤
            (polarCoord.symm u).1 ^ 2 +
              (polarCoord.symm u).2 ^ 2
          rw [hsq]
          nlinarith [sq_nonneg (u.1 - 1)]
        rw [Set.indicator_of_mem hur]
        unfold f
        rw [Set.indicator_of_mem hext]
        unfold radial
        rw [hsq, hrpow]
        simp only [smul_eq_mul]
        rw [← ENNReal.ofReal_mul hrpos.le]
        congr 1
        have hpowpos : 0 < Real.rpow u.1 (2 * p) :=
          Real.rpow_pos_of_pos hrpos _
        have hsub :
            Real.rpow u.1 (2 * p - 1) =
              Real.rpow u.1 (2 * p) / u.1 := by
          simpa only [Real.rpow_one] using
            Real.rpow_sub hrpos (2 * p) 1
        rw [hsub]
        field_simp [ne_of_gt hrpos, ne_of_gt hpowpos]
      · have hur : u ∉ rect := by
          intro h
          exact hr h.1
        have hext : polarCoord.symm u ∉ exterior := by
          intro h
          apply hr
          change 1 ≤
            (polarCoord.symm u).1 ^ 2 +
              (polarCoord.symm u).2 ^ 2 at h
          rw [hsq] at h
          nlinarith [sq_nonneg (u.1 - 1)]
        rw [Set.indicator_of_notMem hur]
        unfold f
        rw [Set.indicator_of_notMem hext]
        simp
    · rw [Set.indicator_of_notMem hu]
      have hur : u ∉ rect := by
        intro h
        apply hu
        refine ⟨?_, h.2⟩
        change 0 < u.1
        exact zero_lt_one.trans_le h.1
      rw [Set.indicator_of_notMem hur]
  rw [hrestrict]
  have hi :
      AEMeasurable (fun u : ℝ × ℝ => radial p u.1)
        ((volume.prod volume).restrict rect) :=
    ((radial_measurable p).comp measurable_fst).aemeasurable
  change
    (∫⁻ u in rect, radial p u.1 ∂volume.prod volume) =
      ENNReal.ofReal (2 * Real.pi) * radialIntegral p
  rw [setLIntegral_prod _ hi]
  have htheta : ∀ r : ℝ,
      (∫⁻ _θ in Set.Ioo (-Real.pi) Real.pi, radial p r) =
        ENNReal.ofReal (2 * Real.pi) * radial p r := by
    intro r
    rw [setLIntegral_const, Real.volume_Ioo]
    have hangle :
        ENNReal.ofReal (Real.pi - -Real.pi) =
          ENNReal.ofReal (2 * Real.pi) := by
      congr 1
      ring
    rw [hangle, mul_comm]
  simp_rw [htheta]
  rw [lintegral_const_mul
    (ENNReal.ofReal (2 * Real.pi)) (radial_measurable p)]
  rfl

private theorem lintegral_rpow_of_lt (s : ℝ) (hs : s < -1) :
    (∫⁻ x in Set.Ici (1 : ℝ),
        ENNReal.ofReal (Real.rpow x s)) =
      ENNReal.ofReal (-1 / (s + 1)) := by
  rw [← setLIntegral_congr
    (Ioi_ae_eq_Ici : Set.Ioi (1 : ℝ) =ᵐ[volume] Set.Ici 1)]
  have hi : IntegrableOn (fun x : ℝ => Real.rpow x s)
      (Set.Ioi (1 : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt hs zero_lt_one
  have hn : 0 ≤ᵐ[volume.restrict (Set.Ioi (1 : ℝ))]
      (fun x : ℝ => Real.rpow x s) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact Real.rpow_nonneg (zero_lt_one.trans hx).le _
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn]
  have hval :
      (∫ x in Set.Ioi (1 : ℝ), Real.rpow x s) =
        -Real.rpow 1 (s + 1) / (s + 1) := by
    simpa using
      (integral_Ioi_rpow_of_lt (a := s) (c := (1 : ℝ))
        hs zero_lt_one)
  rw [hval]
  simp

private theorem lintegral_rpow_top (s : ℝ) (hs : -1 ≤ s) :
    (∫⁻ x in Set.Ici (1 : ℝ),
        ENNReal.ofReal (Real.rpow x s)) = ⊤ := by
  rw [← setLIntegral_congr
    (Ioi_ae_eq_Ici : Set.Ioi (1 : ℝ) =ᵐ[volume] Set.Ici 1)]
  have hm : AEStronglyMeasurable
      (fun x : ℝ => Real.rpow x s)
      (volume.restrict (Set.Ioi (1 : ℝ))) := by
    exact (continuousOn_id.rpow_const
      (fun x hx =>
        Or.inl (ne_of_gt (zero_lt_one.trans hx)))).aestronglyMeasurable
          measurableSet_Ioi
  have hn : 0 ≤ᵐ[volume.restrict (Set.Ioi (1 : ℝ))]
      (fun x : ℝ => Real.rpow x s) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact Real.rpow_nonneg (zero_lt_one.trans hx).le _
  by_contra htop
  have hi : IntegrableOn (fun x : ℝ => Real.rpow x s)
      (Set.Ioi (1 : ℝ)) :=
    (lintegral_ofReal_ne_top_iff_integrable hm hn).mp htop
  have hs' := (integrableOn_Ioi_rpow_iff zero_lt_one).mp hi
  linarith

private theorem radialIntegral_formula (p : ℝ) :
    radialIntegral p =
      if 1 < p
      then ENNReal.ofReal (1 / (2 * (p - 1)))
      else ⊤ := by
  by_cases hp : 1 < p
  · rw [if_pos hp]
    unfold radialIntegral
    calc
      (∫⁻ r in Set.Ici (1 : ℝ), radial p r) =
          ∫⁻ r in Set.Ici (1 : ℝ),
            ENNReal.ofReal (Real.rpow r (1 - 2 * p)) := by
        apply setLIntegral_congr_fun measurableSet_Ici
        intro r hr
        exact radial_eq_rpow p r hr
      _ = ENNReal.ofReal (-1 / ((1 - 2 * p) + 1)) :=
        lintegral_rpow_of_lt (1 - 2 * p) (by linarith)
      _ = ENNReal.ofReal (1 / (2 * (p - 1))) := by
        congr 1
        have hden : (1 - 2 * p) + 1 ≠ 0 := by linarith
        have hpden : p - 1 ≠ 0 := by linarith
        field_simp [hden, hpden]
        ring
  · rw [if_neg hp]
    unfold radialIntegral
    calc
      (∫⁻ r in Set.Ici (1 : ℝ), radial p r) =
          ∫⁻ r in Set.Ici (1 : ℝ),
            ENNReal.ofReal (Real.rpow r (1 - 2 * p)) := by
        apply setLIntegral_congr_fun measurableSet_Ici
        intro r hr
        exact radial_eq_rpow p r hr
      _ = ⊤ :=
        lintegral_rpow_top (1 - 2 * p) (by linarith)

private theorem common_value (p : ℝ) :
    ENNReal.ofReal (2 * Real.pi) * radialIntegral p =
      if 1 < p then ENNReal.ofReal (Real.pi / (p - 1)) else ⊤ := by
  rw [radialIntegral_formula]
  by_cases hp : 1 < p
  · rw [if_pos hp, if_pos hp]
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * Real.pi)]
    congr 1
    have hpden : p - 1 ≠ 0 := by linarith
    field_simp [hpden]
  · rw [if_neg hp, if_neg hp]
    have hpos : 0 < ENNReal.ofReal (2 * Real.pi) := by
      rw [ENNReal.ofReal_pos]
      positivity
    exact ENNReal.mul_top hpos.ne'

theorem gap1 (p : ℝ) :
    surfaceIntegral p = polarIntegral p := by
  rw [surfaceIntegral_factor, polarIntegral_factor]

theorem gap2 (p : ℝ) :
    polarIntegral p =
      if 1 < p then ENNReal.ofReal (Real.pi / (p - 1)) else ⊤ := by
  rw [polarIntegral_factor]
  exact common_value p

theorem gap3 (p : ℝ) :
    surfaceIntegral p =
      if 1 < p then ENNReal.ofReal (Real.pi / (p - 1)) else ⊤ := by
  rw [surfaceIntegral_factor]
  exact common_value p

end

end ProofGap.Exercise4172
