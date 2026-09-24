import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace ProofGap.Exercise4176

noncomputable section

open Filter MeasureTheory
open scoped Interval

def gaussian (x y : ℝ) : ℝ :=
  Real.exp (-(x ^ 2 + y ^ 2))

def oscillatory (x y : ℝ) : ℝ :=
  gaussian x y * Real.cos (x ^ 2 + y ^ 2)

def cartesianIntegral : ℝ :=
  ∫ y : ℝ, ∫ x : ℝ, oscillatory x y

def polarIntegral : ℝ :=
  ∫ theta in (0 : ℝ)..2 * Real.pi,
    ∫ r in Set.Ici (0 : ℝ),
      r * Real.exp (-r ^ 2) * Real.cos (r ^ 2)

def oneDimensionalIntegral : ℝ :=
  ∫ t in Set.Ici (0 : ℝ), Real.exp (-t) * Real.cos t

def dampedPrimitive (t : ℝ) : ℝ :=
  Real.pi * (Real.sin t - Real.cos t) / 2 * Real.exp (-t)

private def radialOsc (r : ℝ) : ℝ :=
  r * Real.exp (-r ^ 2) * Real.cos (r ^ 2)

private def radialIntegral : ℝ :=
  ∫ r in Set.Ioi (0 : ℝ), radialOsc r

private def primitive (t : ℝ) : ℝ :=
  (Real.sin t - Real.cos t) / 2 * Real.exp (-t)

private theorem gaussian_factor (x y : ℝ) :
    gaussian x y =
      Real.exp (-x ^ 2) * Real.exp (-y ^ 2) := by
  unfold gaussian
  rw [← Real.exp_add]
  congr 1
  ring

private theorem gaussian_integrable :
    Integrable (fun p : ℝ × ℝ => gaussian p.1 p.2) := by
  have h₁ : Integrable (fun x : ℝ => Real.exp (-x ^ 2)) := by
    simpa using integrable_exp_neg_mul_sq (b := (1 : ℝ)) zero_lt_one
  rw [Measure.volume_eq_prod]
  have hp := h₁.mul_prod h₁
  exact hp.congr (ae_of_all _ fun p => (gaussian_factor p.1 p.2).symm)

private theorem oscillatory_bound (x y : ℝ) :
    |oscillatory x y| ≤ gaussian x y := by
  unfold oscillatory
  have hg : 0 ≤ gaussian x y := by
    unfold gaussian
    positivity
  rw [abs_mul, abs_of_nonneg hg]
  exact mul_le_of_le_one_right hg
    (abs_le.2 ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩)

private theorem oscillatory_integrable :
    Integrable (fun p : ℝ × ℝ => oscillatory p.1 p.2) := by
  have hm : AEStronglyMeasurable
      (fun p : ℝ × ℝ => oscillatory p.1 p.2) := by
    have hc : Continuous
        (fun p : ℝ × ℝ => oscillatory p.1 p.2) := by
      unfold oscillatory gaussian
      fun_prop
    exact hc.aestronglyMeasurable
  refine gaussian_integrable.mono' hm ?_
  filter_upwards with p
  rw [Real.norm_eq_abs]
  exact oscillatory_bound p.1 p.2

private theorem cartesian_as_plane :
    cartesianIntegral =
      ∫ p : ℝ × ℝ, oscillatory p.1 p.2 := by
  unfold cartesianIntegral
  rw [Measure.volume_eq_prod]
  exact
    (integral_prod_symm
      (fun p : ℝ × ℝ => oscillatory p.1 p.2)
      oscillatory_integrable).symm

private theorem polar_point (r θ : ℝ) :
    r * oscillatory (r * Real.cos θ) (r * Real.sin θ) =
      radialOsc r := by
  have hsq :
      (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 = r ^ 2 := by
    nlinarith [Real.cos_sq_add_sin_sq θ]
  unfold oscillatory gaussian radialOsc
  rw [hsq]
  ring

private theorem cartesianIntegral_factor :
    cartesianIntegral = 2 * Real.pi * radialIntegral := by
  rw [cartesian_as_plane]
  rw [← integral_comp_polarCoord_symm, polarCoord_target]
  have hangle :
      (∫ _θ in Set.Ioo (-Real.pi) Real.pi, (1 : ℝ)) =
        2 * Real.pi := by
    rw [setIntegral_const, Real.volume_real_Ioo_of_le]
    · simp only [smul_eq_mul, mul_one]
      ring
    · linarith [Real.pi_pos]
  calc
    (∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
        p.1 • oscillatory
          (polarCoord.symm p).1 (polarCoord.symm p).2) =
        ∫ p in Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
          radialOsc p.1 * (1 : ℝ) := by
      apply setIntegral_congr_fun
        (measurableSet_Ioi.prod measurableSet_Ioo)
      intro p hp
      simp only [polarCoord_symm_apply, smul_eq_mul, mul_one]
      exact polar_point p.1 p.2
    _ = (∫ r in Set.Ioi (0 : ℝ), radialOsc r) *
          ∫ _θ in Set.Ioo (-Real.pi) Real.pi, (1 : ℝ) := by
      simpa only [Measure.volume_eq_prod] using
        (setIntegral_prod_mul
          (μ := volume) (ν := volume)
          radialOsc (fun _θ : ℝ => (1 : ℝ))
          (Set.Ioi (0 : ℝ)) (Set.Ioo (-Real.pi) Real.pi))
    _ = 2 * Real.pi * radialIntegral := by
      rw [hangle]
      unfold radialIntegral
      ring

private theorem polarIntegral_factor :
    polarIntegral = 2 * Real.pi * radialIntegral := by
  have hset :
      (∫ r in Set.Ici (0 : ℝ), radialOsc r) = radialIntegral := by
    unfold radialIntegral
    exact setIntegral_congr_set Ioi_ae_eq_Ici.symm
  unfold polarIntegral
  change
    (∫ _theta in (0 : ℝ)..2 * Real.pi,
      ∫ r in Set.Ici (0 : ℝ), radialOsc r) =
      2 * Real.pi * radialIntegral
  rw [hset, intervalIntegral.integral_const]
  simp only [smul_eq_mul, sub_zero]

private theorem damped_cos_integrable_Ici :
    IntegrableOn (fun t : ℝ => Real.exp (-t) * Real.cos t)
      (Set.Ici (0 : ℝ)) := by
  have heIoi : IntegrableOn (fun t : ℝ => Real.exp (-t))
      (Set.Ioi (0 : ℝ)) :=
    integrableOn_exp_neg_Ioi 0
  have heIci : IntegrableOn (fun t : ℝ => Real.exp (-t))
      (Set.Ici (0 : ℝ)) :=
    heIoi.congr_set_ae Ioi_ae_eq_Ici.symm
  refine heIci.mono'
    (by fun_prop : AEStronglyMeasurable
      (fun t : ℝ => Real.exp (-t) * Real.cos t)
      (volume.restrict (Set.Ici (0 : ℝ)))) ?_
  filter_upwards with t
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  have hc : |Real.cos t| ≤ 1 :=
    abs_le.2 ⟨Real.neg_one_le_cos t, Real.cos_le_one t⟩
  nlinarith [Real.exp_pos (-t)]

private theorem square_composition_integrable :
    IntegrableOn
      (fun x : ℝ =>
        (((fun t : ℝ => Real.exp (-t) * Real.cos t) ∘
          (fun r : ℝ => r ^ 2)) x) * (2 * x))
      (Set.Ici (0 : ℝ)) := by
  have hb : Integrable
      (fun x : ℝ => 2 * (x * Real.exp (-x ^ 2))) := by
    simpa using
      (integrable_mul_exp_neg_mul_sq
        (b := (1 : ℝ)) zero_lt_one).const_mul 2
  refine hb.integrableOn.mono'
    (by fun_prop : AEStronglyMeasurable
      (fun x : ℝ =>
        (((fun t : ℝ => Real.exp (-t) * Real.cos t) ∘
          (fun r : ℝ => r ^ 2)) x) * (2 * x))
      (volume.restrict (Set.Ici (0 : ℝ)))) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
  have hx0 : 0 ≤ x := hx
  have hc : |Real.cos (x ^ 2)| ≤ 1 :=
    abs_le.2 ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  simp only [Function.comp_apply]
  change
    ‖(Real.exp (-(x ^ 2)) * Real.cos (x ^ 2)) * (2 * x)‖ ≤
      2 * (x * Real.exp (-x ^ 2))
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
    abs_of_pos (Real.exp_pos _),
    abs_of_nonneg hx0, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have he : 0 ≤ Real.exp (-(x ^ 2)) := (Real.exp_pos _).le
  calc
    Real.exp (-(x ^ 2)) * |Real.cos (x ^ 2)| * (2 * x) ≤
        Real.exp (-(x ^ 2)) * 1 * (2 * x) := by
      gcongr
    _ = 2 * (x * Real.exp (-x ^ 2)) := by ring

private theorem radialIntegral_eq_half :
    radialIntegral = (1 / 2 : ℝ) * oneDimensionalIntegral := by
  have hderiv (x : ℝ) :
      HasDerivAt (fun r : ℝ => r ^ 2) (2 * x) x := by
    simpa [id, mul_comm] using (hasDerivAt_id x).pow 2
  have hcont : Continuous (fun x : ℝ => x ^ 2) :=
    continuous_id.pow 2
  have hderivCont : Continuous (fun x : ℝ => 2 * x) :=
    continuous_const.mul continuous_id
  have hgCont : Continuous
      (fun t : ℝ => Real.exp (-t) * Real.cos t) := by
    fun_prop
  have htendsto :
      Tendsto (fun x : ℝ => x ^ 2) atTop atTop := by
    simpa using
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < (2 : ℕ)))
  have hsubRaw :
      (∫ x in Set.Ioi (0 : ℝ),
        (((fun t : ℝ => Real.exp (-t) * Real.cos t) ∘
          (fun r : ℝ => r ^ 2)) x) * (2 * x)) =
        ∫ t in Set.Ioi ((fun r : ℝ => r ^ 2) 0),
          Real.exp (-t) * Real.cos t := by
    apply integral_comp_mul_deriv_Ioi
    · exact hcont.continuousOn
    · exact htendsto
    · intro x hx
      exact (hderiv x).hasDerivWithinAt
    · exact hgCont.continuousOn
    · refine damped_cos_integrable_Ici.mono_set ?_
      rintro t ⟨x, hx, rfl⟩
      exact sq_nonneg x
    · exact square_composition_integrable
  have hsub :
      (∫ x in Set.Ioi (0 : ℝ),
        (Real.exp (-(x ^ 2)) * Real.cos (x ^ 2)) * (2 * x)) =
        ∫ t in Set.Ioi (0 : ℝ), Real.exp (-t) * Real.cos t := by
    simpa [Function.comp_apply] using hsubRaw
  have hone :
      (∫ t in Set.Ioi (0 : ℝ), Real.exp (-t) * Real.cos t) =
        oneDimensionalIntegral := by
    unfold oneDimensionalIntegral
    exact setIntegral_congr_set Ioi_ae_eq_Ici
  unfold radialIntegral radialOsc
  calc
    (∫ r in Set.Ioi (0 : ℝ),
        r * Real.exp (-r ^ 2) * Real.cos (r ^ 2)) =
        ∫ r in Set.Ioi (0 : ℝ),
          ((Real.exp (-(r ^ 2)) * Real.cos (r ^ 2)) *
            (2 * r)) / 2 := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      ring
    _ = (∫ r in Set.Ioi (0 : ℝ),
          (Real.exp (-(r ^ 2)) * Real.cos (r ^ 2)) *
            (2 * r)) / 2 := by
      rw [integral_div]
    _ = (∫ t in Set.Ioi (0 : ℝ),
          Real.exp (-t) * Real.cos t) / 2 := by
      rw [hsub]
    _ = (1 / 2 : ℝ) * oneDimensionalIntegral := by
      rw [hone]
      ring

private theorem primitive_derivative (t : ℝ) :
    HasDerivAt primitive (Real.exp (-t) * Real.cos t) t := by
  have hs := Real.hasDerivAt_sin t
  have hc := Real.hasDerivAt_cos t
  have he :
      HasDerivAt (fun x : ℝ => Real.exp (-x)) (-Real.exp (-t)) t := by
    convert (Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_id t).neg
      using 1 <;> ring
  unfold primitive
  convert ((hs.sub hc).div_const 2).mul he using 1 <;>
    simp only [Pi.sub_apply] <;> ring

private theorem primitive_tendsto :
    Tendsto primitive atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' ?_ ?_ Real.tendsto_exp_neg_atTop_nhds_zero
  · filter_upwards with t
    exact norm_nonneg _
  · filter_upwards with t
    unfold primitive
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have hs : |Real.sin t| ≤ 1 :=
      abs_le.2 ⟨Real.neg_one_le_sin t, Real.sin_le_one t⟩
    have hc : |Real.cos t| ≤ 1 :=
      abs_le.2 ⟨Real.neg_one_le_cos t, Real.cos_le_one t⟩
    have hsub : |Real.sin t - Real.cos t| ≤ 2 := by
      calc
        |Real.sin t - Real.cos t| ≤
            |Real.sin t| + |Real.cos t| := abs_sub _ _
        _ ≤ 2 := by linarith
    have : |(Real.sin t - Real.cos t) / 2| ≤ 1 := by
      rw [abs_div]
      norm_num
      linarith
    nlinarith [Real.exp_pos (-t)]

private theorem oneDimensionalIntegral_value :
    oneDimensionalIntegral = (1 / 2 : ℝ) := by
  have hiIoi :
      IntegrableOn (fun t : ℝ => Real.exp (-t) * Real.cos t)
        (Set.Ioi (0 : ℝ)) :=
    damped_cos_integrable_Ici.mono_set Set.Ioi_subset_Ici_self
  have hFTC :
      (∫ t in Set.Ioi (0 : ℝ), Real.exp (-t) * Real.cos t) =
        0 - primitive 0 := by
    exact integral_Ioi_of_hasDerivAt_of_tendsto'
      (fun t ht => primitive_derivative t) hiIoi primitive_tendsto
  unfold oneDimensionalIntegral
  rw [← setIntegral_congr_set Ioi_ae_eq_Ici]
  rw [hFTC]
  norm_num [primitive]

private theorem common_integral_value :
    cartesianIntegral = polarIntegral := by
  rw [cartesianIntegral_factor, polarIntegral_factor]

theorem gap1 (x y : ℝ) :
    |oscillatory x y| ≤ gaussian x y := by
  exact oscillatory_bound x y

theorem gap2 :
    Integrable (fun p : ℝ × ℝ => gaussian p.1 p.2) := by
  exact gaussian_integrable

theorem gap3 :
    Integrable (fun p : ℝ × ℝ => oscillatory p.1 p.2) := by
  exact oscillatory_integrable

theorem gap4 :
    cartesianIntegral = polarIntegral := by
  exact common_integral_value

theorem gap5 :
    polarIntegral =
      Real.pi * oneDimensionalIntegral := by
  rw [polarIntegral_factor, radialIntegral_eq_half]
  ring

theorem gap6 :
    cartesianIntegral =
      Real.pi * oneDimensionalIntegral := by
  rw [cartesianIntegral_factor, radialIntegral_eq_half]
  ring

theorem gap7 :
    Real.pi * oneDimensionalIntegral =
      0 - dampedPrimitive 0 := by
  rw [oneDimensionalIntegral_value]
  norm_num [dampedPrimitive]
  ring

theorem gap8 :
    0 - dampedPrimitive 0 = Real.pi / 2 := by
  norm_num [dampedPrimitive]
  ring

theorem gap9 :
    Real.pi * oneDimensionalIntegral = Real.pi / 2 := by
  rw [oneDimensionalIntegral_value]
  ring

end

end ProofGap.Exercise4176
