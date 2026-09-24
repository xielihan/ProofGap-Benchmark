import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4161

noncomputable section

open MeasureTheory Filter
open scoped ENNReal

abbrev Point := ℝ × ℝ

def exterior : Set Point :=
  {z | 1 < z.1 ^ 2 + z.2 ^ 2}

def kernel (p x y : ℝ) : ℝ :=
  1 / Real.rpow (x ^ 2 + y ^ 2) p

def weightedAbsIntegral (φ : ℝ → ℝ → ℝ) (p : ℝ) : ℝ≥0∞ :=
  ∫⁻ z in exterior, ENNReal.ofReal (|φ z.1 z.2| * kernel p z.1 z.2)

def baselineIntegral (p : ℝ) : ℝ≥0∞ :=
  ∫⁻ z in exterior, ENNReal.ofReal (kernel p z.1 z.2)

def polarBaseline (p : ℝ) : ℝ≥0∞ :=
  ∫⁻ θ in Set.Icc (0 : ℝ) (2 * Real.pi),
    ∫⁻ r in Set.Ioi (1 : ℝ),
      ENNReal.ofReal (r / Real.rpow r (2 * p))

private def radial (p r : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (r / Real.rpow r (2 * p))

private def radialIntegral (p : ℝ) : ℝ≥0∞ :=
  ∫⁻ r in Set.Ioi (1 : ℝ), radial p r

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
  exact (measurable_id.div
    (measurable_rpow (2 * p))).ennreal_ofReal

private theorem radial_eq_rpow (p r : ℝ) (hr : 1 < r) :
    radial p r =
      ENNReal.ofReal (Real.rpow r (1 - 2 * p)) := by
  unfold radial
  congr 1
  have h := Real.rpow_sub
    (show 0 < r by linarith) (1 : ℝ) (2 * p)
  simpa only [Real.rpow_eq_pow, Real.rpow_one] using h.symm

private theorem polarBaseline_factor (p : ℝ) :
    polarBaseline p =
      ENNReal.ofReal (2 * Real.pi) * radialIntegral p := by
  unfold polarBaseline radialIntegral radial
  rw [setLIntegral_const, Real.volume_Icc]
  simp only [sub_zero]
  rw [mul_comm]

private theorem baseline_factor (p : ℝ) :
    baselineIntegral p =
      ENNReal.ofReal (2 * Real.pi) * radialIntegral p := by
  let f : ℝ × ℝ → ℝ≥0∞ := fun z =>
    exterior.indicator
      (fun w => ENNReal.ofReal (kernel p w.1 w.2)) z
  have hf :
      baselineIntegral p = ∫⁻ z : ℝ × ℝ, f z := by
    unfold baselineIntegral
    rw [← lintegral_indicator exterior_measurable]
  rw [hf, ← lintegral_comp_polarCoord_symm]
  let rect : Set (ℝ × ℝ) :=
    Set.Ioi (1 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi
  have htarget : MeasurableSet polarCoord.target :=
    polarCoord.open_target.measurableSet
  have hrect : MeasurableSet rect :=
    measurableSet_Ioi.prod measurableSet_Ioo
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
      by_cases hr : 1 < u.1
      · have hur : u ∈ rect := ⟨hr, hu.2⟩
        have hext : polarCoord.symm u ∈ exterior := by
          change 1 <
            (polarCoord.symm u).1 ^ 2 +
              (polarCoord.symm u).2 ^ 2
          rw [hsq]
          nlinarith [sq_nonneg (u.1 - 1)]
        rw [Set.indicator_of_mem hur]
        unfold f
        rw [Set.indicator_of_mem hext]
        unfold kernel radial
        rw [hsq, hrpow]
        simp only [smul_eq_mul]
        rw [← ENNReal.ofReal_mul hrpos.le]
        congr 1
        ring
      · have hur : u ∉ rect := by
          intro h
          exact hr h.1
        have hext : polarCoord.symm u ∉ exterior := by
          intro h
          apply hr
          change 1 <
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
        exact lt_trans zero_lt_one h.1
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
    (∫⁻ x in Set.Ioi (1 : ℝ),
        ENNReal.ofReal (Real.rpow x s)) =
      ENNReal.ofReal (-1 / (s + 1)) := by
  have hi : IntegrableOn (fun x : ℝ => Real.rpow x s)
      (Set.Ioi (1 : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt hs zero_lt_one
  have hn : 0 ≤ᵐ[volume.restrict (Set.Ioi (1 : ℝ))]
      (fun x : ℝ => Real.rpow x s) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact Real.rpow_nonneg (le_trans zero_le_one hx.le) _
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn]
  have hval := integral_Ioi_rpow_of_lt hs zero_lt_one
  rw [show (∫ x in Set.Ioi (1 : ℝ), Real.rpow x s) =
      -Real.rpow 1 (s + 1) / (s + 1) by simpa using hval]
  have hone : Real.rpow 1 (s + 1) = 1 := by
    rw [Real.rpow_eq_pow, Real.one_rpow]
  rw [hone]

private theorem lintegral_rpow_top (s : ℝ) (hs : -1 ≤ s) :
    (∫⁻ x in Set.Ioi (1 : ℝ),
        ENNReal.ofReal (Real.rpow x s)) = ⊤ := by
  have hmeas : AEStronglyMeasurable
      (fun x : ℝ => Real.rpow x s)
      (volume.restrict (Set.Ioi (1 : ℝ))) := by
    exact (continuousOn_id.rpow_const
      (fun x hx =>
        Or.inl (ne_of_gt (zero_lt_one.trans hx)))).aestronglyMeasurable
          measurableSet_Ioi
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioi (1 : ℝ))]
      (fun x : ℝ => Real.rpow x s) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact Real.rpow_nonneg
      (le_of_lt (zero_lt_one.trans hx)) _
  by_contra htop
  have hi : IntegrableOn (fun x : ℝ => Real.rpow x s)
      (Set.Ioi (1 : ℝ)) :=
    (lintegral_ofReal_ne_top_iff_integrable
      hmeas hnonneg).mp htop
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
      (∫⁻ r in Set.Ioi (1 : ℝ), radial p r) =
          ∫⁻ r in Set.Ioi (1 : ℝ),
            ENNReal.ofReal (Real.rpow r (1 - 2 * p)) := by
        apply setLIntegral_congr_fun measurableSet_Ioi
        intro r hr
        exact radial_eq_rpow p r hr
      _ = ENNReal.ofReal (-1 / ((1 - 2 * p) + 1)) :=
        lintegral_rpow_of_lt (1 - 2 * p) (by linarith)
      _ = ENNReal.ofReal (1 / (2 * (p - 1))) := by
        congr 1
        have hden : (1 - 2 * p) + 1 ≠ 0 := by
          linarith
        field_simp [hden, ne_of_gt (sub_pos.mpr hp)]
        ring
  · rw [if_neg hp]
    unfold radialIntegral
    calc
      (∫⁻ r in Set.Ioi (1 : ℝ), radial p r) =
          ∫⁻ r in Set.Ioi (1 : ℝ),
            ENNReal.ofReal (Real.rpow r (1 - 2 * p)) := by
        apply setLIntegral_congr_fun measurableSet_Ioi
        intro r hr
        exact radial_eq_rpow p r hr
      _ = ⊤ :=
        lintegral_rpow_top (1 - 2 * p) (by linarith)

private theorem kernel_nonneg (p x y : ℝ) :
    0 ≤ kernel p x y := by
  unfold kernel
  exact one_div_nonneg.mpr
    (Real.rpow_nonneg (by positivity) p)

theorem gap1 (φ : ℝ → ℝ → ℝ) (m p x y : ℝ)
    (hm : ∀ x y, m ≤ |φ x y|)
    (hxy : 1 < x ^ 2 + y ^ 2) :
    m * kernel p x y ≤ |φ x y| * kernel p x y := by
  exact mul_le_mul_of_nonneg_right
    (hm x y) (kernel_nonneg p x y)

theorem gap2 (φ : ℝ → ℝ → ℝ) (M p x y : ℝ)
    (hM : ∀ x y, |φ x y| ≤ M)
    (hxy : 1 < x ^ 2 + y ^ 2) :
    |φ x y| * kernel p x y ≤ M * kernel p x y := by
  exact mul_le_mul_of_nonneg_right
    (hM x y) (kernel_nonneg p x y)

theorem gap3 (m M p x y : ℝ)
    (hm : 0 < m) (hM : m ≤ M)
    (hxy : 1 < x ^ 2 + y ^ 2) :
    m * kernel p x y ≤ M * kernel p x y := by
  exact mul_le_mul_of_nonneg_right hM (kernel_nonneg p x y)

theorem gap4 (φ : ℝ → ℝ → ℝ) (m p : ℝ)
    (hm : 0 < m) (hlower : ∀ x y, m ≤ |φ x y|) :
    ENNReal.ofReal m * baselineIntegral p ≤
      weightedAbsIntegral φ p := by
  unfold baselineIntegral weightedAbsIntegral
  rw [← lintegral_const_mul'
    (μ := volume.restrict exterior)
    (ENNReal.ofReal m)
    (fun z : ℝ × ℝ =>
      ENNReal.ofReal (kernel p z.1 z.2))
    ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro z
  change
    ENNReal.ofReal m *
        ENNReal.ofReal (kernel p z.1 z.2) ≤
      ENNReal.ofReal
        (|φ z.1 z.2| * kernel p z.1 z.2)
  rw [← ENNReal.ofReal_mul hm.le]
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right
    (hlower z.1 z.2) (kernel_nonneg p z.1 z.2)

theorem gap5 (φ : ℝ → ℝ → ℝ) (M p : ℝ)
    (hM0 : 0 ≤ M) (hupper : ∀ x y, |φ x y| ≤ M) :
    weightedAbsIntegral φ p ≤
      ENNReal.ofReal M * baselineIntegral p := by
  unfold baselineIntegral weightedAbsIntegral
  rw [← lintegral_const_mul'
    (μ := volume.restrict exterior)
    (ENNReal.ofReal M)
    (fun z : ℝ × ℝ =>
      ENNReal.ofReal (kernel p z.1 z.2))
    ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro z
  change
    ENNReal.ofReal
        (|φ z.1 z.2| * kernel p z.1 z.2) ≤
      ENNReal.ofReal M *
        ENNReal.ofReal (kernel p z.1 z.2)
  rw [← ENNReal.ofReal_mul hM0]
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right
    (hupper z.1 z.2) (kernel_nonneg p z.1 z.2)

theorem gap6 (m M p : ℝ) (hm : 0 ≤ m) (hmM : m ≤ M) :
    ENNReal.ofReal m * baselineIntegral p ≤
      ENNReal.ofReal M * baselineIntegral p := by
  exact mul_le_mul_right'
    (ENNReal.ofReal_le_ofReal hmM) (baselineIntegral p)

theorem gap7 (p : ℝ) :
    baselineIntegral p = polarBaseline p := by
  rw [baseline_factor, polarBaseline_factor]

theorem gap8 (p : ℝ) :
    polarBaseline p =
      if 1 < p
      then ENNReal.ofReal (Real.pi / (p - 1))
      else ⊤ := by
  rw [polarBaseline_factor, radialIntegral_formula]
  by_cases hp : 1 < p
  · simp only [if_pos hp]
    rw [← ENNReal.ofReal_mul
      (show 0 ≤ 2 * Real.pi by positivity)]
    congr 1
    field_simp [ne_of_gt (sub_pos.mpr hp)]
  · simp only [if_neg hp]
    exact ENNReal.mul_top (ne_of_gt (by
      rw [ENNReal.ofReal_pos]
      positivity))

theorem gap9 (p : ℝ) :
    baselineIntegral p =
      if 1 < p
      then ENNReal.ofReal (Real.pi / (p - 1))
      else ⊤ := by
  rw [gap7, gap8]

theorem gap10 (φ : ℝ → ℝ → ℝ) (m M p : ℝ)
    (hm : 0 < m) (hM : 0 < M)
    (hlower : ∀ x y, m ≤ |φ x y|)
    (hupper : ∀ x y, |φ x y| ≤ M) :
    ∃ finiteValue : ℝ≥0∞,
      finiteValue ≠ ⊤ ∧
        weightedAbsIntegral φ p =
          if 1 < p then finiteValue else ⊤ := by
  by_cases hp : 1 < p
  · refine ⟨weightedAbsIntegral φ p, ?_, by simp [hp]⟩
    have hle := gap5 φ M p hM.le hupper
    rw [gap9, if_pos hp] at hle
    exact ne_top_of_le_ne_top
      (ENNReal.mul_ne_top
        ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hle
  · refine ⟨0, ENNReal.zero_ne_top, ?_⟩
    simp only [if_neg hp]
    have hle := gap4 φ m p hm hlower
    rw [gap9, if_neg hp] at hle
    have hmne : ENNReal.ofReal m ≠ 0 := ne_of_gt (by
      rw [ENNReal.ofReal_pos]
      exact hm)
    rw [ENNReal.mul_top hmne] at hle
    exact top_unique hle

end

end ProofGap.Exercise4161
