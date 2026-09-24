import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3727

noncomputable section

open Filter MeasureTheory
open scoped Interval Topology

def RegularOn (φ : ℝ → ℝ) (a : ℝ) : Prop :=
  DifferentiableOn ℝ φ (Set.Icc 0 a) ∧
    ContinuousOn (deriv φ) (Set.Icc 0 a)

def abelIntegral (φ : ℝ → ℝ) (α : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..α, φ x / Real.sqrt (α - x)

def scaledIntegral (φ : ℝ → ℝ) (α : ℝ) : ℝ :=
  Real.sqrt α *
    ∫ t in (0 : ℝ)..1, φ (α * t) / Real.sqrt (1 - t)

-- Statement correction: parenthesize the first integral so the following
-- summand is not captured by the interval-integral binder.
def scaledDerivative (φ : ℝ → ℝ) (α : ℝ) : ℝ :=
  (1 / (2 * Real.sqrt α)) *
      (∫ t in (0 : ℝ)..1, φ (α * t) / Real.sqrt (1 - t)) +
    Real.sqrt α *
      ∫ t in (0 : ℝ)..1,
        t * deriv φ (α * t) / Real.sqrt (1 - t)

def finalDerivative (φ : ℝ → ℝ) (α : ℝ) : ℝ :=
  φ 0 / Real.sqrt α +
    ∫ x in (0 : ℝ)..α, deriv φ x / Real.sqrt (α - x)

private def kernelWeight (t : ℝ) : ℝ :=
  1 / Real.sqrt (1 - t)

private def scaledCore (φ : ℝ → ℝ) (α : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, φ (α * t) * kernelWeight t

private def derivativeCore (φ : ℝ → ℝ) (α : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, deriv φ (α * t) * kernelWeight t

private def weightedDerivativeCore (φ : ℝ → ℝ) (α : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, t * deriv φ (α * t) * kernelWeight t

private def scaledValue (φ : ℝ → ℝ) (α : ℝ) : ℝ :=
  Real.sqrt α * scaledCore φ α

private theorem kernelWeight_intervalIntegrable :
    IntervalIntegrable kernelWeight volume 0 1 := by
  have hpow :
      IntervalIntegrable (fun x : ℝ => x ^ (-(1 / 2 : ℝ)))
        volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hsub :
      IntervalIntegrable (fun t : ℝ => (1 - t) ^ (-(1 / 2 : ℝ)))
        volume 0 1 := by
    simpa only [sub_self, sub_zero] using (hpow.comp_sub_left 1).symm
  apply hsub.congr
  intro t ht
  rw [Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] at ht
  have hnonneg : 0 ≤ 1 - t := by linarith [ht.2]
  change (1 - t) ^ (-(1 / 2 : ℝ)) = kernelWeight t
  unfold kernelWeight
  rw [Real.sqrt_eq_rpow, Real.rpow_neg hnonneg]
  ring

private theorem scaledFunction_intervalIntegrable
    (a : ℝ) (φ : ℝ → ℝ) (ha : 0 < a)
    (hreg : RegularOn φ a)
    (β : ℝ) (hβ0 : 0 ≤ β) (hβa : β ≤ a) :
    IntervalIntegrable
      (fun t : ℝ => φ (β * t) * kernelWeight t)
      volume 0 1 := by
  have hcomp :
      ContinuousOn (fun t : ℝ => φ (β * t)) (Set.uIcc 0 1) := by
    apply hreg.1.continuousOn.comp
      (continuous_const.mul continuous_id).continuousOn
    intro t ht
    rw [Set.uIcc_of_le (by norm_num)] at ht
    constructor
    · exact mul_nonneg hβ0 ht.1
    · exact (mul_le_of_le_one_right hβ0 ht.2).trans hβa
  have hmul := kernelWeight_intervalIntegrable.mul_continuousOn hcomp
  exact hmul.congr fun t _ => by
    change kernelWeight t * φ (β * t) = φ (β * t) * kernelWeight t
    ring

private theorem derivativeFunction_intervalIntegrable
    (a : ℝ) (φ : ℝ → ℝ) (ha : 0 < a)
    (hreg : RegularOn φ a)
    (β : ℝ) (hβ0 : 0 ≤ β) (hβa : β ≤ a) :
    IntervalIntegrable
      (fun t : ℝ => deriv φ (β * t) * kernelWeight t)
      volume 0 1 := by
  have hcomp :
      ContinuousOn (fun t : ℝ => deriv φ (β * t))
        (Set.uIcc 0 1) := by
    apply hreg.2.comp (continuous_const.mul continuous_id).continuousOn
    intro t ht
    rw [Set.uIcc_of_le (by norm_num)] at ht
    constructor
    · exact mul_nonneg hβ0 ht.1
    · exact (mul_le_of_le_one_right hβ0 ht.2).trans hβa
  have hbase := kernelWeight_intervalIntegrable.mul_continuousOn hcomp
  exact hbase.congr fun t _ => by ring

private theorem weightedDerivativeFunction_intervalIntegrable
    (a : ℝ) (φ : ℝ → ℝ) (ha : 0 < a)
    (hreg : RegularOn φ a)
    (β : ℝ) (hβ0 : 0 ≤ β) (hβa : β ≤ a) :
    IntervalIntegrable
      (fun t : ℝ => t * deriv φ (β * t) * kernelWeight t)
      volume 0 1 := by
  have h :=
    derivativeFunction_intervalIntegrable a φ ha hreg β hβ0 hβa
  have hmul := h.mul_continuousOn continuous_id.continuousOn
  exact hmul.congr fun t _ => by
    simp only [id_eq]
    ring

private theorem abel_scale (ψ : ℝ → ℝ) (α : ℝ) (hα : 0 < α) :
    (∫ x in (0 : ℝ)..α, ψ x / Real.sqrt (α - x)) =
      Real.sqrt α *
        ∫ t in (0 : ℝ)..1, ψ (α * t) * kernelWeight t := by
  have hscale :=
    intervalIntegral.smul_integral_comp_mul_right
      (f := fun x : ℝ => ψ x / Real.sqrt (α - x))
      (a := (0 : ℝ)) (b := 1) α
  norm_num only [zero_mul, one_mul, smul_eq_mul] at hscale
  rw [← hscale]
  rw [← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le (by norm_num)] at ht
  have hsα : Real.sqrt α ≠ 0 := (Real.sqrt_pos.2 hα).ne'
  have hsquare : Real.sqrt α ^ 2 = α := Real.sq_sqrt hα.le
  by_cases hlast : 1 - t = 0
  · have ht1 : t = 1 := by linarith
    subst t
    simp [kernelWeight]
  · have hnonneg : 0 ≤ 1 - t := by linarith [ht.2]
    have hsone : Real.sqrt (1 - t) ≠ 0 :=
      (Real.sqrt_pos.2 (lt_of_le_of_ne hnonneg (Ne.symm hlast))).ne'
    have hsqrt :
        Real.sqrt (α - t * α) =
          Real.sqrt α * Real.sqrt (1 - t) := by
      rw [show α - t * α = α * (1 - t) by ring,
        Real.sqrt_mul hα.le]
    change
      α * (ψ (t * α) / Real.sqrt (α - t * α)) =
        Real.sqrt α * (ψ (α * t) * kernelWeight t)
    rw [show α * t = t * α by ring, hsqrt]
    unfold kernelWeight
    field_simp [hsα, hsone]
    rw [hsquare]
    ring

private theorem abelIntegral_eq_scaledValue
    (φ : ℝ → ℝ) (α : ℝ) (hα : 0 < α) :
    abelIntegral φ α = scaledValue φ α := by
  unfold abelIntegral scaledValue scaledCore
  exact abel_scale φ α hα

private theorem hasDerivAt_scaledCore
    (a : ℝ) (φ : ℝ → ℝ) (ha : 0 < a)
    (hreg : RegularOn φ a)
    (α : ℝ) (hα : 0 < α) (hαa : α < a) :
    HasDerivAt (scaledCore φ) (weightedDerivativeCore φ α) α := by
  let δ : ℝ := α / 2
  let r : ℝ := (α + a) / 2
  let s : Set ℝ := Set.Icc δ r
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hδa : δ < α := by dsimp [δ]; linarith
  have hαr : α < r := by dsimp [r]; linarith
  have hra : r < a := by dsimp [r]; linarith
  have hs : s ∈ 𝓝 α := by
    apply Icc_mem_nhds
    · simpa [s] using hδa
    · simpa [s] using hαr
  obtain ⟨C, hC⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn hreg.2
  have hC0 : 0 ≤ C := by
    have hz := hC 0 (by simp [ha.le])
    linarith [norm_nonneg (deriv φ 0)]
  have hF_meas :
      ∀ᶠ β in 𝓝 α,
        AEStronglyMeasurable
          (fun t : ℝ => φ (β * t) * kernelWeight t)
          (volume.restrict (Set.uIoc 0 1)) := by
    filter_upwards [hs] with β hβ
    have hβ0 : 0 ≤ β := by
      have : δ ≤ β := hβ.1
      linarith
    have hβa : β ≤ a := by
      have : β ≤ r := hβ.2
      linarith
    have hi :=
      scaledFunction_intervalIntegrable a φ ha hreg β hβ0 hβa
    simpa only [Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using
      hi.aestronglyMeasurable
  have hF_int :
      IntervalIntegrable
        (fun t : ℝ => φ (α * t) * kernelWeight t)
        volume 0 1 :=
    scaledFunction_intervalIntegrable a φ ha hreg α hα.le hαa.le
  have hF'_int :
      IntervalIntegrable
        (fun t : ℝ => t * deriv φ (α * t) * kernelWeight t)
        volume 0 1 :=
    weightedDerivativeFunction_intervalIntegrable
      a φ ha hreg α hα.le hαa.le
  have hF'_meas :
      AEStronglyMeasurable
        (fun t : ℝ => t * deriv φ (α * t) * kernelWeight t)
        (volume.restrict (Set.uIoc 0 1)) := by
    simpa only [Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using
      hF'_int.aestronglyMeasurable
  have hbound :
      ∀ᵐ t ∂volume, t ∈ Set.uIoc (0 : ℝ) 1 →
        ∀ β ∈ s,
          ‖t * deriv φ (β * t) * kernelWeight t‖ ≤
            C * kernelWeight t := by
    filter_upwards [] with t ht β hβ
    rw [Set.uIoc_of_le (by norm_num)] at ht
    have hβ0 : 0 < β := by
      have : δ ≤ β := hβ.1
      linarith
    have hβa : β < a := by
      have : β ≤ r := hβ.2
      linarith
    have hxt0 : 0 < β * t := mul_pos hβ0 ht.1
    have hxta : β * t < a := by
      calc
        β * t ≤ β := mul_le_of_le_one_right hβ0.le ht.2
        _ < a := hβa
    have hd := hC (β * t) ⟨hxt0.le, hxta.le⟩
    rw [Real.norm_eq_abs] at hd
    have hw0 : 0 ≤ kernelWeight t := by
      unfold kernelWeight
      positivity
    have hnum : t * |deriv φ (β * t)| ≤ C := by
      calc
        t * |deriv φ (β * t)| ≤ |deriv φ (β * t)| :=
          mul_le_of_le_one_left (abs_nonneg _) ht.2
        _ ≤ C := hd
    rw [Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_nonneg ht.1.le, abs_of_nonneg hw0]
    exact mul_le_mul_of_nonneg_right hnum hw0
  have hbound_int :
      IntervalIntegrable (fun t : ℝ => C * kernelWeight t)
        volume 0 1 :=
    kernelWeight_intervalIntegrable.const_mul C
  have hdiff :
      ∀ᵐ t ∂volume, t ∈ Set.uIoc (0 : ℝ) 1 →
        ∀ β ∈ s,
          HasDerivAt
            (fun β => φ (β * t) * kernelWeight t)
            (t * deriv φ (β * t) * kernelWeight t) β := by
    filter_upwards [] with t ht β hβ
    rw [Set.uIoc_of_le (by norm_num)] at ht
    have hβ0 : 0 < β := by
      have : δ ≤ β := hβ.1
      linarith
    have hβa : β < a := by
      have : β ≤ r := hβ.2
      linarith
    have hxt0 : 0 < β * t := mul_pos hβ0 ht.1
    have hxta : β * t < a := by
      calc
        β * t ≤ β := mul_le_of_le_one_right hβ0.le ht.2
        _ < a := hβa
    have hxmem : β * t ∈ Set.Icc (0 : ℝ) a :=
      ⟨hxt0.le, hxta.le⟩
    have hxnhds : Set.Icc (0 : ℝ) a ∈ 𝓝 (β * t) :=
      Icc_mem_nhds hxt0 hxta
    have hφ' :
        HasDerivAt φ (deriv φ (β * t)) (β * t) :=
      ((hreg.1 (β * t) hxmem).differentiableAt hxnhds).hasDerivAt
    have hmul :
        HasDerivAt (fun q : ℝ => q * t) t β := by
      simpa using (hasDerivAt_id β).mul_const t
    convert (hφ'.comp β hmul).mul_const (kernelWeight t) using 1 <;>
      ring
  unfold scaledCore weightedDerivativeCore
  exact
    (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun β t => φ (β * t) * kernelWeight t)
      (F' := fun β t => t * deriv φ (β * t) * kernelWeight t)
      (bound := fun t => C * kernelWeight t)
      (s := s) hs hF_meas hF_int hF'_meas hbound hbound_int hdiff).2

private theorem hasDerivAt_scaledValue
    (a : ℝ) (φ : ℝ → ℝ) (ha : 0 < a)
    (hreg : RegularOn φ a)
    (α : ℝ) (hα : 0 < α) (hαa : α < a) :
    HasDerivAt (scaledValue φ)
      ((1 / (2 * Real.sqrt α)) * scaledCore φ α +
        Real.sqrt α * weightedDerivativeCore φ α) α := by
  have hsqrt :
      HasDerivAt Real.sqrt (1 / (2 * Real.sqrt α)) α := by
    simpa [one_div] using Real.hasDerivAt_sqrt hα.ne'
  have hcore := hasDerivAt_scaledCore a φ ha hreg α hα hαa
  unfold scaledValue
  convert hsqrt.mul hcore using 1 <;> ring

private theorem deriv_abel_formula
    (a : ℝ) (φ : ℝ → ℝ) (ha : 0 < a)
    (hreg : RegularOn φ a)
    (α : ℝ) (hα : 0 < α) (hαa : α < a) :
    deriv (abelIntegral φ) α =
      (1 / (2 * Real.sqrt α)) * scaledCore φ α +
        Real.sqrt α * weightedDerivativeCore φ α := by
  have heq : abelIntegral φ =ᶠ[𝓝 α] scaledValue φ := by
    filter_upwards [Ioi_mem_nhds hα] with β hβ
    exact abelIntegral_eq_scaledValue φ β hβ
  rw [heq.deriv_eq]
  exact (hasDerivAt_scaledValue a φ ha hreg α hα hαa).deriv

private def sqrtDerivativeCore (φ : ℝ → ℝ) (α : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, deriv φ (α * t) * Real.sqrt (1 - t)

private theorem sqrtDerivativeFunction_intervalIntegrable
    (a : ℝ) (φ : ℝ → ℝ) (ha : 0 < a)
    (hreg : RegularOn φ a)
    (α : ℝ) (hα : 0 ≤ α) (hαa : α ≤ a) :
    IntervalIntegrable
      (fun t : ℝ => deriv φ (α * t) * Real.sqrt (1 - t))
      volume 0 1 := by
  have hcomp :
      ContinuousOn (fun t : ℝ => deriv φ (α * t))
        (Set.uIcc 0 1) := by
    apply hreg.2.comp (continuous_const.mul continuous_id).continuousOn
    intro t ht
    rw [Set.uIcc_of_le (by norm_num)] at ht
    constructor
    · exact mul_nonneg hα ht.1
    · exact (mul_le_of_le_one_right hα ht.2).trans hαa
  have hroot :
      ContinuousOn (fun t : ℝ => Real.sqrt (1 - t))
        (Set.uIcc 0 1) :=
    (continuous_const.sub continuous_id).sqrt.continuousOn
  exact (hcomp.mul hroot).intervalIntegrable

private theorem integration_by_parts_identity
    (a : ℝ) (φ : ℝ → ℝ) (ha : 0 < a)
    (hreg : RegularOn φ a)
    (α : ℝ) (hα : 0 < α) (hαa : α < a) :
    (1 / 2 : ℝ) * scaledCore φ α =
      φ 0 + α * sqrtDerivativeCore φ α := by
  let G : ℝ → ℝ := fun t => φ (α * t) * Real.sqrt (1 - t)
  let Aterm : ℝ → ℝ :=
    fun t => α * deriv φ (α * t) * Real.sqrt (1 - t)
  let Bterm : ℝ → ℝ :=
    fun t => φ (α * t) / (2 * Real.sqrt (1 - t))
  have hφcomp :
      ContinuousOn (fun t : ℝ => φ (α * t)) (Set.uIcc 0 1) := by
    apply hreg.1.continuousOn.comp
      (continuous_const.mul continuous_id).continuousOn
    intro t ht
    rw [Set.uIcc_of_le (by norm_num)] at ht
    constructor
    · exact mul_nonneg hα.le ht.1
    · exact
        (mul_le_of_le_one_right hα.le ht.2).trans hαa.le
  have hGcont : ContinuousOn G (Set.uIcc 0 1) :=
    hφcomp.mul ((continuous_const.sub continuous_id).sqrt.continuousOn)
  have hsqrtInt :=
    sqrtDerivativeFunction_intervalIntegrable
      a φ ha hreg α hα.le hαa.le
  have hAint : IntervalIntegrable Aterm volume 0 1 := by
    have h := hsqrtInt.const_mul α
    exact h.congr fun t _ => by
      dsimp [Aterm]
      ring
  have hscaledInt :=
    scaledFunction_intervalIntegrable a φ ha hreg α hα.le hαa.le
  have hBint : IntervalIntegrable Bterm volume 0 1 := by
    have h := hscaledInt.const_mul (1 / 2 : ℝ)
    apply h.congr
    intro t _
    dsimp [Bterm]
    unfold kernelWeight
    ring
  have hGderiv :
      ∀ t ∈ Set.Ioo (0 : ℝ) 1,
        HasDerivWithinAt G (Aterm t - Bterm t) (Set.Ioi t) t := by
    intro t ht
    have hxt0 : 0 < α * t := mul_pos hα ht.1
    have hxta : α * t < a := by
      calc
        α * t ≤ α := mul_le_of_le_one_right hα.le ht.2.le
        _ < a := hαa
    have hxmem : α * t ∈ Set.Icc (0 : ℝ) a :=
      ⟨hxt0.le, hxta.le⟩
    have hxnhds : Set.Icc (0 : ℝ) a ∈ 𝓝 (α * t) :=
      Icc_mem_nhds hxt0 hxta
    have hφ' :
        HasDerivAt φ (deriv φ (α * t)) (α * t) :=
      ((hreg.1 (α * t) hxmem).differentiableAt hxnhds).hasDerivAt
    have hmul :
        HasDerivAt (fun q : ℝ => α * q) α t := by
      simpa using (hasDerivAt_const t α).mul (hasDerivAt_id t)
    have hφt := hφ'.comp t hmul
    have hinner :
        HasDerivAt (fun q : ℝ => 1 - q) (-1) t := by
      convert (hasDerivAt_const t 1).sub (hasDerivAt_id t) using 1 <;>
        norm_num
    have hroot :
        HasDerivAt (fun q : ℝ => Real.sqrt (1 - q))
          (-1 / (2 * Real.sqrt (1 - t))) t := by
      have hpos : 0 < 1 - t := sub_pos.mpr ht.2
      convert (Real.hasDerivAt_sqrt hpos.ne').comp t hinner using 1 <;>
        field_simp [Real.sqrt_ne_zero'.mpr hpos] <;> ring
    apply (hφt.mul hroot).hasDerivWithinAt.congr_deriv
    dsimp [G, Aterm, Bterm]
    ring
  have hFTC :
      (∫ t in (0 : ℝ)..1, (Aterm t - Bterm t)) =
        G 1 - G 0 :=
    intervalIntegral.integral_eq_sub_of_hasDeriv_right
      hGcont (by simpa using hGderiv) (hAint.sub hBint)
  have hAval :
      (∫ t in (0 : ℝ)..1, Aterm t) =
        α * sqrtDerivativeCore φ α := by
    unfold Aterm sqrtDerivativeCore
    calc
      (∫ t in (0 : ℝ)..1,
          α * deriv φ (α * t) * Real.sqrt (1 - t)) =
          ∫ t in (0 : ℝ)..1,
            α * (deriv φ (α * t) * Real.sqrt (1 - t)) := by
              apply intervalIntegral.integral_congr
              intro t _
              ring
      _ = α * ∫ t in (0 : ℝ)..1,
          deriv φ (α * t) * Real.sqrt (1 - t) :=
        intervalIntegral.integral_const_mul
          (a := (0 : ℝ)) (b := 1) (μ := volume)
          α (fun t : ℝ => deriv φ (α * t) * Real.sqrt (1 - t))
  have hBval :
      (∫ t in (0 : ℝ)..1, Bterm t) =
        (1 / 2 : ℝ) * scaledCore φ α := by
    unfold Bterm scaledCore
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    unfold kernelWeight
    ring
  rw [intervalIntegral.integral_sub hAint hBint, hAval, hBval] at hFTC
  norm_num [G] at hFTC
  linarith

private theorem sqrtDerivativeCore_eq_sub
    (a : ℝ) (φ : ℝ → ℝ) (ha : 0 < a)
    (hreg : RegularOn φ a)
    (α : ℝ) (hα : 0 < α) (hαa : α < a) :
    sqrtDerivativeCore φ α =
      derivativeCore φ α - weightedDerivativeCore φ α := by
  have hD0 :=
    derivativeFunction_intervalIntegrable
      a φ ha hreg α hα.le hαa.le
  have hD1 :=
    weightedDerivativeFunction_intervalIntegrable
      a φ ha hreg α hα.le hαa.le
  unfold sqrtDerivativeCore derivativeCore weightedDerivativeCore
  rw [← intervalIntegral.integral_sub hD0 hD1]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le (by norm_num)] at ht
  have hnonneg : 0 ≤ 1 - t := by linarith [ht.2]
  have hrootEq :
      Real.sqrt (1 - t) = (1 - t) * kernelWeight t := by
    by_cases hzero : 1 - t = 0
    · simp [hzero, kernelWeight]
    · have hs : Real.sqrt (1 - t) ≠ 0 :=
        (Real.sqrt_pos.2
          (lt_of_le_of_ne hnonneg (Ne.symm hzero))).ne'
      unfold kernelWeight
      field_simp [hs]
      rw [Real.sq_sqrt hnonneg]
  change
    deriv φ (α * t) * Real.sqrt (1 - t) =
      deriv φ (α * t) * kernelWeight t -
        t * deriv φ (α * t) * kernelWeight t
  rw [hrootEq]
  ring

private theorem scaled_derivative_eq
    (a : ℝ) (φ : ℝ → ℝ) (ha : 0 < a)
    (hreg : RegularOn φ a)
    (α : ℝ) (hα : 0 < α) (hαa : α < a) :
    (1 / (2 * Real.sqrt α)) * scaledCore φ α +
        Real.sqrt α * weightedDerivativeCore φ α =
      φ 0 / Real.sqrt α + Real.sqrt α * derivativeCore φ α := by
  have hparts :=
    integration_by_parts_identity a φ ha hreg α hα hαa
  rw [sqrtDerivativeCore_eq_sub a φ ha hreg α hα hαa] at hparts
  have hs0 : Real.sqrt α ≠ 0 := (Real.sqrt_pos.2 hα).ne'
  have hs2 : Real.sqrt α ^ 2 = α := Real.sq_sqrt hα.le
  calc
    (1 / (2 * Real.sqrt α)) * scaledCore φ α +
        Real.sqrt α * weightedDerivativeCore φ α =
        (1 / Real.sqrt α) *
          ((1 / 2 : ℝ) * scaledCore φ α +
            α * weightedDerivativeCore φ α) := by
              field_simp [hs0]
              rw [hs2]
              ring
    _ =
        (1 / Real.sqrt α) *
          (φ 0 + α *
            (derivativeCore φ α - weightedDerivativeCore φ α) +
            α * weightedDerivativeCore φ α) := by rw [hparts]
    _ =
        φ 0 / Real.sqrt α + Real.sqrt α * derivativeCore φ α := by
              field_simp [hs0]
              rw [hs2]
              ring

theorem gap1 (α t : ℝ) (hα : 0 ≤ α)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∃ x ∈ Set.Icc (0 : ℝ) α, x = α * t := by
  refine ⟨α * t, ?_, rfl⟩
  exact
    ⟨mul_nonneg hα ht.1,
      mul_le_of_le_one_right hα ht.2⟩

theorem gap2 (a α : ℝ) (φ : ℝ → ℝ) (hα : 0 < α)
    (hαa : α < a) (hreg : RegularOn φ a) :
    abelIntegral φ α = scaledIntegral φ α := by
  unfold abelIntegral scaledIntegral
  simpa [kernelWeight, div_eq_mul_inv] using abel_scale φ α hα

theorem gap3 (a α : ℝ) (φ : ℝ → ℝ) (hα : 0 < α)
    (hαa : α < a) (hreg : RegularOn φ a) :
    deriv (abelIntegral φ) α = scaledDerivative φ α := by
  have hcore :
      scaledCore φ α =
        ∫ t in (0 : ℝ)..1, φ (α * t) / Real.sqrt (1 - t) := by
    unfold scaledCore
    apply intervalIntegral.integral_congr
    intro t _
    simp [kernelWeight, div_eq_mul_inv]
  have hweighted :
      weightedDerivativeCore φ α =
        ∫ t in (0 : ℝ)..1,
          t * deriv φ (α * t) / Real.sqrt (1 - t) := by
    unfold weightedDerivativeCore
    apply intervalIntegral.integral_congr
    intro t _
    simp [kernelWeight, div_eq_mul_inv]
  rw [deriv_abel_formula a φ (lt_trans hα hαa) hreg α hα hαa]
  rw [hcore, hweighted]
  unfold scaledDerivative
  ring

private theorem weighted_abel_scale
    (φ : ℝ → ℝ) (α : ℝ) (hα : 0 < α) :
    (∫ x in (0 : ℝ)..α,
        x * deriv φ x / Real.sqrt (α - x)) =
      Real.sqrt α * (α * weightedDerivativeCore φ α) := by
  rw [abel_scale (fun x => x * deriv φ x) α hα]
  congr 1
  unfold weightedDerivativeCore
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  ring

theorem gap4 (a α : ℝ) (φ : ℝ → ℝ) (hα : 0 < α)
    (hαa : α < a) (hreg : RegularOn φ a) :
    deriv (abelIntegral φ) α =
      (1 / (2 * α)) * abelIntegral φ α +
        (1 / α) *
          ∫ x in (0 : ℝ)..α,
            x * deriv φ x / Real.sqrt (α - x) := by
  rw [deriv_abel_formula a φ (lt_trans hα hαa) hreg α hα hαa]
  rw [abelIntegral_eq_scaledValue φ α hα,
    weighted_abel_scale φ α hα]
  unfold scaledValue
  let C : ℝ := scaledCore φ α
  let W : ℝ := weightedDerivativeCore φ α
  change
    (1 / (2 * Real.sqrt α)) * C + Real.sqrt α * W =
      (1 / (2 * α)) * (Real.sqrt α * C) +
        (1 / α) * (Real.sqrt α * (α * W))
  have hs0 : Real.sqrt α ≠ 0 := (Real.sqrt_pos.2 hα).ne'
  have hs2 : Real.sqrt α ^ 2 = α := Real.sq_sqrt hα.le
  field_simp [hα.ne', hs0]
  rw [hs2]
  ring

private theorem sqrtDerivative_scale
    (φ : ℝ → ℝ) (α : ℝ) (hα : 0 < α) :
    (∫ x in (0 : ℝ)..α,
        Real.sqrt (α - x) * deriv φ x) =
      α * Real.sqrt α * sqrtDerivativeCore φ α := by
  have hscale :=
    intervalIntegral.smul_integral_comp_mul_right
      (f := fun x : ℝ => Real.sqrt (α - x) * deriv φ x)
      (a := (0 : ℝ)) (b := 1) α
  norm_num only [zero_mul, one_mul, smul_eq_mul] at hscale
  calc
    (∫ x in (0 : ℝ)..α,
        Real.sqrt (α - x) * deriv φ x) =
        α * ∫ t in (0 : ℝ)..1,
          Real.sqrt (α - t * α) * deriv φ (t * α) :=
      hscale.symm
    _ = α * ∫ t in (0 : ℝ)..1,
          Real.sqrt α *
            (deriv φ (α * t) * Real.sqrt (1 - t)) := by
      congr 1
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le (by norm_num)] at ht
      have hnonneg : 0 ≤ 1 - t := by linarith [ht.2]
      change
        Real.sqrt (α - t * α) * deriv φ (t * α) =
          Real.sqrt α * (deriv φ (α * t) * Real.sqrt (1 - t))
      rw [show α - t * α = α * (1 - t) by ring,
        Real.sqrt_mul hα.le]
      ring
    _ = α * (Real.sqrt α *
          ∫ t in (0 : ℝ)..1,
            deriv φ (α * t) * Real.sqrt (1 - t)) := by
      rw [intervalIntegral.integral_const_mul]
    _ = α * Real.sqrt α * sqrtDerivativeCore φ α := by
      unfold sqrtDerivativeCore
      ring

theorem gap5 (a α : ℝ) (φ : ℝ → ℝ) (hα : 0 < α)
    (hαa : α < a) (hreg : RegularOn φ a) :
    (1 / α) * abelIntegral φ α =
      (2 / Real.sqrt α) * φ 0 +
        (2 / α) *
          ∫ x in (0 : ℝ)..α, Real.sqrt (α - x) * deriv φ x := by
  have hparts :=
    integration_by_parts_identity
      a φ (lt_trans hα hαa) hreg α hα hαa
  rw [abelIntegral_eq_scaledValue φ α hα,
    sqrtDerivative_scale φ α hα]
  unfold scaledValue
  let C : ℝ := scaledCore φ α
  let S : ℝ := sqrtDerivativeCore φ α
  change
    (1 / α) * (Real.sqrt α * C) =
      (2 / Real.sqrt α) * φ 0 +
        (2 / α) * (α * Real.sqrt α * S)
  change (1 / 2 : ℝ) * C = φ 0 + α * S at hparts
  have hcore : C = 2 * (φ 0 + α * S) := by
    linarith [hparts]
  have hs0 : Real.sqrt α ≠ 0 := (Real.sqrt_pos.2 hα).ne'
  have hs2 : Real.sqrt α ^ 2 = α := Real.sq_sqrt hα.le
  rw [hcore]
  field_simp [hα.ne', hs0]
  rw [hs2]

theorem gap6 (a α : ℝ) (φ : ℝ → ℝ) (hα : 0 < α)
    (hαa : α < a) (hreg : RegularOn φ a) :
    (∫ x in (0 : ℝ)..α,
        x * deriv φ x / Real.sqrt (α - x)) =
      -(∫ x in (0 : ℝ)..α, Real.sqrt (α - x) * deriv φ x) +
        α * ∫ x in (0 : ℝ)..α,
          deriv φ x / Real.sqrt (α - x) := by
  rw [weighted_abel_scale φ α hα,
    sqrtDerivative_scale φ α hα,
    abel_scale (deriv φ) α hα,
    sqrtDerivativeCore_eq_sub
      a φ (lt_trans hα hαa) hreg α hα hαa]
  change
    Real.sqrt α * (α * weightedDerivativeCore φ α) =
      -(α * Real.sqrt α *
          (derivativeCore φ α - weightedDerivativeCore φ α)) +
        α * (Real.sqrt α * derivativeCore φ α)
  ring

theorem gap7 (a α : ℝ) (φ : ℝ → ℝ) (hα : 0 < α)
    (hαa : α < a) (hreg : RegularOn φ a) :
    deriv (abelIntegral φ) α = finalDerivative φ α := by
  rw [deriv_abel_formula
      a φ (lt_trans hα hαa) hreg α hα hαa,
    scaled_derivative_eq
      a φ (lt_trans hα hαa) hreg α hα hαa]
  have hscale := abel_scale (deriv φ) α hα
  unfold finalDerivative derivativeCore
  rw [hscale]

theorem gap8 (a : ℝ) (φ : ℝ → ℝ) (hreg : RegularOn φ a) :
    ∀ α ∈ Set.Ioo (0 : ℝ) a,
      deriv (abelIntegral φ) α = finalDerivative φ α := by
  intro α hα
  exact gap7 a α φ hα.1 hα.2 hreg

end

end ProofGap.Exercise3727
