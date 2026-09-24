import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace ProofGap.Exercise4433

noncomputable section

open Filter MeasureTheory
open scoped Interval Topology

def angularDifferenceQuotient
    (aPhi : ℝ → ℝ → ℝ) (r φ h : ℝ) : ℝ :=
  (aPhi r (φ + h) - aPhi r φ) / h

def radialWeightedDifferenceQuotient
    (aR : ℝ → ℝ → ℝ) (r φ h : ℝ) : ℝ :=
  ((r + h) * aR (r + h) φ - r * aR r φ) / h

def angularFaceFlux
    (aPhi : ℝ → ℝ → ℝ) (r φ Δr Δφ : ℝ) : ℝ :=
  ∫ s in r..r + Δr, aPhi s (φ + Δφ) - aPhi s φ

def radialFaceFlux
    (aR : ℝ → ℝ → ℝ) (r φ Δr Δφ : ℝ) : ℝ :=
  ∫ θ in φ..φ + Δφ,
    (r + Δr) * aR (r + Δr) θ - r * aR r θ

def rectangleFlux (aR aPhi : ℝ → ℝ → ℝ)
    (r φ Δr Δφ : ℝ) : ℝ :=
  angularFaceFlux aPhi r φ Δr Δφ +
    radialFaceFlux aR r φ Δr Δφ

def polarRectangleArea (r Δr Δφ : ℝ) : ℝ :=
  ∫ s in r..r + Δr, ∫ _θ in (0 : ℝ)..Δφ, s

def normalizedFlux (aR aPhi : ℝ → ℝ → ℝ)
    (r φ Δr Δφ : ℝ) : ℝ :=
  rectangleFlux aR aPhi r φ Δr Δφ /
    polarRectangleArea r Δr Δφ

def positiveIncrements : Set (ℝ × ℝ) :=
  {h | 0 < h.1 ∧ 0 < h.2}

def HasPolarFluxLimit (aR aPhi : ℝ → ℝ → ℝ)
    (r φ value : ℝ) : Prop :=
  Tendsto
    (fun h : ℝ × ℝ => normalizedFlux aR aPhi r φ h.1 h.2)
    (nhdsWithin (0, 0) positiveIncrements) (nhds value)

def polarDivergence (aR aPhi : ℝ → ℝ → ℝ)
    (r φ : ℝ) : ℝ :=
  1 / r *
    (deriv (fun s => s * aR s φ) r +
      deriv (fun θ => aPhi r θ) φ)

private def angularDerivative
    (aPhi : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  fderiv ℝ (fun q : ℝ × ℝ => aPhi q.1 q.2) p (0, 1)

private def weightedRadial (aR : ℝ → ℝ → ℝ)
    (p : ℝ × ℝ) : ℝ :=
  p.1 * aR p.1 p.2

private def radialDerivative
    (aR : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  fderiv ℝ (weightedRadial aR) p (1, 0)

private lemma angularDerivative_eq_deriv
    (aPhi : ℝ → ℝ → ℝ)
    (hPhi : ContDiff ℝ 1 (fun p : ℝ × ℝ => aPhi p.1 p.2))
    (s θ : ℝ) :
    angularDerivative aPhi (s, θ) =
      deriv (fun x => aPhi s x) θ := by
  have hs :
      HasFDerivAt (fun x : ℝ => (s, x))
        ((0 : ℝ →L[ℝ] ℝ).prod (1 : ℝ →L[ℝ] ℝ)) θ := by
    fun_prop
  have hc :=
    (hPhi.differentiable one_ne_zero).differentiableAt.hasFDerivAt.comp θ hs
  simpa [angularDerivative] using hc.hasDerivAt.deriv.symm

private lemma radialDerivative_eq_deriv
    (aR : ℝ → ℝ → ℝ)
    (hR : ContDiff ℝ 1 (fun p : ℝ × ℝ => aR p.1 p.2))
    (s θ : ℝ) :
    radialDerivative aR (s, θ) =
      deriv (fun x => x * aR x θ) s := by
  have hw : ContDiff ℝ 1 (weightedRadial aR) := by
    unfold weightedRadial
    exact contDiff_fst.mul hR
  have hs :
      HasFDerivAt (fun x : ℝ => (x, θ))
        ((1 : ℝ →L[ℝ] ℝ).prod (0 : ℝ →L[ℝ] ℝ)) s := by
    fun_prop
  have hc :=
    (hw.differentiable one_ne_zero).differentiableAt.hasFDerivAt.comp s hs
  simpa [radialDerivative, weightedRadial] using hc.hasDerivAt.deriv.symm

private lemma angularDerivative_continuous
    (aPhi : ℝ → ℝ → ℝ)
    (hPhi : ContDiff ℝ 1 (fun p : ℝ × ℝ => aPhi p.1 p.2)) :
    Continuous (angularDerivative aPhi) := by
  have hf :
      ContDiff ℝ 0
        (fderiv ℝ (fun p : ℝ × ℝ => aPhi p.1 p.2)) :=
    hPhi.fderiv_right (m := 0) (by norm_num)
  unfold angularDerivative
  exact (hf.clm_apply contDiff_const).continuous

private lemma radialDerivative_continuous
    (aR : ℝ → ℝ → ℝ)
    (hR : ContDiff ℝ 1 (fun p : ℝ × ℝ => aR p.1 p.2)) :
    Continuous (radialDerivative aR) := by
  have hw : ContDiff ℝ 1 (weightedRadial aR) := by
    unfold weightedRadial
    exact contDiff_fst.mul hR
  have hf : ContDiff ℝ 0 (fderiv ℝ (weightedRadial aR)) :=
    hw.fderiv_right (m := 0) (by norm_num)
  unfold radialDerivative
  exact (hf.clm_apply contDiff_const).continuous

private def angularAverage
    (aPhi : ℝ → ℝ → ℝ) (r φ : ℝ) (h : ℝ × ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1,
    ∫ u in (0 : ℝ)..1,
      angularDerivative aPhi (r + h.1 * t, φ + h.2 * u)

private def radialAverage
    (aR : ℝ → ℝ → ℝ) (r φ : ℝ) (h : ℝ × ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1,
    ∫ u in (0 : ℝ)..1,
      radialDerivative aR (r + h.1 * u, φ + h.2 * t)

private lemma angularAverage_continuous
    (aPhi : ℝ → ℝ → ℝ) (r φ : ℝ)
    (hPhi : ContDiff ℝ 1 (fun p : ℝ × ℝ => aPhi p.1 p.2)) :
    Continuous (angularAverage aPhi r φ) := by
  have hD := angularDerivative_continuous aPhi hPhi
  have hinner :
      Continuous
        (fun z : (ℝ × ℝ) × ℝ =>
          ∫ u in (0 : ℝ)..1,
            angularDerivative aPhi
              (r + z.1.1 * z.2, φ + z.1.2 * u)) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    exact hD.comp (by fun_prop)
  unfold angularAverage
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact hinner

private lemma radialAverage_continuous
    (aR : ℝ → ℝ → ℝ) (r φ : ℝ)
    (hR : ContDiff ℝ 1 (fun p : ℝ × ℝ => aR p.1 p.2)) :
    Continuous (radialAverage aR r φ) := by
  have hD := radialDerivative_continuous aR hR
  have hinner :
      Continuous
        (fun z : (ℝ × ℝ) × ℝ =>
          ∫ u in (0 : ℝ)..1,
            radialDerivative aR
              (r + z.1.1 * u, φ + z.1.2 * z.2)) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    exact hD.comp (by fun_prop)
  unfold radialAverage
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact hinner

private lemma angularAverage_zero
    (aPhi : ℝ → ℝ → ℝ) (r φ : ℝ) :
    angularAverage aPhi r φ (0, 0) =
      angularDerivative aPhi (r, φ) := by
  simp [angularAverage]

private lemma radialAverage_zero
    (aR : ℝ → ℝ → ℝ) (r φ : ℝ) :
    radialAverage aR r φ (0, 0) =
      radialDerivative aR (r, φ) := by
  simp [radialAverage]

private lemma angularDifferenceQuotient_eq_integral
    (aPhi : ℝ → ℝ → ℝ)
    (hPhi : ContDiff ℝ 1 (fun p : ℝ × ℝ => aPhi p.1 p.2))
    (s φ h : ℝ) (hh : h ≠ 0) :
    angularDifferenceQuotient aPhi s φ h =
      ∫ u in (0 : ℝ)..1,
        angularDerivative aPhi (s, φ + h * u) := by
  have hslice : ContDiff ℝ 1 (fun x => aPhi s x) := by
    exact hPhi.comp (contDiff_const.prodMk contDiff_id)
  have hFTC :
      (∫ x in φ..φ + h, angularDerivative aPhi (s, x)) =
        aPhi s (φ + h) - aPhi s φ := by
    calc
      (∫ x in φ..φ + h, angularDerivative aPhi (s, x)) =
          ∫ x in φ..φ + h, deriv (fun y => aPhi s y) x := by
            apply intervalIntegral.integral_congr
            intro x hx
            exact angularDerivative_eq_deriv aPhi hPhi s x
      _ = aPhi s (φ + h) - aPhi s φ :=
        intervalIntegral.integral_deriv_of_contDiffOn_uIcc hslice.contDiffOn
  have hchange :
      h * (∫ u in (0 : ℝ)..1,
        angularDerivative aPhi (s, φ + h * u)) =
        ∫ x in φ..φ + h, angularDerivative aPhi (s, x) := by
    simpa only [smul_eq_mul, mul_zero, add_zero, mul_one] using
      (intervalIntegral.smul_integral_comp_add_mul
        (a := (0 : ℝ)) (b := 1)
        (fun x => angularDerivative aPhi (s, x)) h φ)
  rw [angularDifferenceQuotient]
  apply (div_eq_iff hh).2
  calc
    aPhi s (φ + h) - aPhi s φ =
        h * (∫ u in (0 : ℝ)..1,
          angularDerivative aPhi (s, φ + h * u)) :=
      (hchange.trans hFTC).symm
    _ = (∫ u in (0 : ℝ)..1,
          angularDerivative aPhi (s, φ + h * u)) * h := by ring

private lemma radialDifferenceQuotient_eq_integral
    (aR : ℝ → ℝ → ℝ)
    (hR : ContDiff ℝ 1 (fun p : ℝ × ℝ => aR p.1 p.2))
    (r θ h : ℝ) (hh : h ≠ 0) :
    radialWeightedDifferenceQuotient aR r θ h =
      ∫ u in (0 : ℝ)..1,
        radialDerivative aR (r + h * u, θ) := by
  have hw : ContDiff ℝ 1 (fun x => x * aR x θ) := by
    exact contDiff_id.mul (hR.comp (contDiff_id.prodMk contDiff_const))
  have hFTC :
      (∫ x in r..r + h, radialDerivative aR (x, θ)) =
        (r + h) * aR (r + h) θ - r * aR r θ := by
    calc
      (∫ x in r..r + h, radialDerivative aR (x, θ)) =
          ∫ x in r..r + h, deriv (fun y => y * aR y θ) x := by
            apply intervalIntegral.integral_congr
            intro x hx
            exact radialDerivative_eq_deriv aR hR x θ
      _ = (r + h) * aR (r + h) θ - r * aR r θ :=
        intervalIntegral.integral_deriv_of_contDiffOn_uIcc hw.contDiffOn
  have hchange :
      h * (∫ u in (0 : ℝ)..1,
        radialDerivative aR (r + h * u, θ)) =
        ∫ x in r..r + h, radialDerivative aR (x, θ) := by
    simpa only [smul_eq_mul, mul_zero, add_zero, mul_one] using
      (intervalIntegral.smul_integral_comp_add_mul
        (a := (0 : ℝ)) (b := 1)
        (fun x => radialDerivative aR (x, θ)) h r)
  rw [radialWeightedDifferenceQuotient]
  apply (div_eq_iff hh).2
  calc
    (r + h) * aR (r + h) θ - r * aR r θ =
        h * (∫ u in (0 : ℝ)..1,
          radialDerivative aR (r + h * u, θ)) :=
      (hchange.trans hFTC).symm
    _ = (∫ u in (0 : ℝ)..1,
          radialDerivative aR (r + h * u, θ)) * h := by ring

private lemma angularFaceFlux_eq_average
    (aPhi : ℝ → ℝ → ℝ)
    (hPhi : ContDiff ℝ 1 (fun p : ℝ × ℝ => aPhi p.1 p.2))
    (r φ Δr Δφ : ℝ) (hΔφ : Δφ ≠ 0) :
    angularFaceFlux aPhi r φ Δr Δφ =
      Δr * Δφ * angularAverage aPhi r φ (Δr, Δφ) := by
  have hpoint (s : ℝ) :
      aPhi s (φ + Δφ) - aPhi s φ =
        Δφ * (∫ u in (0 : ℝ)..1,
          angularDerivative aPhi (s, φ + Δφ * u)) := by
    have hq :=
      angularDifferenceQuotient_eq_integral aPhi hPhi s φ Δφ hΔφ
    rw [angularDifferenceQuotient] at hq
    have := (div_eq_iff hΔφ).mp hq
    simpa only [mul_comm] using this
  have hchange :
      Δr * (∫ t in (0 : ℝ)..1,
        ∫ u in (0 : ℝ)..1,
          angularDerivative aPhi
            (r + Δr * t, φ + Δφ * u)) =
        ∫ s in r..r + Δr,
          ∫ u in (0 : ℝ)..1,
            angularDerivative aPhi (s, φ + Δφ * u) := by
    simpa only [smul_eq_mul, mul_zero, add_zero, mul_one] using
      (intervalIntegral.smul_integral_comp_add_mul
        (a := (0 : ℝ)) (b := 1)
        (fun s => ∫ u in (0 : ℝ)..1,
          angularDerivative aPhi (s, φ + Δφ * u)) Δr r)
  unfold angularFaceFlux
  calc
    (∫ s in r..r + Δr, aPhi s (φ + Δφ) - aPhi s φ) =
        ∫ s in r..r + Δr,
          Δφ * (∫ u in (0 : ℝ)..1,
            angularDerivative aPhi (s, φ + Δφ * u)) := by
              apply intervalIntegral.integral_congr
              intro s hs
              exact hpoint s
    _ = Δφ * (∫ s in r..r + Δr,
          ∫ u in (0 : ℝ)..1,
            angularDerivative aPhi (s, φ + Δφ * u)) := by
              rw [intervalIntegral.integral_const_mul]
    _ = Δr * Δφ * angularAverage aPhi r φ (Δr, Δφ) := by
      rw [← hchange]
      unfold angularAverage
      ring

private lemma radialFaceFlux_eq_average
    (aR : ℝ → ℝ → ℝ)
    (hR : ContDiff ℝ 1 (fun p : ℝ × ℝ => aR p.1 p.2))
    (r φ Δr Δφ : ℝ) (hΔr : Δr ≠ 0) :
    radialFaceFlux aR r φ Δr Δφ =
      Δr * Δφ * radialAverage aR r φ (Δr, Δφ) := by
  have hpoint (θ : ℝ) :
      (r + Δr) * aR (r + Δr) θ - r * aR r θ =
        Δr * (∫ u in (0 : ℝ)..1,
          radialDerivative aR (r + Δr * u, θ)) := by
    have hq :=
      radialDifferenceQuotient_eq_integral aR hR r θ Δr hΔr
    rw [radialWeightedDifferenceQuotient] at hq
    simpa only [mul_comm] using (div_eq_iff hΔr).mp hq
  have hchange :
      Δφ * (∫ t in (0 : ℝ)..1,
        ∫ u in (0 : ℝ)..1,
          radialDerivative aR
            (r + Δr * u, φ + Δφ * t)) =
        ∫ θ in φ..φ + Δφ,
          ∫ u in (0 : ℝ)..1,
            radialDerivative aR (r + Δr * u, θ) := by
    simpa only [smul_eq_mul, mul_zero, add_zero, mul_one] using
      (intervalIntegral.smul_integral_comp_add_mul
        (a := (0 : ℝ)) (b := 1)
        (fun θ => ∫ u in (0 : ℝ)..1,
          radialDerivative aR (r + Δr * u, θ)) Δφ φ)
  unfold radialFaceFlux
  calc
    (∫ θ in φ..φ + Δφ,
        (r + Δr) * aR (r + Δr) θ - r * aR r θ) =
        ∫ θ in φ..φ + Δφ,
          Δr * (∫ u in (0 : ℝ)..1,
            radialDerivative aR (r + Δr * u, θ)) := by
              apply intervalIntegral.integral_congr
              intro θ hθ
              exact hpoint θ
    _ = Δr * (∫ θ in φ..φ + Δφ,
          ∫ u in (0 : ℝ)..1,
            radialDerivative aR (r + Δr * u, θ)) := by
              rw [intervalIntegral.integral_const_mul]
    _ = Δr * Δφ * radialAverage aR r φ (Δr, Δφ) := by
      rw [← hchange]
      unfold radialAverage
      ring

private lemma polarRectangleArea_eq
    (r Δr Δφ : ℝ) :
    polarRectangleArea r Δr Δφ =
      Δr * Δφ * (r + Δr / 2) := by
  unfold polarRectangleArea
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  rw [intervalIntegral.integral_const_mul]
  rw [show (∫ s in r..r + Δr, s) =
      ((r + Δr) ^ 2 - r ^ 2) / 2 by
    simpa [pow_two] using
      (integral_pow (a := r) (b := r + Δr) (n := 1))]
  ring

private lemma normalizedFlux_eq_average
    (aR aPhi : ℝ → ℝ → ℝ)
    (hR : ContDiff ℝ 1 (fun p : ℝ × ℝ => aR p.1 p.2))
    (hPhi : ContDiff ℝ 1 (fun p : ℝ × ℝ => aPhi p.1 p.2))
    (r φ Δr Δφ : ℝ) (hΔr : Δr ≠ 0) (hΔφ : Δφ ≠ 0) :
    normalizedFlux aR aPhi r φ Δr Δφ =
      (angularAverage aPhi r φ (Δr, Δφ) +
          radialAverage aR r φ (Δr, Δφ)) /
        (r + Δr / 2) := by
  unfold normalizedFlux rectangleFlux
  rw [angularFaceFlux_eq_average aPhi hPhi r φ Δr Δφ hΔφ,
    radialFaceFlux_eq_average aR hR r φ Δr Δφ hΔr,
    polarRectangleArea_eq]
  rw [← mul_add]
  exact mul_div_mul_left _ _ (mul_ne_zero hΔr hΔφ)

theorem gap1 (aPhi : ℝ → ℝ → ℝ) (r φ : ℝ)
    (hDerivative :
      HasDerivAt (fun θ => aPhi r θ)
        (deriv (fun θ => aPhi r θ) φ) φ) :
    Tendsto (fun h => angularDifferenceQuotient aPhi r φ h)
      (nhdsWithin 0 ({0}ᶜ))
      (nhds (deriv (fun θ => aPhi r θ) φ)) := by
  simpa only [angularDifferenceQuotient, div_eq_inv_mul, inv_smul_eq_iff₀,
    smul_eq_mul] using hDerivative.tendsto_slope_zero

theorem gap2 (aR : ℝ → ℝ → ℝ) (r φ : ℝ)
    (hDerivative :
      HasDerivAt (fun s => s * aR s φ)
        (deriv (fun s => s * aR s φ) r) r) :
    Tendsto (fun h => radialWeightedDifferenceQuotient aR r φ h)
      (nhdsWithin 0 ({0}ᶜ))
      (nhds (deriv (fun s => s * aR s φ) r)) := by
  simpa only [radialWeightedDifferenceQuotient, div_eq_inv_mul,
    inv_smul_eq_iff₀, smul_eq_mul] using hDerivative.tendsto_slope_zero

theorem gap3 (aR aPhi : ℝ → ℝ → ℝ)
    (r φ Δr Δφ : ℝ) :
    rectangleFlux aR aPhi r φ Δr Δφ =
      (∫ s in r..r + Δr, aPhi s (φ + Δφ) - aPhi s φ) +
      ∫ θ in φ..φ + Δφ,
        (r + Δr) * aR (r + Δr) θ - r * aR r θ := by
  rfl

theorem gap4 (aR aPhi : ℝ → ℝ → ℝ) (r φ : ℝ)
    (hr : 0 < r)
    (hRegular :
      ContDiff ℝ 1 (fun p : ℝ × ℝ => aR p.1 p.2) ∧
      ContDiff ℝ 1 (fun p : ℝ × ℝ => aPhi p.1 p.2)) :
    HasPolarFluxLimit aR aPhi r φ
      (1 / r *
        (deriv (fun s => s * aR s φ) r +
          deriv (fun θ => aPhi r θ) φ)) := by
  rcases hRegular with ⟨hR, hPhi⟩
  have hA := angularAverage_continuous aPhi r φ hPhi
  have hB := radialAverage_continuous aR r φ hR
  have hnum :
      Tendsto
        (fun h : ℝ × ℝ =>
          angularAverage aPhi r φ h + radialAverage aR r φ h)
        (nhdsWithin (0, 0) positiveIncrements)
        (nhds
          (angularDerivative aPhi (r, φ) +
            radialDerivative aR (r, φ))) := by
    have hfull :
        ContinuousAt
          (fun h : ℝ × ℝ =>
            angularAverage aPhi r φ h + radialAverage aR r φ h)
          (0, 0) :=
      (hA.add hB).continuousAt
    convert hfull.mono_left inf_le_left using 1 <;>
      simp [angularAverage_zero, radialAverage_zero]
  have hden :
      Tendsto (fun h : ℝ × ℝ => r + h.1 / 2)
        (nhdsWithin (0, 0) positiveIncrements) (nhds r) := by
    have hfull : ContinuousAt (fun h : ℝ × ℝ => r + h.1 / 2) (0, 0) := by
      fun_prop
    convert hfull.mono_left inf_le_left using 1 <;> norm_num
  have hquot :=
    hnum.div hden (ne_of_gt hr)
  have heq :
      (fun h : ℝ × ℝ =>
        normalizedFlux aR aPhi r φ h.1 h.2) =ᶠ[
          nhdsWithin (0, 0) positiveIncrements]
        (fun h =>
          (angularAverage aPhi r φ h + radialAverage aR r φ h) /
            (r + h.1 / 2)) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact normalizedFlux_eq_average aR aPhi hR hPhi r φ h.1 h.2
      hh.1.ne' hh.2.ne'
  unfold HasPolarFluxLimit
  apply Tendsto.congr' heq.symm
  convert hquot using 1
  rw [angularDerivative_eq_deriv aPhi hPhi r φ,
    radialDerivative_eq_deriv aR hR r φ]
  field_simp [ne_of_gt hr]
  ring

theorem gap5 (aR aPhi : ℝ → ℝ → ℝ) (r φ : ℝ)
    (hr : 0 < r)
    (hRegular :
      ContDiff ℝ 1 (fun p : ℝ × ℝ => aR p.1 p.2) ∧
      ContDiff ℝ 1 (fun p : ℝ × ℝ => aPhi p.1 p.2)) :
    HasPolarFluxLimit aR aPhi r φ
      (polarDivergence aR aPhi r φ) := by
  simpa [polarDivergence] using gap4 aR aPhi r φ hr hRegular

theorem gap6 (aR aPhi : ℝ → ℝ → ℝ) (r φ : ℝ)
    (hr : 0 < r) :
    polarDivergence aR aPhi r φ =
      1 / r *
        (deriv (fun s => s * aR s φ) r +
          deriv (fun θ => aPhi r θ) φ) := by
  rfl

theorem gap7 (aR aPhi : ℝ → ℝ → ℝ) (r φ : ℝ)
    (hr : 0 < r) :
    1 / r *
        (deriv (fun s => s * aR s φ) r +
          deriv (fun θ => aPhi r θ) φ) =
      1 / r *
        (deriv (fun θ => aPhi r θ) φ +
          deriv (fun s => s * aR s φ) r) := by
  ring

theorem gap8 (aR aPhi : ℝ → ℝ → ℝ) (r φ : ℝ)
    (hr : 0 < r) :
    polarDivergence aR aPhi r φ =
      1 / r *
        (deriv (fun s => s * aR s φ) r +
          deriv (fun θ => aPhi r θ) φ) := by
  rfl

end

end ProofGap.Exercise4433
