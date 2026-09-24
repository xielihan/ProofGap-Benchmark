import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ProofGap.Exercise2432
noncomputable section

open MeasureTheory Set
open scoped Interval

def y (p x : ℝ) : ℝ := Real.sqrt (2 * p * x)
def arcIntegrand (p x : ℝ) : ℝ :=
  (1 / Real.sqrt 2) * Real.sqrt (p + 2 * x) / Real.sqrt x
def s (p x₀ : ℝ) : ℝ := 2 * ∫ x in (0 : ℝ)..x₀, arcIntegrand p x

def primitive (p u : ℝ) : ℝ :=
  Real.sqrt 2 * u * Real.sqrt (p + 2 * u ^ 2) +
    p * Real.log ((Real.sqrt 2 * u + Real.sqrt (p + 2 * u ^ 2)) / Real.sqrt p)

def closedForm (p x₀ : ℝ) : ℝ :=
  2 * Real.sqrt (x₀ * (x₀ + p / 2)) +
    p * Real.log
      ((Real.sqrt x₀ + Real.sqrt (x₀ + p / 2)) / Real.sqrt (p / 2))

theorem gap1 (p x : ℝ) (hp : 0 < p) (hx : 0 < x) :
    HasDerivAt (y p) (p / y p x) x := by
  have hi : HasDerivAt (fun t : ℝ => 2 * p * t) (2 * p) x := by
    convert (hasDerivAt_id x).const_mul (2 * p) using 1 <;> ring
  have hs := hi.sqrt (by positivity)
  unfold y
  convert hs using 1
  field_simp [Real.sqrt_ne_zero'.mpr (mul_pos (mul_pos two_pos hp) hx)]

theorem gap2 (p x : ℝ) (hp : 0 < p) (hx : 0 < x) :
    Real.sqrt (1 + (p / y p x) ^ 2) =
      Real.sqrt (1 + p ^ 2 / (y p x) ^ 2) := by
  congr 1
  have hy : y p x ≠ 0 := by
    unfold y
    exact Real.sqrt_ne_zero'.mpr (mul_pos (mul_pos two_pos hp) hx)
  field_simp [hy]

theorem gap3 (p x : ℝ) (hp : 0 < p) (hx : 0 < x) :
    Real.sqrt (1 + p ^ 2 / (y p x) ^ 2) =
      Real.sqrt (1 + p / (2 * x)) := by
  congr 1
  have hy2 : (y p x) ^ 2 = 2 * p * x := by
    unfold y
    exact Real.sq_sqrt (by positivity)
  rw [hy2]
  field_simp [hp.ne', hx.ne']

theorem gap4 (p x : ℝ) (hp : 0 < p) (hx : 0 < x) :
    Real.sqrt (1 + p / (2 * x)) =
      (1 / Real.sqrt 2) * Real.sqrt (p + 2 * x) / Real.sqrt x := by
  have hpx : 0 ≤ p + 2 * x := by positivity
  have h2x : 0 ≤ 2 * x := by positivity
  have hs2 : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  have hsx : Real.sqrt x ≠ 0 := Real.sqrt_ne_zero'.mpr hx
  calc
    Real.sqrt (1 + p / (2 * x)) = Real.sqrt ((p + 2 * x) / (2 * x)) := by
      congr 1
      field_simp [hx.ne']
      ring
    _ = Real.sqrt (p + 2 * x) / Real.sqrt (2 * x) := Real.sqrt_div hpx (2 * x)
    _ = Real.sqrt (p + 2 * x) / (Real.sqrt 2 * Real.sqrt x) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) x]
    _ = (1 / Real.sqrt 2) * Real.sqrt (p + 2 * x) / Real.sqrt x := by
      field_simp [hs2, hsx]

theorem gap5 (p x : ℝ) (hp : 0 < p) (hx : 0 < x) :
    Real.sqrt (1 + (p / y p x) ^ 2) = arcIntegrand p x := by
  rw [gap2 p x hp hx, gap3 p x hp hx, gap4 p x hp hx]
  rfl

theorem gap6 (p x₀ : ℝ) (hp : 0 < p) (hx₀ : 0 ≤ x₀) :
    s p x₀ = 2 * ∫ x in (0 : ℝ)..x₀, arcIntegrand p x := by
  rfl

private theorem primitive_hasDerivAt (p u : ℝ) (hp : 0 < p) (hu : 0 ≤ u) :
    HasDerivAt (primitive p) (2 * Real.sqrt 2 * Real.sqrt (p + 2 * u ^ 2)) u := by
  have hq : 0 < p + 2 * u ^ 2 := by positivity
  have hquad : HasDerivAt (fun t : ℝ => p + 2 * t ^ 2) (4 * u) u := by
    convert (hasDerivAt_const u p).add (((hasDerivAt_id u).pow 2).const_mul 2) using 1 <;>
      simp [id] <;> ring
  have hr := hquad.sqrt hq.ne'
  have hs2u : HasDerivAt (fun t : ℝ => Real.sqrt 2 * t) (Real.sqrt 2) u := by
    convert (hasDerivAt_id u).const_mul (Real.sqrt 2) using 1 <;> ring
  have harg := (hs2u.add hr).div_const (Real.sqrt p)
  have hargPos : 0 <
      (Real.sqrt 2 * u + Real.sqrt (p + 2 * u ^ 2)) / Real.sqrt p := by
    positivity
  have hlog := harg.log hargPos.ne'
  have hfirst := hs2u.mul hr
  have htotal := hfirst.add (hlog.const_mul p)
  unfold primitive
  convert htotal using 1
  have hr0 : Real.sqrt (p + 2 * u ^ 2) ≠ 0 := Real.sqrt_ne_zero'.mpr hq
  have hsp0 : Real.sqrt p ≠ 0 := Real.sqrt_ne_zero'.mpr hp
  have hA0 : Real.sqrt 2 * u + Real.sqrt (p + 2 * u ^ 2) ≠ 0 := by positivity
  have hs2sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hrsq : (Real.sqrt (p + 2 * u ^ 2)) ^ 2 = p + 2 * u ^ 2 :=
    Real.sq_sqrt hq.le
  simp only [Pi.add_apply] at *
  field_simp [hr0, hsp0, hA0]
  rw [hrsq]
  ring_nf
  rw [hs2sq]
  ring

private theorem arcIntegrand_intervalIntegrable (p x₀ : ℝ) (hx₀ : 0 < x₀) :
    IntervalIntegrable (arcIntegrand p) volume 0 x₀ := by
  have hrpow : IntervalIntegrable (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) volume 0 x₀ := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hx₀.le]
    rw [intervalIntegral.integrableOn_Ioo_rpow_iff hx₀]
    norm_num
  have hcont : Continuous (fun x : ℝ =>
      (1 / Real.sqrt 2) * Real.sqrt (p + 2 * x)) := by
    fun_prop
  have hprod := hrpow.continuousOn_mul hcont.continuousOn
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hx₀.le] at hprod ⊢
  refine hprod.congr_fun ?_ measurableSet_Icc
  intro x hx
  unfold arcIntegrand
  change (1 / Real.sqrt 2) * Real.sqrt (p + 2 * x) * x ^ (-(1 / 2 : ℝ)) =
    (1 / Real.sqrt 2) * Real.sqrt (p + 2 * x) / Real.sqrt x
  rw [Real.rpow_neg hx.1 (1 / 2 : ℝ), ← Real.sqrt_eq_rpow]
  simp only [div_eq_mul_inv]

private theorem arcIntegrand_continuousAt (p x : ℝ) (hx : 0 < x) :
    ContinuousAt (arcIntegrand p) x := by
  unfold arcIntegrand
  have hsx : Real.sqrt x ≠ 0 := Real.sqrt_ne_zero'.mpr hx
  apply ContinuousAt.div
  · fun_prop
  · fun_prop
  · exact hsx

theorem gap7 (p x₀ : ℝ) (hp : 0 < p) (hx₀ : 0 ≤ x₀) :
    2 * (∫ x in (0 : ℝ)..x₀, arcIntegrand p x) =
      2 * Real.sqrt 2 *
        ∫ u in (0 : ℝ)..Real.sqrt x₀, Real.sqrt (p + 2 * u ^ 2) := by
  rcases eq_or_lt_of_le hx₀ with hzero | hxpos
  · subst x₀
    simp
  let b := Real.sqrt x₀
  have hb : 0 ≤ b := by
    dsimp [b]
    exact Real.sqrt_nonneg x₀
  have hbpos : 0 < b := by
    dsimp [b]
    exact Real.sqrt_pos.2 hxpos
  have hb2 : b ^ 2 = x₀ := by
    dsimp [b]
    exact Real.sq_sqrt hx₀
  have hf : ContinuousOn (fun u : ℝ => u ^ 2) [[(0 : ℝ), b]] := by
    fun_prop
  have hderiv : ∀ u ∈ Ioo (min (0 : ℝ) b) (max (0 : ℝ) b),
      HasDerivWithinAt (fun t : ℝ => t ^ 2) (2 * u) (Ioi u) u := by
    intro u hu
    convert ((hasDerivAt_id u).pow 2).hasDerivWithinAt using 1 <;>
      simp [id] <;> ring
  have hgcont : ContinuousOn (arcIntegrand p)
      ((fun u : ℝ => u ^ 2) '' Ioo (min (0 : ℝ) b) (max (0 : ℝ) b)) := by
    rintro x ⟨u, hu, rfl⟩
    have hu' : u ∈ Ioo (0 : ℝ) b := by
      simpa [min_eq_left hb, max_eq_right hb] using hu
    exact (arcIntegrand_continuousAt p (u ^ 2) (sq_pos_of_pos hu'.1)).continuousWithinAt
  have hArcIcc : IntegrableOn (arcIntegrand p) (Icc (0 : ℝ) x₀) volume := by
    rw [← intervalIntegrable_iff_integrableOn_Icc_of_le hx₀]
    exact arcIntegrand_intervalIntegrable p x₀ hxpos
  have hg1 : IntegrableOn (arcIntegrand p)
      ((fun u : ℝ => u ^ 2) '' [[(0 : ℝ), b]]) volume := by
    refine hArcIcc.mono_set ?_
    rintro x ⟨u, hu, rfl⟩
    rw [uIcc_of_le hb] at hu
    constructor
    · positivity
    · calc
        u ^ 2 ≤ b ^ 2 := (sq_le_sq₀ hu.1 hb).2 hu.2
        _ = x₀ := hb2
  have htarget : IntegrableOn
      (fun u : ℝ => Real.sqrt 2 * Real.sqrt (p + 2 * u ^ 2)) (Ioc (0 : ℝ) b) volume := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hb]
    exact (by fun_prop : Continuous
      (fun u : ℝ => Real.sqrt 2 * Real.sqrt (p + 2 * u ^ 2))).intervalIntegrable 0 b
  have hg2 : IntegrableOn
      (fun u : ℝ => ((arcIntegrand p) ∘ fun t : ℝ => t ^ 2) u * (2 * u))
      [[(0 : ℝ), b]] volume := by
    rw [uIcc_of_le hb, integrableOn_Icc_iff_integrableOn_Ioc]
    refine htarget.congr_fun ?_ measurableSet_Ioc
    intro u hu
    change Real.sqrt 2 * Real.sqrt (p + 2 * u ^ 2) =
      (1 / Real.sqrt 2) * Real.sqrt (p + 2 * u ^ 2) /
        Real.sqrt (u ^ 2) * (2 * u)
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hu.1]
    have hs2 : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
    have hs2sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    field_simp [hs2, hu.1.ne']
    nlinarith
  have hchange :
      (∫ u in (0 : ℝ)..b,
        ((arcIntegrand p) ∘ fun t : ℝ => t ^ 2) u * (2 * u)) =
        ∫ x in (0 : ℝ)..x₀, arcIntegrand p x := by
    simpa [hb2] using
      (intervalIntegral.integral_comp_mul_deriv'''
        (f := fun u : ℝ => u ^ 2) (f' := fun u : ℝ => 2 * u)
        (g := arcIntegrand p) hf hderiv hgcont hg1 hg2)
  have hcongr :
      (∫ u in (0 : ℝ)..b,
        ((arcIntegrand p) ∘ fun t : ℝ => t ^ 2) u * (2 * u)) =
        ∫ u in (0 : ℝ)..b, Real.sqrt 2 * Real.sqrt (p + 2 * u ^ 2) := by
    apply intervalIntegral.integral_congr_ae
    refine Filter.Eventually.of_forall ?_
    intro u hu
    rw [uIoc_of_le hb] at hu
    change (1 / Real.sqrt 2) * Real.sqrt (p + 2 * u ^ 2) /
        Real.sqrt (u ^ 2) * (2 * u) =
      Real.sqrt 2 * Real.sqrt (p + 2 * u ^ 2)
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hu.1]
    have hs2 : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
    have hs2sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    field_simp [hs2, hu.1.ne']
    nlinarith
  change 2 * (∫ x in (0 : ℝ)..x₀, arcIntegrand p x) =
    2 * Real.sqrt 2 * ∫ u in (0 : ℝ)..b, Real.sqrt (p + 2 * u ^ 2)
  rw [← hchange, hcongr, intervalIntegral.integral_const_mul]
  ring

theorem gap8 (p x₀ : ℝ) (hp : 0 < p) (hx₀ : 0 ≤ x₀) :
    s p x₀ =
      2 * Real.sqrt 2 *
        ∫ u in (0 : ℝ)..Real.sqrt x₀, Real.sqrt (p + 2 * u ^ 2) := by
  rw [gap6 p x₀ hp hx₀, gap7 p x₀ hp hx₀]

theorem gap9 (p x₀ : ℝ) (hp : 0 < p) (hx₀ : 0 ≤ x₀) :
    s p x₀ = primitive p (Real.sqrt x₀) - primitive p 0 := by
  have hsx : 0 ≤ Real.sqrt x₀ := Real.sqrt_nonneg x₀
  have hderiv : ∀ u ∈ [[(0 : ℝ), Real.sqrt x₀]],
      HasDerivAt (primitive p)
        (2 * Real.sqrt 2 * Real.sqrt (p + 2 * u ^ 2)) u := by
    intro u hu
    rw [uIcc_of_le hsx] at hu
    exact primitive_hasDerivAt p u hp hu.1
  have hint : IntervalIntegrable
      (fun u : ℝ => 2 * Real.sqrt 2 * Real.sqrt (p + 2 * u ^ 2))
      volume 0 (Real.sqrt x₀) := by
    exact (by fun_prop : Continuous
      (fun u : ℝ => 2 * Real.sqrt 2 * Real.sqrt (p + 2 * u ^ 2))).intervalIntegrable
        0 (Real.sqrt x₀)
  rw [gap8 p x₀ hp hx₀, ← intervalIntegral.integral_const_mul]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

theorem gap10 (p x₀ : ℝ) (hp : 0 < p) (hx₀ : 0 ≤ x₀) :
    s p x₀ = closedForm p x₀ := by
  have hpx : 0 ≤ x₀ + p / 2 := by positivity
  have hp2 : 0 < p / 2 := by positivity
  have hs2ne : Real.sqrt 2 ≠ 0 := Real.sqrt_ne_zero'.mpr (by norm_num)
  have hsp2ne : Real.sqrt (p / 2) ≠ 0 := Real.sqrt_ne_zero'.mpr hp2
  have hs2sq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrtArg : Real.sqrt (p + 2 * x₀) =
      Real.sqrt 2 * Real.sqrt (x₀ + p / 2) := by
    calc
      Real.sqrt (p + 2 * x₀) = Real.sqrt (2 * (x₀ + p / 2)) := by
        congr 1
        ring
      _ = Real.sqrt 2 * Real.sqrt (x₀ + p / 2) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hsqrtP : Real.sqrt p = Real.sqrt 2 * Real.sqrt (p / 2) := by
    calc
      Real.sqrt p = Real.sqrt (2 * (p / 2)) := by
        congr 1
        ring
      _ = Real.sqrt 2 * Real.sqrt (p / 2) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hsqrtProd : Real.sqrt (x₀ * (x₀ + p / 2)) =
      Real.sqrt x₀ * Real.sqrt (x₀ + p / 2) := by
    rw [Real.sqrt_mul hx₀]
  have hfirst : Real.sqrt 2 * Real.sqrt x₀ * Real.sqrt (p + 2 * x₀) =
      2 * Real.sqrt (x₀ * (x₀ + p / 2)) := by
    rw [hsqrtArg, hsqrtProd]
    calc
      Real.sqrt 2 * Real.sqrt x₀ *
          (Real.sqrt 2 * Real.sqrt (x₀ + p / 2)) =
          (Real.sqrt 2) ^ 2 *
            (Real.sqrt x₀ * Real.sqrt (x₀ + p / 2)) := by ring
      _ = 2 * (Real.sqrt x₀ * Real.sqrt (x₀ + p / 2)) := by rw [hs2sq]
  have harg :
      (Real.sqrt 2 * Real.sqrt x₀ + Real.sqrt (p + 2 * x₀)) / Real.sqrt p =
        (Real.sqrt x₀ + Real.sqrt (x₀ + p / 2)) / Real.sqrt (p / 2) := by
    rw [hsqrtArg, hsqrtP]
    field_simp [hs2ne, hsp2ne]
  have hprim0 : primitive p 0 = 0 := by
    unfold primitive
    simp [Real.sqrt_ne_zero'.mpr hp]
  rw [gap9 p x₀ hp hx₀, hprim0, sub_zero]
  unfold primitive closedForm
  rw [Real.sq_sqrt hx₀, hfirst, harg]

end
end ProofGap.Exercise2432
