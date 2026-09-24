import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod

namespace ProofGap.Exercise4173

noncomputable section

open Filter MeasureTheory

def region : Set (ℝ × ℝ) :=
  {p | p.1 ^ 2 + 1 ≤ p.2}

def integrand (x y : ℝ) : ℝ :=
  1 / (x ^ 4 + y ^ 2)

def integralValue : ℝ :=
  ∫ p in region, integrand p.1 p.2

def innerIntegral (x : ℝ) : ℝ :=
  ∫ y in Set.Ici (x ^ 2 + 1), integrand x y

def arctanExpression (x : ℝ) : ℝ :=
  1 / x ^ 2 *
    (Real.pi / 2 - Real.arctan (1 + 1 / x ^ 2))

def limitExpression (x : ℝ) : ℝ :=
  (Real.pi / 2 - Real.arctan (1 + 1 / x ^ 2)) / x

def rationalIntegrand (x : ℝ) : ℝ :=
  1 / (x ^ 4 + x ^ 2 + 1 / 2)

def a₁ : ℝ :=
  Real.sqrt (Real.sqrt 2 - 1)

def b₁ : ℝ :=
  1 / Real.sqrt 2

def finalRadical : ℝ :=
  Real.sqrt (2 * (Real.sqrt 2 - 1))

private def c₁ : ℝ :=
  Real.sqrt (Real.sqrt 2 + 1) / 2

private def qPlus (x : ℝ) : ℝ :=
  x ^ 2 + a₁ * x + b₁

private def qMinus (x : ℝ) : ℝ :=
  x ^ 2 - a₁ * x + b₁

private def quarticPrimitive (x : ℝ) : ℝ :=
  1 / (4 * a₁ * b₁) *
      (Real.log (qPlus x) - Real.log (qMinus x)) +
    1 / (4 * b₁ * c₁) *
      (Real.arctan ((x + a₁ / 2) / c₁) +
        Real.arctan ((x - a₁ / 2) / c₁))

private theorem sqrt_two_pos : 0 < Real.sqrt 2 :=
  Real.sqrt_pos.2 (by norm_num)

private theorem sqrt_two_ne : Real.sqrt 2 ≠ 0 :=
  ne_of_gt sqrt_two_pos

private theorem sqrt_two_sq : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
  Real.sq_sqrt (by norm_num)

private theorem sqrt_two_gt_one : 1 < Real.sqrt 2 := by
  have h := Real.sqrt_nonneg (2 : ℝ)
  nlinarith [sqrt_two_sq]

private theorem a₁_pos : 0 < a₁ := by
  unfold a₁
  exact Real.sqrt_pos.2 (sub_pos.2 sqrt_two_gt_one)

private theorem a₁_ne : a₁ ≠ 0 :=
  ne_of_gt a₁_pos

private theorem a₁_sq : a₁ ^ 2 = Real.sqrt 2 - 1 := by
  unfold a₁
  exact Real.sq_sqrt (sub_nonneg.2 sqrt_two_gt_one.le)

private theorem b₁_pos : 0 < b₁ := by
  unfold b₁
  positivity

private theorem b₁_ne : b₁ ≠ 0 :=
  ne_of_gt b₁_pos

private theorem b₁_sq : b₁ ^ 2 = (1 / 2 : ℝ) := by
  unfold b₁
  field_simp [sqrt_two_ne]
  nlinarith [sqrt_two_sq]

private theorem two_mul_b₁ : 2 * b₁ = Real.sqrt 2 := by
  unfold b₁
  field_simp [sqrt_two_ne]
  nlinarith [sqrt_two_sq]

private theorem c₁_pos : 0 < c₁ := by
  unfold c₁
  positivity

private theorem c₁_ne : c₁ ≠ 0 :=
  ne_of_gt c₁_pos

private theorem c₁_sq :
    c₁ ^ 2 = (Real.sqrt 2 + 1) / 4 := by
  unfold c₁
  rw [div_pow, Real.sq_sqrt (by positivity : 0 ≤ Real.sqrt 2 + 1)]
  norm_num

private theorem b_sub_a_sq :
    b₁ - a₁ ^ 2 / 4 = c₁ ^ 2 := by
  rw [a₁_sq, c₁_sq]
  have hb : b₁ = Real.sqrt 2 / 2 := by
    nlinarith [two_mul_b₁]
  rw [hb]
  ring

private theorem qPlus_eq (x : ℝ) :
    qPlus x = (x + a₁ / 2) ^ 2 + c₁ ^ 2 := by
  unfold qPlus
  rw [← b_sub_a_sq]
  ring

private theorem qMinus_eq (x : ℝ) :
    qMinus x = (x - a₁ / 2) ^ 2 + c₁ ^ 2 := by
  unfold qMinus
  rw [← b_sub_a_sq]
  ring

private theorem qPlus_pos (x : ℝ) : 0 < qPlus x := by
  rw [qPlus_eq]
  nlinarith [sq_nonneg (x + a₁ / 2), sq_pos_of_pos c₁_pos]

private theorem qMinus_pos (x : ℝ) : 0 < qMinus x := by
  rw [qMinus_eq]
  nlinarith [sq_nonneg (x - a₁ / 2), sq_pos_of_pos c₁_pos]

private theorem qPlus_mul_qMinus (x : ℝ) :
    qPlus x * qMinus x =
      x ^ 4 + x ^ 2 + (1 / 2 : ℝ) := by
  unfold qPlus qMinus
  calc
    (x ^ 2 + a₁ * x + b₁) * (x ^ 2 - a₁ * x + b₁) =
        x ^ 4 + (2 * b₁ - a₁ ^ 2) * x ^ 2 + b₁ ^ 2 := by
      ring
    _ = x ^ 4 + x ^ 2 + 1 / 2 := by
      rw [a₁_sq, b₁_sq]
      nlinarith [two_mul_b₁]

private theorem rational_denominator_pos (x : ℝ) :
    0 < x ^ 4 + x ^ 2 + (1 / 2 : ℝ) := by
  nlinarith [sq_nonneg (x ^ 2), sq_nonneg x]

private theorem rational_integrable :
    Integrable rationalIntegrand := by
  let g : ℝ → ℝ := fun x => 2 * (1 + x ^ 2)⁻¹
  have hg : Integrable g := integrable_inv_one_add_sq.const_mul 2
  refine hg.mono' (by
    have hc : Continuous rationalIntegrand := by
      unfold rationalIntegrand
      apply Continuous.div continuous_const
      · fun_prop
      · intro x
        exact ne_of_gt (rational_denominator_pos x)
    exact hc.aestronglyMeasurable) ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_pos (by
    unfold rationalIntegrand
    exact one_div_pos.2 (rational_denominator_pos x))]
  dsimp [g]
  unfold rationalIntegrand
  have hden := rational_denominator_pos x
  have hone : 0 < 1 + x ^ 2 := by positivity
  change 1 / (x ^ 4 + x ^ 2 + 1 / 2) ≤ 2 / (1 + x ^ 2)
  exact (div_le_div_iff₀ hden hone).2 (by
    nlinarith [sq_nonneg (x ^ 2)])

private theorem qPlus_hasDerivAt (x : ℝ) :
    HasDerivAt qPlus (2 * x + a₁) x := by
  unfold qPlus
  convert (((hasDerivAt_id x).pow 2).add
    ((hasDerivAt_id x).const_mul a₁)).add_const b₁ using 1 <;>
    simp <;> ring

private theorem qMinus_hasDerivAt (x : ℝ) :
    HasDerivAt qMinus (2 * x - a₁) x := by
  unfold qMinus
  convert (((hasDerivAt_id x).pow 2).sub
    ((hasDerivAt_id x).const_mul a₁)).add_const b₁ using 1 <;>
    simp <;> ring

private theorem quarticPrimitive_hasDerivAt (x : ℝ) :
    HasDerivAt quarticPrimitive (rationalIntegrand x) x := by
  have hqp : qPlus x ≠ 0 := ne_of_gt (qPlus_pos x)
  have hqm : qMinus x ≠ 0 := ne_of_gt (qMinus_pos x)
  have hargp :
      HasDerivAt (fun t : ℝ => (t + a₁ / 2) / c₁)
        (1 / c₁) x := by
    convert ((hasDerivAt_id x).add_const (a₁ / 2)).div_const c₁
      using 1 <;> ring
  have hargm :
      HasDerivAt (fun t : ℝ => (t - a₁ / 2) / c₁)
        (1 / c₁) x := by
    convert ((hasDerivAt_id x).sub_const (a₁ / 2)).div_const c₁
      using 1 <;> ring
  have hp :
      (x + a₁ / 2) ^ 2 + c₁ ^ 2 ≠ 0 := by
    rw [← qPlus_eq]
    exact ne_of_gt (qPlus_pos x)
  have hm :
      (x - a₁ / 2) ^ 2 + c₁ ^ 2 ≠ 0 := by
    rw [← qMinus_eq]
    exact ne_of_gt (qMinus_pos x)
  have hatanp_value :
      1 / (1 + ((x + a₁ / 2) / c₁) ^ 2) * (1 / c₁) =
        c₁ / qPlus x := by
    rw [qPlus_eq]
    field_simp [c₁_ne, hp]
    ring
  have hatanm_value :
      1 / (1 + ((x - a₁ / 2) / c₁) ^ 2) * (1 / c₁) =
        c₁ / qMinus x := by
    rw [qMinus_eq]
    field_simp [c₁_ne, hm]
    ring
  have hlog :=
    (((qPlus_hasDerivAt x).log hqp).sub
        ((qMinus_hasDerivAt x).log hqm)).const_mul
      (1 / (4 * a₁ * b₁))
  have hatan :=
    (((Real.hasDerivAt_arctan _).comp x hargp).add
        ((Real.hasDerivAt_arctan _).comp x hargm)).const_mul
      (1 / (4 * b₁ * c₁))
  have h := hlog.add hatan
  convert h using 1
  · unfold rationalIntegrand
    rw [hatanp_value, hatanm_value]
    rw [← qPlus_mul_qMinus]
    field_simp [a₁_ne, b₁_ne, c₁_ne, hqp, hqm]
    unfold qPlus qMinus
    ring

private theorem quarticPrimitive_tendsto :
    Tendsto quarticPrimitive atTop
      (nhds (Real.pi / (4 * b₁ * c₁))) := by
  have hinv : Tendsto (fun x : ℝ => x⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  have hinv2 : Tendsto (fun x : ℝ => x⁻¹ ^ 2) atTop (nhds 0) := by
    simpa using hinv.pow 2
  have hnum :
      Tendsto
        (fun x : ℝ => 1 + a₁ * x⁻¹ + b₁ * x⁻¹ ^ 2)
        atTop (nhds 1) := by
    simpa using
      (tendsto_const_nhds.add (tendsto_const_nhds.mul hinv)).add
        (tendsto_const_nhds.mul hinv2)
  have hden :
      Tendsto
        (fun x : ℝ => 1 - a₁ * x⁻¹ + b₁ * x⁻¹ ^ 2)
        atTop (nhds 1) := by
    simpa using
      (tendsto_const_nhds.sub (tendsto_const_nhds.mul hinv)).add
        (tendsto_const_nhds.mul hinv2)
  have hratio' :
      Tendsto
        (fun x : ℝ =>
          (1 + a₁ * x⁻¹ + b₁ * x⁻¹ ^ 2) /
            (1 - a₁ * x⁻¹ + b₁ * x⁻¹ ^ 2))
        atTop (nhds 1) := by
    simpa using hnum.div hden (by norm_num)
  have heq :
      (fun x : ℝ => qPlus x / qMinus x) =ᶠ[atTop]
        (fun x : ℝ =>
          (1 + a₁ * x⁻¹ + b₁ * x⁻¹ ^ 2) /
            (1 - a₁ * x⁻¹ + b₁ * x⁻¹ ^ 2)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    unfold qPlus qMinus
    field_simp [hx.ne']
  have hratio :
      Tendsto (fun x : ℝ => qPlus x / qMinus x)
        atTop (nhds 1) :=
    hratio'.congr' heq.symm
  have hlogratio :
      Tendsto
        (fun x : ℝ => Real.log (qPlus x) - Real.log (qMinus x))
        atTop (nhds 0) := by
    have hlog :
        Tendsto (fun x : ℝ => Real.log (qPlus x / qMinus x))
          atTop (nhds 0) := by
      simpa using
        (Real.continuousAt_log one_ne_zero).tendsto.comp hratio
    have heqlog :
        (fun x : ℝ => Real.log (qPlus x / qMinus x)) =
          (fun x : ℝ => Real.log (qPlus x) - Real.log (qMinus x)) := by
      funext x
      exact Real.log_div (ne_of_gt (qPlus_pos x)) (ne_of_gt (qMinus_pos x))
    rw [← heqlog]
    exact hlog
  have hxplus :
      Tendsto (fun x : ℝ => x + a₁ / 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop (a₁ / 2) tendsto_id
  have hxminus :
      Tendsto (fun x : ℝ => x + (-a₁ / 2)) atTop atTop :=
    tendsto_atTop_add_const_right atTop (-a₁ / 2) tendsto_id
  have hargp :
      Tendsto (fun x : ℝ => (x + a₁ / 2) / c₁) atTop atTop :=
    hxplus.atTop_div_const c₁_pos
  have hargm :
      Tendsto (fun x : ℝ => (x - a₁ / 2) / c₁) atTop atTop := by
    convert hxminus.atTop_div_const c₁_pos using 1
    funext x
    ring
  have hatanp :
      Tendsto (fun x : ℝ => Real.arctan ((x + a₁ / 2) / c₁))
        atTop (nhds (Real.pi / 2)) :=
    (tendsto_nhds_of_tendsto_nhdsWithin
      Real.tendsto_arctan_atTop).comp hargp
  have hatanm :
      Tendsto (fun x : ℝ => Real.arctan ((x - a₁ / 2) / c₁))
        atTop (nhds (Real.pi / 2)) :=
    (tendsto_nhds_of_tendsto_nhdsWithin
      Real.tendsto_arctan_atTop).comp hargm
  unfold quarticPrimitive
  convert
    (tendsto_const_nhds.mul hlogratio).add
      (tendsto_const_nhds.mul (hatanp.add hatanm)) using 1 <;>
    ring

private theorem quarticPrimitive_zero :
    quarticPrimitive 0 = 0 := by
  unfold quarticPrimitive qPlus qMinus
  rw [show (0 : ℝ) ^ 2 + a₁ * 0 + b₁ = b₁ by ring,
    show (0 : ℝ) ^ 2 - a₁ * 0 + b₁ = b₁ by ring]
  rw [sub_self]
  simp only [mul_zero, zero_add]
  have hp : a₁ / 2 / c₁ = a₁ / (2 * c₁) := by ring
  have hm : (0 - a₁ / 2) / c₁ = -(a₁ / (2 * c₁)) := by ring
  rw [hp, hm, Real.arctan_neg]
  ring

private theorem finalRadical_pos : 0 < finalRadical := by
  unfold finalRadical
  exact Real.sqrt_pos.2 (mul_pos (by norm_num) (sub_pos.2 sqrt_two_gt_one))

private theorem finalRadical_sq :
    finalRadical ^ 2 = 2 * (Real.sqrt 2 - 1) := by
  unfold finalRadical
  exact Real.sq_sqrt
    (mul_nonneg (by norm_num) (sub_nonneg.2 sqrt_two_gt_one.le))

private theorem reciprocal_bc :
    1 / (2 * b₁ * c₁) = finalRadical := by
  have hprodpos : 0 < finalRadical * (2 * b₁ * c₁) := by
    exact mul_pos finalRadical_pos (mul_pos (mul_pos (by norm_num) b₁_pos) c₁_pos)
  have hprodsq :
      (finalRadical * (2 * b₁ * c₁)) ^ 2 = 1 := by
    rw [mul_pow, finalRadical_sq]
    rw [show (2 * b₁ * c₁) ^ 2 =
        4 * b₁ ^ 2 * c₁ ^ 2 by ring, b₁_sq, c₁_sq]
    nlinarith [sqrt_two_sq]
  have hprod : finalRadical * (2 * b₁ * c₁) = 1 := by
    nlinarith
  have hbc : 2 * b₁ * c₁ ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) b₁_ne) c₁_ne
  exact ((eq_div_iff hbc).2 hprod).symm

private theorem region_measurable : MeasurableSet region := by
  unfold region
  measurability

private theorem integrand_nonneg (x y : ℝ) :
    0 ≤ integrand x y := by
  unfold integrand
  positivity

private theorem innerIntegral_nonneg (x : ℝ) :
    0 ≤ innerIntegral x := by
  unfold innerIntegral
  exact integral_nonneg (fun y => integrand_nonneg x y)

private theorem inner_integrable_nonzero (x : ℝ) (hx : x ≠ 0) :
    IntegrableOn (integrand x) (Set.Ici (x ^ 2 + 1)) := by
  have hx2 : x ^ 2 ≠ 0 := pow_ne_zero 2 hx
  have hbase :
      Integrable
        (fun y : ℝ => (1 + ((1 / x ^ 2) * y) ^ 2)⁻¹) := by
    exact integrable_inv_one_add_sq.comp_mul_left'
      (one_div_ne_zero hx2)
  have hscaled :=
    hbase.const_mul (1 / (x ^ 2) ^ 2)
  have heq :
      integrand x =
        fun y : ℝ =>
          (1 / (x ^ 2) ^ 2) *
            (1 + ((1 / x ^ 2) * y) ^ 2)⁻¹ := by
    funext y
    unfold integrand
    field_simp [hx]
  rw [heq]
  exact hscaled.integrableOn

private theorem innerIntegral_formula (x : ℝ) (hx : x ≠ 0) :
    innerIntegral x = arctanExpression x := by
  have hx2pos : 0 < x ^ 2 := sq_pos_of_ne_zero hx
  have hx2 : x ^ 2 ≠ 0 := ne_of_gt hx2pos
  let P : ℝ → ℝ :=
    fun y => 1 / x ^ 2 * Real.arctan (y / x ^ 2)
  have hderiv (y : ℝ) :
      HasDerivAt P (integrand x y) y := by
    have harg :
        HasDerivAt (fun t : ℝ => t / x ^ 2) (1 / x ^ 2) y := by
      convert (hasDerivAt_id y).div_const (x ^ 2) using 1 <;> ring
    have h :=
      ((Real.hasDerivAt_arctan (y / x ^ 2)).comp y harg).const_mul
        (1 / x ^ 2)
    convert h using 1
    unfold integrand
    field_simp [hx]
  have hargTop :
      Tendsto (fun y : ℝ => y / x ^ 2) atTop atTop :=
    tendsto_id.atTop_div_const hx2pos
  have hatanTop :
      Tendsto (fun y : ℝ => Real.arctan (y / x ^ 2))
        atTop (nhds (Real.pi / 2)) :=
    (tendsto_nhds_of_tendsto_nhdsWithin
      Real.tendsto_arctan_atTop).comp hargTop
  have hPTop :
      Tendsto P atTop (nhds (1 / x ^ 2 * (Real.pi / 2))) := by
    exact tendsto_const_nhds.mul hatanTop
  have hi :
      IntegrableOn (integrand x) (Set.Ioi (x ^ 2 + 1)) :=
    (inner_integrable_nonzero x hx).mono_set Set.Ioi_subset_Ici_self
  have hFTC :
      (∫ y in Set.Ioi (x ^ 2 + 1), integrand x y) =
        1 / x ^ 2 * (Real.pi / 2) - P (x ^ 2 + 1) := by
    exact integral_Ioi_of_hasDerivAt_of_tendsto'
      (fun y hy => hderiv y) hi hPTop
  unfold innerIntegral
  rw [← setIntegral_congr_set Ioi_ae_eq_Ici]
  rw [hFTC]
  unfold P arctanExpression
  congr 1
  field_simp [hx]

private theorem arctan_le_self_of_nonneg (z : ℝ) (hz : 0 ≤ z) :
    Real.arctan z ≤ z := by
  calc
    Real.arctan z ≤ Real.tan (Real.arctan z) :=
      Real.le_tan (Real.arctan_nonneg.mpr hz)
        (Real.arctan_lt_pi_div_two z)
    _ = z := Real.tan_arctan z

private theorem abs_arctan_le_abs (z : ℝ) :
    |Real.arctan z| ≤ |z| := by
  by_cases hz : 0 ≤ z
  · rw [abs_of_nonneg (Real.arctan_nonneg.mpr hz), abs_of_nonneg hz]
    exact arctan_le_self_of_nonneg z hz
  · have hnz : 0 ≤ -z := neg_nonneg.mpr (le_of_not_ge hz)
    calc
      |Real.arctan z| = |Real.arctan (-z)| := by
        rw [Real.arctan_neg, abs_neg]
      _ = Real.arctan (-z) :=
        abs_of_nonneg (Real.arctan_nonneg.mpr hnz)
      _ ≤ -z := arctan_le_self_of_nonneg (-z) hnz
      _ = |z| := (abs_of_nonpos (le_of_not_ge hz)).symm

private theorem innerIntegral_le (x : ℝ) (hx : x ≠ 0) :
    innerIntegral x ≤ 1 / (1 + x ^ 2) := by
  have hx2pos : 0 < x ^ 2 := sq_pos_of_ne_zero hx
  have hsumpos : 0 < x ^ 2 + 1 := by positivity
  have ht : 0 < 1 + 1 / x ^ 2 := by positivity
  have hinv :
      (1 + 1 / x ^ 2)⁻¹ = x ^ 2 / (x ^ 2 + 1) := by
    field_simp [hx]
  rw [innerIntegral_formula x hx]
  unfold arctanExpression
  rw [← Real.arctan_inv_of_pos ht, hinv]
  have hu : 0 ≤ x ^ 2 / (x ^ 2 + 1) := by positivity
  have hatan :=
    arctan_le_self_of_nonneg (x ^ 2 / (x ^ 2 + 1)) hu
  have hcoef : 0 ≤ 1 / x ^ 2 := by positivity
  calc
    1 / x ^ 2 * Real.arctan (x ^ 2 / (x ^ 2 + 1)) ≤
        1 / x ^ 2 * (x ^ 2 / (x ^ 2 + 1)) :=
      mul_le_mul_of_nonneg_left hatan hcoef
    _ = 1 / (1 + x ^ 2) := by
      field_simp [hx]
      ring

private def planeFunction (p : ℝ × ℝ) : ℝ :=
  region.indicator (fun q => integrand q.1 q.2) p

private theorem planeFunction_measurable :
    Measurable planeFunction := by
  unfold planeFunction integrand
  exact (by measurability : Measurable
    (fun p : ℝ × ℝ => 1 / (p.1 ^ 4 + p.2 ^ 2))).indicator
      region_measurable

private theorem plane_section_eq (x : ℝ) :
    (fun y : ℝ => planeFunction (x, y)) =
      (Set.Ici (x ^ 2 + 1)).indicator (integrand x) := by
  funext y
  by_cases hy : x ^ 2 + 1 ≤ y <;>
    simp [planeFunction, region, hy]

private theorem plane_section_integrable (x : ℝ) (hx : x ≠ 0) :
    Integrable (fun y : ℝ => planeFunction (x, y)) := by
  rw [plane_section_eq]
  exact (inner_integrable_nonzero x hx).integrable_indicator measurableSet_Ici

private theorem plane_norm_section_eq (x : ℝ) :
    (∫ y : ℝ, ‖planeFunction (x, y)‖) = innerIntegral x := by
  have heqnorm :
      (fun y : ℝ => ‖planeFunction (x, y)‖) =
        fun y : ℝ =>
          ‖(Set.Ici (x ^ 2 + 1)).indicator (integrand x) y‖ := by
    funext y
    rw [congrFun (plane_section_eq x) y]
  rw [heqnorm]
  have hfun :
      (fun y : ℝ =>
        ‖(Set.Ici (x ^ 2 + 1)).indicator (integrand x) y‖) =
        (Set.Ici (x ^ 2 + 1)).indicator (integrand x) := by
    funext y
    by_cases hy : y ∈ Set.Ici (x ^ 2 + 1)
    · rw [Set.indicator_of_mem hy]
      rw [Real.norm_eq_abs, abs_of_nonneg (integrand_nonneg x y)]
    · rw [Set.indicator_of_notMem hy]
      simp
  rw [hfun, integral_indicator measurableSet_Ici]
  rfl

private theorem innerIntegral_aestronglyMeasurable :
    AEStronglyMeasurable innerIntegral := by
  have hstrong :
      StronglyMeasurable
        (fun x : ℝ => ∫ y : ℝ, planeFunction (x, y)) :=
    planeFunction_measurable.stronglyMeasurable.integral_prod_right'
  have heq :
      (fun x : ℝ => ∫ y : ℝ, planeFunction (x, y)) =
        innerIntegral := by
    funext x
    rw [plane_section_eq, integral_indicator measurableSet_Ici]
    rfl
  rw [← heq]
  exact hstrong.aestronglyMeasurable

private theorem innerIntegral_integrable :
    Integrable innerIntegral := by
  have hbase :
      Integrable (fun x : ℝ => (1 + x ^ 2)⁻¹) :=
    integrable_inv_one_add_sq
  refine hbase.mono' innerIntegral_aestronglyMeasurable ?_
  filter_upwards [MeasureTheory.volume.ae_ne (0 : ℝ)] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (innerIntegral_nonneg x)]
  change innerIntegral x ≤ (1 + x ^ 2)⁻¹
  simpa only [one_div] using innerIntegral_le x hx

private theorem planeFunction_integrable :
    Integrable planeFunction := by
  rw [Measure.volume_eq_prod]
  apply (integrable_prod_iff
    planeFunction_measurable.aestronglyMeasurable).2
  constructor
  · filter_upwards [MeasureTheory.volume.ae_ne (0 : ℝ)] with x hx
    exact plane_section_integrable x hx
  · exact innerIntegral_integrable.congr
      (ae_of_all _ fun x => (plane_norm_section_eq x).symm)

private theorem innerIntegral_abs (x : ℝ) :
    innerIntegral |x| = innerIntegral x := by
  have hs : |x| ^ 2 = x ^ 2 := sq_abs x
  have h4 : |x| ^ 4 = x ^ 4 := by
    rw [show |x| ^ 4 = (|x| ^ 2) ^ 2 by ring, hs]
    ring
  unfold innerIntegral integrand
  rw [hs, h4]

theorem gap1 :
    integralValue =
      ∫ x : ℝ, innerIntegral x := by
  unfold integralValue
  rw [← integral_indicator region_measurable]
  change (∫ p : ℝ × ℝ, planeFunction p) = _
  rw [Measure.volume_eq_prod, integral_prod _ planeFunction_integrable]
  apply integral_congr_ae
  filter_upwards with x
  rw [plane_section_eq, integral_indicator measurableSet_Ici]
  rfl

theorem gap2 :
    integralValue =
      2 * ∫ x in Set.Ici (0 : ℝ), innerIntegral x := by
  rw [gap1]
  calc
    (∫ x : ℝ, innerIntegral x) =
        ∫ x : ℝ, innerIntegral |x| := by
      apply integral_congr_ae
      filter_upwards with x
      exact (innerIntegral_abs x).symm
    _ = 2 * ∫ x in Set.Ioi (0 : ℝ), innerIntegral x :=
      integral_comp_abs
    _ = 2 * ∫ x in Set.Ici (0 : ℝ), innerIntegral x := by
      rw [setIntegral_congr_set Ioi_ae_eq_Ici]

theorem gap3 (x : ℝ) (hx : x ≠ 0) :
    innerIntegral x = arctanExpression x := by
  exact innerIntegral_formula x hx

theorem gap4 :
    integralValue =
      2 * ∫ x in Set.Ici (0 : ℝ), arctanExpression x := by
  rw [gap2]
  congr 1
  apply integral_congr_ae
  have hne :
      ∀ᵐ x : ℝ ∂volume.restrict (Set.Ici (0 : ℝ)), x ≠ 0 :=
    ae_mono Measure.restrict_le_self
      (MeasureTheory.volume.ae_ne (0 : ℝ))
  filter_upwards [hne] with x hx
  exact gap3 x hx

theorem gap5 :
    Tendsto limitExpression (nhds 0) (nhds 0) := by
  have hbound (x : ℝ) : |limitExpression x| ≤ |x| := by
    by_cases hx : x = 0
    · subst x
      simp [limitExpression]
    · have hx2pos : 0 < x ^ 2 := sq_pos_of_ne_zero hx
      have ht : 0 < 1 + 1 / x ^ 2 := by positivity
      have hinv :
          (1 + 1 / x ^ 2)⁻¹ = x ^ 2 / (x ^ 2 + 1) := by
        field_simp [hx]
      unfold limitExpression
      rw [← Real.arctan_inv_of_pos ht, hinv, abs_div]
      calc
        |Real.arctan (x ^ 2 / (x ^ 2 + 1))| / |x| ≤
            |x ^ 2 / (x ^ 2 + 1)| / |x| := by
          exact div_le_div_of_nonneg_right
            (abs_arctan_le_abs _) (abs_nonneg x)
        _ = |x| / (x ^ 2 + 1) := by
          rw [abs_div, abs_of_nonneg (sq_nonneg x),
            abs_of_pos (by positivity : 0 < x ^ 2 + 1)]
          have habs : |x| ≠ 0 := abs_ne_zero.mpr hx
          rw [← sq_abs x]
          field_simp [habs]
        _ ≤ |x| := by
          have hden : 1 ≤ x ^ 2 + 1 := by
            nlinarith [sq_nonneg x]
          exact (div_le_iff₀ (by
            nlinarith [sq_nonneg x] : 0 < x ^ 2 + 1)).2
            (by nlinarith [abs_nonneg x])
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero
    (fun x => norm_nonneg _)
    (fun x => by simpa only [Real.norm_eq_abs] using hbound x)
    (by simpa only [Real.norm_eq_abs, abs_zero] using
      (continuous_abs.tendsto (0 : ℝ)))

private theorem limitExpression_zero :
    limitExpression 0 = 0 := by
  simp [limitExpression]

private theorem limitExpression_tendsto_atTop :
    Tendsto limitExpression atTop (nhds 0) := by
  have hinv : Tendsto (fun x : ℝ => x⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  have hfrac :
      Tendsto (fun x : ℝ => 1 / x ^ 2) atTop (nhds 0) := by
    simpa [one_div, inv_pow] using hinv.pow 2
  have harg :
      Tendsto (fun x : ℝ => 1 + 1 / x ^ 2)
        atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add hfrac
  have hatan :
      Tendsto (fun x : ℝ => Real.arctan (1 + 1 / x ^ 2))
        atTop (nhds (Real.arctan 1)) :=
    Real.continuous_arctan.continuousAt.tendsto.comp harg
  have hnum :
      Tendsto
        (fun x : ℝ =>
          Real.pi / 2 - Real.arctan (1 + 1 / x ^ 2))
        atTop (nhds (Real.pi / 2 - Real.arctan 1)) :=
    tendsto_const_nhds.sub hatan
  unfold limitExpression
  simpa [div_eq_mul_inv] using hnum.mul hinv

private theorem limitExpression_hasDerivAt
    (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt limitExpression
      (rationalIntegrand x - arctanExpression x) x := by
  have hx2 : x ^ 2 ≠ 0 := pow_ne_zero 2 hx
  have hsquare :
      HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by
    convert (hasDerivAt_id x).pow 2 using 1 <;> simp <;> ring
  have hrecip :
      HasDerivAt (fun t : ℝ => 1 / t ^ 2)
        ((0 * x ^ 2 - 1 * (2 * x)) / (x ^ 2) ^ 2) x :=
    (hasDerivAt_const x (1 : ℝ)).div hsquare hx2
  have harg :
      HasDerivAt (fun t : ℝ => 1 + 1 / t ^ 2)
        (0 + (0 * x ^ 2 - 1 * (2 * x)) / (x ^ 2) ^ 2) x :=
    (hasDerivAt_const x (1 : ℝ)).add hrecip
  have hnum :=
    (hasDerivAt_const x (Real.pi / 2)).sub
      ((Real.hasDerivAt_arctan (1 + 1 / x ^ 2)).comp x harg)
  have hnum' :
      HasDerivAt
        (fun t : ℝ =>
          Real.pi / 2 - Real.arctan (1 + 1 / t ^ 2))
        (x * rationalIntegrand x) x := by
    convert hnum using 1
    unfold rationalIntegrand
    have hd : x ^ 4 + x ^ 2 + (1 / 2 : ℝ) ≠ 0 :=
      ne_of_gt (rational_denominator_pos x)
    field_simp [hx, hd]
    ring
  have hquot := hnum'.div (hasDerivAt_id x) hx
  convert hquot using 1
  simp only [id_eq]
  unfold rationalIntegrand arctanExpression
  have hd : x ^ 4 + x ^ 2 + (1 / 2 : ℝ) ≠ 0 :=
    ne_of_gt (rational_denominator_pos x)
  field_simp [hx, hd]

private theorem arctanExpression_integrableOn_Ioi :
    IntegrableOn arctanExpression (Set.Ioi (0 : ℝ)) := by
  exact innerIntegral_integrable.integrableOn.congr_fun
    (fun x hx => innerIntegral_formula x (ne_of_gt hx))
      measurableSet_Ioi

theorem gap6 :
    integralValue =
      2 * ∫ x in Set.Ici (0 : ℝ), rationalIntegrand x := by
  have hr :
      IntegrableOn rationalIntegrand (Set.Ioi (0 : ℝ)) :=
    rational_integrable.integrableOn
  have ha :
      IntegrableOn arctanExpression (Set.Ioi (0 : ℝ)) :=
    arctanExpression_integrableOn_Ioi
  have hdiff :
      IntegrableOn
        (fun x : ℝ => rationalIntegrand x - arctanExpression x)
        (Set.Ioi (0 : ℝ)) :=
    hr.sub ha
  have hcont :
      ContinuousWithinAt limitExpression (Set.Ici (0 : ℝ)) 0 := by
    apply ContinuousAt.continuousWithinAt
    change Tendsto limitExpression (nhds 0)
      (nhds (limitExpression 0))
    rw [limitExpression_zero]
    exact gap5
  have hFTC :
      (∫ x in Set.Ioi (0 : ℝ),
        (rationalIntegrand x - arctanExpression x)) = 0 := by
    have h :=
      integral_Ioi_of_hasDerivAt_of_tendsto hcont
        (fun x hx => limitExpression_hasDerivAt x (ne_of_gt hx))
        hdiff limitExpression_tendsto_atTop
    simpa [limitExpression_zero] using h
  have hsplit :
      (∫ x in Set.Ioi (0 : ℝ),
          (rationalIntegrand x - arctanExpression x)) =
        (∫ x in Set.Ioi (0 : ℝ), rationalIntegrand x) -
          ∫ x in Set.Ioi (0 : ℝ), arctanExpression x :=
    integral_sub hr ha
  rw [hsplit] at hFTC
  have heq :
      (∫ x in Set.Ioi (0 : ℝ), arctanExpression x) =
        ∫ x in Set.Ioi (0 : ℝ), rationalIntegrand x := by
    linarith
  rw [gap4]
  congr 1
  calc
    (∫ x in Set.Ici (0 : ℝ), arctanExpression x) =
        ∫ x in Set.Ioi (0 : ℝ), arctanExpression x :=
      (setIntegral_congr_set Ioi_ae_eq_Ici).symm
    _ = ∫ x in Set.Ioi (0 : ℝ), rationalIntegrand x := heq
    _ = ∫ x in Set.Ici (0 : ℝ), rationalIntegrand x :=
      setIntegral_congr_set Ioi_ae_eq_Ici

theorem gap7 (x : ℝ) :
    rationalIntegrand x =
      1 / ((x ^ 2 + b₁) ^ 2 - (a₁ * x) ^ 2) := by
  unfold rationalIntegrand
  congr 1
  symm
  calc
    (x ^ 2 + b₁) ^ 2 - (a₁ * x) ^ 2 =
        x ^ 4 + (2 * b₁ - a₁ ^ 2) * x ^ 2 + b₁ ^ 2 := by ring
    _ = x ^ 4 + x ^ 2 + 1 / 2 := by
      rw [a₁_sq, b₁_sq]
      nlinarith [two_mul_b₁]

theorem gap8 (x : ℝ) :
    rationalIntegrand x =
      1 /
        ((x ^ 2 + a₁ * x + b₁) *
          (x ^ 2 - a₁ * x + b₁)) := by
  rw [gap7]
  congr 1
  ring

theorem gap9 :
    (∫ x in Set.Ici (0 : ℝ), rationalIntegrand x) =
      Real.pi * finalRadical / 2 := by
  have hi : IntegrableOn rationalIntegrand (Set.Ioi (0 : ℝ)) :=
    rational_integrable.integrableOn
  have hFTC :
      (∫ x in Set.Ioi (0 : ℝ), rationalIntegrand x) =
        Real.pi / (4 * b₁ * c₁) - quarticPrimitive 0 :=
    integral_Ioi_of_hasDerivAt_of_tendsto'
      (fun x hx => quarticPrimitive_hasDerivAt x) hi
        quarticPrimitive_tendsto
  rw [← setIntegral_congr_set Ioi_ae_eq_Ici]
  rw [hFTC, quarticPrimitive_zero, sub_zero]
  rw [show Real.pi / (4 * b₁ * c₁) =
      Real.pi * (1 / (2 * b₁ * c₁)) / 2 by ring,
    reciprocal_bc]

theorem gap10 :
    integralValue = Real.pi * finalRadical := by
  rw [gap6, gap9]
  ring

end

end ProofGap.Exercise4173
