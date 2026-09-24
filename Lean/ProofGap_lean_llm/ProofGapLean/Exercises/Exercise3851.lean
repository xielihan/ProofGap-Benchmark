import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace ProofGap.Exercise3851

noncomputable section

open Filter MeasureTheory Set
open scoped Interval

def HasImproperIntegral (a : ℝ) (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Tendsto (fun b : ℝ => ∫ x in a..b, f x) atTop (nhds L)

def improperIntegral (a : ℝ) (f : ℝ → ℝ) : ℝ :=
  sInf {L : ℝ | HasImproperIntegral a f L}

def betaFn (x y : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..1,
    Real.rpow u (x - 1) * Real.rpow (1 - u) (y - 1)

def integrand (m n x : ℝ) : ℝ :=
  Real.rpow x (m - 1) / (1 + Real.rpow x n)

private def betaKernel (u v t : ℝ) : ℝ :=
  Real.rpow t (u - 1) * Real.rpow (1 - t) (v - 1)

private def canonicalKernel (q x : ℝ) : ℝ :=
  Real.rpow x (q - 1) / (1 + x)

private theorem betaKernel_intervalIntegrable
    (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    IntervalIntegrable (betaKernel u v) volume 0 1 := by
  have huLeft :
      IntervalIntegrable (fun t : ℝ => Real.rpow t (u - 1))
        volume 0 (1 / 2 : ℝ) :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hvContLeft :
      ContinuousOn (fun t : ℝ => Real.rpow (1 - t) (v - 1))
        [[(0 : ℝ), 1 / 2]] := by
    apply continuousOn_of_forall_continuousAt
    intro t ht
    norm_num [Set.uIcc] at ht
    have hbase : 1 - t ≠ 0 := by linarith
    simpa [Function.comp_def] using
      (Real.continuousAt_rpow_const (1 - t) (v - 1) (Or.inl hbase)).comp
        (continuous_const.sub continuous_id).continuousAt
  have hleft :
      IntervalIntegrable (betaKernel u v) volume 0 (1 / 2 : ℝ) := by
    simpa only [betaKernel] using huLeft.mul_continuousOn hvContLeft
  have hvRight :
      IntervalIntegrable (fun t : ℝ => Real.rpow (1 - t) (v - 1))
        volume (1 / 2 : ℝ) 1 := by
    have h :=
      (intervalIntegral.intervalIntegrable_rpow'
        (a := (0 : ℝ)) (b := 1 / 2) (by linarith : -1 < v - 1)).comp_sub_left 1
    convert h.symm using 1 <;> norm_num
  have huContRight :
      ContinuousOn (fun t : ℝ => Real.rpow t (u - 1))
        [[(1 / 2 : ℝ), 1]] := by
    apply continuousOn_of_forall_continuousAt
    intro t ht
    norm_num [Set.uIcc] at ht
    have hbase : t ≠ 0 := by linarith
    exact Real.continuousAt_rpow_const t (u - 1) (Or.inl hbase)
  have hright :
      IntervalIntegrable (betaKernel u v) volume (1 / 2 : ℝ) 1 := by
    simpa only [betaKernel] using hvRight.continuousOn_mul huContRight
  exact hleft.trans hright

private theorem betaKernel_integrable_iff (u v : ℝ) :
    IntegrableOn (betaKernel u v) (Ioo (0 : ℝ) 1) volume ↔
      0 < u ∧ 0 < v := by
  constructor
  · intro hInt
    have hleftOn :
        IntegrableOn (betaKernel u v) (Ioo (0 : ℝ) (1 / 2)) volume :=
      hInt.mono_set (Ioo_subset_Ioo (le_refl 0) (by norm_num))
    have hleft :
        IntervalIntegrable (betaKernel u v) volume 0 (1 / 2) :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)).2 hleftOn
    let qLeft : ℝ → ℝ := fun t => Real.rpow (1 - t) (1 - v)
    have hqLeft : ContinuousOn qLeft [[(0 : ℝ), 1 / 2]] := by
      apply continuousOn_of_forall_continuousAt
      intro t ht
      have ht' : t ∈ Icc (0 : ℝ) (1 / 2) := by
        rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] at ht
        exact ht
      have hbase : 1 - t ≠ 0 := by linarith [ht'.2]
      dsimp [qLeft]
      simpa [Function.comp_def] using
        (Real.continuousAt_rpow_const (1 - t) (1 - v) (Or.inl hbase)).comp
          (continuous_const.sub continuous_id).continuousAt
    have hleftProduct :
        IntervalIntegrable
          (fun t => betaKernel u v t * qLeft t) volume 0 (1 / 2) :=
      hleft.mul_continuousOn hqLeft
    have huPow :
        IntervalIntegrable (fun t : ℝ => Real.rpow t (u - 1))
          volume 0 (1 / 2) := by
      apply hleftProduct.congr
      intro t ht
      have ht' : t ∈ Icc (0 : ℝ) (1 / 2) := by
        have ht'' : t ∈ Ioc (0 : ℝ) (1 / 2) := by
          rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] at ht
          exact ht
        exact ⟨ht''.1.le, ht''.2⟩
      have hbase : 0 < 1 - t := by linarith [ht'.2]
      dsimp [betaKernel, qLeft]
      calc
        Real.rpow t (u - 1) * Real.rpow (1 - t) (v - 1) *
              Real.rpow (1 - t) (1 - v) =
            Real.rpow t (u - 1) *
              (Real.rpow (1 - t) (v - 1) *
                Real.rpow (1 - t) (1 - v)) := by ring
        _ = Real.rpow t (u - 1) *
              Real.rpow (1 - t) ((v - 1) + (1 - v)) := by
            congr 1
            exact (Real.rpow_add hbase _ _).symm
        _ = Real.rpow t (u - 1) := by simp
    have huOn :
        IntegrableOn (fun t : ℝ => Real.rpow t (u - 1))
          (Ioo (0 : ℝ) (1 / 2)) volume :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)).1 huPow
    have huExp :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff
        (by norm_num : (0 : ℝ) < 1 / 2)).1 huOn
    have hrightOn :
        IntegrableOn (betaKernel u v) (Ioo (1 / 2 : ℝ) 1) volume :=
      hInt.mono_set (Ioo_subset_Ioo (by norm_num) (le_refl 1))
    have hright :
        IntervalIntegrable (betaKernel u v) volume (1 / 2) 1 :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)).2 hrightOn
    let qRight : ℝ → ℝ := fun t => Real.rpow t (1 - u)
    have hqRight : ContinuousOn qRight [[(1 / 2 : ℝ), 1]] := by
      apply continuousOn_of_forall_continuousAt
      intro t ht
      have ht' : t ∈ Icc (1 / 2 : ℝ) 1 := by
        rw [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)] at ht
        exact ht
      have hbase : t ≠ 0 := by linarith [ht'.1]
      dsimp [qRight]
      exact Real.continuousAt_rpow_const t (1 - u) (Or.inl hbase)
    have hrightProduct :
        IntervalIntegrable
          (fun t => betaKernel u v t * qRight t) volume (1 / 2) 1 :=
      hright.mul_continuousOn hqRight
    have hvShift :
        IntervalIntegrable (fun t : ℝ => Real.rpow (1 - t) (v - 1))
          volume (1 / 2) 1 := by
      apply hrightProduct.congr
      intro t ht
      have ht'' : t ∈ Ioc (1 / 2 : ℝ) 1 := by
        rw [Set.uIoc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)] at ht
        exact ht
      have hbase : 0 < t := by linarith [ht''.1]
      dsimp [betaKernel, qRight]
      calc
        Real.rpow t (u - 1) * Real.rpow (1 - t) (v - 1) *
              Real.rpow t (1 - u) =
            (Real.rpow t (u - 1) * Real.rpow t (1 - u)) *
              Real.rpow (1 - t) (v - 1) := by ring
        _ = Real.rpow t ((u - 1) + (1 - u)) *
              Real.rpow (1 - t) (v - 1) := by
            congr 1
            exact (Real.rpow_add hbase _ _).symm
        _ = Real.rpow (1 - t) (v - 1) := by simp
    have hvPow :
        IntervalIntegrable (fun t : ℝ => Real.rpow t (v - 1))
          volume 0 (1 / 2) := by
      have h := hvShift.comp_sub_left 1
      have hs := h.symm
      convert hs using 1 <;> norm_num
    have hvOn :
        IntegrableOn (fun t : ℝ => Real.rpow t (v - 1))
          (Ioo (0 : ℝ) (1 / 2)) volume :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)).1 hvPow
    have hvExp :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff
        (by norm_num : (0 : ℝ) < 1 / 2)).1 hvOn
    constructor <;> linarith
  · rintro ⟨hu, hv⟩
    exact
      (intervalIntegrable_iff_integrableOn_Ioo_of_le
        (by norm_num : (0 : ℝ) ≤ 1)).1
        (betaKernel_intervalIntegrable u v hu hv)

private theorem betaPrime_substitution_integrand
    {a b t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (1 / (1 - t) ^ 2) *
        ((t / (1 - t)).rpow (a - 1) /
          (1 + t / (1 - t)).rpow (a + b)) =
      betaKernel a b t := by
  have ht0 : 0 < t := ht.1
  have ht1 : 0 < 1 - t := sub_pos.mpr ht.2
  have hfrac : 1 + t / (1 - t) = 1 / (1 - t) := by
    field_simp [ht1.ne']
    ring
  unfold betaKernel
  simp only [Real.rpow_eq_pow]
  rw [Real.div_rpow ht0.le ht1.le, hfrac,
    Real.div_rpow zero_le_one ht1.le, Real.one_rpow]
  have hpow : (1 - t) ^ (2 : ℕ) = Real.rpow (1 - t) (2 : ℝ) :=
    (Real.rpow_natCast (1 - t) 2).symm
  rw [hpow]
  have hne1 : Real.rpow (1 - t) (a - 1) ≠ 0 :=
    (Real.rpow_pos_of_pos ht1 _).ne'
  have hne2 : Real.rpow (1 - t) (a + b) ≠ 0 :=
    (Real.rpow_pos_of_pos ht1 _).ne'
  have hne3 : Real.rpow (1 - t) (2 : ℝ) ≠ 0 :=
    (Real.rpow_pos_of_pos ht1 _).ne'
  field_simp [hne1, hne2, hne3]
  calc
    Real.rpow (1 - t) (a + b) =
        Real.rpow (1 - t) (((2 : ℝ) + (a - 1)) + (b - 1)) := by
      congr 1
      ring
    _ = Real.rpow (1 - t) ((2 : ℝ) + (a - 1)) *
        Real.rpow (1 - t) (b - 1) :=
      Real.rpow_add ht1 _ _
    _ = Real.rpow (1 - t) (2 : ℝ) *
        Real.rpow (1 - t) (a - 1) *
        Real.rpow (1 - t) (b - 1) := by
      congr 1
      exact Real.rpow_add ht1 _ _

private theorem canonical_transformed
    {q t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (1 / (1 - t) ^ 2) * canonicalKernel q (t / (1 - t)) =
      betaKernel q (1 - q) t := by
  have h := betaPrime_substitution_integrand
    (a := q) (b := 1 - q) ht
  simpa [canonicalKernel] using h

private theorem canonical_integrable_iff (q : ℝ) :
    IntegrableOn (canonicalKernel q) (Ioi (0 : ℝ)) volume ↔
      0 < q ∧ q < 1 := by
  let f : ℝ → ℝ := fun t => t / (1 - t)
  let f' : ℝ → ℝ := fun t => 1 / (1 - t) ^ 2
  have hf' :
      ∀ t ∈ Ioo (0 : ℝ) 1,
        HasDerivWithinAt f (f' t) (Ioo (0 : ℝ) 1) t := by
    intro t ht
    apply HasDerivAt.hasDerivWithinAt
    dsimp [f, f']
    have hdenDeriv : HasDerivAt (fun y : ℝ => 1 - y) (-1) t := by
      simpa only [Pi.sub_apply, Pi.one_apply, id_eq, zero_sub] using
        (hasDerivAt_const t 1).sub (hasDerivAt_id t)
    have hne : 1 - t ≠ 0 := (sub_pos.mpr ht.2).ne'
    convert (hasDerivAt_id t).div hdenDeriv hne using 1
    simp only [id_eq]
    field_simp [hne]
    ring
  have hinj : Set.InjOn f (Ioo (0 : ℝ) 1) := by
    intro a ha b hb hab
    dsimp [f] at hab
    have ha0 : 1 - a ≠ 0 := (sub_pos.mpr ha.2).ne'
    have hb0 : 1 - b ≠ 0 := (sub_pos.mpr hb.2).ne'
    field_simp [ha0, hb0] at hab
    linarith
  have himage : f '' Ioo (0 : ℝ) 1 = Ioi 0 := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact div_pos ht.1 (sub_pos.mpr ht.2)
    · intro hx
      have hx' : 0 < x := hx
      have hden : 0 < 1 + x := by linarith
      refine ⟨x / (1 + x), ?_, ?_⟩
      · constructor
        · exact div_pos hx hden
        · exact (div_lt_one hden).2 (by linarith)
      · dsimp [f]
        field_simp [hden.ne']
        ring
  have hchange :=
    integrableOn_image_iff_integrableOn_abs_deriv_smul
      measurableSet_Ioo hf' hinj (canonicalKernel q)
  rw [himage] at hchange
  rw [hchange]
  have hcongr :
      IntegrableOn
          (fun t => |f' t| • canonicalKernel q (f t))
          (Ioo (0 : ℝ) 1) volume ↔
        IntegrableOn (betaKernel q (1 - q)) (Ioo (0 : ℝ) 1) volume := by
    apply integrableOn_congr_fun
    · intro t ht
      dsimp [f, f']
      rw [abs_of_pos
        (one_div_pos.mpr (sq_pos_of_ne_zero (sub_ne_zero.mpr ht.2.ne')))]
      exact canonical_transformed ht
    · exact measurableSet_Ioo
  rw [hcongr, betaKernel_integrable_iff]
  constructor
  · rintro ⟨hq, h1q⟩
    exact ⟨hq, by linarith⟩
  · rintro ⟨hq, hq1⟩
    exact ⟨hq, by linarith⟩

private theorem ofReal_beta_setIntegral
    {u v : ℝ} :
    (((∫ t in Ioo (0 : ℝ) 1, betaKernel u v t ∂volume) : ℝ) : ℂ) =
      Complex.betaIntegral (u : ℂ) (v : ℂ) := by
  rw [Complex.betaIntegral, intervalIntegral.integral_of_le (by norm_num),
    MeasureTheory.integral_Ioc_eq_integral_Ioo]
  calc
    (((∫ t in Ioo (0 : ℝ) 1, betaKernel u v t) : ℝ) : ℂ) =
        ∫ t in Ioo (0 : ℝ) 1, ((betaKernel u v t : ℝ) : ℂ) :=
      integral_ofReal.symm
    _ = _ := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
      intro t ht
      dsimp [betaKernel]
      rw [Complex.ofReal_mul]
      congr 1
      · calc
          ((t.rpow (u - 1) : ℝ) : ℂ) = (t : ℂ) ^ ((u - 1 : ℝ) : ℂ) :=
            Complex.ofReal_cpow ht.1.le (u - 1)
          _ = (t : ℂ) ^ ((u : ℂ) - 1) := by push_cast; rfl
      · calc
          (((1 - t).rpow (v - 1) : ℝ) : ℂ) =
              ((1 - t : ℝ) : ℂ) ^ ((v - 1 : ℝ) : ℂ) :=
            Complex.ofReal_cpow (sub_nonneg.mpr ht.2.le) (v - 1)
          _ = (1 - (t : ℂ)) ^ ((v : ℂ) - 1) := by push_cast; rfl

private theorem beta_setIntegral_eq_gamma
    {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    (∫ t in Ioo (0 : ℝ) 1, betaKernel u v t ∂volume) =
      Real.Gamma u * Real.Gamma v / Real.Gamma (u + v) := by
  apply Complex.ofReal_injective
  rw [ofReal_beta_setIntegral,
    Complex.betaIntegral_eq_Gamma_mul_div (u := (u : ℂ)) (v := (v : ℂ))
      (by simpa) (by simpa)]
  simp only [← Complex.Gamma_ofReal, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_add]

private theorem canonical_integral (q : ℝ) (hq : 0 < q) (hq1 : q < 1) :
    (∫ x in Ioi (0 : ℝ), canonicalKernel q x ∂volume) =
      Real.pi / Real.sin (q * Real.pi) := by
  let f : ℝ → ℝ := fun t => t / (1 - t)
  let f' : ℝ → ℝ := fun t => 1 / (1 - t) ^ 2
  have hf' :
      ∀ t ∈ Ioo (0 : ℝ) 1,
        HasDerivWithinAt f (f' t) (Ioo (0 : ℝ) 1) t := by
    intro t ht
    apply HasDerivAt.hasDerivWithinAt
    dsimp [f, f']
    have hdenDeriv : HasDerivAt (fun y : ℝ => 1 - y) (-1) t := by
      simpa only [Pi.sub_apply, Pi.one_apply, id_eq, zero_sub] using
        (hasDerivAt_const t 1).sub (hasDerivAt_id t)
    have hne : 1 - t ≠ 0 := (sub_pos.mpr ht.2).ne'
    convert (hasDerivAt_id t).div hdenDeriv hne using 1
    simp only [id_eq]
    field_simp [hne]
    ring
  have hinj : Set.InjOn f (Ioo (0 : ℝ) 1) := by
    intro a ha b hb hab
    dsimp [f] at hab
    have ha0 : 1 - a ≠ 0 := (sub_pos.mpr ha.2).ne'
    have hb0 : 1 - b ≠ 0 := (sub_pos.mpr hb.2).ne'
    field_simp [ha0, hb0] at hab
    linarith
  have himage : f '' Ioo (0 : ℝ) 1 = Ioi 0 := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact div_pos ht.1 (sub_pos.mpr ht.2)
    · intro hx
      have hx' : 0 < x := hx
      have hden : 0 < 1 + x := by linarith
      refine ⟨x / (1 + x), ?_, ?_⟩
      · constructor
        · exact div_pos hx hden
        · exact (div_lt_one hden).2 (by linarith)
      · dsimp [f]
        field_simp [hden.ne']
        ring
  have hchange := integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioo hf' hinj (canonicalKernel q)
  rw [himage] at hchange
  have hbeta :
      (∫ x in Ioi (0 : ℝ), canonicalKernel q x ∂volume) =
        ∫ t in Ioo (0 : ℝ) 1, betaKernel q (1 - q) t ∂volume := by
    rw [hchange]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
    intro t ht
    dsimp [f, f']
    rw [abs_of_pos
      (one_div_pos.mpr (sq_pos_of_ne_zero (sub_ne_zero.mpr ht.2.ne')))]
    exact canonical_transformed ht
  rw [hbeta, beta_setIntegral_eq_gamma hq (by linarith)]
  have href := Real.Gamma_mul_Gamma_one_sub q
  rw [show q + (1 - q) = 1 by ring, Real.Gamma_one, div_one]
  simpa only [mul_comm] using href

private theorem power_substitution_pointwise
    {m n x : ℝ} (hn : 0 < n) (hx : x ∈ Ioi (0 : ℝ)) :
    Real.rpow x (n - 1) * canonicalKernel (m / n) (Real.rpow x n) =
      integrand m n x := by
  have hx0 : 0 < x := hx
  unfold canonicalKernel integrand
  simp only [Real.rpow_eq_pow]
  rw [← Real.rpow_mul hx0.le n (m / n - 1)]
  calc
    x ^ (n - 1) * (x ^ (n * (m / n - 1)) / (1 + x ^ n)) =
        (x ^ (n - 1) * x ^ (n * (m / n - 1))) / (1 + x ^ n) := by
      ring
    _ = x ^ ((n - 1) + n * (m / n - 1)) / (1 + x ^ n) := by
      congr 1
      exact (Real.rpow_add hx0 _ _).symm
    _ = x ^ (m - 1) / (1 + x ^ n) := by
      congr 2
      field_simp [hn.ne']
      ring

private theorem integrableOn_integrand_iff_canonical
    (m n : ℝ) (hn : 0 < n) :
    IntegrableOn (integrand m n) (Ioi (0 : ℝ)) volume ↔
      IntegrableOn (canonicalKernel (m / n)) (Ioi (0 : ℝ)) volume := by
  calc
    IntegrableOn (integrand m n) (Ioi (0 : ℝ)) volume ↔
        IntegrableOn
          (fun x : ℝ =>
            Real.rpow x (n - 1) •
              canonicalKernel (m / n) (Real.rpow x n))
          (Ioi (0 : ℝ)) volume := by
      apply integrableOn_congr_fun
      · intro x hx
        simp only [smul_eq_mul]
        exact (power_substitution_pointwise hn hx).symm
      · exact measurableSet_Ioi
    _ ↔ IntegrableOn (canonicalKernel (m / n)) (Ioi (0 : ℝ)) volume :=
      integrableOn_Ioi_comp_rpow_iff' (canonicalKernel (m / n)) hn.ne'

private theorem integral_integrand_eq_scaled_canonical
    (m n : ℝ) (hn : 0 < n) :
    (∫ x in Ioi (0 : ℝ), integrand m n x ∂volume) =
      1 / n *
        ∫ y in Ioi (0 : ℝ), canonicalKernel (m / n) y ∂volume := by
  have hsub := integral_comp_rpow_Ioi_of_pos
    (g := canonicalKernel (m / n)) (p := n) hn
  simp only [smul_eq_mul] at hsub
  have hleft :
      (∫ x in Ioi (0 : ℝ),
          (n * Real.rpow x (n - 1)) *
            canonicalKernel (m / n) (Real.rpow x n) ∂volume) =
        ∫ x in Ioi (0 : ℝ), n * integrand m n x ∂volume := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    calc
      n * Real.rpow x (n - 1) *
            canonicalKernel (m / n) (Real.rpow x n) =
          n * (Real.rpow x (n - 1) *
            canonicalKernel (m / n) (Real.rpow x n)) := by ring
      _ = n * integrand m n x := by
        rw [power_substitution_pointwise hn hx]
  have hleft' := hleft
  simp only [Real.rpow_eq_pow] at hleft'
  rw [hleft', MeasureTheory.integral_const_mul] at hsub
  calc
    (∫ x in Ioi (0 : ℝ), integrand m n x ∂volume) =
        1 / n *
          (n * ∫ x in Ioi (0 : ℝ), integrand m n x ∂volume) := by
      field_simp [hn.ne']
    _ = 1 / n *
        ∫ y in Ioi (0 : ℝ), canonicalKernel (m / n) y ∂volume := by
      rw [hsub]

private def transformedIntegrand (m n t : ℝ) : ℝ :=
  Real.rpow t ((m - n) / n) / (1 + t)

private theorem transformed_eq_canonical
    (m n t : ℝ) (hn : 0 < n) :
    transformedIntegrand m n t = canonicalKernel (m / n) t := by
  unfold transformedIntegrand canonicalKernel
  have hexp : (m - n) / n = m / n - 1 := by
    field_simp [hn.ne']
  rw [hexp]

private theorem canonical_integrableOn
    (m n : ℝ) (hn : 0 < n) (hm : 0 < m) (hmn : m < n) :
    IntegrableOn (canonicalKernel (m / n)) (Ioi (0 : ℝ)) := by
  exact (canonical_integrable_iff (m / n)).2
    ⟨div_pos hm hn, (div_lt_one hn).2 hmn⟩

private theorem transformed_integrableOn
    (m n : ℝ) (hn : 0 < n) (hm : 0 < m) (hmn : m < n) :
    IntegrableOn (transformedIntegrand m n) (Ioi (0 : ℝ)) := by
  exact (canonical_integrableOn m n hn hm hmn).congr_fun
    (fun t _ => (transformed_eq_canonical m n t hn).symm)
    measurableSet_Ioi

private theorem source_integrableOn
    (m n : ℝ) (hn : 0 < n) (hm : 0 < m) (hmn : m < n) :
    IntegrableOn (integrand m n) (Ioi (0 : ℝ)) := by
  exact (integrableOn_integrand_iff_canonical m n hn).2
    (canonical_integrableOn m n hn hm hmn)

private theorem improperIntegral_eq_of_hasImproperIntegral
    {a : ℝ} {f : ℝ → ℝ} {L : ℝ}
    (hL : HasImproperIntegral a f L) :
    improperIntegral a f = L := by
  unfold improperIntegral
  have hs :
      {y : ℝ | HasImproperIntegral a f y} = {L} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro hy
      exact tendsto_nhds_unique hy hL
    · rintro rfl
      exact hL
  rw [hs]
  exact csInf_singleton L

private theorem source_improper_eq_setIntegral
    (m n : ℝ) (hn : 0 < n) (hm : 0 < m) (hmn : m < n) :
    improperIntegral 0 (integrand m n) =
      ∫ x in Ioi (0 : ℝ), integrand m n x := by
  apply improperIntegral_eq_of_hasImproperIntegral
  unfold HasImproperIntegral
  exact intervalIntegral_tendsto_integral_Ioi
    0 (source_integrableOn m n hn hm hmn) tendsto_id

private theorem transformed_improper_eq_setIntegral
    (m n : ℝ) (hn : 0 < n) (hm : 0 < m) (hmn : m < n) :
    improperIntegral 0 (transformedIntegrand m n) =
      ∫ t in Ioi (0 : ℝ), transformedIntegrand m n t := by
  apply improperIntegral_eq_of_hasImproperIntegral
  unfold HasImproperIntegral
  exact intervalIntegral_tendsto_integral_Ioi
    0 (transformed_integrableOn m n hn hm hmn) tendsto_id

private theorem betaFn_eq_gamma
    {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    betaFn u v =
      Real.Gamma u * Real.Gamma v / Real.Gamma (u + v) := by
  unfold betaFn
  rw [intervalIntegral.integral_of_le zero_le_one,
    MeasureTheory.integral_Ioc_eq_integral_Ioo]
  simpa only [betaKernel] using beta_setIntegral_eq_gamma hu hv

private theorem canonical_setIntegral_eq_intervalBeta
    (m n : ℝ) (hn : 0 < n) (hm : 0 < m) (hmn : m < n) :
    (∫ t in Ioi (0 : ℝ), canonicalKernel (m / n) t) =
      ∫ u in (0 : ℝ)..1,
        Real.rpow u (m / n - 1) *
          Real.rpow (1 - u) ((n - m) / n - 1) := by
  have hq : 0 < m / n := div_pos hm hn
  have hq1 : m / n < 1 := (div_lt_one hn).2 hmn
  have hv : 0 < (n - m) / n := div_pos (sub_pos.mpr hmn) hn
  have hvEq : (n - m) / n = 1 - m / n := by
    field_simp [hn.ne']
  calc
    (∫ t in Ioi (0 : ℝ), canonicalKernel (m / n) t) =
        Real.pi / Real.sin ((m / n) * Real.pi) :=
      canonical_integral (m / n) hq hq1
    _ = Real.Gamma (m / n) * Real.Gamma ((n - m) / n) /
        Real.Gamma (m / n + (n - m) / n) := by
      rw [hvEq, show m / n + (1 - m / n) = 1 by ring,
        Real.Gamma_one, div_one,
        Real.Gamma_mul_Gamma_one_sub]
      congr 2
      ring
    _ = ∫ u in Ioo (0 : ℝ) 1,
          Real.rpow u (m / n - 1) *
            Real.rpow (1 - u) ((n - m) / n - 1) := by
      simpa only [betaKernel] using
        (beta_setIntegral_eq_gamma hq hv).symm
    _ = _ := by
      rw [intervalIntegral.integral_of_le zero_le_one,
        MeasureTheory.integral_Ioc_eq_integral_Ioo]

theorem gap1 (m n : ℝ) (hn : 0 < n) (hm : 0 < m) (hmn : m < n) :
    improperIntegral 0 (integrand m n) =
      1 / n *
        improperIntegral 0
          (fun t => Real.rpow t ((m - n) / n) / (1 + t)) := by
  change improperIntegral 0 (integrand m n) =
    1 / n * improperIntegral 0 (transformedIntegrand m n)
  rw [source_improper_eq_setIntegral m n hn hm hmn,
    transformed_improper_eq_setIntegral m n hn hm hmn,
    integral_integrand_eq_scaled_canonical m n hn]
  congr 1
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro t _
  exact (transformed_eq_canonical m n t hn).symm

theorem gap2 (m n : ℝ) (hn : 0 < n) (hm : 0 < m) (hmn : m < n) :
    improperIntegral 0 (integrand m n) =
      1 / n *
        ∫ u in (0 : ℝ)..1,
          Real.rpow u (m / n - 1) *
            Real.rpow (1 - u) ((n - m) / n - 1) := by
  rw [source_improper_eq_setIntegral m n hn hm hmn,
    integral_integrand_eq_scaled_canonical m n hn,
    canonical_setIntegral_eq_intervalBeta m n hn hm hmn]

theorem gap3 (m n : ℝ) (hn : 0 < n) :
    0 < m / n ∧ 0 < (n - m) / n ↔
      0 < m ∧ m < n := by
  constructor
  · rintro ⟨hm, hnm⟩
    have hm0 : 0 < m := by
      rcases div_pos_iff.mp hm with hpos | hneg
      · exact hpos.1
      · linarith [hneg.2]
    have hnm0 : 0 < n - m := by
      rcases div_pos_iff.mp hnm with hpos | hneg
      · exact hpos.1
      · linarith [hneg.2]
    exact ⟨hm0, sub_pos.mp hnm0⟩
  · rintro ⟨hm, hmn⟩
    exact ⟨div_pos hm hn, div_pos (sub_pos.mpr hmn) hn⟩

theorem gap4 (m n : ℝ) (hn : 0 < n) (hm : 0 < m) (hmn : m < n) :
    improperIntegral 0 (integrand m n) =
      1 / n * betaFn (m / n) ((n - m) / n) := by
  rw [gap2 m n hn hm hmn]
  rfl

theorem gap5 (m n : ℝ) (hn : 0 < n) (hm : 0 < m) (hmn : m < n) :
    1 / n * betaFn (m / n) ((n - m) / n) =
      1 / n *
        (Real.Gamma (m / n) * Real.Gamma (1 - m / n) /
          Real.Gamma 1) := by
  have hq : 0 < m / n := div_pos hm hn
  have hv : 0 < (n - m) / n := div_pos (sub_pos.mpr hmn) hn
  rw [betaFn_eq_gamma hq hv]
  congr 1
  congr 1
  · congr 1
    field_simp [hn.ne']
  · congr 1
    field_simp [hn.ne']
    ring

theorem gap6 (m n : ℝ) (hn : 0 < n) (hm : 0 < m) (hmn : m < n) :
    1 / n *
        (Real.Gamma (m / n) * Real.Gamma (1 - m / n) /
          Real.Gamma 1) =
      Real.pi / (n * Real.sin (m * Real.pi / n)) := by
  rw [Real.Gamma_one, div_one,
    Real.Gamma_mul_Gamma_one_sub]
  rw [show Real.pi * (m / n) = m * Real.pi / n by ring]
  field_simp [hn.ne']

theorem gap7 (m n : ℝ) (hn : 0 < n) (hm : 0 < m) (hmn : m < n) :
    improperIntegral 0 (integrand m n) =
      Real.pi / (n * Real.sin (m * Real.pi / n)) :=
  (gap4 m n hn hm hmn).trans
    ((gap5 m n hn hm hmn).trans (gap6 m n hn hm hmn))

end

end ProofGap.Exercise3851
