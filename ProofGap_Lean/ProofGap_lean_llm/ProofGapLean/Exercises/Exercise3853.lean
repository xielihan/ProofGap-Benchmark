import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace ProofGap.Exercise3853

noncomputable section

open Filter MeasureTheory Set
open scoped Interval

def HasImproperIntegral (a : ℝ) (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Tendsto (fun b : ℝ => ∫ x in a..b, f x) atTop (nhds L)

def improperIntegral (a : ℝ) (f : ℝ → ℝ) : ℝ :=
  sInf {L : ℝ | HasImproperIntegral a f L}

def betaFn (x y : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1,
    Real.rpow t (x - 1) * Real.rpow (1 - t) (y - 1)

def xOfT (a b n t : ℝ) : ℝ :=
  Real.rpow (a / b) (1 / n) *
    Real.rpow (t / (1 - t)) (1 / n)

private def betaFunctionSet (u v : ℝ) : ℝ :=
  ∫ t in Ioo (0 : ℝ) 1,
    Real.rpow t (u - 1) * Real.rpow (1 - t) (v - 1)
      ∂MeasureTheory.volume

def integrand (a b m n p x : ℝ) : ℝ :=
  Real.rpow x m /
    Real.rpow (a + b * Real.rpow x n) p

private def betaKernel (u v t : ℝ) : ℝ :=
  Real.rpow t (u - 1) * Real.rpow (1 - t) (v - 1)

private def canonicalKernel (q p x : ℝ) : ℝ :=
  Real.rpow x (q - 1) / Real.rpow (1 + x) p

private def reducedKernel (a b q p y : ℝ) : ℝ :=
  Real.rpow y (q - 1) / Real.rpow (a + b * y) p

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

private theorem transformed_canonical
    {q p t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (1 / (1 - t) ^ 2) *
        canonicalKernel q p (t / (1 - t)) =
      betaKernel q (p - q) t := by
  have ht0 : 0 < t := ht.1
  have ht1 : 0 < 1 - t := sub_pos.mpr ht.2
  have hfrac : 1 + t / (1 - t) = 1 / (1 - t) := by
    field_simp [ht1.ne']
    ring
  unfold canonicalKernel betaKernel
  simp only [Real.rpow_eq_pow]
  rw [Real.div_rpow ht0.le ht1.le, hfrac,
    Real.div_rpow zero_le_one ht1.le, Real.one_rpow]
  have hpow : (1 - t) ^ (2 : ℕ) = Real.rpow (1 - t) (2 : ℝ) :=
    (Real.rpow_natCast (1 - t) 2).symm
  rw [hpow]
  have hne1 : Real.rpow (1 - t) (q - 1) ≠ 0 :=
    (Real.rpow_pos_of_pos ht1 _).ne'
  have hne2 : Real.rpow (1 - t) p ≠ 0 :=
    (Real.rpow_pos_of_pos ht1 _).ne'
  have hne3 : Real.rpow (1 - t) (2 : ℝ) ≠ 0 :=
    (Real.rpow_pos_of_pos ht1 _).ne'
  field_simp [hne1, hne2, hne3]
  calc
    Real.rpow (1 - t) p =
        Real.rpow (1 - t)
          (((2 : ℝ) + (q - 1)) + ((p - q) - 1)) := by
      congr 1
      ring
    _ = Real.rpow (1 - t) ((2 : ℝ) + (q - 1)) *
        Real.rpow (1 - t) ((p - q) - 1) :=
      Real.rpow_add ht1 _ _
    _ = Real.rpow (1 - t) (2 : ℝ) *
        Real.rpow (1 - t) (q - 1) *
        Real.rpow (1 - t) ((p - q) - 1) := by
      congr 1
      exact Real.rpow_add ht1 _ _

private theorem canonical_integrable_iff (q p : ℝ) :
    IntegrableOn (canonicalKernel q p) (Ioi (0 : ℝ)) volume ↔
      0 < q ∧ q < p := by
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
    intro c hc d hd hcd
    dsimp [f] at hcd
    have hc0 : 1 - c ≠ 0 := (sub_pos.mpr hc.2).ne'
    have hd0 : 1 - d ≠ 0 := (sub_pos.mpr hd.2).ne'
    field_simp [hc0, hd0] at hcd
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
      measurableSet_Ioo hf' hinj (canonicalKernel q p)
  rw [himage] at hchange
  rw [hchange]
  have hcongr :
      IntegrableOn
          (fun t => |f' t| • canonicalKernel q p (f t))
          (Ioo (0 : ℝ) 1) volume ↔
        IntegrableOn (betaKernel q (p - q)) (Ioo (0 : ℝ) 1) volume := by
    apply integrableOn_congr_fun
    · intro t ht
      dsimp [f, f']
      rw [abs_of_pos
        (one_div_pos.mpr (sq_pos_of_ne_zero (sub_ne_zero.mpr ht.2.ne')))]
      exact transformed_canonical ht
    · exact measurableSet_Ioo
  rw [hcongr, betaKernel_integrable_iff]
  constructor
  · rintro ⟨hq, hpq⟩
    exact ⟨hq, by linarith⟩
  · rintro ⟨hq, hqp⟩
    exact ⟨hq, by linarith⟩

private theorem canonical_integral_eq_betaFunction (q p : ℝ) :
    (∫ x in Ioi (0 : ℝ), canonicalKernel q p x ∂volume) =
      betaFunctionSet q (p - q) := by
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
    intro c hc d hd hcd
    dsimp [f] at hcd
    have hc0 : 1 - c ≠ 0 := (sub_pos.mpr hc.2).ne'
    have hd0 : 1 - d ≠ 0 := (sub_pos.mpr hd.2).ne'
    field_simp [hc0, hd0] at hcd
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
    measurableSet_Ioo hf' hinj (canonicalKernel q p)
  rw [himage] at hchange
  rw [hchange]
  unfold betaFunctionSet
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
  intro t ht
  dsimp [f, f']
  rw [abs_of_pos
    (one_div_pos.mpr (sq_pos_of_ne_zero (sub_ne_zero.mpr ht.2.ne')))]
  exact transformed_canonical ht

private theorem reduced_scaled
    {a b q p z : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hz : z ∈ Ioi (0 : ℝ)) :
    reducedKernel a b q p ((a / b) * z) =
      Real.rpow a (-p) * Real.rpow (a / b) (q - 1) *
        canonicalKernel q p z := by
  have hz0 : 0 < z := hz
  have hd : 0 < a / b := div_pos ha hb
  have hden : a + b * ((a / b) * z) = a * (1 + z) := by
    field_simp [hb.ne']
  unfold reducedKernel canonicalKernel
  simp only [Real.rpow_eq_pow]
  rw [hden, Real.mul_rpow hd.le hz0.le,
    Real.mul_rpow ha.le (by linarith : 0 ≤ 1 + z),
    Real.rpow_neg ha.le]
  have haPow : Real.rpow a p ≠ 0 :=
    (Real.rpow_pos_of_pos ha _).ne'
  have hOnePow : Real.rpow (1 + z) p ≠ 0 :=
    (Real.rpow_pos_of_pos (by linarith) _).ne'
  field_simp [haPow, hOnePow]

private theorem reduced_integrable_iff_canonical
    (a b q p : ℝ) (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn (reducedKernel a b q p) (Ioi (0 : ℝ)) volume ↔
      IntegrableOn (canonicalKernel q p) (Ioi (0 : ℝ)) volume := by
  let d : ℝ := a / b
  let c : ℝ := Real.rpow a (-p) * Real.rpow d (q - 1)
  have hd : 0 < d := by dsimp [d]; exact div_pos ha hb
  have hc : c ≠ 0 := by
    dsimp [c]
    exact mul_ne_zero
      (Real.rpow_pos_of_pos ha _).ne'
      (Real.rpow_pos_of_pos hd _).ne'
  calc
    IntegrableOn (reducedKernel a b q p) (Ioi (0 : ℝ)) volume ↔
        IntegrableOn
          (fun z => reducedKernel a b q p (d * z))
          (Ioi (0 : ℝ)) volume :=
      by
        simpa only [mul_zero] using
          (integrableOn_Ioi_comp_mul_left_iff
            (reducedKernel a b q p) 0 hd).symm
    _ ↔ IntegrableOn
          (fun z => c * canonicalKernel q p z)
          (Ioi (0 : ℝ)) volume := by
      apply integrableOn_congr_fun
      · intro z hz
        dsimp [d, c]
        exact reduced_scaled ha hb hz
      · exact measurableSet_Ioi
    _ ↔ IntegrableOn (canonicalKernel q p) (Ioi (0 : ℝ)) volume := by
      change
        Integrable (fun z => c * canonicalKernel q p z)
            (volume.restrict (Ioi (0 : ℝ))) ↔
          Integrable (canonicalKernel q p)
            (volume.restrict (Ioi (0 : ℝ)))
      exact integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hc) _

private theorem reduced_integral_eq_scaled_canonical
    (a b q p : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∫ y in Ioi (0 : ℝ), reducedKernel a b q p y ∂volume) =
      Real.rpow a (-p) * Real.rpow (a / b) q *
        ∫ z in Ioi (0 : ℝ), canonicalKernel q p z ∂volume := by
  let d : ℝ := a / b
  let c : ℝ := Real.rpow a (-p) * Real.rpow d (q - 1)
  have hd : 0 < d := by dsimp [d]; exact div_pos ha hb
  have hscale := integral_comp_mul_left_Ioi
    (reducedKernel a b q p) 0 hd
  simp only [mul_zero, smul_eq_mul] at hscale
  have hcomp :
      (∫ z in Ioi (0 : ℝ),
          reducedKernel a b q p (d * z) ∂volume) =
        c * ∫ z in Ioi (0 : ℝ), canonicalKernel q p z ∂volume := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro z hz
    dsimp [d, c]
    exact reduced_scaled ha hb hz
  rw [hcomp] at hscale
  calc
    (∫ y in Ioi (0 : ℝ), reducedKernel a b q p y ∂volume) =
        d * (d⁻¹ *
          ∫ y in Ioi (0 : ℝ), reducedKernel a b q p y ∂volume) := by
      field_simp [hd.ne']
    _ = d * (c *
        ∫ z in Ioi (0 : ℝ), canonicalKernel q p z ∂volume) := by
      rw [← hscale]
    _ = Real.rpow a (-p) * Real.rpow (a / b) q *
        ∫ z in Ioi (0 : ℝ), canonicalKernel q p z ∂volume := by
      dsimp [d, c]
      have hpow :
          (a / b) * Real.rpow (a / b) (q - 1) =
            Real.rpow (a / b) q := by
        calc
          (a / b) * Real.rpow (a / b) (q - 1) =
              Real.rpow (a / b) 1 *
                Real.rpow (a / b) (q - 1) := by
            congr 1
            exact (Real.rpow_one _).symm
          _ = Real.rpow (a / b) (1 + (q - 1)) :=
            (Real.rpow_add (div_pos ha hb) _ _).symm
          _ = Real.rpow (a / b) q := by ring_nf
      calc
        (a / b) *
              (Real.rpow a (-p) * Real.rpow (a / b) (q - 1) *
                ∫ z in Ioi (0 : ℝ), canonicalKernel q p z ∂volume) =
            Real.rpow a (-p) *
              ((a / b) * Real.rpow (a / b) (q - 1)) *
                ∫ z in Ioi (0 : ℝ), canonicalKernel q p z ∂volume := by
          ring
        _ = _ := by
          rw [hpow]
          simp only [Real.rpow_eq_pow]

private theorem power_substitution_pointwise
    {a b m n p x : ℝ} (hn : 0 < n) (hx : x ∈ Ioi (0 : ℝ)) :
    Real.rpow x (n - 1) *
        reducedKernel a b ((m + 1) / n) p (Real.rpow x n) =
      integrand a b m n p x := by
  have hx0 : 0 < x := hx
  unfold reducedKernel integrand
  simp only [Real.rpow_eq_pow]
  rw [← Real.rpow_mul hx0.le n ((m + 1) / n - 1)]
  calc
    x ^ (n - 1) *
          (x ^ (n * ((m + 1) / n - 1)) /
            (a + b * x ^ n) ^ p) =
        (x ^ (n - 1) * x ^ (n * ((m + 1) / n - 1))) /
          (a + b * x ^ n) ^ p := by
      ring
    _ = x ^ ((n - 1) + n * ((m + 1) / n - 1)) /
          (a + b * x ^ n) ^ p := by
      congr 1
      exact (Real.rpow_add hx0 _ _).symm
    _ = x ^ m / (a + b * x ^ n) ^ p := by
      congr 2
      field_simp [hn.ne']
      ring

private theorem integrableOn_integrand_iff_reduced
    (a b m n p : ℝ) (hn : 0 < n) :
    IntegrableOn (integrand a b m n p) (Ioi (0 : ℝ)) volume ↔
      IntegrableOn (reducedKernel a b ((m + 1) / n) p)
        (Ioi (0 : ℝ)) volume := by
  calc
    IntegrableOn (integrand a b m n p) (Ioi (0 : ℝ)) volume ↔
        IntegrableOn
          (fun x : ℝ =>
            Real.rpow x (n - 1) •
              reducedKernel a b ((m + 1) / n) p (Real.rpow x n))
          (Ioi (0 : ℝ)) volume := by
      apply integrableOn_congr_fun
      · intro x hx
        simp only [smul_eq_mul]
        exact (power_substitution_pointwise hn hx).symm
      · exact measurableSet_Ioi
    _ ↔ IntegrableOn (reducedKernel a b ((m + 1) / n) p)
          (Ioi (0 : ℝ)) volume :=
      integrableOn_Ioi_comp_rpow_iff'
        (reducedKernel a b ((m + 1) / n) p) hn.ne'

private theorem integral_integrand_eq_scaled_reduced
    (a b m n p : ℝ) (hn : 0 < n) :
    (∫ x in Ioi (0 : ℝ), integrand a b m n p x ∂volume) =
      1 / n *
        ∫ y in Ioi (0 : ℝ),
          reducedKernel a b ((m + 1) / n) p y ∂volume := by
  have hsub := integral_comp_rpow_Ioi_of_pos
    (g := reducedKernel a b ((m + 1) / n) p) (p := n) hn
  simp only [smul_eq_mul] at hsub
  have hleft :
      (∫ x in Ioi (0 : ℝ),
          (n * Real.rpow x (n - 1)) *
            reducedKernel a b ((m + 1) / n) p
              (Real.rpow x n) ∂volume) =
        ∫ x in Ioi (0 : ℝ), n * integrand a b m n p x ∂volume := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    calc
      n * Real.rpow x (n - 1) *
            reducedKernel a b ((m + 1) / n) p (Real.rpow x n) =
          n * (Real.rpow x (n - 1) *
            reducedKernel a b ((m + 1) / n) p (Real.rpow x n)) := by ring
      _ = n * integrand a b m n p x := by
        rw [power_substitution_pointwise hn hx]
  have hleft' := hleft
  simp only [Real.rpow_eq_pow] at hleft'
  rw [hleft', MeasureTheory.integral_const_mul] at hsub
  calc
    (∫ x in Ioi (0 : ℝ), integrand a b m n p x ∂volume) =
        1 / n *
          (n * ∫ x in Ioi (0 : ℝ), integrand a b m n p x ∂volume) := by
      field_simp [hn.ne']
    _ = 1 / n *
        ∫ y in Ioi (0 : ℝ),
          reducedKernel a b ((m + 1) / n) p y ∂volume := by
      rw [hsub]

private def alternateIntegrand (a b m n p x : ℝ) : ℝ :=
  Real.rpow
      (b * Real.rpow x n /
        (a + b * Real.rpow x n)) p *
    Real.rpow x (m - n * p)

private theorem alternate_scaled_eq_source
    {a b m n p x : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hx : x ∈ Ioi (0 : ℝ)) :
    1 / Real.rpow b p * alternateIntegrand a b m n p x =
      integrand a b m n p x := by
  have hx0 : 0 < x := hx
  have hxn : 0 < Real.rpow x n :=
    Real.rpow_pos_of_pos hx0 n
  have hnum : 0 < b * Real.rpow x n := mul_pos hb hxn
  have hden : 0 < a + b * Real.rpow x n := by positivity
  have hbp : Real.rpow b p ≠ 0 :=
    (Real.rpow_pos_of_pos hb p).ne'
  have hdp : Real.rpow (a + b * Real.rpow x n) p ≠ 0 :=
    (Real.rpow_pos_of_pos hden p).ne'
  unfold alternateIntegrand integrand
  simp only [Real.rpow_eq_pow]
  have hxn' : 0 ≤ x ^ n := by
    simpa only [← Real.rpow_eq_pow] using hxn.le
  have hnum' : 0 ≤ b * x ^ n := mul_nonneg hb.le hxn'
  have hden' : 0 ≤ a + b * x ^ n := by positivity
  rw [Real.div_rpow hnum' hden' p,
    Real.mul_rpow hb.le hxn',
    ← Real.rpow_mul hx0.le n p]
  have hmerge :
      x ^ (n * p) * x ^ (m - n * p) = x ^ m := by
    rw [← Real.rpow_add hx0 (n * p) (m - n * p)]
    congr 1
    ring
  rw [← hmerge]
  field_simp [hbp, hdp]

private theorem source_integrableOn
    (a b m n p : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hn : 0 < n) (hq : 0 < (m + 1) / n)
    (hqp : (m + 1) / n < p) :
    IntegrableOn (integrand a b m n p) (Ioi (0 : ℝ)) := by
  apply (integrableOn_integrand_iff_reduced a b m n p hn).2
  apply (reduced_integrable_iff_canonical
    a b ((m + 1) / n) p ha hb).2
  exact (canonical_integrable_iff ((m + 1) / n) p).2
    ⟨hq, hqp⟩

private theorem alternate_integrableOn
    (a b m n p : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hn : 0 < n) (hq : 0 < (m + 1) / n)
    (hqp : (m + 1) / n < p) :
    IntegrableOn (alternateIntegrand a b m n p)
      (Ioi (0 : ℝ)) := by
  have hsource :=
    (source_integrableOn a b m n p ha hb hn hq hqp).const_mul
      (Real.rpow b p)
  refine IntegrableOn.congr_fun hsource ?_ measurableSet_Ioi
  intro x hx
  have hscaled := alternate_scaled_eq_source
    (a := a) (b := b) (m := m) (n := n) (p := p)
    ha hb hx
  have hbp : Real.rpow b p ≠ 0 :=
    (Real.rpow_pos_of_pos hb p).ne'
  calc
    Real.rpow b p * integrand a b m n p x =
        Real.rpow b p *
          (1 / Real.rpow b p *
            alternateIntegrand a b m n p x) := by rw [hscaled]
    _ = alternateIntegrand a b m n p x := by
      field_simp [hbp]

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
    (a b m n p : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hn : 0 < n) (hq : 0 < (m + 1) / n)
    (hqp : (m + 1) / n < p) :
    improperIntegral 0 (integrand a b m n p) =
      ∫ x in Ioi (0 : ℝ), integrand a b m n p x := by
  apply improperIntegral_eq_of_hasImproperIntegral
  unfold HasImproperIntegral
  exact intervalIntegral_tendsto_integral_Ioi
    0 (source_integrableOn a b m n p ha hb hn hq hqp)
    tendsto_id

private theorem alternate_improper_eq_setIntegral
    (a b m n p : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hn : 0 < n) (hq : 0 < (m + 1) / n)
    (hqp : (m + 1) / n < p) :
    improperIntegral 0 (alternateIntegrand a b m n p) =
      ∫ x in Ioi (0 : ℝ), alternateIntegrand a b m n p x := by
  apply improperIntegral_eq_of_hasImproperIntegral
  unfold HasImproperIntegral
  exact intervalIntegral_tendsto_integral_Ioi
    0 (alternate_integrableOn a b m n p ha hb hn hq hqp)
    tendsto_id

private theorem betaFn_eq_betaFunctionSet (u v : ℝ) :
    betaFn u v = betaFunctionSet u v := by
  unfold betaFn betaFunctionSet
  rw [intervalIntegral.integral_of_le zero_le_one,
    MeasureTheory.integral_Ioc_eq_integral_Ioo]

theorem gap1 (a b n t : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hn : 0 < n)
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    xOfT a b n t =
      Real.rpow (a / b) (1 / n) *
        Real.rpow (t / (1 - t)) (1 / n) := by
  rfl

theorem gap2 (a b n t : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hn : 0 < n)
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (xOfT a b n)
      ((1 / n) * Real.rpow (a / b) (1 / n) *
        (Real.rpow t (1 / n - 1) /
          Real.rpow (1 - t) (1 / n + 1))) t := by
  have ht0 : 0 < t := ht.1
  have ht1 : 0 < 1 - t := sub_pos.mpr ht.2
  let u : ℝ → ℝ := fun s => s / (1 - s)
  have hu :
      HasDerivAt u (1 / (1 - t) ^ 2) t := by
    have hdenDeriv :
        HasDerivAt (fun s : ℝ => 1 - s) (-1) t := by
      simpa only [Pi.sub_apply, Pi.one_apply, id_eq,
        zero_sub] using
        (hasDerivAt_const t 1).sub (hasDerivAt_id t)
    have hne : 1 - t ≠ 0 := ht1.ne'
    dsimp [u]
    convert (hasDerivAt_id t).div hdenDeriv hne using 1
    simp only [id_eq]
    field_simp [hne]
    ring
  have hu0 : 0 < u t := by
    dsimp [u]
    exact div_pos ht0 ht1
  have hr :=
    (Real.hasDerivAt_rpow_const
      (p := (1 / n : ℝ)) (Or.inl hu0.ne')).comp t hu
  have hc :=
    hr.const_mul (Real.rpow (a / b) (1 / n))
  unfold xOfT
  convert hc using 1
  dsimp [u]
  rw [Real.div_rpow ht0.le ht1.le]
  have hpow :
      (1 - t) ^ (2 : ℕ) =
        Real.rpow (1 - t) (2 : ℝ) :=
    (Real.rpow_natCast (1 - t) 2).symm
  rw [hpow]
  have hden1 :
      Real.rpow (1 - t) (1 / n - 1) ≠ 0 :=
    (Real.rpow_pos_of_pos ht1 _).ne'
  have hden2 :
      Real.rpow (1 - t) (2 : ℝ) ≠ 0 :=
    (Real.rpow_pos_of_pos ht1 _).ne'
  have hden3 :
      Real.rpow (1 - t) (1 / n + 1) ≠ 0 :=
    (Real.rpow_pos_of_pos ht1 _).ne'
  field_simp [hden1, hden2, hden3]
  change
    Real.rpow (1 - t) ((1 - n) / n) *
        Real.rpow (1 - t) (2 : ℝ) =
      Real.rpow (1 - t) ((1 + n) / n)
  simp only [Real.rpow_eq_pow]
  rw [← Real.rpow_add ht1 ((1 - n) / n) (2 : ℝ)]
  congr 1
  field_simp [hn.ne']
  ring

theorem gap3 (a b m n p : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hn : 0 < n)
    (hq : 0 < (m + 1) / n) (hqp : (m + 1) / n < p) :
    improperIntegral 0 (integrand a b m n p) =
      1 / Real.rpow b p *
        improperIntegral 0
          (fun x =>
            Real.rpow
                (b * Real.rpow x n /
                  (a + b * Real.rpow x n)) p *
              Real.rpow x (m - n * p)) := by
  change improperIntegral 0 (integrand a b m n p) =
    1 / Real.rpow b p *
      improperIntegral 0 (alternateIntegrand a b m n p)
  rw [source_improper_eq_setIntegral a b m n p ha hb hn hq hqp,
    alternate_improper_eq_setIntegral a b m n p ha hb hn hq hqp,
    ← MeasureTheory.integral_const_mul]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  exact (alternate_scaled_eq_source ha hb hx).symm

theorem gap4 (a b m n p : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hn : 0 < n)
    (hq : 0 < (m + 1) / n) (hqp : (m + 1) / n < p) :
    improperIntegral 0 (integrand a b m n p) =
      Real.rpow a (-p) / n *
        Real.rpow (a / b) ((m + 1) / n) *
          ∫ t in (0 : ℝ)..1,
            Real.rpow t ((m + 1) / n - 1) *
              Real.rpow (1 - t) (p - (m + 1) / n - 1) := by
  rw [source_improper_eq_setIntegral a b m n p ha hb hn hq hqp,
    integral_integrand_eq_scaled_reduced a b m n p hn,
    reduced_integral_eq_scaled_canonical
      a b ((m + 1) / n) p ha hb,
    canonical_integral_eq_betaFunction,
    ← betaFn_eq_betaFunctionSet]
  unfold betaFn
  ring

theorem gap5 (a b m n p : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hn : 0 < n)
    (hq : 0 < (m + 1) / n) (hqp : (m + 1) / n < p) :
    improperIntegral 0 (integrand a b m n p) =
      Real.rpow a (-p) / n *
        Real.rpow (a / b) ((m + 1) / n) *
          betaFn ((m + 1) / n) (p - (m + 1) / n) := by
  simpa only [betaFn] using gap4 a b m n p ha hb hn hq hqp

theorem gap6 (m n p : ℝ) (hn : 0 < n) :
    0 < (m + 1) / n ∧ 0 < p - (m + 1) / n ↔
      0 < (m + 1) / n ∧ (m + 1) / n < p := by
  constructor <;> rintro ⟨hq, hp⟩
  · exact ⟨hq, sub_pos.mp hp⟩
  · exact ⟨hq, sub_pos.mpr hp⟩

end

end ProofGap.Exercise3853
