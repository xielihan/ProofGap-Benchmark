import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace ProofGap.Exercise3852

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

def integrand (m n x : ℝ) : ℝ :=
  Real.rpow x (m - 1) / Real.rpow (1 + x) n

private def betaFunctionSet (u v : ℝ) : ℝ :=
  ∫ t in Ioo (0 : ℝ) 1,
    Real.rpow t (u - 1) * Real.rpow (1 - t) (v - 1)
      ∂MeasureTheory.volume

private def betaKernel (u v t : ℝ) : ℝ :=
  Real.rpow t (u - 1) * Real.rpow (1 - t) (v - 1)

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
        simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] using ht
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
          simpa [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)] using ht
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

private theorem transformed_integrand
    {m n t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (1 / (1 - t) ^ 2) *
        integrand m n (t / (1 - t)) =
      betaKernel m (n - m) t := by
  have ht0 : 0 < t := ht.1
  have ht1 : 0 < 1 - t := sub_pos.mpr ht.2
  have hfrac : 1 + t / (1 - t) = 1 / (1 - t) := by
    field_simp [ht1.ne']
    ring
  unfold integrand betaKernel
  simp only [Real.rpow_eq_pow]
  rw [Real.div_rpow ht0.le ht1.le, hfrac,
    Real.div_rpow zero_le_one ht1.le, Real.one_rpow]
  have hpow : (1 - t) ^ (2 : ℕ) = Real.rpow (1 - t) (2 : ℝ) :=
    (Real.rpow_natCast (1 - t) 2).symm
  rw [hpow]
  have hne1 : Real.rpow (1 - t) (m - 1) ≠ 0 :=
    (Real.rpow_pos_of_pos ht1 _).ne'
  have hne2 : Real.rpow (1 - t) n ≠ 0 :=
    (Real.rpow_pos_of_pos ht1 _).ne'
  have hne3 : Real.rpow (1 - t) (2 : ℝ) ≠ 0 :=
    (Real.rpow_pos_of_pos ht1 _).ne'
  field_simp [hne1, hne2, hne3]
  calc
    Real.rpow (1 - t) n =
        Real.rpow (1 - t) (((2 : ℝ) + (m - 1)) + ((n - m) - 1)) := by
      congr 1
      ring
    _ = Real.rpow (1 - t) ((2 : ℝ) + (m - 1)) *
        Real.rpow (1 - t) ((n - m) - 1) :=
      Real.rpow_add ht1 _ _
    _ = Real.rpow (1 - t) (2 : ℝ) *
        Real.rpow (1 - t) (m - 1) *
        Real.rpow (1 - t) ((n - m) - 1) := by
      congr 1
      exact Real.rpow_add ht1 _ _

private theorem integrableOn_integrand_iff_betaKernel (m n : ℝ) :
    IntegrableOn (integrand m n) (Ioi (0 : ℝ)) volume ↔
      IntegrableOn (betaKernel m (n - m)) (Ioo (0 : ℝ) 1) volume := by
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
      measurableSet_Ioo hf' hinj (integrand m n)
  rw [himage] at hchange
  rw [hchange]
  apply integrableOn_congr_fun
  · intro t ht
    dsimp [f, f']
    rw [abs_of_pos
      (one_div_pos.mpr (sq_pos_of_ne_zero (sub_ne_zero.mpr ht.2.ne')))]
    exact transformed_integrand ht
  · exact measurableSet_Ioo

private theorem integral_Ioi_eq_betaFunction (m n : ℝ) :
    (∫ x in Ioi (0 : ℝ), integrand m n x ∂volume) =
      betaFunctionSet m (n - m) := by
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
    measurableSet_Ioo hf' hinj (integrand m n)
  rw [himage] at hchange
  rw [hchange]
  unfold betaFunctionSet
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
  intro t ht
  dsimp [f, f']
  rw [abs_of_pos
    (one_div_pos.mpr (sq_pos_of_ne_zero (sub_ne_zero.mpr ht.2.ne')))]
  exact transformed_integrand ht

/-- Exercise 3852. -/

private theorem improperIntegral_eq_of_hasImproperIntegral
    {a : ℝ} {f : ℝ → ℝ} {L : ℝ}
    (hL : HasImproperIntegral a f L) :
    improperIntegral a f = L := by
  unfold improperIntegral
  have hs : {y : ℝ | HasImproperIntegral a f y} = {L} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro hy
      exact tendsto_nhds_unique hy hL
    · rintro rfl
      exact hL
  rw [hs]
  exact csInf_singleton L

theorem gap1 (m n : ℝ) (hm : 0 < m) (hmn : m < n) :
    improperIntegral 0 (integrand m n) =
      ∫ t in (0 : ℝ)..1,
        Real.rpow t (m - 1) *
          Real.rpow (1 - t) (n - m - 1) := by
  have hkernel :
      IntegrableOn (betaKernel m (n - m))
        (Ioo (0 : ℝ) 1) volume :=
    (betaKernel_integrable_iff m (n - m)).2
      ⟨hm, sub_pos.mpr hmn⟩
  have hint :
      IntegrableOn (integrand m n)
        (Ioi (0 : ℝ)) volume :=
    (integrableOn_integrand_iff_betaKernel m n).2 hkernel
  have himproper :
      improperIntegral 0 (integrand m n) =
        ∫ x in Ioi (0 : ℝ), integrand m n x := by
    apply improperIntegral_eq_of_hasImproperIntegral
    unfold HasImproperIntegral
    exact intervalIntegral_tendsto_integral_Ioi
      0 hint tendsto_id
  rw [himproper, integral_Ioi_eq_betaFunction]
  unfold betaFunctionSet
  rw [intervalIntegral.integral_of_le zero_le_one,
    MeasureTheory.integral_Ioc_eq_integral_Ioo]

theorem gap2 (m n : ℝ) (hm : 0 < m) (hmn : m < n) :
    (∫ t in (0 : ℝ)..1,
        Real.rpow t (m - 1) *
          Real.rpow (1 - t) (n - m - 1)) =
      betaFn m (n - m) := by
  unfold betaFn
  rfl

theorem gap3 (m n : ℝ) (hm : 0 < m) (hmn : m < n) :
    improperIntegral 0 (integrand m n) =
      betaFn m (n - m) :=
  (gap1 m n hm hmn).trans (gap2 m n hm hmn)

theorem gap4 (m n : ℝ) :
    0 < m ∧ 0 < n - m ↔ 0 < m ∧ m < n := by
  constructor <;> rintro ⟨hm, hmn⟩ <;>
    exact ⟨hm, by linarith⟩

end

end ProofGap.Exercise3852
