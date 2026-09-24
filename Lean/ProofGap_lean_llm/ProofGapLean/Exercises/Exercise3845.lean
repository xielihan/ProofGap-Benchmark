import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace ProofGap.Exercise3845

noncomputable section

open Filter MeasureTheory Set
open scoped Interval

def HasImproperIntegral (a : ℝ) (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Tendsto (fun b : ℝ => ∫ x in a..b, f x) atTop (nhds L)

def improperIntegral (a : ℝ) (f : ℝ → ℝ) : ℝ :=
  sInf {L : ℝ | HasImproperIntegral a f L}

def xOfT (t : ℝ) : ℝ :=
  t / (1 - t)

def betaFn (x y : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1,
    Real.rpow t (x - 1) * Real.rpow (1 - t) (y - 1)

def integrand (x : ℝ) : ℝ :=
  Real.rpow x (1 / 4 : ℝ) / (1 + x) ^ 2

private theorem ofReal_beta_setIntegral
    {u v : ℝ} :
    (((∫ t in Ioo (0 : ℝ) 1,
        Real.rpow t (u - 1) * Real.rpow (1 - t) (v - 1)
          ∂MeasureTheory.volume) : ℝ) : ℂ) =
      Complex.betaIntegral (u : ℂ) (v : ℂ) := by
  rw [Complex.betaIntegral, intervalIntegral.integral_of_le (by norm_num),
    MeasureTheory.integral_Ioc_eq_integral_Ioo]
  calc
    (((∫ t in Ioo (0 : ℝ) 1,
        Real.rpow t (u - 1) * Real.rpow (1 - t) (v - 1)) : ℝ) : ℂ) =
        ∫ t in Ioo (0 : ℝ) 1,
          ((Real.rpow t (u - 1) * Real.rpow (1 - t) (v - 1) : ℝ) : ℂ) :=
      integral_ofReal.symm
    _ = _ := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
      intro t ht
      dsimp only
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
    (∫ t in Ioo (0 : ℝ) 1,
        Real.rpow t (u - 1) * Real.rpow (1 - t) (v - 1)
          ∂MeasureTheory.volume) =
      Real.Gamma u * Real.Gamma v / Real.Gamma (u + v) := by
  apply Complex.ofReal_injective
  rw [ofReal_beta_setIntegral,
    Complex.betaIntegral_eq_Gamma_mul_div (u := (u : ℂ)) (v := (v : ℂ))
      (by simpa) (by simpa)]
  simp only [← Complex.Gamma_ofReal, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_add]

private theorem integral_Ioi_eq_integral_Ioo_div
    (g : ℝ → ℝ) :
    (∫ x in Ioi (0 : ℝ), g x ∂MeasureTheory.volume) =
      ∫ t in Ioo (0 : ℝ) 1,
        (1 / (1 - t) ^ 2) * g (t / (1 - t))
          ∂MeasureTheory.volume := by
  let f : ℝ → ℝ := fun t => t / (1 - t)
  let f' : ℝ → ℝ := fun t => 1 / (1 - t) ^ 2
  have hf' : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivWithinAt f (f' t) (Ioo 0 1) t := by
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
  have h := integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioo hf' hinj g
  rw [himage] at h
  rw [h]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
  intro t ht
  dsimp [f, f']
  rw [abs_of_pos]
  exact one_div_pos.mpr (sq_pos_of_ne_zero (sub_ne_zero.mpr ht.2.ne'))

private theorem beta_substitution_integrand
    {a b t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    (1 / (1 - t) ^ 2) *
        ((t / (1 - t)).rpow (a - 1) /
          (1 + t / (1 - t)).rpow (a + b)) =
      t.rpow (a - 1) * (1 - t).rpow (b - 1) := by
  have ht0 : 0 < t := ht.1
  have ht1 : 0 < 1 - t := sub_pos.mpr ht.2
  have hfrac : 1 + t / (1 - t) = 1 / (1 - t) := by
    field_simp [ht1.ne']
    ring
  simp only [Real.rpow_eq_pow]
  rw [Real.div_rpow ht0.le ht1.le, hfrac,
    Real.div_rpow zero_le_one ht1.le, Real.one_rpow]
  have hpow : (1 - t) ^ (2 : ℕ) = (1 - t) ^ (2 : ℝ) :=
    (Real.rpow_natCast (1 - t) 2).symm
  rw [hpow]
  have hne1 : (1 - t) ^ (a - 1) ≠ 0 :=
    (Real.rpow_pos_of_pos ht1 _).ne'
  have hne2 : (1 - t) ^ (a + b) ≠ 0 :=
    (Real.rpow_pos_of_pos ht1 _).ne'
  have hne3 : (1 - t) ^ (2 : ℝ) ≠ 0 :=
    (Real.rpow_pos_of_pos ht1 _).ne'
  field_simp [hne1, hne2, hne3]
  calc
    (1 - t) ^ (a + b) =
        (1 - t) ^ (((2 : ℝ) + (a - 1)) + (b - 1)) := by
      congr 1
      ring
    _ = (1 - t) ^ ((2 : ℝ) + (a - 1)) * (1 - t) ^ (b - 1) :=
      Real.rpow_add ht1 _ _
    _ = (1 - t) ^ (2 : ℝ) * (1 - t) ^ (a - 1) *
        (1 - t) ^ (b - 1) := by rw [Real.rpow_add ht1]

private theorem integral_rpow_div_one_add_rpow_eq_gamma
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ x in Ioi (0 : ℝ),
        x.rpow (a - 1) / (1 + x).rpow (a + b)
          ∂MeasureTheory.volume) =
      Real.Gamma a * Real.Gamma b / Real.Gamma (a + b) := by
  rw [integral_Ioi_eq_integral_Ioo_div]
  calc
    (∫ t in Ioo (0 : ℝ) 1,
        (1 / (1 - t) ^ 2) *
          ((t / (1 - t)).rpow (a - 1) /
            (1 + t / (1 - t)).rpow (a + b))
          ∂MeasureTheory.volume) =
        ∫ t in Ioo (0 : ℝ) 1,
          t.rpow (a - 1) * (1 - t).rpow (b - 1)
            ∂MeasureTheory.volume := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
      intro t ht
      exact beta_substitution_integrand ht
    _ = _ := beta_setIntegral_eq_gamma ha hb

private theorem betaKernel_integrableOn
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn
      (fun t : ℝ => Real.rpow t (a - 1) *
        Real.rpow (1 - t) (b - 1))
      (Ioo (0 : ℝ) 1) := by
  let f : ℝ → ℂ := fun t =>
    (t : ℂ) ^ ((a : ℂ) - 1) *
      (1 - (t : ℂ)) ^ ((b : ℂ) - 1)
  have hfInterval : IntervalIntegrable f volume 0 1 := by
    exact Complex.betaIntegral_convergent
      (by simpa using ha) (by simpa using hb)
  have hf : IntegrableOn f (Ioo (0 : ℝ) 1) := by
    exact hfInterval.def'.mono_set (by
      rw [uIoc_of_le zero_le_one]
      exact Ioo_subset_Ioc_self)
  have hfre : IntegrableOn (fun t => (f t).re) (Ioo (0 : ℝ) 1) := by
    exact hf.re
  refine hfre.congr_fun ?_ measurableSet_Ioo
  intro t ht
  have hta :
      (t : ℂ) ^ ((a : ℂ) - 1) =
        (Real.rpow t (a - 1) : ℂ) := by
    rw [show (a : ℂ) - 1 = ((a - 1 : ℝ) : ℂ) by push_cast; rfl]
    exact (Complex.ofReal_cpow ht.1.le (a - 1)).symm
  have htb :
      (1 - (t : ℂ)) ^ ((b : ℂ) - 1) =
        (Real.rpow (1 - t) (b - 1) : ℂ) := by
    rw [show (1 : ℂ) - (t : ℂ) = ((1 - t : ℝ) : ℂ) by push_cast; rfl]
    rw [show (b : ℂ) - 1 = ((b - 1 : ℝ) : ℂ) by push_cast; rfl]
    exact (Complex.ofReal_cpow (sub_nonneg.mpr ht.2.le) (b - 1)).symm
  dsimp [f]
  rw [hta, htb]
  simp

private theorem general_integrableOn_Ioi
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntegrableOn
      (fun x : ℝ =>
        x.rpow (a - 1) / (1 + x).rpow (a + b))
      (Ioi (0 : ℝ)) := by
  let f : ℝ → ℝ := fun t => t / (1 - t)
  let f' : ℝ → ℝ := fun t => 1 / (1 - t) ^ 2
  have hf' :
      ∀ t ∈ Ioo (0 : ℝ) 1,
        HasDerivWithinAt f (f' t) (Ioo 0 1) t := by
    intro t ht
    apply HasDerivAt.hasDerivWithinAt
    dsimp [f, f']
    have hdenDeriv :
        HasDerivAt (fun y : ℝ => 1 - y) (-1) t := by
      simpa only [Pi.sub_apply, Pi.one_apply, id_eq,
        zero_sub] using
        (hasDerivAt_const t 1).sub (hasDerivAt_id t)
    have hne : 1 - t ≠ 0 :=
      (sub_pos.mpr ht.2).ne'
    convert (hasDerivAt_id t).div hdenDeriv hne using 1
    simp only [id_eq]
    field_simp [hne]
    ring
  have hinj : Set.InjOn f (Ioo (0 : ℝ) 1) := by
    intro u hu v hv huv
    dsimp [f] at huv
    have hu0 : 1 - u ≠ 0 :=
      (sub_pos.mpr hu.2).ne'
    have hv0 : 1 - v ≠ 0 :=
      (sub_pos.mpr hv.2).ne'
    field_simp [hu0, hv0] at huv
    linarith
  have himage : f '' Ioo (0 : ℝ) 1 = Ioi 0 := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact div_pos ht.1 (sub_pos.mpr ht.2)
    · intro hx
      have hxpos : 0 < x := hx
      have hden : 0 < 1 + x := by linarith
      refine ⟨x / (1 + x), ?_, ?_⟩
      · exact ⟨div_pos hx hden,
          (div_lt_one hden).2 (by linarith)⟩
      · dsimp [f]
        field_simp [hden.ne']
        ring
  have hchange :=
    integrableOn_image_iff_integrableOn_abs_deriv_smul
      measurableSet_Ioo hf' hinj
        (fun x : ℝ =>
          x.rpow (a - 1) /
            (1 + x).rpow (a + b))
  rw [himage] at hchange
  rw [hchange]
  refine (betaKernel_integrableOn ha hb).congr_fun ?_
    measurableSet_Ioo
  intro t ht
  dsimp [f, f']
  rw [abs_of_pos
    (one_div_pos.mpr
      (sq_pos_of_ne_zero
        (sub_ne_zero.mpr ht.2.ne')))]
  exact (beta_substitution_integrand ht).symm

private theorem source_integrand_eq_general
    {x : ℝ} (hx : 0 < x) :
    integrand x =
      x.rpow ((5 / 4 : ℝ) - 1) /
        (1 + x).rpow ((5 / 4 : ℝ) + 3 / 4) := by
  unfold integrand
  norm_num

private theorem source_integrableOn_Ioi :
    IntegrableOn integrand (Ioi (0 : ℝ)) := by
  have h :=
    general_integrableOn_Ioi
      (a := (5 / 4 : ℝ)) (b := (3 / 4 : ℝ))
      (by norm_num) (by norm_num)
  exact h.congr_fun
    (fun x hx =>
      (source_integrand_eq_general hx).symm)
    measurableSet_Ioi

private theorem source_setIntegral_eq_beta :
    (∫ x in Ioi (0 : ℝ), integrand x) =
      ∫ t in Ioo (0 : ℝ) 1,
        Real.rpow t (1 / 4 : ℝ) *
          Real.rpow (1 - t) (-1 / 4 : ℝ) := by
  calc
    (∫ x in Ioi (0 : ℝ), integrand x) =
        ∫ x in Ioi (0 : ℝ),
          x.rpow ((5 / 4 : ℝ) - 1) /
            (1 + x).rpow ((5 / 4 : ℝ) + 3 / 4) := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      exact source_integrand_eq_general hx
    _ = _ := by
      rw [integral_Ioi_eq_integral_Ioo_div]
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
      intro t ht
      convert
        beta_substitution_integrand
          (a := (5 / 4 : ℝ)) (b := (3 / 4 : ℝ)) ht using 1 <;>
        norm_num

private theorem betaFn_eq_gamma
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    betaFn a b =
      Real.Gamma a * Real.Gamma b /
        Real.Gamma (a + b) := by
  unfold betaFn
  rw [intervalIntegral.integral_of_le zero_le_one,
    MeasureTheory.integral_Ioc_eq_integral_Ioo]
  exact beta_setIntegral_eq_gamma ha hb

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


theorem gap1 (x t : ℝ) (hx : x ≠ -1)
    (ht : t = x / (1 + x)) :
    x = xOfT t := by
  unfold xOfT
  rw [ht]
  have hden : 1 + x ≠ 0 := by
    intro h
    apply hx
    linarith
  field_simp [hden]
  ring

theorem gap2 (t : ℝ) (ht : t ≠ 1) :
    HasDerivAt xOfT (1 / (1 - t) ^ 2) t := by
  unfold xOfT
  have hdenDeriv :
      HasDerivAt (fun y : ℝ => 1 - y) (-1) t := by
    simpa only [Pi.sub_apply, Pi.one_apply, id_eq,
      zero_sub] using
      (hasDerivAt_const t 1).sub (hasDerivAt_id t)
  have hne : 1 - t ≠ 0 :=
    sub_ne_zero.mpr ht.symm
  convert (hasDerivAt_id t).div hdenDeriv hne using 1
  simp only [id_eq]
  field_simp [hne]
  ring

theorem gap3 :
    improperIntegral 0 integrand =
      ∫ t in (0 : ℝ)..1,
        Real.rpow t (1 / 4 : ℝ) *
          Real.rpow (1 - t) (-1 / 4 : ℝ) := by
  have himproper :
      improperIntegral 0 integrand =
        ∫ x in Ioi (0 : ℝ), integrand x := by
    apply improperIntegral_eq_of_hasImproperIntegral
    unfold HasImproperIntegral
    exact intervalIntegral_tendsto_integral_Ioi
      0 source_integrableOn_Ioi tendsto_id
  rw [himproper, source_setIntegral_eq_beta]
  rw [intervalIntegral.integral_of_le zero_le_one,
    MeasureTheory.integral_Ioc_eq_integral_Ioo]

theorem gap4 :
    (∫ t in (0 : ℝ)..1,
        Real.rpow t (1 / 4 : ℝ) *
          Real.rpow (1 - t) (-1 / 4 : ℝ)) =
      betaFn (5 / 4) (3 / 4) := by
  unfold betaFn
  norm_num

theorem gap5 :
    betaFn (5 / 4) (3 / 4) =
      Real.Gamma (5 / 4) * Real.Gamma (3 / 4) /
        Real.Gamma 2 := by
  convert
    betaFn_eq_gamma
      (a := (5 / 4 : ℝ)) (b := (3 / 4 : ℝ))
      (by norm_num) (by norm_num) using 1 <;>
    norm_num

theorem gap6 :
    Real.Gamma (5 / 4) * Real.Gamma (3 / 4) /
        Real.Gamma 2 =
      (1 / 4 : ℝ) * Real.Gamma (1 / 4) *
        Real.Gamma (3 / 4) := by
  have hadd :=
    Real.Gamma_add_one (s := (1 / 4 : ℝ))
      (by norm_num)
  norm_num at hadd
  rw [hadd]
  norm_num [Real.Gamma_nat_eq_factorial]

theorem gap7 :
    improperIntegral 0 integrand =
      (1 / 4 : ℝ) * Real.Gamma (1 / 4) *
        Real.Gamma (3 / 4) :=
  gap3.trans (gap4.trans (gap5.trans gap6))

theorem gap8 :
    improperIntegral 0 integrand =
      (1 / 4 : ℝ) *
        (Real.pi / Real.sin (Real.pi / 4)) := by
  rw [gap7]
  have href :=
    Real.Gamma_mul_Gamma_one_sub (1 / 4 : ℝ)
  norm_num at href
  rw [show Real.pi * (1 / 4 : ℝ) =
    Real.pi / 4 by ring] at href
  calc
    (1 / 4 : ℝ) * Real.Gamma (1 / 4) *
        Real.Gamma (3 / 4) =
      (1 / 4 : ℝ) *
        (Real.Gamma (1 / 4) *
          Real.Gamma (3 / 4)) := by ring
    _ = _ := by rw [href]

theorem gap9 :
    (1 / 4 : ℝ) * (Real.pi / Real.sin (Real.pi / 4)) =
      Real.pi / (2 * Real.sqrt 2) := by
  rw [Real.sin_pi_div_four]
  have hsqrt : Real.sqrt (2 : ℝ) ≠ 0 := by
    positivity
  field_simp [hsqrt]
  ring

theorem gap10 :
    improperIntegral 0 integrand =
      Real.pi / (2 * Real.sqrt 2) :=
  gap8.trans gap9

end

end ProofGap.Exercise3845
