import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace ProofGap.Exercise3849

noncomputable section

open MeasureTheory Set
open scoped Interval

def betaFn (x y : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1,
    Real.rpow t (x - 1) * Real.rpow (1 - t) (y - 1)

def nthRootIntegrand (n : ℕ) (x : ℝ) : ℝ :=
  1 / Real.rpow (1 - x ^ n) (1 / (n : ℝ))

private def betaKernel (u v t : ℝ) : ℝ :=
  Real.rpow t (u - 1) * Real.rpow (1 - t) (v - 1)

private def rpowIntegrand (m x : ℝ) : ℝ :=
  1 / Real.rpow (1 - Real.rpow x m) (1 / m)

private theorem beta_power_core
    {m x : ℝ} (hm : 0 < m) (hx : x ∈ Ioo (0 : ℝ) 1) :
    Real.rpow x (m - 1) *
        betaKernel (1 / m) (1 - 1 / m) (Real.rpow x m) =
      rpowIntegrand m x := by
  have hx0 : 0 < x := hx.1
  have hxm1 : Real.rpow x m < 1 :=
    Real.rpow_lt_one hx0.le hx.2 hm
  have hbase : 0 < 1 - Real.rpow x m := sub_pos.mpr hxm1
  unfold betaKernel rpowIntegrand
  simp only [Real.rpow_eq_pow]
  rw [← Real.rpow_mul hx0.le m (1 / m - 1)]
  have hexp : (m - 1) + m * (1 / m - 1) = 0 := by
    field_simp [hm.ne']
    ring
  calc
    x ^ (m - 1) *
          (x ^ (m * (1 / m - 1)) *
            (1 - x ^ m) ^ (1 - 1 / m - 1)) =
        (x ^ (m - 1) * x ^ (m * (1 / m - 1))) *
          (1 - x ^ m) ^ (1 - 1 / m - 1) := by ring
    _ = x ^ ((m - 1) + m * (1 / m - 1)) *
          (1 - x ^ m) ^ (1 - 1 / m - 1) := by
      congr 1
      exact (Real.rpow_add hx0 _ _).symm
    _ = (1 - x ^ m) ^ (-(1 / m)) := by
      rw [hexp, Real.rpow_zero, one_mul]
      congr 1
      ring
    _ = 1 / (1 - x ^ m) ^ (1 / m) := by
      simpa only [one_div] using
        (Real.rpow_neg hbase.le (1 / m))

private theorem power_image
    (m : ℝ) (hm : 0 < m) :
    (fun x : ℝ => Real.rpow x m) '' Ioo (0 : ℝ) 1 =
      Ioo (0 : ℝ) 1 := by
  ext t
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨Real.rpow_pos_of_pos hx.1 _,
      Real.rpow_lt_one hx.1.le hx.2 hm⟩
  · intro ht
    refine ⟨Real.rpow t (1 / m), ?_, ?_⟩
    · exact ⟨Real.rpow_pos_of_pos ht.1 _,
        Real.rpow_lt_one ht.1.le ht.2 (one_div_pos.mpr hm)⟩
    · simp only [Real.rpow_eq_pow]
      rw [← Real.rpow_mul ht.1.le, one_div_mul_cancel hm.ne',
        Real.rpow_one]

private theorem integral_rpowIntegrand_eq_betaKernel
    (m : ℝ) (hm : 0 < m) :
    (∫ x in Ioo (0 : ℝ) 1, rpowIntegrand m x ∂volume) =
      1 / m *
        ∫ t in Ioo (0 : ℝ) 1,
          betaKernel (1 / m) (1 - 1 / m) t ∂volume := by
  let f : ℝ → ℝ := fun x => Real.rpow x m
  let f' : ℝ → ℝ := fun x => m * Real.rpow x (m - 1)
  have hf' :
      ∀ x ∈ Ioo (0 : ℝ) 1,
        HasDerivWithinAt f (f' x) (Ioo (0 : ℝ) 1) x := by
    intro x hx
    dsimp [f, f']
    exact
      (Real.hasDerivAt_rpow_const (Or.inl hx.1.ne')).hasDerivWithinAt
  have hinj : Set.InjOn f (Ioo (0 : ℝ) 1) := by
    apply StrictMonoOn.injOn
    intro x hx y _ hxy
    dsimp [f]
    exact Real.rpow_lt_rpow hx.1.le hxy hm
  have hchange := integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioo hf' hinj
      (betaKernel (1 / m) (1 - 1 / m))
  rw [power_image m hm] at hchange
  have hright :
      (∫ x in Ioo (0 : ℝ) 1,
          |f' x| • betaKernel (1 / m) (1 - 1 / m) (f x)
            ∂volume) =
        ∫ x in Ioo (0 : ℝ) 1, m * rpowIntegrand m x ∂volume := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
    intro x hx
    dsimp [f, f']
    rw [abs_of_pos
      (mul_pos hm (Real.rpow_pos_of_pos hx.1 _))]
    rw [mul_assoc]
    have hcore := beta_power_core hm hx
    simp only [Real.rpow_eq_pow] at hcore
    rw [hcore]
  rw [hright, MeasureTheory.integral_const_mul] at hchange
  calc
    (∫ x in Ioo (0 : ℝ) 1, rpowIntegrand m x ∂volume) =
        1 / m *
          (m * ∫ x in Ioo (0 : ℝ) 1, rpowIntegrand m x ∂volume) := by
      field_simp [hm.ne']
    _ = 1 / m *
        ∫ t in Ioo (0 : ℝ) 1,
          betaKernel (1 / m) (1 - 1 / m) t ∂volume := by
      rw [← hchange]

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

private theorem integrand_eq_rpowIntegrand (n : ℕ) (x : ℝ) :
    nthRootIntegrand n x = rpowIntegrand (n : ℝ) x := by
  unfold nthRootIntegrand rpowIntegrand
  simp only [Real.rpow_eq_pow, Real.rpow_natCast]

theorem gap1 (n : ℕ) (hn : 1 < n) :
    (∫ x in (0 : ℝ)..1, nthRootIntegrand n x) =
      (1 / (n : ℝ)) *
        ∫ t in (0 : ℝ)..1,
          Real.rpow t ((1 - (n : ℝ)) / (n : ℝ)) *
            Real.rpow (1 - t) (-(1 / (n : ℝ))) := by
  have hnReal : 0 < (n : ℝ) := by
    exact_mod_cast (zero_lt_one.trans hn)
  rw [intervalIntegral.integral_of_le zero_le_one,
    MeasureTheory.integral_Ioc_eq_integral_Ioo]
  rw [intervalIntegral.integral_of_le zero_le_one,
    MeasureTheory.integral_Ioc_eq_integral_Ioo]
  calc
    (∫ x in Ioo (0 : ℝ) 1, nthRootIntegrand n x) =
        ∫ x in Ioo (0 : ℝ) 1,
          rpowIntegrand (n : ℝ) x := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
      intro x hx
      exact integrand_eq_rpowIntegrand n x
    _ = 1 / (n : ℝ) *
        ∫ t in Ioo (0 : ℝ) 1,
          betaKernel (1 / (n : ℝ))
            (1 - 1 / (n : ℝ)) t :=
      integral_rpowIntegrand_eq_betaKernel
        (n : ℝ) hnReal
    _ = _ := by
      congr 1
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
      intro t ht
      unfold betaKernel
      congr 1
      · field_simp [hnReal.ne']
      · congr 1
        ring

theorem gap2 (n : ℕ) (hn : 1 < n) :
    (1 / (n : ℝ)) *
        (∫ t in (0 : ℝ)..1,
          Real.rpow t ((1 - (n : ℝ)) / (n : ℝ)) *
            Real.rpow (1 - t) (-(1 / (n : ℝ)))) =
      (1 / (n : ℝ)) *
        betaFn (1 / (n : ℝ)) (((n : ℝ) - 1) / (n : ℝ)) := by
  have hn0 : (n : ℝ) ≠ 0 := by
    positivity
  unfold betaFn
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  congr 1
  · field_simp [hn0]
    ring

theorem gap3 (n : ℕ) (hn : 1 < n) :
    (1 / (n : ℝ)) *
        betaFn (1 / (n : ℝ)) (((n : ℝ) - 1) / (n : ℝ)) =
      (1 / (n : ℝ)) *
        (Real.Gamma (1 / (n : ℝ)) *
            Real.Gamma (((n : ℝ) - 1) / (n : ℝ)) /
          Real.Gamma 1) := by
  have hnReal : 0 < (n : ℝ) := by
    exact_mod_cast (zero_lt_one.trans hn)
  have hu : 0 < 1 / (n : ℝ) :=
    one_div_pos.mpr hnReal
  have hv : 0 < ((n : ℝ) - 1) / (n : ℝ) :=
    div_pos (sub_pos.mpr (by exact_mod_cast hn)) hnReal
  unfold betaFn
  rw [intervalIntegral.integral_of_le zero_le_one,
    MeasureTheory.integral_Ioc_eq_integral_Ioo]
  change
    1 / (n : ℝ) *
        (∫ t in Ioo (0 : ℝ) 1,
          betaKernel (1 / (n : ℝ))
            (((n : ℝ) - 1) / (n : ℝ)) t) =
      _
  rw [beta_setIntegral_eq_gamma hu hv]
  congr 4
  field_simp [hnReal.ne']
  ring

theorem gap4 (n : ℕ) (hn : 1 < n) :
    (1 / (n : ℝ)) *
        (Real.Gamma (1 / (n : ℝ)) *
            Real.Gamma (((n : ℝ) - 1) / (n : ℝ)) /
          Real.Gamma 1) =
      Real.pi /
        ((n : ℝ) * Real.sin (Real.pi / (n : ℝ))) := by
  have hnReal : 0 < (n : ℝ) := by
    exact_mod_cast (zero_lt_one.trans hn)
  rw [show ((n : ℝ) - 1) / (n : ℝ) =
      1 - 1 / (n : ℝ) by
        field_simp [hnReal.ne']
        ]
  rw [Real.Gamma_one, div_one,
    Real.Gamma_mul_Gamma_one_sub]
  rw [show Real.pi * (1 / (n : ℝ)) =
      Real.pi / (n : ℝ) by ring]
  ring

theorem gap5 (n : ℕ) (hn : 1 < n) :
    (∫ x in (0 : ℝ)..1, nthRootIntegrand n x) =
      Real.pi /
        ((n : ℝ) * Real.sin (Real.pi / (n : ℝ))) :=
  (gap1 n hn).trans
    ((gap2 n hn).trans ((gap3 n hn).trans (gap4 n hn)))

end

end ProofGap.Exercise3849
