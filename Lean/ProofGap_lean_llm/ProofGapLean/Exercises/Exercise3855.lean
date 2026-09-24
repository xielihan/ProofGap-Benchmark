import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace ProofGap.Exercise3855

noncomputable section

open MeasureTheory Set
open scoped Interval

def betaFn (x y : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1,
    Real.rpow t (x - 1) * Real.rpow (1 - t) (y - 1)

def rootIntegrand (m n x : ℝ) : ℝ :=
  1 / Real.rpow (1 - Real.rpow x m) (1 / n)

private def betaFunctionSet (u v : ℝ) : ℝ :=
  ∫ t in Ioo (0 : ℝ) 1,
    Real.rpow t (u - 1) * Real.rpow (1 - t) (v - 1)
      ∂MeasureTheory.volume

private def betaKernel (u v t : ℝ) : ℝ :=
  Real.rpow t (u - 1) * Real.rpow (1 - t) (v - 1)
private theorem beta_power_core
    {m n x : ℝ} (hm : 0 < m)
    (hx : x ∈ Ioo (0 : ℝ) 1) :
    Real.rpow x (m - 1) *
        betaKernel (1 / m) (1 - 1 / n) (Real.rpow x m) =
      rootIntegrand m n x := by
  have hx0 : 0 < x := hx.1
  have hxm0 : 0 < Real.rpow x m := Real.rpow_pos_of_pos hx0 _
  have hxm1 : Real.rpow x m < 1 :=
    Real.rpow_lt_one hx0.le hx.2 hm
  have hbase : 0 < 1 - Real.rpow x m := sub_pos.mpr hxm1
  unfold betaKernel rootIntegrand
  simp only [Real.rpow_eq_pow]
  rw [← Real.rpow_mul hx0.le m (1 / m - 1)]
  have hexp : (m - 1) + m * (1 / m - 1) = 0 := by
    field_simp [hm.ne']
    ring
  calc
    x ^ (m - 1) *
          (x ^ (m * (1 / m - 1)) *
            (1 - x ^ m) ^ (1 - 1 / n - 1)) =
        (x ^ (m - 1) * x ^ (m * (1 / m - 1))) *
          (1 - x ^ m) ^ (1 - 1 / n - 1) := by ring
    _ = x ^ ((m - 1) + m * (1 / m - 1)) *
          (1 - x ^ m) ^ (1 - 1 / n - 1) := by
      congr 1
      exact (Real.rpow_add hx0 _ _).symm
    _ = (1 - x ^ m) ^ (-(1 / n)) := by
      rw [hexp, Real.rpow_zero, one_mul]
      congr 1
      ring
    _ = 1 / (1 - x ^ m) ^ (1 / n) := by
      simpa only [one_div] using
        (Real.rpow_neg hbase.le (1 / n))

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

private theorem integral_integrand_eq_betaFunction
    (m n : ℝ) (hm : 0 < m) :
    (∫ x in Ioo (0 : ℝ) 1, rootIntegrand m n x ∂volume) =
      1 / m * betaFunctionSet (1 / m) (1 - 1 / n) := by
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
      (betaKernel (1 / m) (1 - 1 / n))
  rw [power_image m hm] at hchange
  have hright :
      (∫ x in Ioo (0 : ℝ) 1,
          |f' x| • betaKernel (1 / m) (1 - 1 / n) (f x)
            ∂volume) =
        ∫ x in Ioo (0 : ℝ) 1, m * rootIntegrand m n x ∂volume := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
    intro x hx
    dsimp [f, f']
    rw [abs_of_pos
      (mul_pos hm (Real.rpow_pos_of_pos hx.1 _))]
    rw [mul_assoc]
    have hcore := beta_power_core (n := n) hm hx
    simp only [Real.rpow_eq_pow] at hcore
    rw [hcore]
  rw [hright, MeasureTheory.integral_const_mul] at hchange
  unfold betaFunctionSet
  calc
    (∫ x in Ioo (0 : ℝ) 1, rootIntegrand m n x ∂volume) =
        1 / m *
          (m * ∫ x in Ioo (0 : ℝ) 1, rootIntegrand m n x ∂volume) := by
      field_simp [hm.ne']
    _ = 1 / m *
        ∫ t in Ioo (0 : ℝ) 1,
          Real.rpow t (1 / m - 1) *
            Real.rpow (1 - t) (1 - 1 / n - 1) ∂volume := by
      rw [← hchange]
      rfl

private theorem one_sub_inv_pos_iff (n : ℝ) (hn : n ≠ 0) :
    0 < 1 - 1 / n ↔ n < 0 ∨ 1 < n := by
  rcases lt_or_gt_of_ne hn with hnneg | hnpos
  · constructor
    · intro _
      exact Or.inl hnneg
    · intro _
      have hinv : 1 / n < 0 := one_div_neg.mpr hnneg
      linarith
  · constructor
    · intro h
      right
      have hinv : 1 / n < 1 := by linarith
      exact
        (one_div_lt_one_div hnpos zero_lt_one).mp
          (by simpa using hinv)
    · intro h
      rcases h with hneg | hone
      · linarith
      · have hinv : 1 / n < 1 :=
          by
            simpa using
              (one_div_lt_one_div hnpos zero_lt_one).mpr hone
        linarith

theorem gap1 (m n : ℝ)
    (hm : 0 < m) (hn : n < 0 ∨ 1 < n) :
    (∫ x in (0 : ℝ)..1, rootIntegrand m n x) =
      1 / m *
        ∫ t in (0 : ℝ)..1,
          Real.rpow t (1 / m - 1) *
            Real.rpow (1 - t) (-(1 / n)) := by
  rw [intervalIntegral.integral_of_le zero_le_one,
    MeasureTheory.integral_Ioc_eq_integral_Ioo]
  rw [integral_integrand_eq_betaFunction m n hm]
  unfold betaFunctionSet
  rw [intervalIntegral.integral_of_le zero_le_one,
    MeasureTheory.integral_Ioc_eq_integral_Ioo]
  congr 1
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
  intro t ht
  congr 1
  ring

theorem gap2 (m n : ℝ)
    (hm : 0 < m) (hn : n < 0 ∨ 1 < n) :
    1 / m *
        (∫ t in (0 : ℝ)..1,
          Real.rpow t (1 / m - 1) *
            Real.rpow (1 - t) (-(1 / n))) =
      1 / m * betaFn (1 / m) (1 - 1 / n) := by
  unfold betaFn
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  congr 1
  ring

theorem gap3 (m n : ℝ)
    (hm : 0 < m) (hn : n < 0 ∨ 1 < n) :
    (∫ x in (0 : ℝ)..1, rootIntegrand m n x) =
      1 / m * betaFn (1 / m) (1 - 1 / n) :=
  (gap1 m n hm hn).trans (gap2 m n hm hn)

theorem gap4 (n : ℝ) (hn : n ≠ 0) :
    0 < 1 - 1 / n ↔ n < 0 ∨ 1 < n :=
  one_sub_inv_pos_iff n hn

end

end ProofGap.Exercise3855
