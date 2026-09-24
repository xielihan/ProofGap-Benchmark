import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4298

noncomputable section

open MeasureTheory
open scoped Interval

abbrev Point := ℝ × ℝ

def P (p : Point) : ℝ :=
  -p.1 ^ 2 * p.2

def Q (p : Point) : ℝ :=
  p.1 * p.2 ^ 2

def circle (a t : ℝ) : Point :=
  (a * Real.cos t, a * Real.sin t)

def lineIntegral (a : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..2 * Real.pi,
    P (circle a t) * deriv (fun s => (circle a s).1) t +
      Q (circle a t) * deriv (fun s => (circle a s).2) t

def disk (a : ℝ) : Set Point :=
  {p | p.1 ^ 2 + p.2 ^ 2 ≤ a ^ 2}

def areaIntegral (a : ℝ) : ℝ :=
  ∫ p in disk a, p.1 ^ 2 + p.2 ^ 2

def polarIntegral (a : ℝ) : ℝ :=
  ∫ φ in (0 : ℝ)..2 * Real.pi, ∫ r in (0 : ℝ)..a, r ^ 3

def directTrigonometricIntegral (a : ℝ) : ℝ :=
  a ^ 4 * ∫ t in (0 : ℝ)..2 * Real.pi,
    Real.cos t ^ 2 * Real.sin t ^ 2 +
      Real.cos t ^ 2 * Real.sin t ^ 2

private theorem angular_full :
    (∫ θ in Set.Ioo (-Real.pi) Real.pi, (1 : ℝ)) =
      2 * Real.pi := by
  calc
    _ = ∫ θ in Set.Ioc (-Real.pi) Real.pi, (1 : ℝ) :=
      (integral_Ioc_eq_integral_Ioo
        (f := fun _ : ℝ => (1 : ℝ))).symm
    _ = ∫ θ in -Real.pi..Real.pi, (1 : ℝ) := by
      rw [intervalIntegral.integral_of_le]
      exact neg_le_self Real.pi_nonneg
    _ = 2 * Real.pi := by
      simp only [intervalIntegral.integral_const, smul_eq_mul]
      ring

private theorem radial_cube (a : ℝ) :
    (∫ r in (0 : ℝ)..a, r ^ 3) = a ^ 4 / 4 := by
  have hd (r : ℝ) :
      HasDerivAt (fun x : ℝ => x ^ 4 / 4) (r ^ 3) r := by
    convert ((hasDerivAt_id r).pow 4).div_const 4 using 1 <;>
      simp
  simpa using
    (intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := (0 : ℝ)) (b := a)
      (fun r hr => hd r)
      ((continuous_id.pow 3).intervalIntegrable (0 : ℝ) a))

private theorem area_value (a : ℝ) (ha : 0 < a) :
    areaIntegral a = Real.pi * a ^ 4 / 2 := by
  have hdisk : MeasurableSet (disk a) := by
    unfold disk
    exact
      (isClosed_le
        ((continuous_fst.pow 2).add (continuous_snd.pow 2))
        continuous_const).measurableSet
  have hp := integral_comp_polarCoord_symm
    ((disk a).indicator
      (fun p : Point => p.1 ^ 2 + p.2 ^ 2))
  rw [integral_indicator hdisk] at hp
  have hpoint (p : ℝ × ℝ) (hp : p ∈ polarCoord.target) :
      p.1 • (disk a).indicator
          (fun q : Point => q.1 ^ 2 + q.2 ^ 2)
          (polarCoord.symm p) =
        (Set.Iic a).indicator (fun r : ℝ => r ^ 3) p.1 *
          (1 : ℝ) := by
    rcases p with ⟨r, θ⟩
    have hr : 0 < r := hp.1
    have htrig :
        (r * Real.cos θ) ^ 2 +
            (r * Real.sin θ) ^ 2 = r ^ 2 := by
      calc
        _ = r ^ 2 *
            (Real.cos θ ^ 2 + Real.sin θ ^ 2) := by
          ring
        _ = r ^ 2 := by
          rw [Real.cos_sq_add_sin_sq]
          ring
    have hmem :
        polarCoord.symm (r, θ) ∈ disk a ↔ r ≤ a := by
      rw [polarCoord_symm_apply]
      simp only [disk, Set.mem_setOf_eq]
      rw [htrig]
      exact sq_le_sq₀ hr.le ha.le
    simp only [Set.indicator, hmem, Set.mem_Iic, smul_eq_mul]
    by_cases hra : r ≤ a
    · simp only [hra, if_true, mul_one]
      rw [polarCoord_symm_apply]
      rw [htrig]
      ring
    · simp [hra]
  have hprod :
      (∫ p in polarCoord.target,
        p.1 • (disk a).indicator
          (fun q : Point => q.1 ^ 2 + q.2 ^ 2)
          (polarCoord.symm p)) =
        (∫ r in Set.Ioi (0 : ℝ),
          (Set.Iic a).indicator (fun r : ℝ => r ^ 3) r) *
        ∫ θ in Set.Ioo (-Real.pi) Real.pi, (1 : ℝ) := by
    rw [polarCoord_target]
    calc
      _ = ∫ p in
          Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-Real.pi) Real.pi,
          (Set.Iic a).indicator (fun r : ℝ => r ^ 3) p.1 *
            (1 : ℝ) := by
        apply setIntegral_congr_fun
          (measurableSet_Ioi.prod measurableSet_Ioo)
        intro p hp'
        exact hpoint p hp'
      _ = _ := by
        exact setIntegral_prod_mul
          ((Set.Iic a).indicator (fun r : ℝ => r ^ 3))
          (fun _θ : ℝ => (1 : ℝ))
          (Set.Ioi (0 : ℝ))
          (Set.Ioo (-Real.pi) Real.pi)
  have hrad :
      (∫ r in Set.Ioi (0 : ℝ),
        (Set.Iic a).indicator (fun r : ℝ => r ^ 3) r) =
        ∫ r in (0 : ℝ)..a, r ^ 3 := by
    rw [setIntegral_indicator measurableSet_Iic]
    have hinter :
        Set.Ioi (0 : ℝ) ∩ Set.Iic a =
          Set.Ioc (0 : ℝ) a := by
      ext r
      simp
    rw [hinter, intervalIntegral.integral_of_le ha.le]
  rw [hprod, hrad, angular_full, radial_cube] at hp
  unfold areaIntegral
  rw [← hp]
  ring

private theorem line_eq_direct (a : ℝ) :
    lineIntegral a = directTrigonometricIntegral a := by
  have hx (t : ℝ) :
      deriv (fun s => (circle a s).1) t =
        -a * Real.sin t := by
    simpa [circle] using
      ((Real.hasDerivAt_cos t).const_mul a).deriv
  have hy (t : ℝ) :
      deriv (fun s => (circle a s).2) t =
        a * Real.cos t := by
    simpa [circle] using
      ((Real.hasDerivAt_sin t).const_mul a).deriv
  unfold lineIntegral directTrigonometricIntegral
  calc
    (∫ t in (0 : ℝ)..2 * Real.pi,
      P (circle a t) *
          deriv (fun s => (circle a s).1) t +
        Q (circle a t) *
          deriv (fun s => (circle a s).2) t) =
        ∫ t in (0 : ℝ)..2 * Real.pi,
          a ^ 4 *
            (Real.cos t ^ 2 * Real.sin t ^ 2 +
              Real.cos t ^ 2 * Real.sin t ^ 2) := by
      apply intervalIntegral.integral_congr
      intro t ht
      change
        P (circle a t) *
              deriv (fun s => (circle a s).1) t +
            Q (circle a t) *
              deriv (fun s => (circle a s).2) t =
          a ^ 4 *
            (Real.cos t ^ 2 * Real.sin t ^ 2 +
              Real.cos t ^ 2 * Real.sin t ^ 2)
      rw [hx, hy]
      simp only [P, Q, circle]
      ring
    _ = a ^ 4 * ∫ t in (0 : ℝ)..2 * Real.pi,
        Real.cos t ^ 2 * Real.sin t ^ 2 +
          Real.cos t ^ 2 * Real.sin t ^ 2 := by
      rw [intervalIntegral.integral_const_mul]

private theorem direct_eq_half_sin (a : ℝ) :
    directTrigonometricIntegral a =
      a ^ 4 / 2 *
        ∫ t in (0 : ℝ)..2 * Real.pi,
          Real.sin (2 * t) ^ 2 := by
  have hi :
      (∫ t in (0 : ℝ)..2 * Real.pi,
        Real.cos t ^ 2 * Real.sin t ^ 2 +
          Real.cos t ^ 2 * Real.sin t ^ 2) =
        (1 / 2 : ℝ) *
          ∫ t in (0 : ℝ)..2 * Real.pi,
            Real.sin (2 * t) ^ 2 := by
    calc
      _ = ∫ t in (0 : ℝ)..2 * Real.pi,
          (1 / 2 : ℝ) * Real.sin (2 * t) ^ 2 := by
        apply intervalIntegral.integral_congr
        intro t ht
        change
          Real.cos t ^ 2 * Real.sin t ^ 2 +
              Real.cos t ^ 2 * Real.sin t ^ 2 =
            (1 / 2 : ℝ) * Real.sin (2 * t) ^ 2
        rw [Real.sin_two_mul]
        ring
      _ = (1 / 2 : ℝ) *
          ∫ t in (0 : ℝ)..2 * Real.pi,
            Real.sin (2 * t) ^ 2 := by
        rw [intervalIntegral.integral_const_mul]
  unfold directTrigonometricIntegral
  rw [hi]
  ring

private theorem sin_sq_integral :
    (∫ t in (0 : ℝ)..2 * Real.pi,
      Real.sin (2 * t) ^ 2) = Real.pi := by
  let F : ℝ → ℝ := fun t =>
    t / 2 - Real.sin (4 * t) / 8
  have hF (t : ℝ) :
      HasDerivAt F (Real.sin (2 * t) ^ 2) t := by
    have hinner :
        HasDerivAt (fun x : ℝ => 4 * x) 4 t := by
      simpa using (hasDerivAt_id t).const_mul 4
    have hs :=
      (Real.hasDerivAt_sin (4 * t)).comp
        (h := fun x : ℝ => 4 * x) t hinner
    have hraw :=
      (hasDerivAt_id t).div_const 2 |>.sub
        (hs.div_const 8)
    convert hraw using 1
    have htrig := Real.sin_sq_add_cos_sq (2 * t)
    rw [show 4 * t = 2 * (2 * t) by ring,
      Real.cos_two_mul]
    nlinarith
  have hcont :
      Continuous (fun t : ℝ => Real.sin (2 * t) ^ 2) := by
    fun_prop
  calc
    (∫ t in (0 : ℝ)..2 * Real.pi,
      Real.sin (2 * t) ^ 2) =
        F (2 * Real.pi) - F 0 := by
      exact intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t ht => hF t)
        (hcont.intervalIntegrable _ _)
    _ = Real.pi := by
      dsimp [F]
      rw [show 4 * (2 * Real.pi) =
          (8 : ℕ) * Real.pi by ring,
        Real.sin_nat_mul_pi]
      norm_num

private theorem line_value (a : ℝ) :
    lineIntegral a = Real.pi * a ^ 4 / 2 := by
  rw [line_eq_direct, direct_eq_half_sin,
    sin_sq_integral]
  ring

private theorem polar_value (a : ℝ) :
    polarIntegral a = Real.pi * a ^ 4 / 2 := by
  unfold polarIntegral
  simp_rw [radial_cube]
  rw [intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul]
  ring

theorem gap1 (a : ℝ) (ha : 0 < a) :
    lineIntegral a = areaIntegral a := by
  calc
    lineIntegral a = Real.pi * a ^ 4 / 2 :=
      line_value a
    _ = areaIntegral a := (area_value a ha).symm

theorem gap2 (a : ℝ) (ha : 0 < a) :
    areaIntegral a = polarIntegral a := by
  calc
    areaIntegral a = Real.pi * a ^ 4 / 2 :=
      area_value a ha
    _ = polarIntegral a := (polar_value a).symm

theorem gap3 (a : ℝ) (ha : 0 < a) :
    polarIntegral a = Real.pi * a ^ 4 / 2 := by
  exact polar_value a

theorem gap4 (a : ℝ) (ha : 0 < a) :
    lineIntegral a = Real.pi * a ^ 4 / 2 := by
  exact line_value a

theorem gap5 (a : ℝ) :
    lineIntegral a = directTrigonometricIntegral a := by
  exact line_eq_direct a

theorem gap6 (a : ℝ) :
    directTrigonometricIntegral a =
      a ^ 4 / 2 *
        ∫ t in (0 : ℝ)..2 * Real.pi,
          Real.sin (2 * t) ^ 2 := by
  exact direct_eq_half_sin a

theorem gap7 (a : ℝ) :
    a ^ 4 / 2 *
        (∫ t in (0 : ℝ)..2 * Real.pi,
          Real.sin (2 * t) ^ 2) =
      Real.pi * a ^ 4 / 2 := by
  rw [sin_sq_integral]
  ring

theorem gap8 (a : ℝ) :
    lineIntegral a = Real.pi * a ^ 4 / 2 := by
  exact line_value a

end

end ProofGap.Exercise4298
