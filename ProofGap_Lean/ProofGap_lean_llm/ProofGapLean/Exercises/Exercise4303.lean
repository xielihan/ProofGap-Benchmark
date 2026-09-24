import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4303

noncomputable section

open MeasureTheory
open scoped Interval

private abbrev Point := ℝ × ℝ

def P (m x y : ℝ) : ℝ :=
  Real.exp x * Real.sin y - m * y

def Q (m x y : ℝ) : ℝ :=
  Real.exp x * Real.cos y - m

def pathIntegral
    (m : ℝ) (γ : ℝ → ℝ × ℝ) (c d : ℝ) : ℝ :=
  ∫ t in c..d,
    P m (γ t).1 (γ t).2 * deriv (fun s => (γ s).1) t +
      Q m (γ t).1 (γ t).2 * deriv (fun s => (γ s).2) t

def upperArc (a t : ℝ) : ℝ × ℝ :=
  (a / 2 * (1 + Real.cos t), a / 2 * Real.sin t)

def baseSegment (t : ℝ) : ℝ × ℝ := (t, 0)

def arcIntegral (a m : ℝ) : ℝ :=
  pathIntegral m (upperArc a) 0 Real.pi

def baseIntegral (a m : ℝ) : ℝ :=
  pathIntegral m baseSegment 0 a

def closedIntegral (a m : ℝ) : ℝ :=
  arcIntegral a m + baseIntegral a m

def halfDisk (a : ℝ) : Set (ℝ × ℝ) :=
  {z | z.1 ^ 2 + z.2 ^ 2 ≤ a * z.1 ∧ 0 ≤ z.2}

def areaIntegral (a m : ℝ) : ℝ :=
  ∫ _z in halfDisk a, m

private theorem base_value (a m : ℝ) :
    baseIntegral a m = 0 := by
  have hx (t : ℝ) :
      deriv (fun s => (baseSegment s).1) t = 1 := by
    simpa [baseSegment] using (hasDerivAt_id t).deriv
  have hy (t : ℝ) :
      deriv (fun s => (baseSegment s).2) t = 0 := by
    simpa [baseSegment] using (hasDerivAt_const t (0 : ℝ)).deriv
  unfold baseIntegral pathIntegral
  calc
    _ = ∫ _t in (0 : ℝ)..a, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      change
        P m t 0 *
              deriv (fun s : ℝ => s) t +
            Q m t 0 *
              deriv (fun _s : ℝ => (0 : ℝ)) t =
          0
      have h1 :
          deriv (fun s : ℝ => s) t = 1 := by
        simpa using (hasDerivAt_id t).deriv
      have h0 :
          deriv (fun _s : ℝ => (0 : ℝ)) t = 0 := by
        simpa using (hasDerivAt_const t (0 : ℝ)).deriv
      rw [h1, h0]
      simp [P, Q]
    _ = 0 := by simp

private theorem arc_value (a m : ℝ) :
    arcIntegral a m = Real.pi * m * a ^ 2 / 8 := by
  let F : ℝ → ℝ := fun t =>
    Real.exp (a / 2 * (1 + Real.cos t)) *
        Real.sin (a / 2 * Real.sin t) +
      m * a ^ 2 / 8 * t -
      m * a ^ 2 / 16 * Real.sin (2 * t) -
      m * a / 2 * Real.sin t
  have hx (t : ℝ) :
      HasDerivAt (fun s => (upperArc a s).1)
        (-a / 2 * Real.sin t) t := by
    convert
      ((Real.hasDerivAt_cos t).const_add 1).const_mul (a / 2)
        using 1 <;> ring
  have hy (t : ℝ) :
      HasDerivAt (fun s => (upperArc a s).2)
        (a / 2 * Real.cos t) t := by
    simpa [upperArc] using
      ((Real.hasDerivAt_sin t).const_mul (a / 2))
  have hF (t : ℝ) :
      HasDerivAt F
        (P m (upperArc a t).1 (upperArc a t).2 *
            deriv (fun s => (upperArc a s).1) t +
          Q m (upperArc a t).1 (upperArc a t).2 *
            deriv (fun s => (upperArc a s).2) t) t := by
    have hpot :
        HasDerivAt
          (fun s =>
            Real.exp ((upperArc a s).1) *
              Real.sin ((upperArc a s).2))
          (Real.exp ((upperArc a t).1) *
              (-a / 2 * Real.sin t) *
              Real.sin ((upperArc a t).2) +
            Real.exp ((upperArc a t).1) *
              (Real.cos ((upperArc a t).2) *
                (a / 2 * Real.cos t))) t := by
      convert
        ((Real.hasDerivAt_exp ((upperArc a t).1)).comp t (hx t)).mul
          ((Real.hasDerivAt_sin ((upperArc a t).2)).comp t (hy t))
        using 1 <;> ring
    have ht :
        HasDerivAt (fun s : ℝ => m * a ^ 2 / 8 * s)
          (m * a ^ 2 / 8) t := by
      simpa using (hasDerivAt_id t).const_mul (m * a ^ 2 / 8)
    have hsin2 :
        HasDerivAt
          (fun s : ℝ => m * a ^ 2 / 16 * Real.sin (2 * s))
          (m * a ^ 2 / 8 * Real.cos (2 * t)) t := by
      have hi :
          HasDerivAt (fun s : ℝ => 2 * s) 2 t := by
        simpa using (hasDerivAt_id t).const_mul 2
      convert
        ((Real.hasDerivAt_sin (2 * t)).comp t hi).const_mul
          (m * a ^ 2 / 16)
        using 1 <;> ring
    have hsin :
        HasDerivAt
          (fun s : ℝ => m * a / 2 * Real.sin s)
          (m * a / 2 * Real.cos t) t := by
      convert (Real.hasDerivAt_sin t).const_mul (m * a / 2)
        using 1 <;> ring
    have hraw := ((hpot.add ht).sub hsin2).sub hsin
    convert hraw using 1
    dsimp [F]
    simp only [upperArc]
    have hxd := (hx t).deriv
    have hyd := (hy t).deriv
    simp only [upperArc] at hxd hyd
    rw [hxd, hyd]
    simp only [P, Q]
    rw [Real.cos_two_mul]
    have hcos :
        Real.cos t ^ 2 = 1 - Real.sin t ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq t]
    rw [hcos]
    ring
  have hcont :
      Continuous (fun t =>
        P m (upperArc a t).1 (upperArc a t).2 *
            deriv (fun s => (upperArc a s).1) t +
          Q m (upperArc a t).1 (upperArc a t).2 *
            deriv (fun s => (upperArc a s).2) t) := by
    simp_rw [(hx _).deriv, (hy _).deriv]
    simp only [P, Q, upperArc]
    fun_prop
  unfold arcIntegral pathIntegral
  calc
    _ = F Real.pi - F 0 := by
      exact intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t ht => hF t)
        (hcont.intervalIntegrable _ _)
    _ = Real.pi * m * a ^ 2 / 8 := by
      dsimp [F]
      rw [Real.sin_pi, Real.sin_zero]
      norm_num
      ring

private def halfUnitDisk : Set Point :=
  {p | p.1 ^ 2 + p.2 ^ 2 ≤ 1 ∧ 0 ≤ p.2}

private theorem angular_upper :
    (∫ θ in Set.Ioo (-Real.pi) Real.pi,
      (Set.Ici (0 : ℝ)).indicator
        (fun _θ : ℝ => (1 : ℝ)) θ) = Real.pi := by
  rw [setIntegral_indicator measurableSet_Ici]
  have hinter :
      Set.Ioo (-Real.pi) Real.pi ∩ Set.Ici 0 =
        Set.Ico 0 Real.pi := by
    ext θ
    simp only [Set.mem_inter_iff, Set.mem_Ioo,
      Set.mem_Ici, Set.mem_Ico]
    constructor
    · rintro ⟨⟨hneg, hpi⟩, hzero⟩
      exact ⟨hzero, hpi⟩
    · rintro ⟨hzero, hpi⟩
      exact
        ⟨⟨lt_of_lt_of_le (neg_lt_zero.mpr Real.pi_pos)
            hzero, hpi⟩, hzero⟩
  rw [hinter, integral_Ico_eq_integral_Ioo,
    ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le Real.pi_nonneg]
  simp

private theorem radial_half (c : ℝ) :
    (∫ r in (0 : ℝ)..1, r * c) = c / 2 := by
  have hd (r : ℝ) :
      HasDerivAt (fun x : ℝ => x ^ 2 / 2) r r := by
    convert ((hasDerivAt_id r).pow 2).div_const 2 using 1 <;>
      simp
  have hi :
      (∫ r in (0 : ℝ)..1, r) = (1 : ℝ) / 2 := by
    simpa using
      (intervalIntegral.integral_eq_sub_of_hasDerivAt
        (a := (0 : ℝ)) (b := (1 : ℝ))
        (fun r hr => hd r)
        (continuous_id.intervalIntegrable (0 : ℝ) 1))
  rw [intervalIntegral.integral_mul_const, hi]
  ring

private theorem halfUnitDisk_const (c : ℝ) :
    (∫ p in halfUnitDisk, c) = c * Real.pi / 2 := by
  have hdisk : MeasurableSet halfUnitDisk := by
    unfold halfUnitDisk
    exact
      (isClosed_le
        ((continuous_fst.pow 2).add (continuous_snd.pow 2))
        continuous_const).inter
        (isClosed_le continuous_const continuous_snd)
        |>.measurableSet
  have hp := integral_comp_polarCoord_symm
    (halfUnitDisk.indicator (fun _p : Point => c))
  rw [integral_indicator hdisk] at hp
  have hpoint (p : ℝ × ℝ) (hp : p ∈ polarCoord.target) :
      p.1 • halfUnitDisk.indicator (fun _q : Point => c)
          (polarCoord.symm p) =
        (Set.Iic (1 : ℝ)).indicator
            (fun r : ℝ => r * c) p.1 *
          (Set.Ici (0 : ℝ)).indicator
            (fun _θ : ℝ => (1 : ℝ)) p.2 := by
    rcases p with ⟨r, θ⟩
    have hr : 0 < r := hp.1
    have hθneg : -Real.pi < θ := hp.2.1
    have hθpi : θ < Real.pi := hp.2.2
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
    have hsin :
        0 ≤ r * Real.sin θ ↔ 0 ≤ θ := by
      constructor
      · intro hrs
        by_contra hn
        have hθ0 : θ < 0 := lt_of_not_ge hn
        have hs0 :
            Real.sin θ < 0 :=
          Real.sin_neg_of_neg_of_neg_pi_lt hθ0 hθneg
        exact (not_lt_of_ge hrs) (mul_neg_of_pos_of_neg hr hs0)
      · intro hθ0
        exact
          mul_nonneg hr.le
            (Real.sin_nonneg_of_nonneg_of_le_pi
              hθ0 hθpi.le)
    have hmem :
        polarCoord.symm (r, θ) ∈ halfUnitDisk ↔
          r ≤ 1 ∧ 0 ≤ θ := by
      rw [polarCoord_symm_apply]
      simp only [halfUnitDisk, Set.mem_setOf_eq]
      rw [htrig, hsin]
      have hsq : r ^ 2 ≤ 1 ↔ r ≤ 1 := by
        simpa using sq_le_sq₀ hr.le zero_le_one
      exact and_congr hsq Iff.rfl
    simp only [Set.indicator, hmem, Set.mem_Iic,
      Set.mem_Ici, smul_eq_mul]
    by_cases hr1 : r ≤ 1 <;>
      by_cases hθ0 : 0 ≤ θ <;> simp [hr1, hθ0]
  have hprod :
      (∫ p in polarCoord.target,
        p.1 • halfUnitDisk.indicator
          (fun _q : Point => c) (polarCoord.symm p)) =
        (∫ r in Set.Ioi (0 : ℝ),
          (Set.Iic (1 : ℝ)).indicator
            (fun r : ℝ => r * c) r) *
        ∫ θ in Set.Ioo (-Real.pi) Real.pi,
          (Set.Ici (0 : ℝ)).indicator
            (fun _θ : ℝ => (1 : ℝ)) θ := by
    rw [polarCoord_target]
    calc
      _ = ∫ p in
          Set.Ioi (0 : ℝ) ×ˢ
              Set.Ioo (-Real.pi) Real.pi,
          (Set.Iic (1 : ℝ)).indicator
              (fun r : ℝ => r * c) p.1 *
            (Set.Ici (0 : ℝ)).indicator
              (fun _θ : ℝ => (1 : ℝ)) p.2 := by
        apply setIntegral_congr_fun
          (measurableSet_Ioi.prod measurableSet_Ioo)
        intro p hp'
        exact hpoint p hp'
      _ = _ := by
        exact setIntegral_prod_mul
          ((Set.Iic (1 : ℝ)).indicator
            (fun r : ℝ => r * c))
          ((Set.Ici (0 : ℝ)).indicator
            (fun _θ : ℝ => (1 : ℝ)))
          (Set.Ioi (0 : ℝ))
          (Set.Ioo (-Real.pi) Real.pi)
  have hrad :
      (∫ r in Set.Ioi (0 : ℝ),
        (Set.Iic (1 : ℝ)).indicator
          (fun r : ℝ => r * c) r) =
        ∫ r in (0 : ℝ)..1, r * c := by
    rw [setIntegral_indicator measurableSet_Iic]
    have hinter :
        Set.Ioi (0 : ℝ) ∩ Set.Iic 1 =
          Set.Ioc (0 : ℝ) 1 := by
      ext r
      simp
    rw [hinter,
      intervalIntegral.integral_of_le zero_le_one]
  rw [hprod, hrad, angular_upper, radial_half] at hp
  rw [← hp]
  ring

private def scaleCLM (r : ℝ) : Point →L[ℝ] Point :=
  (ContinuousLinearMap.lsmul ℝ ℝ r).prodMap
    (ContinuousLinearMap.lsmul ℝ ℝ r)

private def halfDiskMap (a : ℝ) (p : Point) : Point :=
  (a / 2, 0) + scaleCLM (a / 2) p

private theorem halfDiskMap_apply (a : ℝ) (p : Point) :
    halfDiskMap a p =
      (a / 2 + a / 2 * p.1, a / 2 * p.2) := by
  apply Prod.ext <;>
    simp [halfDiskMap, scaleCLM]

private theorem halfDisk_image (a : ℝ) (ha : 0 < a) :
    halfDiskMap a '' halfUnitDisk = halfDisk a := by
  let r : ℝ := a / 2
  have hr : 0 < r := by
    dsimp [r]
    linarith
  have har : a = 2 * r := by
    dsimp [r]
    ring
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    rw [halfDiskMap_apply]
    change
      (r + r * q.1) ^ 2 + (r * q.2) ^ 2 ≤
          a * (r + r * q.1) ∧
        0 ≤ r * q.2
    change q.1 ^ 2 + q.2 ^ 2 ≤ 1 ∧ 0 ≤ q.2 at hq
    rw [har]
    constructor
    · have hmul :
          r ^ 2 *
              (q.1 ^ 2 + q.2 ^ 2 - 1) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos
          (sq_nonneg r) (sub_nonpos.mpr hq.1)
      nlinarith
    · exact mul_nonneg hr.le hq.2
  · intro hp
    refine
      ⟨((p.1 - r) / r, p.2 / r), ?_, ?_⟩
    · change
        ((p.1 - r) / r) ^ 2 +
              (p.2 / r) ^ 2 ≤ 1 ∧
            0 ≤ p.2 / r
      change
        p.1 ^ 2 + p.2 ^ 2 ≤ a * p.1 ∧
          0 ≤ p.2 at hp
      rw [har] at hp
      constructor
      · field_simp [ne_of_gt hr]
        nlinarith
      · exact div_nonneg hp.2 hr.le
    · apply Prod.ext
      · rw [halfDiskMap_apply]
        change
          r + r * ((p.1 - r) / r) = p.1
        field_simp [ne_of_gt hr]
        ring
      · rw [halfDiskMap_apply]
        change r * (p.2 / r) = p.2
        field_simp [ne_of_gt hr]

private theorem halfDiskMap_inj (a : ℝ) (ha : 0 < a) :
    Function.Injective (halfDiskMap a) := by
  let r : ℝ := a / 2
  have hr : 0 < r := by
    dsimp [r]
    linarith
  intro p q h
  rw [halfDiskMap_apply, halfDiskMap_apply] at h
  apply Prod.ext
  · have h1 := congrArg Prod.fst h
    change r + r * p.1 = r + r * q.1 at h1
    have hm : r * p.1 = r * q.1 := by linarith
    exact mul_left_cancel₀ (ne_of_gt hr) hm
  · have h2 := congrArg Prod.snd h
    change r * p.2 = r * q.2 at h2
    exact mul_left_cancel₀ (ne_of_gt hr) h2

private theorem halfDisk_change (a c : ℝ) (ha : 0 < a) :
    (∫ p in halfDisk a, c) =
      ∫ p in halfUnitDisk, (a / 2) ^ 2 * c := by
  have hdisk : MeasurableSet halfUnitDisk := by
    unfold halfUnitDisk
    exact
      (isClosed_le
        ((continuous_fst.pow 2).add (continuous_snd.pow 2))
        continuous_const).inter
        (isClosed_le continuous_const continuous_snd)
        |>.measurableSet
  have hdet :
      (scaleCLM (a / 2)).det = (a / 2) ^ 2 := by
    unfold scaleCLM ContinuousLinearMap.det
    change
      (LinearMap.prodMap
        (LinearMap.mulLeft ℝ (a / 2))
        (LinearMap.mulLeft ℝ (a / 2))).det =
          (a / 2) ^ 2
    rw [LinearMap.det_prodMap, LinearMap.det_mulLeft]
    ring
  have hderiv (p : Point) :
      HasFDerivAt (halfDiskMap a)
        (scaleCLM (a / 2)) p := by
    unfold halfDiskMap
    exact
      (scaleCLM (a / 2)).hasFDerivAt.const_add
        (a / 2, 0)
  have hcv :=
    integral_image_eq_integral_abs_det_fderiv_smul
      (volume : Measure Point) hdisk
      (fun p hp => (hderiv p).hasFDerivWithinAt)
      (fun x hx y hy h => halfDiskMap_inj a ha h)
      (fun _p : Point => c)
  rw [halfDisk_image a ha] at hcv
  have hr : 0 < a / 2 := by linarith
  simpa [hdet, abs_of_pos (sq_pos_of_pos hr),
    smul_eq_mul] using hcv

private theorem area_value (a m : ℝ) (ha : 0 < a) :
    areaIntegral a m = Real.pi * m * a ^ 2 / 8 := by
  unfold areaIntegral
  rw [halfDisk_change a m ha, halfUnitDisk_const]
  ring

theorem gap1 (a m : ℝ) :
    baseIntegral a m = 0 := by
  exact base_value a m

theorem gap2 (a m : ℝ) :
    closedIntegral a m = arcIntegral a m := by
  unfold closedIntegral
  rw [base_value]
  ring

theorem gap3 (a m : ℝ) (ha : 0 < a) :
    closedIntegral a m = areaIntegral a m := by
  calc
    closedIntegral a m = arcIntegral a m := gap2 a m
    _ = Real.pi * m * a ^ 2 / 8 := arc_value a m
    _ = areaIntegral a m := (area_value a m ha).symm

theorem gap4 (a m : ℝ) (ha : 0 < a) :
    areaIntegral a m = Real.pi * m * a ^ 2 / 8 := by
  exact area_value a m ha

theorem gap5 (a m : ℝ) (ha : 0 < a) :
    closedIntegral a m = Real.pi * m * a ^ 2 / 8 := by
  rw [gap2]
  exact arc_value a m

theorem gap6 (a m : ℝ) (ha : 0 < a) :
    arcIntegral a m = Real.pi * m * a ^ 2 / 8 := by
  exact arc_value a m

end

end ProofGap.Exercise4303
