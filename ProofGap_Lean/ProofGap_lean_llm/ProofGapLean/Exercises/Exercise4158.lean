import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Sign
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Measurability
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4158

noncomputable section

open MeasureTheory
open scoped Interval

abbrev Point3 := ℝ × ℝ × ℝ

def ball (R : ℝ) : Set Point3 :=
  {p | p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 ≤ R ^ 2}

def density (R M : ℝ) : ℝ :=
  3 * M / (4 * Real.pi * R ^ 3)

def distanceSquared (a : ℝ) (p : Point3) : ℝ :=
  p.1 ^ 2 + p.2.1 ^ 2 + (p.2.2 - a) ^ 2

def forceX (R a k M m : ℝ) : ℝ :=
  k * density R M * m *
    ∫ p in ball R,
      p.1 / Real.rpow (distanceSquared a p) ((3 : ℝ) / 2)

def forceY (R a k M m : ℝ) : ℝ :=
  k * density R M * m *
    ∫ p in ball R,
      p.2.1 / Real.rpow (distanceSquared a p) ((3 : ℝ) / 2)

def forceZ (R a k M m : ℝ) : ℝ :=
  k * density R M * m *
    ∫ p in ball R,
      (p.2.2 - a) /
        Real.rpow (distanceSquared a p) ((3 : ℝ) / 2)

private def flipX : Point3 ≃ᵐ Point3 where
  toFun p := (-p.1, p.2)
  invFun p := (-p.1, p.2)
  left_inv := by
    rintro ⟨x, yz⟩
    simp
  right_inv := by
    rintro ⟨x, yz⟩
    simp
  measurable_toFun := measurable_fst.neg.prodMk measurable_snd
  measurable_invFun := measurable_fst.neg.prodMk measurable_snd

private def flipY : Point3 ≃ᵐ Point3 where
  toFun p := (p.1, (-p.2.1, p.2.2))
  invFun p := (p.1, (-p.2.1, p.2.2))
  left_inv := by
    rintro ⟨x, y, z⟩
    simp
  right_inv := by
    rintro ⟨x, y, z⟩
    simp
  measurable_toFun :=
    measurable_fst.prodMk
      ((measurable_fst.comp measurable_snd).neg.prodMk
        (measurable_snd.comp measurable_snd))
  measurable_invFun :=
    measurable_fst.prodMk
      ((measurable_fst.comp measurable_snd).neg.prodMk
        (measurable_snd.comp measurable_snd))

private theorem flipX_measurePreserving :
    MeasurePreserving flipX := by
  have hneg : MeasurePreserving (fun x : ℝ => -x) := by
    refine ⟨measurable_id.neg, ?_⟩
    simpa using
      (Real.map_volume_mul_left (a := (-1 : ℝ)) (by norm_num))
  rw [Measure.volume_eq_prod]
  simpa [flipX, Prod.map] using
    hneg.prod
      (MeasurePreserving.id (volume : Measure (ℝ × ℝ)))

private theorem flipY_measurePreserving :
    MeasurePreserving flipY := by
  have hneg : MeasurePreserving (fun x : ℝ => -x) := by
    refine ⟨measurable_id.neg, ?_⟩
    simpa using
      (Real.map_volume_mul_left (a := (-1 : ℝ)) (by norm_num))
  have hpair : MeasurePreserving
      (fun q : ℝ × ℝ => (-q.1, q.2)) := by
    rw [Measure.volume_eq_prod]
    simpa [Prod.map] using
      hneg.prod
        (MeasurePreserving.id (volume : Measure ℝ))
  rw [Measure.volume_eq_prod]
  simpa [flipY, Prod.map] using
    (MeasurePreserving.id (volume : Measure ℝ)).prod hpair

private theorem ball_measurable (R : ℝ) :
    MeasurableSet (ball R) := by
  unfold ball
  measurability

private theorem flipX_mem_ball (R : ℝ) (p : Point3) :
    flipX p ∈ ball R ↔ p ∈ ball R := by
  rcases p with ⟨x, y, z⟩
  change
    (-x) ^ 2 + y ^ 2 + z ^ 2 ≤ R ^ 2 ↔
      x ^ 2 + y ^ 2 + z ^ 2 ≤ R ^ 2
  ring_nf

private theorem flipY_mem_ball (R : ℝ) (p : Point3) :
    flipY p ∈ ball R ↔ p ∈ ball R := by
  rcases p with ⟨x, y, z⟩
  change
    x ^ 2 + (-y) ^ 2 + z ^ 2 ≤ R ^ 2 ↔
      x ^ 2 + y ^ 2 + z ^ 2 ≤ R ^ 2
  ring_nf

private theorem distanceSquared_flipX (a : ℝ) (p : Point3) :
    distanceSquared a (flipX p) = distanceSquared a p := by
  rcases p with ⟨x, y, z⟩
  change
    (-x) ^ 2 + y ^ 2 + (z - a) ^ 2 =
      x ^ 2 + y ^ 2 + (z - a) ^ 2
  ring

private theorem distanceSquared_flipY (a : ℝ) (p : Point3) :
    distanceSquared a (flipY p) = distanceSquared a p := by
  rcases p with ⟨x, y, z⟩
  change
    x ^ 2 + (-y) ^ 2 + (z - a) ^ 2 =
      x ^ 2 + y ^ 2 + (z - a) ^ 2
  ring

theorem gap1 (R a k M m : ℝ) (hR : 0 < R) (ha : 0 ≤ a) :
    forceX R a k M m = 0 := by
  unfold forceX
  rw [← integral_indicator (ball_measurable R)]
  let G : Point3 → ℝ := fun p =>
    p.1 / Real.rpow (distanceSquared a p) ((3 : ℝ) / 2)
  change k * density R M * m *
    (∫ p : Point3, (ball R).indicator G p) = 0
  have hodd :
      (fun p : Point3 => (ball R).indicator G (flipX p)) =
        fun p => -((ball R).indicator G p) := by
    funext p
    by_cases hp : p ∈ ball R
    · have hfp : flipX p ∈ ball R :=
        (flipX_mem_ball R p).mpr hp
      rw [Set.indicator_of_mem hfp, Set.indicator_of_mem hp]
      dsimp [G]
      rw [distanceSquared_flipX]
      change
        (-p.1) /
            Real.rpow (distanceSquared a p) ((3 : ℝ) / 2) =
          -(p.1 /
            Real.rpow (distanceSquared a p) ((3 : ℝ) / 2))
      ring
    · have hfp : flipX p ∉ ball R := by
        intro hfp'
        exact hp ((flipX_mem_ball R p).mp hfp')
      rw [Set.indicator_of_notMem hfp,
        Set.indicator_of_notMem hp, neg_zero]
  have hchange :=
    flipX_measurePreserving.integral_comp'
      ((ball R).indicator G)
  rw [hodd, integral_neg] at hchange
  rw [show (∫ p : Point3, (ball R).indicator G p) = 0 by
    linarith]
  ring

theorem gap2 (R a k M m : ℝ) (hR : 0 < R) (ha : 0 ≤ a) :
    forceY R a k M m = 0 := by
  unfold forceY
  rw [← integral_indicator (ball_measurable R)]
  let G : Point3 → ℝ := fun p =>
    p.2.1 / Real.rpow (distanceSquared a p) ((3 : ℝ) / 2)
  change k * density R M * m *
    (∫ p : Point3, (ball R).indicator G p) = 0
  have hodd :
      (fun p : Point3 => (ball R).indicator G (flipY p)) =
        fun p => -((ball R).indicator G p) := by
    funext p
    by_cases hp : p ∈ ball R
    · have hfp : flipY p ∈ ball R :=
        (flipY_mem_ball R p).mpr hp
      rw [Set.indicator_of_mem hfp, Set.indicator_of_mem hp]
      dsimp [G]
      rw [distanceSquared_flipY]
      change
        (-p.2.1) /
            Real.rpow (distanceSquared a p) ((3 : ℝ) / 2) =
          -(p.2.1 /
            Real.rpow (distanceSquared a p) ((3 : ℝ) / 2))
      ring
    · have hfp : flipY p ∉ ball R := by
        intro hfp'
        exact hp ((flipY_mem_ball R p).mp hfp')
      rw [Set.indicator_of_notMem hfp,
        Set.indicator_of_notMem hp, neg_zero]
  have hchange :=
    flipY_measurePreserving.integral_comp'
      ((ball R).indicator G)
  rw [hodd, integral_neg] at hchange
  rw [show (∫ p : Point3, (ball R).indicator G p) = 0 by
    linarith]
  ring

theorem gap3 (R a k M m : ℝ) (hR : 0 < R) (ha : 0 ≤ a) :
    forceZ R a k M m =
      k * density R M * m *
        ∫ p in ball R,
          (p.2.2 - a) /
            Real.rpow (distanceSquared a p) ((3 : ℝ) / 2) := by
  rfl

private theorem rpow_three_halves_eq
    (u : ℝ) (hu : 0 < u) :
    Real.rpow u ((3 : ℝ) / 2) = u * Real.sqrt u := by
  calc
    Real.rpow u ((3 : ℝ) / 2) =
        Real.rpow u (1 + (1 / 2 : ℝ)) := by
      congr 1
      norm_num
    _ = Real.rpow u 1 * Real.rpow u (1 / 2 : ℝ) :=
      Real.rpow_add hu 1 (1 / 2 : ℝ)
    _ = u * Real.rpow u (1 / 2 : ℝ) :=
      congrArg (fun v : ℝ => v * Real.rpow u (1 / 2 : ℝ))
        (Real.rpow_one u)
    _ = u * Real.sqrt u :=
      congrArg (fun v : ℝ => u * v)
        (Real.sqrt_eq_rpow u).symm

private theorem radial_kernel_integral (s d : ℝ) (hs : 0 < s) :
    (∫ r in (0 : ℝ)..s,
      r * d /
        Real.rpow (r ^ 2 + d ^ 2) ((3 : ℝ) / 2)) =
      Real.sign d - d / Real.sqrt (s ^ 2 + d ^ 2) := by
  by_cases hd : d = 0
  · simp [hd]
  let F : ℝ → ℝ := fun r =>
    -d / Real.sqrt (r ^ 2 + d ^ 2)
  have hderiv : ∀ r ∈ Set.uIcc (0 : ℝ) s,
      HasDerivAt F
        (r * d /
          Real.rpow (r ^ 2 + d ^ 2) ((3 : ℝ) / 2)) r := by
    intro r _
    have hu : 0 < r ^ 2 + d ^ 2 := by
      nlinarith [sq_nonneg r, sq_pos_of_ne_zero hd]
    have hinner :
        HasDerivAt (fun x : ℝ => x ^ 2 + d ^ 2) (2 * r) r := by
      convert ((hasDerivAt_id r).pow 2).add_const (d ^ 2) using 1 <;>
        simp only [id_eq] <;> ring
    have hsqrt :
        HasDerivAt (fun x : ℝ => Real.sqrt (x ^ 2 + d ^ 2))
          (1 / (2 * Real.sqrt (r ^ 2 + d ^ 2)) * (2 * r)) r := by
      simpa only [Function.comp_apply] using
        (Real.hasDerivAt_sqrt hu.ne').comp r hinner
    have hsqrtne : Real.sqrt (r ^ 2 + d ^ 2) ≠ 0 :=
      Real.sqrt_ne_zero'.mpr hu
    have hsquare :
        Real.sqrt (r ^ 2 + d ^ 2) ^ 2 = r ^ 2 + d ^ 2 :=
      Real.sq_sqrt hu.le
    have hrpow :
        Real.rpow (r ^ 2 + d ^ 2) ((3 : ℝ) / 2) =
          (r ^ 2 + d ^ 2) *
            Real.sqrt (r ^ 2 + d ^ 2) :=
      rpow_three_halves_eq _ hu
    dsimp [F]
    convert (hasDerivAt_const r (-d)).div hsqrt hsqrtne using 1
    change
      r * d /
          Real.rpow (r ^ 2 + d ^ 2) ((3 : ℝ) / 2) =
        (0 * Real.sqrt (r ^ 2 + d ^ 2) -
          -d *
            (1 / (2 * Real.sqrt (r ^ 2 + d ^ 2)) * (2 * r))) /
              Real.sqrt (r ^ 2 + d ^ 2) ^ 2
    rw [hrpow]
    field_simp [hsqrtne]
    rw [hsquare]
    ring
  have hcont : Continuous
      (fun r : ℝ =>
        r * d /
          Real.rpow (r ^ 2 + d ^ 2) ((3 : ℝ) / 2)) := by
    have hbase : Continuous (fun r : ℝ => r ^ 2 + d ^ 2) :=
      (continuous_id.pow 2).add continuous_const
    have hden : Continuous
        (fun r : ℝ =>
          Real.rpow (r ^ 2 + d ^ 2) ((3 : ℝ) / 2)) := by
      have heq :
          (fun r : ℝ =>
            Real.rpow (r ^ 2 + d ^ 2) ((3 : ℝ) / 2)) =
            fun r =>
              (r ^ 2 + d ^ 2) *
                Real.sqrt (r ^ 2 + d ^ 2) := by
        funext r
        apply rpow_three_halves_eq
        nlinarith [sq_nonneg r, sq_pos_of_ne_zero hd]
      rw [heq]
      exact hbase.mul (Real.continuous_sqrt.comp hbase)
    apply Continuous.div
    · fun_prop
    · exact hden
    · intro r
      exact ne_of_gt (Real.rpow_pos_of_pos
        (by nlinarith [sq_nonneg r, sq_pos_of_ne_zero hd]) _)
  have hFTC :
      (∫ r in (0 : ℝ)..s,
        r * d /
          Real.rpow (r ^ 2 + d ^ 2) ((3 : ℝ) / 2)) =
        F s - F 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      hderiv (hcont.intervalIntegrable _ _)
  rw [hFTC]
  dsimp [F]
  rw [show (0 : ℝ) ^ 2 + d ^ 2 = d ^ 2 by ring,
    Real.sqrt_sq_eq_abs]
  by_cases hdpos : 0 < d
  · rw [abs_of_pos hdpos, Real.sign_of_pos hdpos]
    field_simp [hdpos.ne']
    ring
  · have hdneg : d < 0 :=
      lt_of_le_of_ne (le_of_not_gt hdpos) hd
    rw [abs_of_neg hdneg, Real.sign_of_neg hdneg]
    field_simp [hdneg.ne]
    ring

private def disk (s : ℝ) : Set (ℝ × ℝ) :=
  {q | q.1 ^ 2 + q.2 ^ 2 ≤ s ^ 2}

private theorem disk_closed (s : ℝ) : IsClosed (disk s) := by
  exact isClosed_le
    ((continuous_fst.pow 2).add (continuous_snd.pow 2))
    continuous_const

private theorem disk_compact (s : ℝ) (hs : 0 < s) :
    IsCompact (disk s) := by
  apply (isCompact_Icc :
    IsCompact (Set.Icc (-s, -s) (s, s))).of_isClosed_subset
      (disk_closed s)
  intro q hq
  change q.1 ^ 2 + q.2 ^ 2 ≤ s ^ 2 at hq
  have hx : q.1 ^ 2 ≤ s ^ 2 := by
    nlinarith [sq_nonneg q.2]
  have hy : q.2 ^ 2 ≤ s ^ 2 := by
    nlinarith [sq_nonneg q.1]
  exact ⟨
    ⟨by nlinarith [sq_nonneg (q.1 + s)],
      by nlinarith [sq_nonneg (q.2 + s)]⟩,
    ⟨by nlinarith [sq_nonneg (q.1 - s)],
      by nlinarith [sq_nonneg (q.2 - s)]⟩⟩

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

private def planeNorm (d : ℝ) (q : ℝ × ℝ) : ℝ :=
  |d| /
    Real.rpow (q.1 ^ 2 + q.2 ^ 2 + d ^ 2) ((3 : ℝ) / 2)

private theorem planeNorm_polar_pointwise
    (s d : ℝ) (hs : 0 < s)
    (p : ℝ × ℝ) (hp : p ∈ polarCoord.target) :
    p.1 • (disk s).indicator (planeNorm d) (polarCoord.symm p) =
      (Set.Iic s).indicator
          (fun r =>
            r * |d| /
              Real.rpow (r ^ 2 + d ^ 2) ((3 : ℝ) / 2)) p.1 *
        (1 : ℝ) := by
  rcases p with ⟨r, θ⟩
  have hr : 0 < r := hp.1
  have htrig :
      (r * Real.cos θ) ^ 2 +
        (r * Real.sin θ) ^ 2 = r ^ 2 := by
    calc
      _ = r ^ 2 *
          (Real.cos θ ^ 2 + Real.sin θ ^ 2) := by ring
      _ = r ^ 2 := by
        rw [Real.cos_sq_add_sin_sq]
        ring
  have hmem :
      polarCoord.symm (r, θ) ∈ disk s ↔ r ≤ s := by
    rw [polarCoord_symm_apply]
    simp only [disk, Set.mem_setOf_eq]
    rw [htrig]
    exact sq_le_sq₀ hr.le hs.le
  simp only [Set.indicator, hmem, Set.mem_Iic, smul_eq_mul]
  by_cases hrs : r ≤ s
  · simp only [hrs, if_true, mul_one]
    rw [polarCoord_symm_apply]
    unfold planeNorm
    rw [htrig]
    ring
  · simp [hrs]

private theorem planeNorm_integral (s d : ℝ)
    (hs : 0 < s) (hd : d ≠ 0) :
    (∫ q in disk s, planeNorm d q) =
      2 * Real.pi *
        (1 - |d| / Real.sqrt (s ^ 2 + d ^ 2)) := by
  have hp := integral_comp_polarCoord_symm
    ((disk s).indicator (planeNorm d))
  rw [integral_indicator (disk_closed s).measurableSet] at hp
  have hprod :
      (∫ p in polarCoord.target,
          p.1 • (disk s).indicator (planeNorm d)
            (polarCoord.symm p)) =
        (∫ r in Set.Ioi (0 : ℝ),
            (Set.Iic s).indicator
              (fun r =>
                r * |d| /
                  Real.rpow (r ^ 2 + d ^ 2)
                    ((3 : ℝ) / 2)) r) *
          ∫ θ in Set.Ioo (-Real.pi) Real.pi, (1 : ℝ) := by
    rw [polarCoord_target]
    calc
      _ = ∫ p in Set.Ioi (0 : ℝ) ×ˢ
          Set.Ioo (-Real.pi) Real.pi,
          (Set.Iic s).indicator
              (fun r =>
                r * |d| /
                  Real.rpow (r ^ 2 + d ^ 2)
                    ((3 : ℝ) / 2)) p.1 *
            (1 : ℝ) := by
        apply setIntegral_congr_fun
          (measurableSet_Ioi.prod measurableSet_Ioo)
        intro p hp'
        exact planeNorm_polar_pointwise s d hs p hp'
      _ = _ := by
        exact setIntegral_prod_mul
          (fun r : ℝ =>
            (Set.Iic s).indicator
              (fun r =>
                r * |d| /
                  Real.rpow (r ^ 2 + d ^ 2)
                    ((3 : ℝ) / 2)) r)
          (fun _θ : ℝ => (1 : ℝ))
          (Set.Ioi (0 : ℝ))
          (Set.Ioo (-Real.pi) Real.pi)
  have hrad :
      (∫ r in Set.Ioi (0 : ℝ),
          (Set.Iic s).indicator
            (fun r =>
              r * |d| /
                Real.rpow (r ^ 2 + d ^ 2)
                  ((3 : ℝ) / 2)) r) =
        ∫ r in (0 : ℝ)..s,
          r * |d| /
            Real.rpow (r ^ 2 + d ^ 2) ((3 : ℝ) / 2) := by
    rw [setIntegral_indicator measurableSet_Iic]
    have hinter :
        Set.Ioi (0 : ℝ) ∩ Set.Iic s =
          Set.Ioc (0 : ℝ) s := by
      ext r
      simp
    rw [hinter, intervalIntegral.integral_of_le hs.le]
  have hdabs : 0 < |d| := abs_pos.mpr hd
  have hsquared : |d| ^ 2 = d ^ 2 := sq_abs d
  have hkernel := radial_kernel_integral s |d| hs
  rw [Real.sign_of_pos hdabs, hsquared] at hkernel
  rw [hprod, hrad, angular_full, hkernel] at hp
  nlinarith [Real.pi_pos]

private theorem planeNorm_integral_le (s d : ℝ)
    (hs : 0 < s) (hd : d ≠ 0) :
    (∫ q in disk s, planeNorm d q) ≤ 2 * Real.pi := by
  rw [planeNorm_integral s d hs hd]
  have hratio :
      0 ≤ |d| / Real.sqrt (s ^ 2 + d ^ 2) :=
    div_nonneg (abs_nonneg d) (Real.sqrt_nonneg _)
  exact mul_le_of_le_one_right
    (by positivity : 0 ≤ 2 * Real.pi) (by linarith)

private def axialPlane (d : ℝ) (q : ℝ × ℝ) : ℝ :=
  d /
    Real.rpow (q.1 ^ 2 + q.2 ^ 2 + d ^ 2) ((3 : ℝ) / 2)

private theorem axialPlane_integral_closed
    (s d : ℝ) (hs : 0 < s) :
    (∫ q in disk s, axialPlane d q) =
      2 * Real.pi * d *
        (1 / |d| - 1 / Real.sqrt (s ^ 2 + d ^ 2)) := by
  by_cases hd : d = 0
  · subst d
    simp [axialPlane]
  have hpoint :
      axialPlane d =
        fun q => Real.sign d * planeNorm d q := by
    funext q
    unfold axialPlane planeNorm
    by_cases hdpos : 0 < d
    · rw [Real.sign_of_pos hdpos, abs_of_pos hdpos]
      ring
    · have hdneg : d < 0 :=
        lt_of_le_of_ne (le_of_not_gt hdpos) hd
      rw [Real.sign_of_neg hdneg, abs_of_neg hdneg]
      ring
  rw [hpoint, MeasureTheory.integral_const_mul,
    planeNorm_integral s d hs hd]
  by_cases hdpos : 0 < d
  · rw [Real.sign_of_pos hdpos, abs_of_pos hdpos]
    field_simp [hdpos.ne']
  · have hdneg : d < 0 :=
      lt_of_le_of_ne (le_of_not_gt hdpos) hd
    rw [Real.sign_of_neg hdneg, abs_of_neg hdneg]
    field_simp [hdneg.ne]
    ring

private def sliceRadius (R ζ : ℝ) : ℝ :=
  Real.sqrt (R ^ 2 - ζ ^ 2)

private def ballSet (R : ℝ) : Set ((ℝ × ℝ) × ℝ) :=
  {p | p.1.1 ^ 2 + p.1.2 ^ 2 + p.2 ^ 2 ≤ R ^ 2}

private def ballProduct (R a : ℝ)
    (p : (ℝ × ℝ) × ℝ) : ℝ :=
  (ballSet R).indicator
    (fun p => axialPlane (p.2 - a) p.1) p

private theorem ballSet_measurable (R : ℝ) :
    MeasurableSet (ballSet R) := by
  unfold ballSet
  measurability

private theorem sliceRadius_pos
    (R ζ : ℝ) (hR : 0 < R) (hζ : ζ ∈ Set.Ioo (-R) R) :
    0 < sliceRadius R ζ := by
  apply Real.sqrt_pos.2
  have hp : 0 < (R - ζ) * (R + ζ) :=
    mul_pos (sub_pos.mpr hζ.2) (by linarith [hζ.1])
  nlinarith

private theorem slice_mem_disk
    (R ζ : ℝ) (hζ : ζ ∈ Set.Icc (-R) R)
    (q : ℝ × ℝ) :
    (q, ζ) ∈ ballSet R ↔ q ∈ disk (sliceRadius R ζ) := by
  have harg : 0 ≤ R ^ 2 - ζ ^ 2 := by
    have hp : 0 ≤ (R - ζ) * (R + ζ) :=
      mul_nonneg (sub_nonneg.mpr hζ.2) (by linarith [hζ.1])
    nlinarith
  have hsquare :
      sliceRadius R ζ ^ 2 = R ^ 2 - ζ ^ 2 := by
    unfold sliceRadius
    exact Real.sq_sqrt harg
  unfold ballSet disk
  simp only [Set.mem_setOf_eq]
  rw [hsquare]
  constructor <;> intro h <;> linarith

private theorem axialPlane_continuous
    (d : ℝ) (hd : d ≠ 0) :
    Continuous (axialPlane d) := by
  have hbase : Continuous
      (fun q : ℝ × ℝ => q.1 ^ 2 + q.2 ^ 2 + d ^ 2) := by
    fun_prop
  have hden : Continuous
      (fun q : ℝ × ℝ =>
        Real.rpow (q.1 ^ 2 + q.2 ^ 2 + d ^ 2)
          ((3 : ℝ) / 2)) := by
    have heq :
        (fun q : ℝ × ℝ =>
          Real.rpow (q.1 ^ 2 + q.2 ^ 2 + d ^ 2)
            ((3 : ℝ) / 2)) =
          fun q =>
            (q.1 ^ 2 + q.2 ^ 2 + d ^ 2) *
              Real.sqrt (q.1 ^ 2 + q.2 ^ 2 + d ^ 2) := by
      funext q
      apply rpow_three_halves_eq
      nlinarith [sq_nonneg q.1, sq_nonneg q.2,
        sq_pos_of_ne_zero hd]
    rw [heq]
    exact hbase.mul (Real.continuous_sqrt.comp hbase)
  unfold axialPlane
  apply Continuous.div continuous_const hden
  intro q
  exact ne_of_gt (Real.rpow_pos_of_pos
    (by nlinarith [sq_nonneg q.1, sq_nonneg q.2,
      sq_pos_of_ne_zero hd]) _)

private theorem ballProduct_integrable
    (R a : ℝ) (hR : 0 < R) :
    Integrable (ballProduct R a) := by
  have hset : MeasurableSet (ballSet R) :=
    ballSet_measurable R
  have hraw : Measurable
      (fun p : (ℝ × ℝ) × ℝ =>
        axialPlane (p.2 - a) p.1) := by
    unfold axialPlane
    measurability
  have hmeas : AEStronglyMeasurable (ballProduct R a) :=
    (hraw.indicator hset).aestronglyMeasurable
  rw [Measure.volume_eq_prod] at hmeas ⊢
  rw [integrable_prod_iff' hmeas]
  constructor
  · filter_upwards [volume.ae_ne a, volume.ae_ne R,
      volume.ae_ne (-R)] with ζ hζa hζR hζmR
    by_cases hζ : ζ ∈ Set.Ioo (-R) R
    · have hd : ζ - a ≠ 0 := sub_ne_zero.mpr hζa
      have hs : 0 < sliceRadius R ζ :=
        sliceRadius_pos R ζ hR hζ
      have hi : Integrable
          ((disk (sliceRadius R ζ)).indicator
            (axialPlane (ζ - a))) :=
        ((axialPlane_continuous (ζ - a) hd).continuousOn.integrableOn_compact
          (disk_compact _ hs)).integrable_indicator
            (disk_closed _).measurableSet
      convert hi using 1
      funext q
      have hζIcc : ζ ∈ Set.Icc (-R) R :=
        ⟨hζ.1.le, hζ.2.le⟩
      have hmem := slice_mem_disk R ζ hζIcc q
      by_cases hq : q ∈ disk (sliceRadius R ζ)
      · rw [Set.indicator_of_mem hq]
        unfold ballProduct
        rw [Set.indicator_of_mem (hmem.mpr hq)]
      · rw [Set.indicator_of_notMem hq]
        unfold ballProduct
        rw [Set.indicator_of_notMem]
        exact fun hp => hq (hmem.mp hp)
    · have hout : ζ < -R ∨ R < ζ := by
        rw [Set.mem_Ioo, not_and_or, not_lt, not_lt] at hζ
        rcases hζ with hζ | hζ
        · exact Or.inl (lt_of_le_of_ne hζ hζmR)
        · exact Or.inr (lt_of_le_of_ne hζ (Ne.symm hζR))
      have hzero :
          (fun q : ℝ × ℝ => ballProduct R a (q, ζ)) =
            fun _q => (0 : ℝ) := by
        funext q
        unfold ballProduct
        rw [Set.indicator_of_notMem]
        intro hp
        change q.1 ^ 2 + q.2 ^ 2 + ζ ^ 2 ≤ R ^ 2 at hp
        rcases hout with hout | hout
        · have hsquare : R ^ 2 < (-ζ) ^ 2 :=
            (sq_lt_sq₀ hR.le (by linarith : 0 ≤ -ζ)).2
              (by linarith : R < -ζ)
          nlinarith [sq_nonneg q.1, sq_nonneg q.2]
        · have hsquare : R ^ 2 < ζ ^ 2 :=
            (sq_lt_sq₀ hR.le (by linarith : 0 ≤ ζ)).2 hout
          nlinarith [sq_nonneg q.1, sq_nonneg q.2]
      rw [hzero]
      exact integrable_zero _ _ _
  · let D : ℝ → ℝ :=
      (Set.Ioo (-R) R).indicator (fun _ζ => 2 * Real.pi)
    have hD : Integrable D := by
      have hc : IntegrableOn
          (fun _ζ : ℝ => 2 * Real.pi)
          (Set.Ioo (-R) R) :=
        integrableOn_const (C := (2 * Real.pi : ℝ))
          measure_Ioo_lt_top.ne
      exact hc.integrable_indicator measurableSet_Ioo
    have hgmeas : AEStronglyMeasurable
        (fun ζ : ℝ =>
          ∫ q : ℝ × ℝ, ‖ballProduct R a (q, ζ)‖) :=
      hmeas.norm.prod_swap.integral_prod_right'
    refine hD.mono' hgmeas ?_
    filter_upwards [volume.ae_ne a, volume.ae_ne R,
      volume.ae_ne (-R)] with ζ hζa hζR hζmR
    by_cases hζ : ζ ∈ Set.Ioo (-R) R
    · have hd : ζ - a ≠ 0 := sub_ne_zero.mpr hζa
      have hs : 0 < sliceRadius R ζ :=
        sliceRadius_pos R ζ hR hζ
      have hζIcc : ζ ∈ Set.Icc (-R) R :=
        ⟨hζ.1.le, hζ.2.le⟩
      have heq :
          (∫ q : ℝ × ℝ, ‖ballProduct R a (q, ζ)‖) =
            ∫ q in disk (sliceRadius R ζ),
              planeNorm (ζ - a) q := by
        rw [← integral_indicator (disk_closed _).measurableSet]
        apply integral_congr_ae
        filter_upwards [] with q
        have hmem := slice_mem_disk R ζ hζIcc q
        by_cases hq : q ∈ disk (sliceRadius R ζ)
        · rw [Set.indicator_of_mem hq]
          unfold ballProduct
          rw [Set.indicator_of_mem (hmem.mpr hq)]
          have hu :
              0 < q.1 ^ 2 + q.2 ^ 2 + (ζ - a) ^ 2 := by
            nlinarith [sq_nonneg q.1, sq_nonneg q.2,
              sq_pos_of_ne_zero hd]
          have hpw :
              0 < Real.rpow
                (q.1 ^ 2 + q.2 ^ 2 + (ζ - a) ^ 2)
                ((3 : ℝ) / 2) :=
            Real.rpow_pos_of_pos hu _
          unfold axialPlane planeNorm
          rw [Real.norm_eq_abs, abs_div, abs_of_pos hpw]
        · rw [Set.indicator_of_notMem hq]
          unfold ballProduct
          rw [Set.indicator_of_notMem]
          · simp
          · exact fun hp => hq (hmem.mp hp)
      have hnonneg :
          0 ≤ ∫ q : ℝ × ℝ,
            ‖ballProduct R a (q, ζ)‖ :=
        integral_nonneg fun _q => norm_nonneg _
      have hnonneg' :
          0 ≤ ∫ q : ℝ × ℝ,
            |ballProduct R a (q, ζ)| := by
        simpa only [Real.norm_eq_abs] using hnonneg
      change
        (∫ q : ℝ × ℝ, |ballProduct R a (q, ζ)|) =
          ∫ q in disk (sliceRadius R ζ),
            planeNorm (ζ - a) q at heq
      dsimp [D]
      rw [abs_of_nonneg hnonneg',
        Set.indicator_of_mem hζ, heq]
      exact planeNorm_integral_le
        (sliceRadius R ζ) (ζ - a) hs hd
    · have hout : ζ < -R ∨ R < ζ := by
        rw [Set.mem_Ioo, not_and_or, not_lt, not_lt] at hζ
        rcases hζ with hζ | hζ
        · exact Or.inl (lt_of_le_of_ne hζ hζmR)
        · exact Or.inr (lt_of_le_of_ne hζ (Ne.symm hζR))
      have hzero (q : ℝ × ℝ) :
          ballProduct R a (q, ζ) = 0 := by
        unfold ballProduct
        rw [Set.indicator_of_notMem]
        intro hp
        change q.1 ^ 2 + q.2 ^ 2 + ζ ^ 2 ≤ R ^ 2 at hp
        rcases hout with hout | hout
        · have hsquare : R ^ 2 < (-ζ) ^ 2 :=
            (sq_lt_sq₀ hR.le (by linarith : 0 ≤ -ζ)).2
              (by linarith : R < -ζ)
          nlinarith [sq_nonneg q.1, sq_nonneg q.2]
        · have hsquare : R ^ 2 < ζ ^ 2 :=
            (sq_lt_sq₀ hR.le (by linarith : 0 ≤ ζ)).2 hout
          nlinarith [sq_nonneg q.1, sq_nonneg q.2]
      dsimp [D]
      rw [Set.indicator_of_notMem hζ]
      simp_rw [hzero]
      simp

private theorem axialBall_integral
    (R a : ℝ) (hR : 0 < R) :
    (∫ p in ball R,
        (p.2.2 - a) /
          Real.rpow (distanceSquared a p) ((3 : ℝ) / 2)) =
      2 * Real.pi *
        ∫ ζ in -R..R,
          (ζ - a) *
            (1 / |ζ - a| -
              1 / Real.sqrt (R ^ 2 - 2 * a * ζ + a ^ 2)) := by
  let G : Point3 → ℝ := fun p =>
    (p.2.2 - a) /
      Real.rpow (distanceSquared a p) ((3 : ℝ) / 2)
  let e :=
    (MeasurableEquiv.prodAssoc :
      ((ℝ × ℝ) × ℝ) ≃ᵐ Point3)
  have hball := ball_measurable R
  have hind :
      (fun q : (ℝ × ℝ) × ℝ =>
        (ball R).indicator G (e q)) =
        ballProduct R a := by
    funext q
    rcases q with ⟨⟨x, y⟩, ζ⟩
    have hmem :
        e ((x, y), ζ) ∈ ball R ↔
          ((x, y), ζ) ∈ ballSet R := by
      change
        x ^ 2 + y ^ 2 + ζ ^ 2 ≤ R ^ 2 ↔
          x ^ 2 + y ^ 2 + ζ ^ 2 ≤ R ^ 2
      rfl
    by_cases hp : ((x, y), ζ) ∈ ballSet R
    · rw [Set.indicator_of_mem (hmem.mpr hp)]
      unfold ballProduct
      rw [Set.indicator_of_mem hp]
      dsimp [G, e]
      unfold axialPlane distanceSquared
      change
        (ζ - a) /
            Real.rpow (x ^ 2 + y ^ 2 + (ζ - a) ^ 2)
              ((3 : ℝ) / 2) =
          (ζ - a) /
            Real.rpow (x ^ 2 + y ^ 2 + (ζ - a) ^ 2)
              ((3 : ℝ) / 2)
      rfl
    · rw [Set.indicator_of_notMem]
      · unfold ballProduct
        rw [Set.indicator_of_notMem hp]
      · exact fun he => hp (hmem.mp he)
  have hreassoc :
      (∫ q : (ℝ × ℝ) × ℝ,
          (ball R).indicator G (e q)) =
        ∫ p : Point3, (ball R).indicator G p :=
    volume_preserving_prodAssoc.integral_comp'
      ((ball R).indicator G)
  rw [hind] at hreassoc
  rw [← integral_indicator hball]
  change (∫ p : Point3, (ball R).indicator G p) = _
  rw [← hreassoc]
  have hFubini :
      (∫ q : (ℝ × ℝ) × ℝ, ballProduct R a q) =
        ∫ ζ : ℝ,
          ∫ q : ℝ × ℝ, ballProduct R a (q, ζ) := by
    exact integral_prod_symm
      (ballProduct R a) (ballProduct_integrable R a hR)
  rw [hFubini]
  have hsection : ∀ᵐ ζ : ℝ ∂volume,
      (∫ q : ℝ × ℝ, ballProduct R a (q, ζ)) =
        (Set.Ioo (-R) R).indicator
          (fun ζ =>
            2 * Real.pi * (ζ - a) *
              (1 / |ζ - a| -
                1 / Real.sqrt
                  (R ^ 2 - 2 * a * ζ + a ^ 2))) ζ := by
    filter_upwards [volume.ae_ne R,
      volume.ae_ne (-R)] with ζ hζR hζmR
    by_cases hζ : ζ ∈ Set.Ioo (-R) R
    · rw [Set.indicator_of_mem hζ]
      have hζIcc : ζ ∈ Set.Icc (-R) R :=
        ⟨hζ.1.le, hζ.2.le⟩
      have hs : 0 < sliceRadius R ζ :=
        sliceRadius_pos R ζ hR hζ
      have hpoint :
          (fun q : ℝ × ℝ =>
            (disk (sliceRadius R ζ)).indicator
              (axialPlane (ζ - a)) q) =
            fun q : ℝ × ℝ => ballProduct R a (q, ζ) := by
        funext q
        have hmem := slice_mem_disk R ζ hζIcc q
        by_cases hq : q ∈ disk (sliceRadius R ζ)
        · rw [Set.indicator_of_mem hq]
          unfold ballProduct
          rw [Set.indicator_of_mem (hmem.mpr hq)]
        · rw [Set.indicator_of_notMem hq]
          unfold ballProduct
          rw [Set.indicator_of_notMem]
          exact fun hp => hq (hmem.mp hp)
      rw [← hpoint,
        integral_indicator (disk_closed _).measurableSet,
        axialPlane_integral_closed _ _ hs]
      have harg : 0 ≤ R ^ 2 - ζ ^ 2 := by
        have hp : 0 ≤ (R - ζ) * (R + ζ) :=
          mul_nonneg (sub_nonneg.mpr hζ.2.le)
            (by linarith [hζ.1])
        nlinarith
      have hsquare :
          sliceRadius R ζ ^ 2 = R ^ 2 - ζ ^ 2 := by
        unfold sliceRadius
        exact Real.sq_sqrt harg
      rw [hsquare]
      rw [show
        R ^ 2 - ζ ^ 2 + (ζ - a) ^ 2 =
          R ^ 2 - 2 * a * ζ + a ^ 2 by ring]
    · rw [Set.indicator_of_notMem hζ]
      have hout : ζ < -R ∨ R < ζ := by
        rw [Set.mem_Ioo, not_and_or, not_lt, not_lt] at hζ
        rcases hζ with hζ | hζ
        · exact Or.inl (lt_of_le_of_ne hζ hζmR)
        · exact Or.inr (lt_of_le_of_ne hζ (Ne.symm hζR))
      have hzero (q : ℝ × ℝ) :
          ballProduct R a (q, ζ) = 0 := by
        unfold ballProduct
        rw [Set.indicator_of_notMem]
        intro hp
        change q.1 ^ 2 + q.2 ^ 2 + ζ ^ 2 ≤ R ^ 2 at hp
        rcases hout with hout | hout
        · have hsquare : R ^ 2 < (-ζ) ^ 2 :=
            (sq_lt_sq₀ hR.le (by linarith : 0 ≤ -ζ)).2
              (by linarith : R < -ζ)
          nlinarith [sq_nonneg q.1, sq_nonneg q.2]
        · have hsquare : R ^ 2 < ζ ^ 2 :=
            (sq_lt_sq₀ hR.le (by linarith : 0 ≤ ζ)).2 hout
          nlinarith [sq_nonneg q.1, sq_nonneg q.2]
      simp_rw [hzero]
      simp
  rw [integral_congr_ae hsection,
    integral_indicator measurableSet_Ioo]
  calc
    (∫ ζ in Set.Ioo (-R) R,
        2 * Real.pi * (ζ - a) *
          (1 / |ζ - a| -
            1 / Real.sqrt
              (R ^ 2 - 2 * a * ζ + a ^ 2))) =
        ∫ ζ in Set.Ioc (-R) R,
          2 * Real.pi * (ζ - a) *
            (1 / |ζ - a| -
              1 / Real.sqrt
                (R ^ 2 - 2 * a * ζ + a ^ 2)) :=
      (integral_Ioc_eq_integral_Ioo
        (f := fun ζ : ℝ =>
          2 * Real.pi * (ζ - a) *
            (1 / |ζ - a| -
              1 / Real.sqrt
                (R ^ 2 - 2 * a * ζ + a ^ 2)))).symm
    _ = ∫ ζ in -R..R,
          2 * Real.pi * ((ζ - a) *
            (1 / |ζ - a| -
              1 / Real.sqrt
                (R ^ 2 - 2 * a * ζ + a ^ 2))) := by
      rw [intervalIntegral.integral_of_le (by linarith : -R ≤ R)]
      apply setIntegral_congr_fun measurableSet_Ioc
      intro ζ _
      ring
    _ = 2 * Real.pi *
        ∫ ζ in -R..R,
          (ζ - a) *
            (1 / |ζ - a| -
              1 / Real.sqrt
                (R ^ 2 - 2 * a * ζ + a ^ 2)) := by
      rw [intervalIntegral.integral_const_mul]

theorem gap4 (R a k M m : ℝ) (hR : 0 < R) (ha : 0 ≤ a) :
    forceZ R a k M m =
      2 * Real.pi * k * m * density R M *
        ∫ ζ in -R..R,
          (ζ - a) *
            (1 / |ζ - a| -
              1 / Real.sqrt (R ^ 2 - 2 * a * ζ + a ^ 2)) := by
  unfold forceZ
  rw [axialBall_integral R a hR]
  ring

private theorem sign_intervalIntegrable (b s t : ℝ) :
    IntervalIntegrable (fun ζ : ℝ => Real.sign (b - ζ))
      volume s t := by
  rw [intervalIntegrable_iff]
  apply Measure.integrableOn_of_bounded (M := 1)
  · rw [Real.volume_uIoc]
    exact ENNReal.ofReal_ne_top
  · have hm : Measurable (fun ζ : ℝ => Real.sign (b - ζ)) := by
      unfold Real.sign
      have harg : Measurable (fun ζ : ℝ => b - ζ) :=
        measurable_const.sub measurable_id
      exact Measurable.ite (measurableSet_lt harg measurable_const)
        measurable_const
        (Measurable.ite (measurableSet_lt measurable_const harg)
          measurable_const measurable_const)
    exact hm.aestronglyMeasurable
  · filter_upwards [] with ζ
    rcases Real.sign_apply_eq (b - ζ) with hζ | hζ | hζ
    · simp [hζ]
    · simp [hζ]
    · simp [hζ]

private theorem sign_integral_positive (s t b : ℝ)
    (hst : s < t) (htb : t ≤ b) :
    (∫ ζ in s..t, Real.sign (b - ζ)) = t - s := by
  have hae : ∀ᵐ ζ : ℝ ∂volume,
      ζ ∈ Set.uIoc s t →
        Real.sign (b - ζ) = (1 : ℝ) := by
    filter_upwards [volume.ae_ne b] with ζ hζb hζ
    rw [Set.uIoc_of_le hst.le] at hζ
    rw [Real.sign_of_pos]
    have : ζ < b := lt_of_le_of_ne (hζ.2.trans htb) hζb
    linarith
  rw [intervalIntegral.integral_congr_ae hae]
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  ring

private theorem sign_integral_negative (s t b : ℝ)
    (hst : s < t) (hbs : b ≤ s) :
    (∫ ζ in s..t, Real.sign (b - ζ)) = -(t - s) := by
  have hae : ∀ᵐ ζ : ℝ ∂volume,
      ζ ∈ Set.uIoc s t →
        Real.sign (b - ζ) = (-1 : ℝ) := by
    filter_upwards [volume.ae_ne b] with ζ hζb hζ
    rw [Set.uIoc_of_le hst.le] at hζ
    rw [Real.sign_of_neg]
    have : b < ζ :=
      lt_of_le_of_ne (hbs.trans hζ.1.le) (Ne.symm hζb)
    linarith
  rw [intervalIntegral.integral_congr_ae hae]
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  ring

theorem gap5 (R a : ℝ) (hR : 0 < R) (ha : 0 ≤ a) :
    (∫ ζ in -R..R, Real.sign (ζ - a)) =
      if R ≤ a then -2 * R else -2 * a := by
  have hneg :
      (fun ζ : ℝ => Real.sign (ζ - a)) =
        fun ζ => -Real.sign (a - ζ) := by
    funext ζ
    rw [show ζ - a = -(a - ζ) by ring, Real.sign_neg]
  rw [hneg, intervalIntegral.integral_neg]
  split_ifs with hRa
  · rw [sign_integral_positive (-R) R a (by linarith) hRa]
    ring
  · have haR : a < R := lt_of_not_ge hRa
    have hmRa : -R < a := by linarith
    have hleft :=
      sign_integral_positive (-R) a a hmRa le_rfl
    have hright :=
      sign_integral_negative a R a haR le_rfl
    have hsplit :=
      intervalIntegral.integral_add_adjacent_intervals
        (sign_intervalIntegrable a (-R) a)
        (sign_intervalIntegrable a a R)
    rw [hleft, hright] at hsplit
    rw [← hsplit]
    ring

private def Q (R a ζ : ℝ) : ℝ :=
  R ^ 2 - 2 * a * ζ + a ^ 2

private def primitive (R a ζ : ℝ) : ℝ :=
  -(R ^ 2 - a ^ 2) / (2 * a ^ 2) * Real.sqrt (Q R a ζ) +
    1 / (6 * a ^ 2) * (Q R a ζ * Real.sqrt (Q R a ζ))

private theorem primitive_deriv
    (R a ζ : ℝ) (ha : 0 < a) (hQ : 0 < Q R a ζ) :
    HasDerivAt (primitive R a)
      ((ζ - a) / Real.sqrt (Q R a ζ)) ζ := by
  have hinner :
      HasDerivAt (Q R a) (-2 * a) ζ := by
    unfold Q
    convert
      (((hasDerivAt_const ζ (R ^ 2)).sub
        ((hasDerivAt_const ζ (2 * a)).mul (hasDerivAt_id ζ))).add_const
          (a ^ 2)) using 1 <;> ring
  have hsqrt :
      HasDerivAt (fun x : ℝ => Real.sqrt (Q R a x))
        (1 / (2 * Real.sqrt (Q R a ζ)) * (-2 * a)) ζ := by
    simpa only [Function.comp_apply] using
      (Real.hasDerivAt_sqrt hQ.ne').comp ζ hinner
  have hprod :
      HasDerivAt
        (fun x : ℝ => Q R a x * Real.sqrt (Q R a x))
        ((-2 * a) * Real.sqrt (Q R a ζ) +
          Q R a ζ *
            (1 / (2 * Real.sqrt (Q R a ζ)) * (-2 * a))) ζ :=
    hinner.mul hsqrt
  have hraw :
      HasDerivAt (primitive R a)
        (-(R ^ 2 - a ^ 2) / (2 * a ^ 2) *
            (1 / (2 * Real.sqrt (Q R a ζ)) * (-2 * a)) +
          1 / (6 * a ^ 2) *
            ((-2 * a) * Real.sqrt (Q R a ζ) +
              Q R a ζ *
                (1 / (2 * Real.sqrt (Q R a ζ)) * (-2 * a)))) ζ := by
    unfold primitive
    simpa only [zero_mul, zero_add] using
      ((hasDerivAt_const ζ
        (-(R ^ 2 - a ^ 2) / (2 * a ^ 2))).mul hsqrt).add
        ((hasDerivAt_const ζ (1 / (6 * a ^ 2))).mul hprod)
  convert hraw using 1
  have hsqrt_ne : Real.sqrt (Q R a ζ) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr hQ
  have hsqrt_sq :
      Real.sqrt (Q R a ζ) ^ 2 = Q R a ζ :=
    Real.sq_sqrt hQ.le
  field_simp [ha.ne', hsqrt_ne]
  rw [hsqrt_sq]
  unfold Q
  ring

private theorem Q_pos_on_open
    (R a ζ : ℝ) (hR : 0 < R) (ha : 0 < a)
    (hζ : ζ ∈ Set.Ioo (-R) R) :
    0 < Q R a ζ := by
  have hsq : 0 ≤ (a - R) ^ 2 := sq_nonneg (a - R)
  have hp : 0 < 2 * a * (R - ζ) :=
    mul_pos (mul_pos (by norm_num) ha) (sub_pos.mpr hζ.2)
  have hid :
      Q R a ζ = (a - R) ^ 2 + 2 * a * (R - ζ) := by
    unfold Q
    ring
  rw [hid]
  positivity

private theorem kernel_intervalIntegrable
    (R a : ℝ) (hR : 0 < R) (ha : 0 < a) :
    IntervalIntegrable
      (fun ζ : ℝ => (ζ - a) / Real.sqrt (Q R a ζ))
      volume (-R) R := by
  rw [intervalIntegrable_iff]
  apply Measure.integrableOn_of_bounded (M := 1)
  · rw [Real.volume_uIoc]
    exact ENNReal.ofReal_ne_top
  · have hm :
        Measurable
          (fun ζ : ℝ => (ζ - a) / Real.sqrt (Q R a ζ)) := by
      unfold Q
      measurability
    exact hm.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with ζ hζ
    rw [Set.uIoc_of_le (by linarith : -R ≤ R)] at hζ
    have hζlo : -R ≤ ζ := hζ.1.le
    have hζhi : ζ ≤ R := hζ.2
    have hRz : 0 ≤ R ^ 2 - ζ ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hζhi)
        (by linarith : 0 ≤ R + ζ)]
    have hQnonneg : 0 ≤ Q R a ζ := by
      have hid :
          Q R a ζ = (ζ - a) ^ 2 + (R ^ 2 - ζ ^ 2) := by
        unfold Q
        ring
      rw [hid]
      positivity
    have hsqrt_ge :
        |ζ - a| ≤ Real.sqrt (Q R a ζ) := by
      rw [← Real.sqrt_sq_eq_abs (ζ - a)]
      exact Real.sqrt_le_sqrt
        (by
          have hid :
              Q R a ζ = (ζ - a) ^ 2 + (R ^ 2 - ζ ^ 2) := by
            unfold Q
            ring
          rw [hid]
          linarith)
    rw [Real.norm_eq_abs, abs_div,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    by_cases hs : Real.sqrt (Q R a ζ) = 0
    · simp [hs]
    · exact (div_le_one (lt_of_le_of_ne
          (Real.sqrt_nonneg _) (Ne.symm hs))).2 hsqrt_ge

private theorem kernel_integral_raw
    (R a : ℝ) (hR : 0 < R) (ha : 0 < a) :
    (∫ ζ in -R..R,
        (ζ - a) / Real.sqrt (Q R a ζ)) =
      primitive R a R - primitive R a (-R) := by
  have hprim_cont :
      ContinuousOn (primitive R a) (Set.Icc (-R) R) := by
    unfold primitive Q
    fun_prop
  have hder : ∀ ζ ∈ Set.Ioo (-R) R,
      HasDerivAt (primitive R a)
        ((ζ - a) / Real.sqrt (Q R a ζ)) ζ := by
    intro ζ hζ
    exact primitive_deriv R a ζ ha
      (Q_pos_on_open R a ζ hR ha hζ)
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (by linarith : -R ≤ R) hprim_cont hder
  exact kernel_intervalIntegrable R a hR ha

theorem gap6 (R a : ℝ) (hR : 0 < R) (ha : 0 ≤ a) :
    (∫ ζ in -R..R,
        (ζ - a) / Real.sqrt (R ^ 2 - 2 * a * ζ + a ^ 2)) =
      if R ≤ a then 2 * R ^ 3 / (3 * a ^ 2) - 2 * R
      else -(4 * a / 3) := by
  by_cases ha0 : a = 0
  · subst a
    have hsqrt : Real.sqrt (R ^ 2) = R := by
      rw [Real.sqrt_sq_eq_abs, abs_of_pos hR]
    rw [if_neg (by linarith : ¬R ≤ (0 : ℝ))]
    simp only [mul_zero, zero_mul, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      add_zero, sub_zero, hsqrt, neg_zero]
    rw [show (fun ζ : ℝ => ζ / R) = fun ζ => (1 / R) * ζ by
      funext ζ
      ring]
    rw [intervalIntegral.integral_const_mul,
      integral_id]
    ring
  have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hraw := kernel_integral_raw R a hR hapos
  change
    (∫ ζ in -R..R,
      (ζ - a) / Real.sqrt (Q R a ζ)) = _
  rw [hraw]
  have hQR : Q R a R = (R - a) ^ 2 := by
    unfold Q
    ring
  have hQmR : Q R a (-R) = (R + a) ^ 2 := by
    unfold Q
    ring
  rw [primitive, primitive, hQR, hQmR,
    Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs]
  have hsum : 0 < R + a := by positivity
  rw [abs_of_pos hsum]
  split_ifs with hRa
  · have hdiff : R - a ≤ 0 := sub_nonpos.mpr hRa
    rw [abs_of_nonpos hdiff]
    field_simp [hapos.ne']
    ring
  · have hdiff : 0 < R - a := sub_pos.mpr (lt_of_not_ge hRa)
    rw [abs_of_pos hdiff]
    field_simp [hapos.ne']
    ring

private theorem mul_inv_abs_eq_sign (x : ℝ) :
    x * (1 / |x|) = Real.sign x := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · rw [Real.sign_of_neg hx, abs_of_neg hx]
    field_simp [hx.ne]
  · subst x
    simp
  · rw [Real.sign_of_pos hx, abs_of_pos hx]
    field_simp [hx.ne']

private theorem shiftedSign_intervalIntegrable
    (R a : ℝ) :
    IntervalIntegrable (fun ζ : ℝ => Real.sign (ζ - a))
      volume (-R) R := by
  have hi := (sign_intervalIntegrable a (-R) R).neg
  convert hi using 1
  funext ζ
  rw [show ζ - a = -(a - ζ) by ring, Real.sign_neg]
  rfl

private theorem axialRatio_intervalIntegrable
    (R a : ℝ) (hR : 0 < R) (ha : 0 ≤ a) :
    IntervalIntegrable
      (fun ζ : ℝ =>
        (ζ - a) /
          Real.sqrt (R ^ 2 - 2 * a * ζ + a ^ 2))
      volume (-R) R := by
  by_cases ha0 : a = 0
  · subst a
    have hsqrt : Real.sqrt (R ^ 2) = R := by
      rw [Real.sqrt_sq_eq_abs, abs_of_pos hR]
    simpa only [sub_zero, mul_zero, zero_mul,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      add_zero, hsqrt] using
      (by
        have hc : Continuous (fun ζ : ℝ => ζ / R) := by
          fun_prop
        exact hc.intervalIntegrable (-R) R)
  · have hapos : 0 < a :=
      lt_of_le_of_ne ha (Ne.symm ha0)
    simpa only [Q] using
      kernel_intervalIntegrable R a hR hapos

private theorem axialOuter_integral
    (R a : ℝ) (hR : 0 < R) (ha : 0 ≤ a) :
    (∫ ζ in -R..R,
        (ζ - a) *
          (1 / |ζ - a| -
            1 / Real.sqrt (R ^ 2 - 2 * a * ζ + a ^ 2))) =
      (∫ ζ in -R..R, Real.sign (ζ - a)) -
        ∫ ζ in -R..R,
          (ζ - a) /
            Real.sqrt (R ^ 2 - 2 * a * ζ + a ^ 2) := by
  rw [← intervalIntegral.integral_sub
    (shiftedSign_intervalIntegrable R a)
    (axialRatio_intervalIntegrable R a hR ha)]
  apply intervalIntegral.integral_congr
  intro ζ _
  change
    (ζ - a) *
        (1 / |ζ - a| -
          1 / Real.sqrt (R ^ 2 - 2 * a * ζ + a ^ 2)) =
      Real.sign (ζ - a) -
        (ζ - a) /
          Real.sqrt (R ^ 2 - 2 * a * ζ + a ^ 2)
  rw [mul_sub, mul_inv_abs_eq_sign]
  ring

theorem gap7 (R a k M m : ℝ) (hR : 0 < R) (ha : 0 ≤ a) :
    forceZ R a k M m =
      if R ≤ a then -(k * M * m / a ^ 2)
      else -(k * M * m / R ^ 3) * a := by
  rw [gap4 R a k M m hR ha,
    axialOuter_integral R a hR ha,
    gap5 R a hR ha, gap6 R a hR ha]
  by_cases hRa : R ≤ a
  · rw [if_pos hRa, if_pos hRa, if_pos hRa]
    unfold density
    have ha_pos : 0 < a := lt_of_lt_of_le hR hRa
    field_simp [hR.ne', ha_pos.ne', Real.pi_ne_zero]
    ring
  · rw [if_neg hRa, if_neg hRa, if_neg hRa]
    unfold density
    field_simp [hR.ne', Real.pi_ne_zero]
    ring

theorem gap8 (R a k M m : ℝ) (hR : 0 < R) (ha : 0 ≤ a) :
    (forceX R a k M m, forceY R a k M m, forceZ R a k M m) =
      if R ≤ a then ((0 : ℝ), 0, -(k * M * m / a ^ 2))
      else ((0 : ℝ), 0, -(k * M * m / R ^ 3) * a) := by
  rw [gap1 R a k M m hR ha, gap2 R a k M m hR ha,
    gap7 R a k M m hR ha]
  by_cases hRa : R ≤ a <;> simp [hRa]

end

end ProofGap.Exercise4158
