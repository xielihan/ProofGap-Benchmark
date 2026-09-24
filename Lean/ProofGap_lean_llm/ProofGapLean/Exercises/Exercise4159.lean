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

namespace ProofGap.Exercise4159

noncomputable section

open MeasureTheory
open scoped Interval

abbrev Point3 := ℝ × ℝ × ℝ

def cylinder (a h : ℝ) : Set Point3 :=
  {p |
    p.1 ^ 2 + p.2.1 ^ 2 ≤ a ^ 2 ∧
      0 ≤ p.2.2 ∧ p.2.2 ≤ h}

def distanceSquared (z : ℝ) (p : Point3) : ℝ :=
  p.1 ^ 2 + p.2.1 ^ 2 + (p.2.2 - z) ^ 2

def forceX (a h k ρ₀ z : ℝ) : ℝ :=
  k * ρ₀ *
    ∫ p in cylinder a h,
      p.1 / Real.rpow (distanceSquared z p) ((3 : ℝ) / 2)

def forceY (a h k ρ₀ z : ℝ) : ℝ :=
  k * ρ₀ *
    ∫ p in cylinder a h,
      p.2.1 / Real.rpow (distanceSquared z p) ((3 : ℝ) / 2)

def forceZ (a h k ρ₀ z : ℝ) : ℝ :=
  k * ρ₀ *
    ∫ p in cylinder a h,
      (p.2.2 - z) /
        Real.rpow (distanceSquared z p) ((3 : ℝ) / 2)

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
      (MeasurePreserving.id
        (volume : Measure (ℝ × ℝ)))

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

private theorem cylinder_measurable (a h : ℝ) :
    MeasurableSet (cylinder a h) := by
  unfold cylinder
  measurability

private theorem flipX_mem_cylinder (a h : ℝ) (p : Point3) :
    flipX p ∈ cylinder a h ↔ p ∈ cylinder a h := by
  rcases p with ⟨x, y, z⟩
  change
    ((-x) ^ 2 + y ^ 2 ≤ a ^ 2 ∧ 0 ≤ z ∧ z ≤ h) ↔
      (x ^ 2 + y ^ 2 ≤ a ^ 2 ∧ 0 ≤ z ∧ z ≤ h)
  ring_nf

private theorem flipY_mem_cylinder (a h : ℝ) (p : Point3) :
    flipY p ∈ cylinder a h ↔ p ∈ cylinder a h := by
  rcases p with ⟨x, y, z⟩
  change
    (x ^ 2 + (-y) ^ 2 ≤ a ^ 2 ∧ 0 ≤ z ∧ z ≤ h) ↔
      (x ^ 2 + y ^ 2 ≤ a ^ 2 ∧ 0 ≤ z ∧ z ≤ h)
  ring_nf

private theorem distanceSquared_flipX (z : ℝ) (p : Point3) :
    distanceSquared z (flipX p) = distanceSquared z p := by
  rcases p with ⟨x, y, ζ⟩
  change
    (-x) ^ 2 + y ^ 2 + (ζ - z) ^ 2 =
      x ^ 2 + y ^ 2 + (ζ - z) ^ 2
  ring

private theorem distanceSquared_flipY (z : ℝ) (p : Point3) :
    distanceSquared z (flipY p) = distanceSquared z p := by
  rcases p with ⟨x, y, ζ⟩
  change
    x ^ 2 + (-y) ^ 2 + (ζ - z) ^ 2 =
      x ^ 2 + y ^ 2 + (ζ - z) ^ 2
  ring

theorem gap1 (a h k ρ₀ z : ℝ) (ha : 0 < a) (hh : 0 < h) :
    forceX a h k ρ₀ z = 0 := by
  unfold forceX
  rw [← integral_indicator (cylinder_measurable a h)]
  let G : Point3 → ℝ := fun p =>
    p.1 / Real.rpow (distanceSquared z p) ((3 : ℝ) / 2)
  change k * ρ₀ * (∫ p : Point3,
    (cylinder a h).indicator G p) = 0
  have hodd :
      (fun p : Point3 =>
        (cylinder a h).indicator G (flipX p)) =
        fun p => -((cylinder a h).indicator G p) := by
    funext p
    by_cases hp : p ∈ cylinder a h
    · have hfp : flipX p ∈ cylinder a h :=
        (flipX_mem_cylinder a h p).mpr hp
      rw [Set.indicator_of_mem hfp, Set.indicator_of_mem hp]
      dsimp [G]
      rw [distanceSquared_flipX]
      change
        (-p.1) /
            Real.rpow (distanceSquared z p) ((3 : ℝ) / 2) =
          -(p.1 /
            Real.rpow (distanceSquared z p) ((3 : ℝ) / 2))
      ring
    · have hfp : flipX p ∉ cylinder a h := by
        intro hfp'
        exact hp ((flipX_mem_cylinder a h p).mp hfp')
      rw [Set.indicator_of_notMem hfp,
        Set.indicator_of_notMem hp, neg_zero]
  have hchange :=
    flipX_measurePreserving.integral_comp'
      ((cylinder a h).indicator G)
  rw [hodd, integral_neg] at hchange
  rw [show (∫ p : Point3,
      (cylinder a h).indicator G p) = 0 by linarith]
  ring

theorem gap2 (a h k ρ₀ z : ℝ) (ha : 0 < a) (hh : 0 < h) :
    forceY a h k ρ₀ z = 0 := by
  unfold forceY
  rw [← integral_indicator (cylinder_measurable a h)]
  let G : Point3 → ℝ := fun p =>
    p.2.1 / Real.rpow (distanceSquared z p) ((3 : ℝ) / 2)
  change k * ρ₀ * (∫ p : Point3,
    (cylinder a h).indicator G p) = 0
  have hodd :
      (fun p : Point3 =>
        (cylinder a h).indicator G (flipY p)) =
        fun p => -((cylinder a h).indicator G p) := by
    funext p
    by_cases hp : p ∈ cylinder a h
    · have hfp : flipY p ∈ cylinder a h :=
        (flipY_mem_cylinder a h p).mpr hp
      rw [Set.indicator_of_mem hfp, Set.indicator_of_mem hp]
      dsimp [G]
      rw [distanceSquared_flipY]
      change
        (-p.2.1) /
            Real.rpow (distanceSquared z p) ((3 : ℝ) / 2) =
          -(p.2.1 /
            Real.rpow (distanceSquared z p) ((3 : ℝ) / 2))
      ring
    · have hfp : flipY p ∉ cylinder a h := by
        intro hfp'
        exact hp ((flipY_mem_cylinder a h p).mp hfp')
      rw [Set.indicator_of_notMem hfp,
        Set.indicator_of_notMem hp, neg_zero]
  have hchange :=
    flipY_measurePreserving.integral_comp'
      ((cylinder a h).indicator G)
  rw [hodd, integral_neg] at hchange
  rw [show (∫ p : Point3,
      (cylinder a h).indicator G p) = 0 by linarith]
  ring

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

private theorem radial_kernel_integral (a d : ℝ) (ha : 0 < a) :
    (∫ r in (0 : ℝ)..a,
      r * d /
        Real.rpow (r ^ 2 + d ^ 2) ((3 : ℝ) / 2)) =
      Real.sign d - d / Real.sqrt (a ^ 2 + d ^ 2) := by
  by_cases hd : d = 0
  · simp [hd]
  let F : ℝ → ℝ := fun r =>
    -d / Real.sqrt (r ^ 2 + d ^ 2)
  have hderiv : ∀ r ∈ Set.uIcc (0 : ℝ) a,
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
      (∫ r in (0 : ℝ)..a,
        r * d /
          Real.rpow (r ^ 2 + d ^ 2) ((3 : ℝ) / 2)) =
        F a - F 0 :=
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

private theorem axial_ratio_integral (a h z : ℝ) (ha : 0 < a) :
    (∫ ζ in (0 : ℝ)..h,
      (ζ - z) / Real.sqrt (a ^ 2 + (ζ - z) ^ 2)) =
      Real.sqrt (a ^ 2 + (h - z) ^ 2) -
        Real.sqrt (a ^ 2 + z ^ 2) := by
  let F : ℝ → ℝ := fun ζ =>
    Real.sqrt (a ^ 2 + (ζ - z) ^ 2)
  have hderiv : ∀ ζ ∈ Set.uIcc (0 : ℝ) h,
      HasDerivAt F
        ((ζ - z) / Real.sqrt (a ^ 2 + (ζ - z) ^ 2)) ζ := by
    intro ζ _
    have hu : 0 < a ^ 2 + (ζ - z) ^ 2 := by
      nlinarith [sq_pos_of_pos ha, sq_nonneg (ζ - z)]
    have hlin :
        HasDerivAt (fun x : ℝ => x - z) 1 ζ := by
      convert (hasDerivAt_id ζ).sub_const z using 1
    have hinner :
        HasDerivAt (fun x : ℝ => a ^ 2 + (x - z) ^ 2)
          (2 * (ζ - z)) ζ := by
      convert (hasDerivAt_const ζ (a ^ 2)).add (hlin.pow 2) using 1 <;>
        ring
    have hsqrt :
        HasDerivAt F
          (1 / (2 * Real.sqrt (a ^ 2 + (ζ - z) ^ 2)) *
            (2 * (ζ - z))) ζ := by
      simpa only [F, Function.comp_apply] using
        (Real.hasDerivAt_sqrt hu.ne').comp ζ hinner
    convert hsqrt using 1
    field_simp [Real.sqrt_ne_zero'.mpr hu]
  have hcont : Continuous
      (fun ζ : ℝ =>
        (ζ - z) / Real.sqrt (a ^ 2 + (ζ - z) ^ 2)) := by
    apply Continuous.div
    · fun_prop
    · fun_prop
    · intro ζ
      apply Real.sqrt_ne_zero'.mpr
      nlinarith [sq_nonneg (ζ - z), sq_pos_of_pos ha]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    hderiv (hcont.intervalIntegrable _ _)]
  dsimp [F]
  simp only [zero_sub]
  rw [show (-z) ^ 2 = z ^ 2 by ring]

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

private theorem sign_affine_integral
    (b h : ℝ) (hh : 0 < h) :
    (∫ ζ in (0 : ℝ)..h, Real.sign (b - ζ)) =
      |b| - |b - h| := by
  by_cases hb0 : b ≤ 0
  · rw [sign_integral_negative 0 h b hh hb0,
      abs_of_nonpos hb0,
      abs_of_neg (by linarith : b - h < 0)]
    ring
  by_cases hhb : h ≤ b
  · rw [sign_integral_positive 0 h b hh hhb,
      abs_of_pos (lt_of_lt_of_le hh hhb),
      abs_of_nonneg (sub_nonneg.mpr hhb)]
    ring
  have hbpos : 0 < b := lt_of_not_ge hb0
  have hblt : b < h := lt_of_not_ge hhb
  have hleft := sign_integral_positive 0 b b hbpos le_rfl
  have hright := sign_integral_negative b h b hblt le_rfl
  have hsplit :=
    intervalIntegral.integral_add_adjacent_intervals
      (sign_intervalIntegrable b 0 b)
      (sign_intervalIntegrable b b h)
  rw [hleft, hright] at hsplit
  rw [← hsplit, abs_of_pos hbpos,
    abs_of_neg (sub_neg.mpr hblt)]
  ring

private theorem shifted_sign_integral (h z : ℝ) (hh : 0 < h) :
    (∫ ζ in (0 : ℝ)..h, Real.sign (ζ - z)) =
      |h - z| - |z| := by
  have hfun :
      (fun ζ : ℝ => Real.sign (ζ - z)) =
        fun ζ => -Real.sign (z - ζ) := by
    funext ζ
    rw [show ζ - z = -(z - ζ) by ring, Real.sign_neg]
  rw [hfun, intervalIntegral.integral_neg,
    sign_affine_integral z h hh]
  have habs : |z - h| = |h - z| := by
    rw [show z - h = -(h - z) by ring, abs_neg]
  rw [habs]
  ring

private def disk (a : ℝ) : Set (ℝ × ℝ) :=
  {q | q.1 ^ 2 + q.2 ^ 2 ≤ a ^ 2}

private theorem disk_closed (a : ℝ) : IsClosed (disk a) := by
  exact isClosed_le
    ((continuous_fst.pow 2).add (continuous_snd.pow 2))
    continuous_const

private theorem disk_compact (a : ℝ) (ha : 0 < a) :
    IsCompact (disk a) := by
  apply (isCompact_Icc :
    IsCompact (Set.Icc (-a, -a) (a, a))).of_isClosed_subset
      (disk_closed a)
  intro q hq
  change q.1 ^ 2 + q.2 ^ 2 ≤ a ^ 2 at hq
  have hx : q.1 ^ 2 ≤ a ^ 2 := by
    nlinarith [sq_nonneg q.2]
  have hy : q.2 ^ 2 ≤ a ^ 2 := by
    nlinarith [sq_nonneg q.1]
  exact ⟨
    ⟨by nlinarith [sq_nonneg (q.1 + a)],
      by nlinarith [sq_nonneg (q.2 + a)]⟩,
    ⟨by nlinarith [sq_nonneg (q.1 - a)],
      by nlinarith [sq_nonneg (q.2 - a)]⟩⟩

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
    (a d : ℝ) (ha : 0 < a)
    (p : ℝ × ℝ) (hp : p ∈ polarCoord.target) :
    p.1 • (disk a).indicator (planeNorm d) (polarCoord.symm p) =
      (Set.Iic a).indicator
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
      polarCoord.symm (r, θ) ∈ disk a ↔ r ≤ a := by
    rw [polarCoord_symm_apply]
    simp only [disk, Set.mem_setOf_eq]
    rw [htrig]
    exact sq_le_sq₀ hr.le ha.le
  simp only [Set.indicator, hmem, Set.mem_Iic, smul_eq_mul]
  by_cases hra : r ≤ a
  · simp only [hra, if_true, mul_one]
    rw [polarCoord_symm_apply]
    unfold planeNorm
    rw [htrig]
    ring
  · simp [hra]

private theorem planeNorm_integral (a d : ℝ)
    (ha : 0 < a) (hd : d ≠ 0) :
    (∫ q in disk a, planeNorm d q) =
      2 * Real.pi *
        (1 - |d| / Real.sqrt (a ^ 2 + d ^ 2)) := by
  have hp := integral_comp_polarCoord_symm
    ((disk a).indicator (planeNorm d))
  rw [integral_indicator (disk_closed a).measurableSet] at hp
  have hprod :
      (∫ p in polarCoord.target,
          p.1 • (disk a).indicator (planeNorm d)
            (polarCoord.symm p)) =
        (∫ r in Set.Ioi (0 : ℝ),
            (Set.Iic a).indicator
              (fun r =>
                r * |d| /
                  Real.rpow (r ^ 2 + d ^ 2)
                    ((3 : ℝ) / 2)) r) *
          ∫ θ in Set.Ioo (-Real.pi) Real.pi, (1 : ℝ) := by
    rw [polarCoord_target]
    calc
      _ = ∫ p in Set.Ioi (0 : ℝ) ×ˢ
          Set.Ioo (-Real.pi) Real.pi,
          (Set.Iic a).indicator
              (fun r =>
                r * |d| /
                  Real.rpow (r ^ 2 + d ^ 2)
                    ((3 : ℝ) / 2)) p.1 *
            (1 : ℝ) := by
        apply setIntegral_congr_fun
          (measurableSet_Ioi.prod measurableSet_Ioo)
        intro p hp'
        exact planeNorm_polar_pointwise a d ha p hp'
      _ = _ := by
        exact setIntegral_prod_mul
          (fun r : ℝ =>
            (Set.Iic a).indicator
              (fun r =>
                r * |d| /
                  Real.rpow (r ^ 2 + d ^ 2)
                    ((3 : ℝ) / 2)) r)
          (fun _θ : ℝ => (1 : ℝ))
          (Set.Ioi (0 : ℝ))
          (Set.Ioo (-Real.pi) Real.pi)
  have hrad :
      (∫ r in Set.Ioi (0 : ℝ),
          (Set.Iic a).indicator
            (fun r =>
              r * |d| /
                Real.rpow (r ^ 2 + d ^ 2)
                  ((3 : ℝ) / 2)) r) =
        ∫ r in (0 : ℝ)..a,
          r * |d| /
            Real.rpow (r ^ 2 + d ^ 2) ((3 : ℝ) / 2) := by
    rw [setIntegral_indicator measurableSet_Iic]
    have hinter :
        Set.Ioi (0 : ℝ) ∩ Set.Iic a =
          Set.Ioc (0 : ℝ) a := by
      ext r
      simp
    rw [hinter, intervalIntegral.integral_of_le ha.le]
  have hdabs : 0 < |d| := abs_pos.mpr hd
  have hsquared : |d| ^ 2 = d ^ 2 := sq_abs d
  have hkernel := radial_kernel_integral a |d| ha
  rw [Real.sign_of_pos hdabs, hsquared] at hkernel
  rw [hprod, hrad, angular_full, hkernel] at hp
  nlinarith [Real.pi_pos]

private theorem planeNorm_integral_le (a d : ℝ)
    (ha : 0 < a) (hd : d ≠ 0) :
    (∫ q in disk a, planeNorm d q) ≤ 2 * Real.pi := by
  rw [planeNorm_integral a d ha hd]
  have hratio :
      0 ≤ |d| / Real.sqrt (a ^ 2 + d ^ 2) :=
    div_nonneg (abs_nonneg d) (Real.sqrt_nonneg _)
  exact mul_le_of_le_one_right
    (by positivity : 0 ≤ 2 * Real.pi) (by linarith)

private def axialPlane (d : ℝ) (q : ℝ × ℝ) : ℝ :=
  d /
    Real.rpow (q.1 ^ 2 + q.2 ^ 2 + d ^ 2) ((3 : ℝ) / 2)

private def axialProduct (a h z : ℝ)
    (p : (ℝ × ℝ) × ℝ) : ℝ :=
  (disk a ×ˢ Set.Icc (0 : ℝ) h).indicator
    (fun p => axialPlane (p.2 - z) p.1) p

private theorem axialProduct_integrable
    (a h z : ℝ) (ha : 0 < a) (hh : 0 < h) :
    Integrable (axialProduct a h z) := by
  have hset : MeasurableSet
      (disk a ×ˢ Set.Icc (0 : ℝ) h) :=
    (disk_closed a).measurableSet.prod measurableSet_Icc
  have hraw : Measurable
      (fun p : (ℝ × ℝ) × ℝ =>
        axialPlane (p.2 - z) p.1) := by
    unfold axialPlane
    measurability
  have hmeas : AEStronglyMeasurable (axialProduct a h z) :=
    (hraw.indicator hset).aestronglyMeasurable
  rw [Measure.volume_eq_prod] at hmeas ⊢
  rw [integrable_prod_iff' hmeas]
  constructor
  · filter_upwards [volume.ae_ne z] with ζ hζz
    by_cases hζ : ζ ∈ Set.Icc (0 : ℝ) h
    · have hd : ζ - z ≠ 0 := sub_ne_zero.mpr hζz
      have hbase : Continuous
          (fun q : ℝ × ℝ =>
            q.1 ^ 2 + q.2 ^ 2 + (ζ - z) ^ 2) := by
        fun_prop
      have hden : Continuous
          (fun q : ℝ × ℝ =>
            Real.rpow
              (q.1 ^ 2 + q.2 ^ 2 + (ζ - z) ^ 2)
              ((3 : ℝ) / 2)) := by
        have heq :
            (fun q : ℝ × ℝ =>
              Real.rpow
                (q.1 ^ 2 + q.2 ^ 2 + (ζ - z) ^ 2)
                ((3 : ℝ) / 2)) =
              fun q =>
                (q.1 ^ 2 + q.2 ^ 2 + (ζ - z) ^ 2) *
                  Real.sqrt
                    (q.1 ^ 2 + q.2 ^ 2 + (ζ - z) ^ 2) := by
          funext q
          apply rpow_three_halves_eq
          nlinarith [sq_nonneg q.1, sq_nonneg q.2,
            sq_pos_of_ne_zero hd]
        rw [heq]
        exact hbase.mul (Real.continuous_sqrt.comp hbase)
      have hcont : Continuous (axialPlane (ζ - z)) := by
        unfold axialPlane
        apply Continuous.div continuous_const hden
        intro q
        exact ne_of_gt (Real.rpow_pos_of_pos
          (by nlinarith [sq_nonneg q.1, sq_nonneg q.2,
            sq_pos_of_ne_zero hd]) _)
      have hi : Integrable
          ((disk a).indicator (axialPlane (ζ - z))) :=
        (hcont.continuousOn.integrableOn_compact
          (disk_compact a ha)).integrable_indicator
            (disk_closed a).measurableSet
      convert hi using 1
      funext q
      by_cases hq : q ∈ disk a
      · have hp :
            (q, ζ) ∈ disk a ×ˢ Set.Icc (0 : ℝ) h :=
          ⟨hq, hζ⟩
        unfold axialProduct
        rw [Set.indicator_of_mem hp,
          Set.indicator_of_mem hq]
      · have hp :
            (q, ζ) ∉ disk a ×ˢ Set.Icc (0 : ℝ) h := by
          intro hp'
          exact hq hp'.1
        unfold axialProduct
        rw [Set.indicator_of_notMem hp,
          Set.indicator_of_notMem hq]
    · have hzero :
          (fun q : ℝ × ℝ => axialProduct a h z (q, ζ)) =
            fun _q => (0 : ℝ) := by
        funext q
        simp [axialProduct, hζ, Set.mem_prod]
      rw [hzero]
      exact integrable_zero _ _ _
  · let D : ℝ → ℝ :=
      (Set.Icc (0 : ℝ) h).indicator
        (fun _ζ => 2 * Real.pi)
    have hD : Integrable D := by
      have hc : IntegrableOn
          (fun _ζ : ℝ => 2 * Real.pi)
          (Set.Icc (0 : ℝ) h) :=
        continuous_const.continuousOn.integrableOn_compact
          isCompact_Icc
      exact hc.integrable_indicator measurableSet_Icc
    have hgmeas : AEStronglyMeasurable
        (fun ζ : ℝ =>
          ∫ q : ℝ × ℝ, ‖axialProduct a h z (q, ζ)‖) :=
      hmeas.norm.prod_swap.integral_prod_right'
    refine hD.mono' hgmeas ?_
    filter_upwards [volume.ae_ne z] with ζ hζz
    by_cases hζ : ζ ∈ Set.Icc (0 : ℝ) h
    · have hd : ζ - z ≠ 0 := sub_ne_zero.mpr hζz
      have heq :
          (∫ q : ℝ × ℝ,
              ‖axialProduct a h z (q, ζ)‖) =
            ∫ q in disk a, planeNorm (ζ - z) q := by
        rw [← integral_indicator
          (disk_closed a).measurableSet]
        apply integral_congr_ae
        filter_upwards [] with q
        by_cases hq : q ∈ disk a
        · rw [Set.indicator_of_mem hq]
          have hu :
              0 < q.1 ^ 2 + q.2 ^ 2 + (ζ - z) ^ 2 := by
            nlinarith [sq_nonneg q.1, sq_nonneg q.2,
              sq_pos_of_ne_zero hd]
          simp only [axialProduct, Set.indicator,
            Set.mem_prod, hq, hζ, and_self, if_true]
          unfold axialPlane planeNorm
          have hpw :
              0 < Real.rpow
                (q.1 ^ 2 + q.2 ^ 2 + (ζ - z) ^ 2)
                ((3 : ℝ) / 2) :=
            Real.rpow_pos_of_pos hu _
          rw [Real.norm_eq_abs, abs_div, abs_of_pos hpw]
        · rw [Set.indicator_of_notMem hq]
          simp [axialProduct, hq, Set.mem_prod]
      have hnonneg :
          0 ≤ ∫ q : ℝ × ℝ,
            ‖axialProduct a h z (q, ζ)‖ :=
        integral_nonneg fun _q => norm_nonneg _
      change
        (∫ q : ℝ × ℝ, |axialProduct a h z (q, ζ)|) =
          ∫ q in disk a, planeNorm (ζ - z) q at heq
      have hnonneg' :
          0 ≤ ∫ q : ℝ × ℝ,
            |axialProduct a h z (q, ζ)| := by
        simpa only [Real.norm_eq_abs] using hnonneg
      dsimp [D]
      rw [abs_of_nonneg hnonneg',
        Set.indicator_of_mem hζ, heq]
      exact planeNorm_integral_le a (ζ - z) ha hd
    · have hzero :
          (fun q : ℝ × ℝ => axialProduct a h z (q, ζ)) =
            fun _q => (0 : ℝ) := by
        funext q
        simp [axialProduct, hζ, Set.mem_prod]
      dsimp [D]
      rw [Set.indicator_of_notMem hζ]
      have hζq : ∀ q : ℝ × ℝ,
          axialProduct a h z (q, ζ) = 0 :=
        fun q => congrFun hzero q
      simp_rw [hζq]
      simp

private theorem axialPlane_polar_pointwise
    (a d : ℝ) (ha : 0 < a)
    (p : ℝ × ℝ) (hp : p ∈ polarCoord.target) :
    p.1 • (disk a).indicator (axialPlane d)
        (polarCoord.symm p) =
      (Set.Iic a).indicator
          (fun r =>
            r * d /
              Real.rpow (r ^ 2 + d ^ 2)
                ((3 : ℝ) / 2)) p.1 *
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
      polarCoord.symm (r, θ) ∈ disk a ↔ r ≤ a := by
    rw [polarCoord_symm_apply]
    simp only [disk, Set.mem_setOf_eq]
    rw [htrig]
    exact sq_le_sq₀ hr.le ha.le
  simp only [Set.indicator, hmem, Set.mem_Iic, smul_eq_mul]
  by_cases hra : r ≤ a
  · simp only [hra, if_true, mul_one]
    rw [polarCoord_symm_apply]
    unfold axialPlane
    rw [htrig]
    ring
  · simp [hra]

private theorem axialPlane_integral
    (a d : ℝ) (ha : 0 < a) :
    (∫ q in disk a, axialPlane d q) =
      2 * Real.pi *
        ∫ r in (0 : ℝ)..a,
          r * d /
            Real.rpow (r ^ 2 + d ^ 2) ((3 : ℝ) / 2) := by
  have hp := integral_comp_polarCoord_symm
    ((disk a).indicator (axialPlane d))
  rw [integral_indicator (disk_closed a).measurableSet] at hp
  have hprod :
      (∫ p in polarCoord.target,
          p.1 • (disk a).indicator (axialPlane d)
            (polarCoord.symm p)) =
        (∫ r in Set.Ioi (0 : ℝ),
            (Set.Iic a).indicator
              (fun r =>
                r * d /
                  Real.rpow (r ^ 2 + d ^ 2)
                    ((3 : ℝ) / 2)) r) *
          ∫ θ in Set.Ioo (-Real.pi) Real.pi, (1 : ℝ) := by
    rw [polarCoord_target]
    calc
      _ = ∫ p in Set.Ioi (0 : ℝ) ×ˢ
          Set.Ioo (-Real.pi) Real.pi,
          (Set.Iic a).indicator
              (fun r =>
                r * d /
                  Real.rpow (r ^ 2 + d ^ 2)
                    ((3 : ℝ) / 2)) p.1 *
            (1 : ℝ) := by
        apply setIntegral_congr_fun
          (measurableSet_Ioi.prod measurableSet_Ioo)
        intro p hp'
        exact axialPlane_polar_pointwise a d ha p hp'
      _ = _ := by
        exact setIntegral_prod_mul
          (fun r : ℝ =>
            (Set.Iic a).indicator
              (fun r =>
                r * d /
                  Real.rpow (r ^ 2 + d ^ 2)
                    ((3 : ℝ) / 2)) r)
          (fun _θ : ℝ => (1 : ℝ))
          (Set.Ioi (0 : ℝ))
          (Set.Ioo (-Real.pi) Real.pi)
  have hrad :
      (∫ r in Set.Ioi (0 : ℝ),
          (Set.Iic a).indicator
            (fun r =>
              r * d /
                Real.rpow (r ^ 2 + d ^ 2)
                  ((3 : ℝ) / 2)) r) =
        ∫ r in (0 : ℝ)..a,
          r * d /
            Real.rpow (r ^ 2 + d ^ 2) ((3 : ℝ) / 2) := by
    rw [setIntegral_indicator measurableSet_Iic]
    have hinter :
        Set.Ioi (0 : ℝ) ∩ Set.Iic a =
          Set.Ioc (0 : ℝ) a := by
      ext r
      simp
    rw [hinter, intervalIntegral.integral_of_le ha.le]
  rw [hprod, hrad, angular_full] at hp
  nlinarith [Real.pi_pos]

private theorem axialCylinder_integral
    (a h z : ℝ) (ha : 0 < a) (hh : 0 < h) :
    (∫ p in cylinder a h,
        (p.2.2 - z) /
          Real.rpow (distanceSquared z p) ((3 : ℝ) / 2)) =
      2 * Real.pi *
        ∫ ζ in (0 : ℝ)..h,
          ∫ r in (0 : ℝ)..a,
            r * (ζ - z) /
              Real.rpow (r ^ 2 + (ζ - z) ^ 2)
                ((3 : ℝ) / 2) := by
  let G : Point3 → ℝ := fun p =>
    (p.2.2 - z) /
      Real.rpow (distanceSquared z p) ((3 : ℝ) / 2)
  let e :=
    (MeasurableEquiv.prodAssoc :
      ((ℝ × ℝ) × ℝ) ≃ᵐ Point3)
  have hcyl := cylinder_measurable a h
  have hind :
      (fun q : (ℝ × ℝ) × ℝ =>
        (cylinder a h).indicator G (e q)) =
        axialProduct a h z := by
    funext q
    rcases q with ⟨⟨x, y⟩, ζ⟩
    have hmem :
        e ((x, y), ζ) ∈ cylinder a h ↔
          ((x, y), ζ) ∈
            disk a ×ˢ Set.Icc (0 : ℝ) h := by
      change
        (x ^ 2 + y ^ 2 ≤ a ^ 2 ∧
          0 ≤ ζ ∧ ζ ≤ h) ↔
            ((x, y) ∈ disk a ∧ ζ ∈ Set.Icc (0 : ℝ) h)
      simp only [disk, Set.mem_setOf_eq, Set.mem_Icc]
    by_cases hp :
        ((x, y), ζ) ∈ disk a ×ˢ Set.Icc (0 : ℝ) h
    · have hecyl : e ((x, y), ζ) ∈ cylinder a h :=
        hmem.mpr hp
      rw [Set.indicator_of_mem hecyl]
      unfold axialProduct
      rw [Set.indicator_of_mem hp]
      dsimp [G, e]
      unfold axialPlane distanceSquared
      change
        (ζ - z) /
            Real.rpow (x ^ 2 + y ^ 2 + (ζ - z) ^ 2)
              ((3 : ℝ) / 2) =
          (ζ - z) /
            Real.rpow (x ^ 2 + y ^ 2 + (ζ - z) ^ 2)
              ((3 : ℝ) / 2)
      rfl
    · have hecyl : e ((x, y), ζ) ∉ cylinder a h := by
        intro he
        exact hp (hmem.mp he)
      rw [Set.indicator_of_notMem hecyl]
      unfold axialProduct
      rw [Set.indicator_of_notMem hp]
  have hreassoc :
      (∫ q : (ℝ × ℝ) × ℝ,
          (cylinder a h).indicator G (e q)) =
        ∫ p : Point3, (cylinder a h).indicator G p :=
    volume_preserving_prodAssoc.integral_comp'
      ((cylinder a h).indicator G)
  rw [hind] at hreassoc
  rw [← integral_indicator hcyl]
  change (∫ p : Point3,
    (cylinder a h).indicator G p) = _
  rw [← hreassoc]
  have hFubini :
      (∫ q : (ℝ × ℝ) × ℝ, axialProduct a h z q) =
        ∫ ζ : ℝ,
          ∫ q : ℝ × ℝ, axialProduct a h z (q, ζ) := by
    exact integral_prod_symm
      (axialProduct a h z)
      (axialProduct_integrable a h z ha hh)
  rw [hFubini]
  have hsection (ζ : ℝ) :
      (∫ q : ℝ × ℝ, axialProduct a h z (q, ζ)) =
        (Set.Icc (0 : ℝ) h).indicator
          (fun ζ =>
            2 * Real.pi *
              ∫ r in (0 : ℝ)..a,
                r * (ζ - z) /
                  Real.rpow (r ^ 2 + (ζ - z) ^ 2)
                    ((3 : ℝ) / 2)) ζ := by
    by_cases hζ : ζ ∈ Set.Icc (0 : ℝ) h
    · rw [Set.indicator_of_mem hζ]
      have hpoint :
          (fun q : ℝ × ℝ =>
            (disk a).indicator (axialPlane (ζ - z)) q) =
            fun q : ℝ × ℝ => axialProduct a h z (q, ζ) := by
        funext q
        by_cases hq : q ∈ disk a
        · have hp :
              (q, ζ) ∈ disk a ×ˢ Set.Icc (0 : ℝ) h :=
            ⟨hq, hζ⟩
          simp [axialProduct, hq, hp]
        · have hp :
              (q, ζ) ∉ disk a ×ˢ Set.Icc (0 : ℝ) h := by
            intro hp'
            exact hq hp'.1
          simp [axialProduct, hq, hp]
      rw [← hpoint,
        integral_indicator (disk_closed a).measurableSet,
        axialPlane_integral a (ζ - z) ha]
    · rw [Set.indicator_of_notMem hζ]
      have hzero :
          (fun q : ℝ × ℝ => axialProduct a h z (q, ζ)) =
            fun _q => (0 : ℝ) := by
        funext q
        simp [axialProduct, hζ, Set.mem_prod]
      rw [hzero]
      simp
  simp_rw [hsection]
  rw [integral_indicator measurableSet_Icc,
    integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hh.le]
  rw [intervalIntegral.integral_const_mul]

private theorem radial_abs_integral
    (a d : ℝ) (ha : 0 < a) (hd : d ≠ 0) :
    (∫ r in (0 : ℝ)..a,
        r * |d| /
          Real.rpow (r ^ 2 + d ^ 2) ((3 : ℝ) / 2)) =
      1 - |d| / Real.sqrt (a ^ 2 + d ^ 2) := by
  have hdabs : 0 < |d| := abs_pos.mpr hd
  have hsquared : |d| ^ 2 = d ^ 2 := sq_abs d
  have hkernel := radial_kernel_integral a |d| ha
  rw [Real.sign_of_pos hdabs, hsquared] at hkernel
  exact hkernel

private def radialProduct (a h z : ℝ) (p : ℝ × ℝ) : ℝ :=
  (Set.Icc (0 : ℝ) a ×ˢ Set.Icc (0 : ℝ) h).indicator
    (fun p =>
      p.1 * (p.2 - z) /
        Real.rpow (p.1 ^ 2 + (p.2 - z) ^ 2)
          ((3 : ℝ) / 2)) p

private theorem radialProduct_integrable
    (a h z : ℝ) (ha : 0 < a) (hh : 0 < h) :
    Integrable (radialProduct a h z) := by
  have hset : MeasurableSet
      (Set.Icc (0 : ℝ) a ×ˢ Set.Icc (0 : ℝ) h) :=
    measurableSet_Icc.prod measurableSet_Icc
  have hraw : Measurable
      (fun p : ℝ × ℝ =>
        p.1 * (p.2 - z) /
          Real.rpow (p.1 ^ 2 + (p.2 - z) ^ 2)
            ((3 : ℝ) / 2)) := by
    measurability
  have hmeas : AEStronglyMeasurable (radialProduct a h z) :=
    (hraw.indicator hset).aestronglyMeasurable
  rw [Measure.volume_eq_prod] at hmeas ⊢
  rw [integrable_prod_iff' hmeas]
  constructor
  · filter_upwards [volume.ae_ne z] with ζ hζz
    by_cases hζ : ζ ∈ Set.Icc (0 : ℝ) h
    · have hd : ζ - z ≠ 0 := sub_ne_zero.mpr hζz
      have hbase : Continuous
          (fun r : ℝ => r ^ 2 + (ζ - z) ^ 2) :=
        (continuous_id.pow 2).add continuous_const
      have hden : Continuous
          (fun r : ℝ =>
            Real.rpow (r ^ 2 + (ζ - z) ^ 2)
              ((3 : ℝ) / 2)) := by
        have heq :
            (fun r : ℝ =>
              Real.rpow (r ^ 2 + (ζ - z) ^ 2)
                ((3 : ℝ) / 2)) =
              fun r =>
                (r ^ 2 + (ζ - z) ^ 2) *
                  Real.sqrt (r ^ 2 + (ζ - z) ^ 2) := by
          funext r
          apply rpow_three_halves_eq
          nlinarith [sq_nonneg r, sq_pos_of_ne_zero hd]
        rw [heq]
        exact hbase.mul (Real.continuous_sqrt.comp hbase)
      have hcont : Continuous
          (fun r : ℝ =>
            r * (ζ - z) /
              Real.rpow (r ^ 2 + (ζ - z) ^ 2)
                ((3 : ℝ) / 2)) := by
        apply Continuous.div
        · fun_prop
        · exact hden
        · intro r
          exact ne_of_gt (Real.rpow_pos_of_pos
            (by nlinarith [sq_nonneg r,
              sq_pos_of_ne_zero hd]) _)
      have hi : Integrable
          ((Set.Icc (0 : ℝ) a).indicator
            (fun r =>
              r * (ζ - z) /
                Real.rpow (r ^ 2 + (ζ - z) ^ 2)
                  ((3 : ℝ) / 2))) :=
        hcont.integrableOn_Icc.integrable_indicator
          measurableSet_Icc
      convert hi using 1
      funext r
      by_cases hr : r ∈ Set.Icc (0 : ℝ) a
      · have hp :
            (r, ζ) ∈
              Set.Icc (0 : ℝ) a ×ˢ Set.Icc (0 : ℝ) h :=
          ⟨hr, hζ⟩
        unfold radialProduct
        rw [Set.indicator_of_mem hp,
          Set.indicator_of_mem hr]
      · have hp :
            (r, ζ) ∉
              Set.Icc (0 : ℝ) a ×ˢ Set.Icc (0 : ℝ) h := by
          intro hp'
          exact hr hp'.1
        unfold radialProduct
        rw [Set.indicator_of_notMem hp,
          Set.indicator_of_notMem hr]
    · have hzero :
          (fun r : ℝ => radialProduct a h z (r, ζ)) =
            fun _r => (0 : ℝ) := by
        funext r
        unfold radialProduct
        rw [Set.indicator_of_notMem]
        intro hp
        exact hζ hp.2
      rw [hzero]
      exact integrable_zero _ _ _
  · let D : ℝ → ℝ :=
      (Set.Icc (0 : ℝ) h).indicator (fun _ζ => (1 : ℝ))
    have hD : Integrable D := by
      exact
        (continuous_const.integrableOn_Icc).integrable_indicator
          measurableSet_Icc
    have hgmeas : AEStronglyMeasurable
        (fun ζ : ℝ =>
          ∫ r : ℝ, ‖radialProduct a h z (r, ζ)‖) :=
      hmeas.norm.prod_swap.integral_prod_right'
    refine hD.mono' hgmeas ?_
    filter_upwards [volume.ae_ne z] with ζ hζz
    by_cases hζ : ζ ∈ Set.Icc (0 : ℝ) h
    · have hd : ζ - z ≠ 0 := sub_ne_zero.mpr hζz
      have heq :
          (∫ r : ℝ, ‖radialProduct a h z (r, ζ)‖) =
            ∫ r in (0 : ℝ)..a,
              r * |ζ - z| /
                Real.rpow (r ^ 2 + (ζ - z) ^ 2)
                  ((3 : ℝ) / 2) := by
        rw [intervalIntegral.integral_of_le ha.le]
        rw [← integral_indicator measurableSet_Ioc]
        apply integral_congr_ae
        filter_upwards [volume.ae_ne (0 : ℝ)] with r hrzero
        by_cases hr : r ∈ Set.Ioc (0 : ℝ) a
        · have hrIcc : r ∈ Set.Icc (0 : ℝ) a :=
            ⟨hr.1.le, hr.2⟩
          have hp :
              (r, ζ) ∈
                Set.Icc (0 : ℝ) a ×ˢ Set.Icc (0 : ℝ) h :=
            ⟨hrIcc, hζ⟩
          rw [Set.indicator_of_mem hr,
            radialProduct, Set.indicator_of_mem hp]
          have hu : 0 < r ^ 2 + (ζ - z) ^ 2 := by
            nlinarith [sq_nonneg r, sq_pos_of_ne_zero hd]
          have hpw :
              0 < Real.rpow (r ^ 2 + (ζ - z) ^ 2)
                ((3 : ℝ) / 2) :=
            Real.rpow_pos_of_pos hu _
          change
            |r * (ζ - z) /
                Real.rpow (r ^ 2 + (ζ - z) ^ 2)
                  ((3 : ℝ) / 2)| =
              r * |ζ - z| /
                Real.rpow (r ^ 2 + (ζ - z) ^ 2)
                  ((3 : ℝ) / 2)
          rw [abs_div, abs_of_pos hpw,
            abs_mul, abs_of_pos hr.1]
        · rw [Set.indicator_of_notMem hr]
          have hp :
              (r, ζ) ∉
                Set.Icc (0 : ℝ) a ×ˢ Set.Icc (0 : ℝ) h := by
            intro hp'
            apply hr
            exact ⟨lt_of_le_of_ne hp'.1.1 (Ne.symm hrzero),
              hp'.1.2⟩
          rw [radialProduct, Set.indicator_of_notMem hp]
          simp
      have hval := radial_abs_integral a (ζ - z) ha hd
      have hratio :
          0 ≤ |ζ - z| /
            Real.sqrt (a ^ 2 + (ζ - z) ^ 2) :=
        div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
      have hnonneg :
          0 ≤ ∫ r : ℝ, ‖radialProduct a h z (r, ζ)‖ :=
        integral_nonneg fun _ => norm_nonneg _
      have hnonneg' :
          0 ≤ ∫ r : ℝ, |radialProduct a h z (r, ζ)| := by
        simpa only [Real.norm_eq_abs] using hnonneg
      have heq' :
          (∫ r : ℝ, |radialProduct a h z (r, ζ)|) =
            ∫ r in (0 : ℝ)..a,
              r * |ζ - z| /
                Real.rpow (r ^ 2 + (ζ - z) ^ 2)
                  ((3 : ℝ) / 2) := by
        simpa only [Real.norm_eq_abs] using heq
      dsimp [D]
      rw [Set.indicator_of_mem hζ,
        abs_of_nonneg hnonneg', heq', hval]
      linarith
    · have hzero :
          (fun r : ℝ => radialProduct a h z (r, ζ)) =
            fun _r => (0 : ℝ) := by
        funext r
        unfold radialProduct
        rw [Set.indicator_of_notMem]
        intro hp
        exact hζ hp.2
      dsimp [D]
      rw [Set.indicator_of_notMem hζ]
      have hζr : ∀ r : ℝ,
          radialProduct a h z (r, ζ) = 0 :=
        fun r => congrFun hzero r
      simp_rw [hζr]
      simp

private theorem radial_iterated_swap
    (a h z : ℝ) (ha : 0 < a) (hh : 0 < h) :
    (∫ ζ in (0 : ℝ)..h,
        ∫ r in (0 : ℝ)..a,
          r * (ζ - z) /
            Real.rpow (r ^ 2 + (ζ - z) ^ 2)
              ((3 : ℝ) / 2)) =
      ∫ r in (0 : ℝ)..a,
        ∫ ζ in (0 : ℝ)..h,
          (ζ - z) * r /
            Real.rpow (r ^ 2 + (ζ - z) ^ 2)
              ((3 : ℝ) / 2) := by
  let K : ℝ × ℝ → ℝ := fun p =>
    p.1 * (p.2 - z) /
      Real.rpow (p.1 ^ 2 + (p.2 - z) ^ 2)
        ((3 : ℝ) / 2)
  have hi := radialProduct_integrable a h z ha hh
  have hset : MeasurableSet
      (Set.Icc (0 : ℝ) a ×ˢ Set.Icc (0 : ℝ) h) :=
    measurableSet_Icc.prod measurableSet_Icc
  have hiIcc : IntegrableOn K
      (Set.Icc (0 : ℝ) a ×ˢ Set.Icc (0 : ℝ) h) := by
    have heq :
        radialProduct a h z =
          (Set.Icc (0 : ℝ) a ×ˢ Set.Icc (0 : ℝ) h).indicator K :=
      rfl
    rw [heq, integrable_indicator_iff hset] at hi
    exact hi
  have hiIoc : IntegrableOn K
      (Set.Ioc (0 : ℝ) a ×ˢ Set.Ioc (0 : ℝ) h)
      (volume.prod volume) := by
    have hsuba :
        Set.Ioc (0 : ℝ) a ⊆ Set.Icc (0 : ℝ) a := by
      intro x hx
      exact ⟨hx.1.le, hx.2⟩
    have hsubh :
        Set.Ioc (0 : ℝ) h ⊆ Set.Icc (0 : ℝ) h := by
      intro x hx
      exact ⟨hx.1.le, hx.2⟩
    have hi' := hiIcc.mono_set
      (Set.prod_mono hsuba hsubh)
    simpa only [Measure.volume_eq_prod] using hi'
  have hp :=
    MeasureTheory.setIntegral_prod
      (μ := (volume : Measure ℝ))
      (ν := (volume : Measure ℝ)) K hiIoc
  have hps :=
    MeasureTheory.setIntegral_prod
      (μ := (volume : Measure ℝ))
      (ν := (volume : Measure ℝ))
      (K ∘ Prod.swap) hiIoc.swap
  have hswap :=
    MeasureTheory.setIntegral_prod_swap
      (μ := (volume : Measure ℝ))
      (ν := (volume : Measure ℝ))
      (Set.Ioc (0 : ℝ) a) (Set.Ioc (0 : ℝ) h) K
  simp_rw [intervalIntegral.integral_of_le ha.le,
    intervalIntegral.integral_of_le hh.le]
  have hpoint (r ζ : ℝ) :
      (ζ - z) * r /
          Real.rpow (r ^ 2 + (ζ - z) ^ 2) ((3 : ℝ) / 2) =
        r * (ζ - z) /
          Real.rpow (r ^ 2 + (ζ - z) ^ 2) ((3 : ℝ) / 2) := by
    ring
  simp_rw [hpoint]
  change
    (∫ ζ in Set.Ioc (0 : ℝ) h,
        ∫ r in Set.Ioc (0 : ℝ) a,
          (K ∘ Prod.swap) (ζ, r)) =
      ∫ r in Set.Ioc (0 : ℝ) a,
        ∫ ζ in Set.Ioc (0 : ℝ) h, K (r, ζ)
  rw [← hps, ← hp]
  exact hswap

private theorem axial_inner_integral (r h z : ℝ) :
    (∫ ζ in (0 : ℝ)..h,
        (ζ - z) * r /
          Real.rpow (r ^ 2 + (ζ - z) ^ 2)
            ((3 : ℝ) / 2)) =
      r *
        (1 / Real.sqrt (r ^ 2 + z ^ 2) -
          1 / Real.sqrt (r ^ 2 + (h - z) ^ 2)) := by
  by_cases hr : r = 0
  · subst r
    simp
  let F : ℝ → ℝ := fun ζ =>
    -r / Real.sqrt (r ^ 2 + (ζ - z) ^ 2)
  have hderiv : ∀ ζ ∈ Set.uIcc (0 : ℝ) h,
      HasDerivAt F
        ((ζ - z) * r /
          Real.rpow (r ^ 2 + (ζ - z) ^ 2)
            ((3 : ℝ) / 2)) ζ := by
    intro ζ _
    have hu : 0 < r ^ 2 + (ζ - z) ^ 2 := by
      nlinarith [sq_pos_of_ne_zero hr, sq_nonneg (ζ - z)]
    have hlin :
        HasDerivAt (fun x : ℝ => x - z) 1 ζ := by
      convert (hasDerivAt_id ζ).sub_const z using 1
    have hinner :
        HasDerivAt (fun x : ℝ => r ^ 2 + (x - z) ^ 2)
          (2 * (ζ - z)) ζ := by
      convert (hasDerivAt_const ζ (r ^ 2)).add (hlin.pow 2)
        using 1 <;> ring
    have hsqrt :
        HasDerivAt
          (fun x : ℝ => Real.sqrt (r ^ 2 + (x - z) ^ 2))
          (1 / (2 * Real.sqrt (r ^ 2 + (ζ - z) ^ 2)) *
            (2 * (ζ - z))) ζ := by
      simpa only [Function.comp_apply] using
        (Real.hasDerivAt_sqrt hu.ne').comp ζ hinner
    have hsqrtne :
        Real.sqrt (r ^ 2 + (ζ - z) ^ 2) ≠ 0 :=
      Real.sqrt_ne_zero'.mpr hu
    have hsquare :
        Real.sqrt (r ^ 2 + (ζ - z) ^ 2) ^ 2 =
          r ^ 2 + (ζ - z) ^ 2 :=
      Real.sq_sqrt hu.le
    have hrpow :
        Real.rpow (r ^ 2 + (ζ - z) ^ 2) ((3 : ℝ) / 2) =
          (r ^ 2 + (ζ - z) ^ 2) *
            Real.sqrt (r ^ 2 + (ζ - z) ^ 2) :=
      rpow_three_halves_eq _ hu
    dsimp [F]
    convert (hasDerivAt_const ζ (-r)).div hsqrt hsqrtne using 1
    change
      (ζ - z) * r /
          Real.rpow (r ^ 2 + (ζ - z) ^ 2)
            ((3 : ℝ) / 2) =
        (0 * Real.sqrt (r ^ 2 + (ζ - z) ^ 2) -
          -r *
            (1 / (2 * Real.sqrt (r ^ 2 + (ζ - z) ^ 2)) *
              (2 * (ζ - z)))) /
            Real.sqrt (r ^ 2 + (ζ - z) ^ 2) ^ 2
    rw [hrpow]
    field_simp [hsqrtne]
    rw [hsquare]
    ring
  have hbase : Continuous
      (fun ζ : ℝ => r ^ 2 + (ζ - z) ^ 2) := by
    fun_prop
  have hden : Continuous
      (fun ζ : ℝ =>
        Real.rpow (r ^ 2 + (ζ - z) ^ 2)
          ((3 : ℝ) / 2)) := by
    have heq :
        (fun ζ : ℝ =>
          Real.rpow (r ^ 2 + (ζ - z) ^ 2)
            ((3 : ℝ) / 2)) =
          fun ζ =>
            (r ^ 2 + (ζ - z) ^ 2) *
              Real.sqrt (r ^ 2 + (ζ - z) ^ 2) := by
      funext ζ
      apply rpow_three_halves_eq
      nlinarith [sq_pos_of_ne_zero hr, sq_nonneg (ζ - z)]
    rw [heq]
    exact hbase.mul (Real.continuous_sqrt.comp hbase)
  have hcont : Continuous
      (fun ζ : ℝ =>
        (ζ - z) * r /
          Real.rpow (r ^ 2 + (ζ - z) ^ 2)
            ((3 : ℝ) / 2)) := by
    apply Continuous.div
    · fun_prop
    · exact hden
    · intro ζ
      exact ne_of_gt (Real.rpow_pos_of_pos
        (by nlinarith [sq_pos_of_ne_zero hr,
          sq_nonneg (ζ - z)]) _)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    hderiv (hcont.intervalIntegrable _ _)]
  dsimp [F]
  simp only [zero_sub]
  rw [show (-z) ^ 2 = z ^ 2 by ring]
  ring

private theorem radialSqrtKernelIntegrable
    (s d : ℝ) (hs : 0 ≤ s) :
    IntegrableOn
      (fun r : ℝ => r / Real.sqrt (r ^ 2 + d ^ 2))
      (Set.Ioc 0 s) := by
  by_cases hd : d = 0
  · subst d
    have hconst : Set.EqOn
        (fun r : ℝ => r / Real.sqrt (r ^ 2 + 0 ^ 2))
        (fun _ : ℝ => 1) (Set.Ioc 0 s) := by
      intro r hr
      dsimp
      rw [show (0 : ℝ) ^ 2 = 0 by norm_num, add_zero,
        Real.sqrt_sq_eq_abs, abs_of_pos hr.1,
        div_self (ne_of_gt hr.1)]
    exact
      (integrableOn_const (C := (1 : ℝ))
        measure_Ioc_lt_top.ne).congr_fun
          hconst.symm measurableSet_Ioc
  · have hpos (r : ℝ) : 0 < r ^ 2 + d ^ 2 := by
      nlinarith [sq_nonneg r, sq_pos_of_ne_zero hd]
    have hcont : Continuous
        (fun r : ℝ => r / Real.sqrt (r ^ 2 + d ^ 2)) := by
      apply Continuous.div continuous_id
        (Real.continuous_sqrt.comp
          ((continuous_id.pow 2).add (continuous_const.pow 2)))
      intro r
      exact ne_of_gt (Real.sqrt_pos.2 (hpos r))
    exact hcont.integrableOn_Ioc

private theorem radialSqrtKernelIntegral
    (s d : ℝ) (hs : 0 ≤ s) :
    (∫ r in (0 : ℝ)..s,
        r / Real.sqrt (r ^ 2 + d ^ 2)) =
      Real.sqrt (s ^ 2 + d ^ 2) - |d| := by
  by_cases hd : d = 0
  · subst d
    rw [intervalIntegral.integral_of_le hs]
    calc
      (∫ r in Set.Ioc 0 s,
          r / Real.sqrt (r ^ 2 + 0 ^ 2)) =
          ∫ _r in Set.Ioc 0 s, (1 : ℝ) := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro r hr
        dsimp
        rw [show (0 : ℝ) ^ 2 = 0 by norm_num, add_zero,
          Real.sqrt_sq_eq_abs, abs_of_pos hr.1,
          div_self (ne_of_gt hr.1)]
      _ = s := by simp [hs]
      _ = Real.sqrt (s ^ 2 + 0 ^ 2) - |(0 : ℝ)| := by
        rw [zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero,
          Real.sqrt_sq_eq_abs, abs_of_nonneg hs]
        simp
  · have hpos (r : ℝ) : 0 < r ^ 2 + d ^ 2 := by
      nlinarith [sq_nonneg r, sq_pos_of_ne_zero hd]
    have hcontF : Continuous
        (fun r : ℝ => Real.sqrt (r ^ 2 + d ^ 2)) :=
      Real.continuous_sqrt.comp
        ((continuous_id.pow 2).add (continuous_const.pow 2))
    have hcontf : Continuous
        (fun r : ℝ => r / Real.sqrt (r ^ 2 + d ^ 2)) := by
      apply Continuous.div continuous_id hcontF
      intro r
      exact ne_of_gt (Real.sqrt_pos.2 (hpos r))
    have hder : ∀ r ∈ Set.Ioo 0 s,
        HasDerivAt
          (fun x : ℝ => Real.sqrt (x ^ 2 + d ^ 2))
          (r / Real.sqrt (r ^ 2 + d ^ 2)) r := by
      intro r _
      have hinner :
          HasDerivAt (fun x : ℝ => x ^ 2 + d ^ 2) (2 * r) r := by
        convert ((hasDerivAt_id r).pow 2).add_const (d ^ 2)
          using 1 <;> simp [id] <;> ring
      have hsqrt := hinner.sqrt (ne_of_gt (hpos r))
      convert hsqrt using 1
      field_simp [ne_of_gt (Real.sqrt_pos.2 (hpos r))]
    have hFTC :
        (∫ r in (0 : ℝ)..s,
          r / Real.sqrt (r ^ 2 + d ^ 2)) =
          Real.sqrt (s ^ 2 + d ^ 2) -
            Real.sqrt (0 ^ 2 + d ^ 2) := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hs
        hcontF.continuousOn hder
      exact hcontf.intervalIntegrable 0 s
    rw [hFTC, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      zero_add, Real.sqrt_sq_eq_abs]

theorem gap3 (a h k ρ₀ z : ℝ) (ha : 0 < a) (hh : 0 < h) :
    forceZ a h k ρ₀ z =
      k * ρ₀ *
        ∫ φ in (0 : ℝ)..2 * Real.pi,
          ∫ r in (0 : ℝ)..a,
            ∫ ζ in (0 : ℝ)..h,
              (ζ - z) * r /
                Real.rpow (r ^ 2 + (ζ - z) ^ 2)
                  ((3 : ℝ) / 2) := by
  unfold forceZ
  rw [axialCylinder_integral a h z ha hh,
    radial_iterated_swap a h z ha hh]
  rw [intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul]

theorem gap4 (a h k ρ₀ z : ℝ) (ha : 0 < a) (hh : 0 < h) :
    forceZ a h k ρ₀ z =
      2 * Real.pi * k * ρ₀ *
        ∫ r in (0 : ℝ)..a,
          r *
            (1 / Real.sqrt (r ^ 2 + z ^ 2) -
              1 / Real.sqrt (r ^ 2 + (h - z) ^ 2)) := by
  rw [gap3 a h k ρ₀ z ha hh]
  simp_rw [axial_inner_integral]
  rw [intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul]
  ring

theorem gap5 (a h k ρ₀ z : ℝ) (ha : 0 < a) (hh : 0 < h) :
    forceZ a h k ρ₀ z =
      2 * Real.pi * k * ρ₀ *
        (Real.sqrt (a ^ 2 + z ^ 2) -
          Real.sqrt (a ^ 2 + (h - z) ^ 2) -
            |z| + |h - z|) := by
  rw [gap4 a h k ρ₀ z ha hh]
  have hi₁ : IntervalIntegrable
      (fun r : ℝ => r / Real.sqrt (r ^ 2 + z ^ 2))
      volume 0 a := by
    rw [intervalIntegrable_iff]
    simpa only [Set.uIoc_of_le ha.le] using
      radialSqrtKernelIntegrable a z ha.le
  have hi₂ : IntervalIntegrable
      (fun r : ℝ =>
        r / Real.sqrt (r ^ 2 + (h - z) ^ 2))
      volume 0 a := by
    rw [intervalIntegrable_iff]
    simpa only [Set.uIoc_of_le ha.le] using
      radialSqrtKernelIntegrable a (h - z) ha.le
  have hsep :
      (∫ r in (0 : ℝ)..a,
          r *
            (1 / Real.sqrt (r ^ 2 + z ^ 2) -
              1 / Real.sqrt (r ^ 2 + (h - z) ^ 2))) =
        (∫ r in (0 : ℝ)..a,
          r / Real.sqrt (r ^ 2 + z ^ 2)) -
        ∫ r in (0 : ℝ)..a,
          r / Real.sqrt (r ^ 2 + (h - z) ^ 2) := by
    rw [← intervalIntegral.integral_sub hi₁ hi₂]
    apply intervalIntegral.integral_congr
    intro r _
    ring
  rw [hsep, radialSqrtKernelIntegral a z ha.le,
    radialSqrtKernelIntegral a (h - z) ha.le]
  ring

private theorem sqrt_sub_strictAnti
    (a u v : ℝ) (ha : 0 < a)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u < v) :
    Real.sqrt (a ^ 2 + v ^ 2) - v <
      Real.sqrt (a ^ 2 + u ^ 2) - u := by
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  have huv2 : u ^ 2 < v ^ 2 :=
    (sq_lt_sq₀ hu hv).2 huv
  have hargu : 0 < a ^ 2 + u ^ 2 := by positivity
  have hargv : 0 < a ^ 2 + v ^ 2 := by positivity
  have hslt :
      Real.sqrt (a ^ 2 + u ^ 2) <
        Real.sqrt (a ^ 2 + v ^ 2) :=
    Real.sqrt_lt_sqrt hargu.le (by linarith)
  have hsu :
      0 < Real.sqrt (a ^ 2 + u ^ 2) :=
    Real.sqrt_pos.2 hargu
  have hsv :
      0 < Real.sqrt (a ^ 2 + v ^ 2) :=
    Real.sqrt_pos.2 hargv
  have hdu :
      0 < Real.sqrt (a ^ 2 + u ^ 2) + u := by
    positivity
  have hdv :
      0 < Real.sqrt (a ^ 2 + v ^ 2) + v := by
    positivity
  have hden :
      Real.sqrt (a ^ 2 + u ^ 2) + u <
        Real.sqrt (a ^ 2 + v ^ 2) + v :=
    add_lt_add hslt huv
  have hsqU :
      Real.sqrt (a ^ 2 + u ^ 2) ^ 2 =
        a ^ 2 + u ^ 2 :=
    Real.sq_sqrt hargu.le
  have hsqV :
      Real.sqrt (a ^ 2 + v ^ 2) ^ 2 =
        a ^ 2 + v ^ 2 :=
    Real.sq_sqrt hargv.le
  have hidU :
      Real.sqrt (a ^ 2 + u ^ 2) - u =
        a ^ 2 /
          (Real.sqrt (a ^ 2 + u ^ 2) + u) := by
    field_simp [hdu.ne']
    nlinarith
  have hidV :
      Real.sqrt (a ^ 2 + v ^ 2) - v =
        a ^ 2 /
          (Real.sqrt (a ^ 2 + v ^ 2) + v) := by
    field_simp [hdv.ne']
    nlinarith
  rw [hidU, hidV]
  exact div_lt_div_of_pos_left ha2 hdu hden

private theorem abs_lt_abs_hsub_of_lt_half
    (h z : ℝ) (hh : 0 < h) (hz : z < h / 2) :
    |z| < |h - z| := by
  by_cases hzneg : z < 0
  · rw [abs_of_neg hzneg,
      abs_of_pos (by linarith : 0 < h - z)]
    linarith
  · have hznonneg : 0 ≤ z := le_of_not_gt hzneg
    have hhpos : 0 < h - z := by linarith
    rw [abs_of_nonneg hznonneg, abs_of_pos hhpos]
    linarith

private theorem abs_hsub_lt_abs_of_half_lt
    (h z : ℝ) (hh : 0 < h) (hz : h / 2 < z) :
    |h - z| < |z| := by
  have hzpos : 0 < z := by linarith
  by_cases hle : h ≤ z
  · rw [abs_of_nonpos (sub_nonpos.mpr hle),
      abs_of_pos hzpos]
    linarith
  · have hzlt : z < h := lt_of_not_ge hle
    rw [abs_of_pos (sub_pos.mpr hzlt),
      abs_of_pos hzpos]
    linarith

theorem gap6 (a h k ρ₀ z : ℝ)
    (ha : 0 < a) (hh : 0 < h) (hk : 0 < k) (hρ : 0 < ρ₀)
    (hz : z < h / 2) :
    0 < forceZ a h k ρ₀ z := by
  rw [gap5 a h k ρ₀ z ha hh]
  have habs :
      |z| < |h - z| :=
    abs_lt_abs_hsub_of_lt_half h z hh hz
  have hq :=
    sqrt_sub_strictAnti a |z| |h - z| ha
      (abs_nonneg z) (abs_nonneg (h - z)) habs
  have hbracket :
      0 <
        Real.sqrt (a ^ 2 + z ^ 2) -
          Real.sqrt (a ^ 2 + (h - z) ^ 2) -
            |z| + |h - z| := by
    rw [← sq_abs z, ← sq_abs (h - z)]
    linarith
  positivity

theorem gap7 (a h k ρ₀ z : ℝ)
    (ha : 0 < a) (hh : 0 < h) (hk : 0 < k) (hρ : 0 < ρ₀)
    (hz : h / 2 < z) :
    forceZ a h k ρ₀ z < 0 := by
  rw [gap5 a h k ρ₀ z ha hh]
  have habs :
      |h - z| < |z| :=
    abs_hsub_lt_abs_of_half_lt h z hh hz
  have hq :=
    sqrt_sub_strictAnti a |h - z| |z| ha
      (abs_nonneg (h - z)) (abs_nonneg z) habs
  have hbracket :
      Real.sqrt (a ^ 2 + z ^ 2) -
          Real.sqrt (a ^ 2 + (h - z) ^ 2) -
            |z| + |h - z| < 0 := by
    rw [← sq_abs z, ← sq_abs (h - z)]
    linarith
  have hcoef : 0 < 2 * Real.pi * k * ρ₀ := by
    positivity
  exact mul_neg_of_pos_of_neg hcoef hbracket

theorem gap8 (a h k ρ₀ z : ℝ)
    (ha : 0 < a) (hh : 0 < h) (hz : z = h / 2) :
    forceZ a h k ρ₀ z = 0 := by
  rw [gap5 a h k ρ₀ z ha hh, hz]
  have heq : h - h / 2 = h / 2 := by ring
  rw [heq]
  ring

end

end ProofGap.Exercise4159
