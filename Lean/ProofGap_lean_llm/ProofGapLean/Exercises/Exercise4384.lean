import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring


namespace ProofGap.Exercise4384

noncomputable section

open MeasureTheory
open scoped Interval

abbrev Vec3 := ℝ × ℝ × ℝ

def dot (p q : Vec3) : ℝ :=
  p.1 * q.1 + p.2.1 * q.2.1 + p.2.2 * q.2.2

def cross (p q : Vec3) : Vec3 :=
  (p.2.1 * q.2.2 - p.2.2 * q.2.1,
    p.2.2 * q.1 - p.1 * q.2.2,
    p.1 * q.2.1 - p.2.1 * q.1)

def sideX (a b u v : ℝ) : ℝ :=
  a * Real.cos u * Real.cos v + b * Real.sin u * Real.sin v

def sideY (a b u v : ℝ) : ℝ :=
  a * Real.cos u * Real.sin v - b * Real.sin u * Real.cos v

def sideZ (c u : ℝ) : ℝ :=
  c * Real.sin u

def sidePoint (a b c u v : ℝ) : Vec3 :=
  (sideX a b u v, sideY a b u v, sideZ c u)

def sidePartialU (a b c u v : ℝ) : Vec3 :=
  (deriv (fun s => sideX a b s v) u,
    deriv (fun s => sideY a b s v) u,
    deriv (fun s => sideZ c s) u)

def sidePartialV (a b _c u v : ℝ) : Vec3 :=
  (deriv (fun s => sideX a b u s) v,
    deriv (fun s => sideY a b u s) v,
    0)

def outwardSideAreaVector (a b c u v : ℝ) : Vec3 :=
  let w := cross (sidePartialV a b c u v) (sidePartialU a b c u v)
  ((c / |c|) * w.1, (c / |c|) * w.2.1, (c / |c|) * w.2.2)

def crossSectionRadiusSq (a b c z : ℝ) : ℝ :=
  a ^ 2 + (b ^ 2 - a ^ 2) * (z / c) ^ 2

def crossSectionArea (a b c z : ℝ) : ℝ :=
  Real.pi * crossSectionRadiusSq a b c z

def solidVolume (a b c : ℝ) : ℝ :=
  ∫ z in -|c|..|c|, crossSectionArea a b c z

def capDisk (b : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ^ 2 + p.2 ^ 2 ≤ b ^ 2}

def topCapFlux (b c : ℝ) : ℝ :=
  ∫ _p in capDisk b, |c|

def bottomCapFlux (b c : ℝ) : ℝ :=
  ∫ _p in capDisk b, |c|

def sideFlux (a b c : ℝ) : ℝ :=
  ∫ u in -Real.pi / 2..Real.pi / 2,
    ∫ v in (0 : ℝ)..2 * Real.pi,
      dot (sidePoint a b c u v) (outwardSideAreaVector a b c u v)

def totalBoundaryFlux (a b c : ℝ) : ℝ :=
  topCapFlux b c + bottomCapFlux b c + sideFlux a b c

theorem gap1 (a b u v : ℝ) :
    sideX a b u v ^ 2 + sideY a b u v ^ 2 =
      a ^ 2 * Real.cos u ^ 2 + b ^ 2 * Real.sin u ^ 2 := by
  unfold sideX sideY
  nlinarith [Real.sin_sq_add_cos_sq v]

theorem gap2 (a b c u v : ℝ) (hc : c ≠ 0) :
    sideX a b u v ^ 2 + sideY a b u v ^ 2 +
        (a ^ 2 - b ^ 2) / c ^ 2 * sideZ c u ^ 2 =
      a ^ 2 := by
  rw [gap1]
  unfold sideZ
  field_simp [hc]
  nlinarith [Real.sin_sq_add_cos_sq u]

private theorem capDisk_area (b : ℝ) (hb : 0 < b) :
    (∫ _p in capDisk b, (1 : ℝ)) = Real.pi * b ^ 2 := by
  let f : ℝ × ℝ → ℝ := fun _p => 1
  let q : ℝ → ℝ := fun r => r
  have hdisk : MeasurableSet (capDisk b) := by
    unfold capDisk
    measurability
  have hpoint : ∀ p : ℝ × ℝ,
      polarCoord.target.indicator
          (fun z =>
            z.1 * (capDisk b).indicator f (polarCoord.symm z)) p =
        (Set.Ioc (0 : ℝ) b ×ˢ Set.Ioo (-Real.pi) Real.pi).indicator
          (fun z => q z.1) p := by
    rintro ⟨r, φ⟩
    have htrig :
        (r * Real.cos φ) ^ 2 + (r * Real.sin φ) ^ 2 = r ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq φ]
    by_cases ht : 0 < r ∧ -Real.pi < φ ∧ φ < Real.pi
    · have hriff : r ^ 2 ≤ b ^ 2 ↔ r ≤ b := by
        constructor
        · intro hsq
          nlinarith
        · intro hr
          nlinarith
      by_cases hr : r ≤ b
      · have htargetmem : (r, φ) ∈ polarCoord.target := by
          simpa [polarCoord_target] using ht
        have hrectmem :
            (r, φ) ∈ Set.Ioc (0 : ℝ) b ×ˢ Set.Ioo (-Real.pi) Real.pi :=
          ⟨⟨ht.1, hr⟩, ht.2⟩
        have hpolarmem : polarCoord.symm (r, φ) ∈ capDisk b := by
          simp only [polarCoord_symm_apply, capDisk, Set.mem_setOf_eq, Prod.fst,
            Prod.snd, htrig]
          exact hriff.mpr hr
        rw [Set.indicator_of_mem htargetmem, Set.indicator_of_mem hrectmem,
          Set.indicator_of_mem hpolarmem]
        simp [f, q]
      · have hsq : ¬r ^ 2 ≤ b ^ 2 := by
          intro h
          exact hr (hriff.mp h)
        simp [polarCoord_target, Set.indicator_of_mem, ht, capDisk, f, q,
          htrig, hr, hsq]
    · have hrect :
          (r, φ) ∉ Set.Ioc (0 : ℝ) b ×ˢ Set.Ioo (-Real.pi) Real.pi := by
        intro hp
        exact ht ⟨hp.1.1, hp.2.1, hp.2.2⟩
      have htarget : (r, φ) ∉ polarCoord.target := by
        simpa [polarCoord_target, Set.mem_prod] using ht
      rw [Set.indicator_of_notMem htarget, Set.indicator_of_notMem hrect]
  calc
    (∫ _p in capDisk b, (1 : ℝ)) =
        ∫ p : ℝ × ℝ, (capDisk b).indicator f p := by
          rw [MeasureTheory.integral_indicator hdisk]
    _ = ∫ p in polarCoord.target,
          p.1 * (capDisk b).indicator f (polarCoord.symm p) := by
          simpa [smul_eq_mul] using
            (integral_comp_polarCoord_symm ((capDisk b).indicator f)).symm
    _ = ∫ p : ℝ × ℝ,
          (Set.Ioc (0 : ℝ) b ×ˢ Set.Ioo (-Real.pi) Real.pi).indicator
            (fun z => q z.1) p := by
          rw [← MeasureTheory.integral_indicator polarCoord.open_target.measurableSet]
          apply MeasureTheory.integral_congr_ae
          exact Filter.Eventually.of_forall hpoint
    _ = ∫ p in Set.Ioc (0 : ℝ) b ×ˢ Set.Ioo (-Real.pi) Real.pi,
          q p.1 * (1 : ℝ) := by
          rw [MeasureTheory.integral_indicator
            (measurableSet_Ioc.prod measurableSet_Ioo)]
          apply MeasureTheory.setIntegral_congr_fun
            (measurableSet_Ioc.prod measurableSet_Ioo)
          intro p hp
          simp
    _ = (∫ r in Set.Ioc (0 : ℝ) b, q r) *
          ∫ _φ in Set.Ioo (-Real.pi) Real.pi, (1 : ℝ) := by
          exact MeasureTheory.setIntegral_prod_mul q (fun _ : ℝ => 1)
            (Set.Ioc (0 : ℝ) b) (Set.Ioo (-Real.pi) Real.pi)
    _ = (∫ r in (0 : ℝ)..b, r) * (2 * Real.pi) := by
          have hangle :
              (∫ _φ in Set.Ioo (-Real.pi) Real.pi, (1 : ℝ)) =
                2 * Real.pi := by
            rw [MeasureTheory.setIntegral_const]
            simp [Real.pi_pos.le]
            ring
          rw [intervalIntegral.integral_of_le hb.le]
          simp only [q]
          rw [hangle]
    _ = Real.pi * b ^ 2 := by
      rw [integral_id]
      ring

private theorem topCapFlux_formula
    (b c : ℝ) (hb : 0 < b) :
    topCapFlux b c = |c| * Real.pi * b ^ 2 := by
  unfold topCapFlux
  have hscale :
      (∫ _p in capDisk b, |c|) =
        |c| * ∫ _p in capDisk b, (1 : ℝ) := by
    rw [← MeasureTheory.integral_const_mul]
    simp
  rw [hscale, capDisk_area b hb]
  ring

private theorem bottomCapFlux_formula
    (b c : ℝ) (hb : 0 < b) :
    bottomCapFlux b c = |c| * Real.pi * b ^ 2 := by
  unfold bottomCapFlux
  have hscale :
      (∫ _p in capDisk b, |c|) =
        |c| * ∫ _p in capDisk b, (1 : ℝ) := by
    rw [← MeasureTheory.integral_const_mul]
    simp
  rw [hscale, capDisk_area b hb]
  ring

private theorem sidePartialU_formula (a b c u v : ℝ) :
    sidePartialU a b c u v =
      (-a * Real.sin u * Real.cos v + b * Real.cos u * Real.sin v,
        -a * Real.sin u * Real.sin v - b * Real.cos u * Real.cos v,
        c * Real.cos u) := by
  have hx :
      HasDerivAt (fun s : ℝ => sideX a b s v)
        (-a * Real.sin u * Real.cos v +
          b * Real.cos u * Real.sin v) u := by
    unfold sideX
    convert
      (((Real.hasDerivAt_cos u).const_mul a).mul_const (Real.cos v)).add
        (((Real.hasDerivAt_sin u).const_mul b).mul_const (Real.sin v))
      using 1 <;> ring
  have hy :
      HasDerivAt (fun s : ℝ => sideY a b s v)
        (-a * Real.sin u * Real.sin v -
          b * Real.cos u * Real.cos v) u := by
    unfold sideY
    convert
      (((Real.hasDerivAt_cos u).const_mul a).mul_const (Real.sin v)).sub
        (((Real.hasDerivAt_sin u).const_mul b).mul_const (Real.cos v))
      using 1 <;> ring
  have hz :
      HasDerivAt (fun s : ℝ => sideZ c s) (c * Real.cos u) u := by
    unfold sideZ
    exact (Real.hasDerivAt_sin u).const_mul c
  unfold sidePartialU
  rw [hx.deriv, hy.deriv, hz.deriv]

private theorem sidePartialV_formula (a b c u v : ℝ) :
    sidePartialV a b c u v =
      (-a * Real.cos u * Real.sin v + b * Real.sin u * Real.cos v,
        a * Real.cos u * Real.cos v + b * Real.sin u * Real.sin v,
        0) := by
  have hx :
      HasDerivAt (fun s : ℝ => sideX a b u s)
        (-a * Real.cos u * Real.sin v +
          b * Real.sin u * Real.cos v) v := by
    unfold sideX
    convert
      ((Real.hasDerivAt_cos v).const_mul (a * Real.cos u)).add
        ((Real.hasDerivAt_sin v).const_mul (b * Real.sin u))
      using 1 <;> ring
  have hy :
      HasDerivAt (fun s : ℝ => sideY a b u s)
        (a * Real.cos u * Real.cos v +
          b * Real.sin u * Real.sin v) v := by
    unfold sideY
    convert
      ((Real.hasDerivAt_sin v).const_mul (a * Real.cos u)).sub
        ((Real.hasDerivAt_cos v).const_mul (b * Real.sin u))
      using 1 <;> ring
  unfold sidePartialV
  rw [hx.deriv, hy.deriv]

private theorem side_cross_formula (a b c u v : ℝ) :
    cross (sidePartialV a b c u v) (sidePartialU a b c u v) =
      (c * Real.cos u * sideX a b u v,
        c * Real.cos u * sideY a b u v,
        (a ^ 2 - b ^ 2) * Real.sin u * Real.cos u) := by
  rw [sidePartialU_formula, sidePartialV_formula]
  unfold cross
  dsimp
  apply Prod.ext
  · unfold sideX
    ring
  · apply Prod.ext
    · unfold sideY
      ring
    · calc
        _ = (a ^ 2 - b ^ 2) * Real.sin u * Real.cos u *
            (Real.sin v ^ 2 + Real.cos v ^ 2) := by ring
        _ = (a ^ 2 - b ^ 2) * Real.sin u * Real.cos u := by
          rw [Real.sin_sq_add_cos_sq]
          ring

private theorem side_dot_cross_formula (a b c u v : ℝ) :
    dot (sidePoint a b c u v)
        (cross (sidePartialV a b c u v) (sidePartialU a b c u v)) =
      c * a ^ 2 * Real.cos u := by
  rw [side_cross_formula]
  unfold dot sidePoint sideZ
  dsimp
  calc
    _ = c * Real.cos u *
          (sideX a b u v ^ 2 + sideY a b u v ^ 2) +
        c * (a ^ 2 - b ^ 2) * Real.sin u ^ 2 * Real.cos u := by
      ring
    _ = c * Real.cos u *
          (a ^ 2 * Real.cos u ^ 2 + b ^ 2 * Real.sin u ^ 2) +
        c * (a ^ 2 - b ^ 2) * Real.sin u ^ 2 * Real.cos u := by
      rw [gap1]
    _ = c * a ^ 2 * Real.cos u *
          (Real.sin u ^ 2 + Real.cos u ^ 2) := by ring
    _ = c * a ^ 2 * Real.cos u := by
      rw [Real.sin_sq_add_cos_sq]
      ring

private theorem side_integrand_formula
    (a b c u v : ℝ) (hc : c ≠ 0) :
    dot (sidePoint a b c u v) (outwardSideAreaVector a b c u v) =
      |c| * a ^ 2 * Real.cos u := by
  unfold outwardSideAreaVector
  dsimp only
  calc
    dot (sidePoint a b c u v)
        ((c / |c|) *
            (cross (sidePartialV a b c u v)
              (sidePartialU a b c u v)).1,
          (c / |c|) *
            (cross (sidePartialV a b c u v)
              (sidePartialU a b c u v)).2.1,
          (c / |c|) *
            (cross (sidePartialV a b c u v)
              (sidePartialU a b c u v)).2.2) =
        c / |c| *
          dot (sidePoint a b c u v)
            (cross (sidePartialV a b c u v)
              (sidePartialU a b c u v)) := by
      unfold dot
      dsimp only
      ring
    _ = c / |c| * (c * a ^ 2 * Real.cos u) := by
      rw [side_dot_cross_formula]
    _ = |c| * a ^ 2 * Real.cos u := by
      have habs : |c| ≠ 0 := abs_ne_zero.mpr hc
      have hsq : |c| ^ 2 = c ^ 2 := sq_abs c
      field_simp [habs]
      rw [← hsq]

private theorem sideFlux_formula
    (a b c : ℝ) (hc : c ≠ 0) :
    sideFlux a b c = 4 * Real.pi * |c| * a ^ 2 := by
  unfold sideFlux
  have hinner (u : ℝ) :
      (∫ v in (0 : ℝ)..2 * Real.pi,
        dot (sidePoint a b c u v) (outwardSideAreaVector a b c u v)) =
        2 * Real.pi * (|c| * a ^ 2 * Real.cos u) := by
    calc
      _ = ∫ _v in (0 : ℝ)..2 * Real.pi,
          |c| * a ^ 2 * Real.cos u := by
        apply intervalIntegral.integral_congr
        intro v hv
        exact side_integrand_formula a b c u v hc
      _ = 2 * Real.pi * (|c| * a ^ 2 * Real.cos u) := by
        rw [intervalIntegral.integral_const]
        simp only [smul_eq_mul]
        ring
  simp_rw [hinner]
  have hcos :
      (∫ u in -Real.pi / 2..Real.pi / 2, Real.cos u) = 2 := by
    rw [integral_cos]
    rw [show -Real.pi / 2 = -(Real.pi / 2) by ring,
      Real.sin_neg, Real.sin_pi_div_two]
    norm_num
  calc
    (∫ u in -Real.pi / 2..Real.pi / 2,
        2 * Real.pi * (|c| * a ^ 2 * Real.cos u)) =
        (2 * Real.pi * |c| * a ^ 2) *
          ∫ u in -Real.pi / 2..Real.pi / 2, Real.cos u := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro u hu
      ring
    _ = 4 * Real.pi * |c| * a ^ 2 := by
      rw [hcos]
      ring

private theorem solidVolume_formula
    (a b c : ℝ) (hc : c ≠ 0) :
    solidVolume a b c =
      4 * Real.pi / 3 * (a ^ 2 + b ^ 2 / 2) * |c| := by
  have hpoint :
      (∫ z in -|c|..|c|, crossSectionArea a b c z) =
        ∫ z in -|c|..|c|,
          Real.pi * a ^ 2 +
            (Real.pi * (b ^ 2 - a ^ 2) / c ^ 2) * z ^ 2 := by
    apply intervalIntegral.integral_congr
    intro z hz
    unfold crossSectionArea crossSectionRadiusSq
    field_simp [hc]
  have hconst :
      IntervalIntegrable (fun _z : ℝ => Real.pi * a ^ 2)
        volume (-|c|) |c| :=
    intervalIntegrable_const
  have hsq :
      IntervalIntegrable
        (fun z : ℝ =>
          (Real.pi * (b ^ 2 - a ^ 2) / c ^ 2) * z ^ 2)
        volume (-|c|) |c| :=
    (continuous_const.mul (continuous_id.pow 2)).intervalIntegrable _ _
  have habs : |c| ≠ 0 := abs_ne_zero.mpr hc
  have habs2 : |c| ^ 2 = c ^ 2 := sq_abs c
  unfold solidVolume
  rw [hpoint, intervalIntegral.integral_add hconst hsq,
    intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul, integral_pow]
  simp only [smul_eq_mul, Nat.reduceAdd, Nat.cast_ofNat]
  have hneg3 : (-|c|) ^ 3 = -(|c| ^ 3) := by ring
  rw [hneg3]
  field_simp [hc]
  rw [habs2]
  ring

private theorem angular_cross_section_formula (a b : ℝ) :
    (∫ u in -Real.pi / 2..Real.pi / 2,
        (a ^ 2 + (b ^ 2 - a ^ 2) * Real.sin u ^ 2) *
          Real.cos u) =
      4 / 3 * (a ^ 2 + b ^ 2 / 2) := by
  let F : ℝ → ℝ :=
    fun u =>
      a ^ 2 * Real.sin u +
        (b ^ 2 - a ^ 2) * Real.sin u ^ 3 / 3
  have hF (u : ℝ) :
      HasDerivAt F
        ((a ^ 2 + (b ^ 2 - a ^ 2) * Real.sin u ^ 2) *
          Real.cos u) u := by
    have hs := Real.hasDerivAt_sin u
    have hs3 := hs.pow 3
    dsimp [F]
    convert
      (hs.const_mul (a ^ 2)).add
        ((hs3.const_mul (b ^ 2 - a ^ 2)).div_const 3)
      using 1 <;> ring
  have hint :
      IntervalIntegrable
        (fun u : ℝ =>
          (a ^ 2 + (b ^ 2 - a ^ 2) * Real.sin u ^ 2) *
            Real.cos u)
        volume (-Real.pi / 2) (Real.pi / 2) := by
    exact
      ((continuous_const.add
        (continuous_const.mul (Real.continuous_sin.pow 2))).mul
          Real.continuous_cos).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u hu => hF u) hint]
  dsimp [F]
  rw [show -Real.pi / 2 = -(Real.pi / 2) by ring,
    Real.sin_neg, Real.sin_pi_div_two]
  ring

theorem gap3 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : c ≠ 0) :
    solidVolume a b c = 1 / 3 * totalBoundaryFlux a b c := by
  rw [solidVolume_formula a b c hc]
  unfold totalBoundaryFlux
  rw [topCapFlux_formula b c hb, bottomCapFlux_formula b c hb,
    sideFlux_formula a b c hc]
  ring

theorem gap4 (b c : ℝ) (hb : 0 < b) (hc : c ≠ 0) :
    topCapFlux b c = |c| * Real.pi * b ^ 2 := by
  exact topCapFlux_formula b c hb

theorem gap5 (b c : ℝ) (hb : 0 < b) (hc : c ≠ 0) :
    bottomCapFlux b c = |c| * Real.pi * b ^ 2 := by
  exact bottomCapFlux_formula b c hb

theorem gap6 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : c ≠ 0) :
    sideFlux a b c = 4 * Real.pi * |c| * a ^ 2 := by
  exact sideFlux_formula a b c hc

theorem gap7 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : c ≠ 0) :
    solidVolume a b c =
      1 / 3 *
        (4 * Real.pi * |c| * a ^ 2 +
          |c| * Real.pi * b ^ 2 + |c| * Real.pi * b ^ 2) := by
  rw [solidVolume_formula a b c hc]
  ring

theorem gap8 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : c ≠ 0) :
    solidVolume a b c =
      4 * Real.pi / 3 * (a ^ 2 + b ^ 2 / 2) * |c| := by
  exact solidVolume_formula a b c hc

theorem gap9 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : c ≠ 0) :
    solidVolume a b c =
      ∫ z in -|c|..|c|, crossSectionArea a b c z := by
  rfl

theorem gap10 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : c ≠ 0) :
    solidVolume a b c =
      Real.pi * |c| *
        ∫ u in -Real.pi / 2..Real.pi / 2,
          (a ^ 2 + (b ^ 2 - a ^ 2) * Real.sin u ^ 2) *
            Real.cos u := by
  rw [solidVolume_formula a b c hc,
    angular_cross_section_formula a b]
  ring

theorem gap11 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : c ≠ 0) :
    solidVolume a b c =
      4 * Real.pi / 3 * (a ^ 2 + b ^ 2 / 2) * |c| := by
  exact solidVolume_formula a b c hc

end

end ProofGap.Exercise4384
