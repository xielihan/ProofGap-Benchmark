import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring


namespace ProofGap.Exercise4343

noncomputable section

open MeasureTheory
open scoped Interval

def height (a x y : ℝ) : ℝ :=
  Real.sqrt (a ^ 2 - x ^ 2 - y ^ 2)

def projectionDisk (a : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ^ 2 + p.2 ^ 2 ≤ a ^ 2}

def upperHemisphere : ℝ → Set (ℝ × (ℝ × ℝ)) :=
  fun a =>
    {p |
      p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 = a ^ 2 ∧
        0 ≤ p.2.2}

def graphAreaFactor (a x y : ℝ) : ℝ :=
  Real.sqrt
    (1 + (deriv (fun s => height a s y) x) ^ 2 +
      (deriv (fun s => height a x s) y) ^ 2)

def hemisphereMoment (a : ℝ) : ℝ :=
  ∫ x in -a..a,
    ∫ y in -Real.sqrt (a ^ 2 - x ^ 2)..
        Real.sqrt (a ^ 2 - x ^ 2),
      graphAreaFactor a x y * (x + y + height a x y)

theorem gap1
    (a x y : ℝ) (ha : 0 < a)
    (hxy : x ^ 2 + y ^ 2 < a ^ 2) :
    graphAreaFactor a x y =
      Real.sqrt
        (1 + x ^ 2 / height a x y ^ 2 +
          y ^ 2 / height a x y ^ 2) := by
  have hD : 0 < a ^ 2 - x ^ 2 - y ^ 2 := by linarith
  have hpowx : HasDerivAt (fun s : ℝ => s ^ 2) (2 * x) x := by
    simpa [id, mul_comm] using ((hasDerivAt_id x).pow 2)
  have hpowy : HasDerivAt (fun s : ℝ => s ^ 2) (2 * y) y := by
    simpa [id, mul_comm] using ((hasDerivAt_id y).pow 2)
  have hradx :
      HasDerivAt (fun s : ℝ => a ^ 2 - s ^ 2 - y ^ 2) (-2 * x) x := by
    convert ((hasDerivAt_const x (a ^ 2)).sub hpowx).sub_const (y ^ 2) using 1 <;>
      ring
  have hrady :
      HasDerivAt (fun s : ℝ => a ^ 2 - x ^ 2 - s ^ 2) (-2 * y) y := by
    convert ((hasDerivAt_const y (a ^ 2 - x ^ 2)).sub hpowy) using 1 <;>
      ring
  have hdx :
      HasDerivAt (fun s : ℝ => height a s y)
        (-x / height a x y) x := by
    unfold height
    convert
      (Real.hasDerivAt_sqrt (ne_of_gt hD)).comp x hradx using 1 <;>
      field_simp [Real.sqrt_ne_zero'.2 hD] <;>
      ring
  have hdy :
      HasDerivAt (fun s : ℝ => height a x s)
        (-y / height a x y) y := by
    unfold height
    convert
      (Real.hasDerivAt_sqrt (ne_of_gt hD)).comp y hrady using 1 <;>
      field_simp [Real.sqrt_ne_zero'.2 hD] <;>
      ring
  unfold graphAreaFactor
  rw [hdx.deriv, hdy.deriv]
  simp only [div_pow, neg_sq]

theorem gap2
    (a x y : ℝ) (ha : 0 < a)
    (hxy : x ^ 2 + y ^ 2 < a ^ 2) :
    Real.sqrt
        (1 + x ^ 2 / height a x y ^ 2 +
          y ^ 2 / height a x y ^ 2) =
      a / Real.sqrt (a ^ 2 - x ^ 2 - y ^ 2) := by
  have hD : 0 < a ^ 2 - x ^ 2 - y ^ 2 := by linarith
  have hh : height a x y ^ 2 = a ^ 2 - x ^ 2 - y ^ 2 := by
    simp only [height, Real.sq_sqrt hD.le]
  rw [hh]
  have hinside :
      1 + x ^ 2 / (a ^ 2 - x ^ 2 - y ^ 2) +
          y ^ 2 / (a ^ 2 - x ^ 2 - y ^ 2) =
        a ^ 2 / (a ^ 2 - x ^ 2 - y ^ 2) := by
    field_simp [hD.ne']
    ring
  rw [hinside, Real.sqrt_div (sq_nonneg a), Real.sqrt_sq_eq_abs,
    abs_of_pos ha]

theorem gap3
    (a x y : ℝ) (ha : 0 < a)
    (hxy : x ^ 2 + y ^ 2 < a ^ 2) :
    graphAreaFactor a x y =
      a / Real.sqrt (a ^ 2 - x ^ 2 - y ^ 2) := by
  rw [gap1 a x y ha hxy, gap2 a x y ha hxy]

theorem gap4 (a : ℝ) (ha : 0 < a) :
    hemisphereMoment a =
      ∫ x in -a..a,
        ∫ y in -Real.sqrt (a ^ 2 - x ^ 2)..
            Real.sqrt (a ^ 2 - x ^ 2),
          graphAreaFactor a x y * (x + y + height a x y) := by
  rfl

private def invCircleWeight (u : ℝ) : ℝ :=
  (Real.sqrt (1 - u ^ 2))⁻¹

private theorem ae_real_ne (u : ℝ) :
    ∀ᵐ x : ℝ ∂(volume : Measure ℝ), x ≠ u := by
  rw [ae_iff]
  simpa using measure_singleton u

private theorem invCircleWeight_intervalIntegrable
    (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    IntervalIntegrable invCircleWeight volume 0 c := by
  have hfull :
      IntervalIntegrable invCircleWeight volume (-1 : ℝ) 1 := by
    simpa [invCircleWeight] using
      Polynomial.Chebyshev.intervalIntegrable_sqrt_one_sub_sq_inv
  exact hfull.mono_set (by
    rw [Set.uIcc_of_le hc0, Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    intro u hu
    exact ⟨by linarith [hu.1], by linarith [hu.2]⟩)

private theorem integral_invCircleWeight
    (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    (∫ u in (0 : ℝ)..c, invCircleWeight u) =
      Real.arcsin c - Real.arcsin 0 := by
  have hint := invCircleWeight_intervalIntegrable c hc0 hc1
  apply intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
    hc0 Real.continuous_arcsin.continuousOn
  · intro u hu
    have hneg : u ≠ -1 := by linarith [hu.1]
    have hone : u ≠ 1 := by linarith [hu.2, hc1]
    simpa [invCircleWeight, one_div] using
      (Real.hasDerivAt_arcsin hneg hone).hasDerivWithinAt
  · exact hint

private theorem scaled_slice_intervalIntegrable
    (a s c : ℝ) (hs : 0 < s) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    IntervalIntegrable
      (fun y : ℝ => a / Real.sqrt (s ^ 2 - y ^ 2))
      volume 0 (c * s) := by
  have hbase := invCircleWeight_intervalIntegrable c hc0 hc1
  have hscaled :
      IntervalIntegrable
        (fun y : ℝ => invCircleWeight ((1 / s) * y))
        volume 0 (c * s) := by
    have h := hbase.comp_mul_left (c := (1 / s))
    convert h using 1 <;> field_simp [hs.ne'] <;> ring
  have hmul := hscaled.const_mul (a / s)
  refine hmul.congr ?_
  intro y hy
  change
    a / s * invCircleWeight ((1 / s) * y) =
      a / Real.sqrt (s ^ 2 - y ^ 2)
  have hid :
      s ^ 2 - y ^ 2 =
        s ^ 2 * (1 - ((1 / s) * y) ^ 2) := by
    field_simp [hs.ne']
  rw [hid, Real.sqrt_mul (sq_nonneg s),
    Real.sqrt_sq hs.le]
  dsimp [invCircleWeight]
  field_simp [hs.ne']

private theorem scaled_slice_integral
    (a s c : ℝ) (hs : 0 < s) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    (∫ y in (0 : ℝ)..c * s,
        a / Real.sqrt (s ^ 2 - y ^ 2)) =
      a * (Real.arcsin c - Real.arcsin 0) := by
  have heq :
      (∫ y in (0 : ℝ)..c * s,
          a / Real.sqrt (s ^ 2 - y ^ 2)) =
        ∫ y in (0 : ℝ)..c * s,
          (a / s) * invCircleWeight ((1 / s) * y) := by
    apply intervalIntegral.integral_congr
    intro y hy
    change
      a / Real.sqrt (s ^ 2 - y ^ 2) =
        a / s * invCircleWeight ((1 / s) * y)
    have hid :
        s ^ 2 - y ^ 2 =
          s ^ 2 * (1 - ((1 / s) * y) ^ 2) := by
      field_simp [hs.ne']
    rw [hid, Real.sqrt_mul (sq_nonneg s),
      Real.sqrt_sq hs.le]
    dsimp [invCircleWeight]
    field_simp [hs.ne']
  have hchange :
      (1 / s) *
          (∫ y in (0 : ℝ)..c * s,
            invCircleWeight ((1 / s) * y)) =
        ∫ u in (0 : ℝ)..c, invCircleWeight u := by
    convert
      (intervalIntegral.mul_integral_comp_mul_left
        (f := invCircleWeight) (c := (1 / s))
        (a := (0 : ℝ)) (b := c * s)) using 1 <;>
      field_simp [hs.ne'] <;> ring
  rw [heq, intervalIntegral.integral_const_mul]
  calc
    a / s *
          (∫ y in (0 : ℝ)..c * s,
            invCircleWeight ((1 / s) * y)) =
        a *
          ((1 / s) *
            ∫ y in (0 : ℝ)..c * s,
              invCircleWeight ((1 / s) * y)) := by ring
    _ = a * (∫ u in (0 : ℝ)..c, invCircleWeight u) := by
      rw [hchange]
    _ = a * (Real.arcsin c - Real.arcsin 0) := by
      rw [integral_invCircleWeight c hc0 hc1]

private theorem scaled_symmetric_slice_intervalIntegrable
    (a s c : ℝ) (hs : 0 < s) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    IntervalIntegrable
      (fun y : ℝ => a / Real.sqrt (s ^ 2 - y ^ 2))
      volume (-(c * s)) (c * s) := by
  have hbase :
      IntervalIntegrable invCircleWeight volume (-c) c := by
    have hfull :
        IntervalIntegrable invCircleWeight volume (-1 : ℝ) 1 := by
      simpa [invCircleWeight] using
        Polynomial.Chebyshev.intervalIntegrable_sqrt_one_sub_sq_inv
    refine hfull.mono_set ?_
    rw [Set.uIcc_of_le (by linarith),
      Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    intro u hu
    exact ⟨by linarith [hu.1, hc1], by linarith [hu.2, hc1]⟩
  have hscaled :
      IntervalIntegrable
        (fun y : ℝ => invCircleWeight ((1 / s) * y))
        volume (-(c * s)) (c * s) := by
    have h := hbase.comp_mul_left (c := (1 / s))
    convert h using 1 <;> field_simp [hs.ne'] <;> ring
  have hmul := hscaled.const_mul (a / s)
  refine hmul.congr ?_
  intro y hy
  change
    a / s * invCircleWeight ((1 / s) * y) =
      a / Real.sqrt (s ^ 2 - y ^ 2)
  have hid :
      s ^ 2 - y ^ 2 =
        s ^ 2 * (1 - ((1 / s) * y) ^ 2) := by
    field_simp [hs.ne']
  rw [hid, Real.sqrt_mul (sq_nonneg s),
    Real.sqrt_sq hs.le]
  dsimp [invCircleWeight]
  field_simp [hs.ne']

private theorem scaled_symmetric_slice_integral
    (a s c : ℝ) (hs : 0 < s) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    (∫ y in -(c * s)..c * s,
        a / Real.sqrt (s ^ 2 - y ^ 2)) =
      2 * a * (Real.arcsin c - Real.arcsin 0) := by
  let f : ℝ → ℝ :=
    fun y => a / Real.sqrt (s ^ 2 - y ^ 2)
  have hfull :
      IntervalIntegrable f volume (-(c * s)) (c * s) := by
    simpa [f] using
      scaled_symmetric_slice_intervalIntegrable a s c hs hc0 hc1
  have hcs : 0 ≤ c * s := mul_nonneg hc0 hs.le
  have hleft : IntervalIntegrable f volume (-(c * s)) 0 :=
    hfull.mono_set (by
      rw [Set.uIcc_of_le (neg_nonpos.2 hcs),
        Set.uIcc_of_le (by linarith : -(c * s) ≤ c * s)]
      intro y hy
      exact ⟨hy.1, hy.2.trans hcs⟩)
  have hright : IntervalIntegrable f volume 0 (c * s) :=
    scaled_slice_intervalIntegrable a s c hs hc0 hc1
  have hsplit :=
    intervalIntegral.integral_add_adjacent_intervals hleft hright
  have hreflect :
      (∫ y in -(c * s)..(0 : ℝ), f y) =
        ∫ y in (0 : ℝ)..c * s, f y := by
    calc
      (∫ y in -(c * s)..(0 : ℝ), f y) =
          ∫ y in (0 : ℝ)..c * s, f (-y) := by
        simpa using
          (intervalIntegral.integral_comp_neg
            (f := f) (a := (0 : ℝ)) (b := c * s)).symm
      _ = ∫ y in (0 : ℝ)..c * s, f y := by
        apply intervalIntegral.integral_congr
        intro y hy
        dsimp [f]
        congr 2
        ring
  rw [← hsplit, hreflect]
  dsimp [f]
  have hdouble :
      (∫ y in (0 : ℝ)..c * s,
          a / Real.sqrt (s ^ 2 - y ^ 2)) +
        ∫ y in (0 : ℝ)..c * s,
          a / Real.sqrt (s ^ 2 - y ^ 2) =
        2 *
          ∫ y in (0 : ℝ)..c * s,
            a / Real.sqrt (s ^ 2 - y ^ 2) := by
    ring
  rw [hdouble]
  rw [scaled_slice_integral a s c hs hc0 hc1]
  ring

private theorem odd_scaled_slice_integral_zero
    (a s : ℝ) (hs : 0 < s) :
    (∫ y in -s..s,
        y * (a / Real.sqrt (s ^ 2 - y ^ 2))) = 0 := by
  let q : ℝ → ℝ :=
    fun y => y * (a / Real.sqrt (s ^ 2 - y ^ 2))
  have hbase :
      IntervalIntegrable
        (fun y : ℝ => a / Real.sqrt (s ^ 2 - y ^ 2))
        volume (-s) s := by
    simpa using
      scaled_symmetric_slice_intervalIntegrable a s 1 hs
        (by norm_num) (by norm_num)
  have hq : IntervalIntegrable q volume (-s) s := by
    have h :=
      hbase.mul_continuousOn continuous_id.continuousOn
    exact h.congr (fun y _ => by
      dsimp [q]
      ring)
  have hleft : IntervalIntegrable q volume (-s) 0 :=
    hq.mono_set (by
      rw [Set.uIcc_of_le (by linarith),
        Set.uIcc_of_le (by linarith)]
      intro y hy
      exact ⟨hy.1, hy.2.trans hs.le⟩)
  have hright : IntervalIntegrable q volume 0 s :=
    hq.mono_set (by
      rw [Set.uIcc_of_le hs.le,
        Set.uIcc_of_le (by linarith)]
      intro y hy
      exact ⟨(by linarith [hy.1]), hy.2⟩)
  have hreflect :
      (∫ y in -s..(0 : ℝ), q y) =
        -(∫ y in (0 : ℝ)..s, q y) := by
    calc
      (∫ y in -s..(0 : ℝ), q y) =
          ∫ y in (0 : ℝ)..s, q (-y) := by
        simpa using
          (intervalIntegral.integral_comp_neg
            (f := q) (a := (0 : ℝ)) (b := s)).symm
      _ = ∫ y in (0 : ℝ)..s, -q y := by
        apply intervalIntegral.integral_congr
        intro y hy
        dsimp [q]
        congr 1
        ring
      _ = -(∫ y in (0 : ℝ)..s, q y) := by
        rw [intervalIntegral.integral_neg]
  rw [← intervalIntegral.integral_add_adjacent_intervals hleft hright,
    hreflect]
  simp [q]

private theorem hemisphere_inner_slice
    (a x : ℝ) (ha : 0 < a) (hx : x ^ 2 < a ^ 2) :
    (∫ y in -Real.sqrt (a ^ 2 - x ^ 2)..
        Real.sqrt (a ^ 2 - x ^ 2),
      graphAreaFactor a x y * (x + y + height a x y)) =
      Real.pi * a * x +
        2 * a * Real.sqrt (a ^ 2 - x ^ 2) := by
  let s : ℝ := Real.sqrt (a ^ 2 - x ^ 2)
  have hD : 0 < a ^ 2 - x ^ 2 := by linarith
  have hs : 0 < s := by
    dsimp [s]
    positivity
  have hs2 : s ^ 2 = a ^ 2 - x ^ 2 := by
    dsimp [s]
    rw [Real.sq_sqrt hD.le]
  let b : ℝ → ℝ :=
    fun y => a / Real.sqrt (s ^ 2 - y ^ 2)
  have hbInt : IntervalIntegrable b volume (-s) s := by
    simpa [b] using
      scaled_symmetric_slice_intervalIntegrable a s 1 hs
        (by norm_num) (by norm_num)
  have hbVal :
      (∫ y in -s..s, b y) = Real.pi * a := by
    have h :=
      scaled_symmetric_slice_integral a s 1 hs
        (by norm_num) (by norm_num)
    simp only [one_mul, Real.arcsin_one, Real.arcsin_zero, sub_zero] at h
    dsimp [b]
    nlinarith
  let q : ℝ → ℝ := fun y => y * b y
  have hqInt : IntervalIntegrable q volume (-s) s := by
    have h := hbInt.mul_continuousOn continuous_id.continuousOn
    exact h.congr (fun y _ => by
      dsimp [q]
      ring)
  have hqVal : (∫ y in -s..s, q y) = 0 := by
    simpa [q, b] using odd_scaled_slice_integral_zero a s hs
  have hxbInt :
      IntervalIntegrable (fun y : ℝ => x * b y) volume (-s) s :=
    hbInt.const_mul x
  have haInt :
      IntervalIntegrable (fun _y : ℝ => a) volume (-s) s :=
    intervalIntegrable_const
  have hpoint :
      (∫ y in -s..s,
          graphAreaFactor a x y * (x + y + height a x y)) =
        ∫ y in -s..s, (x * b y + q y) + a := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [ae_real_ne (-s), ae_real_ne s] with y hyn hys hy
    rw [Set.uIoc_of_le (by linarith : -s ≤ s)] at hy
    have hylow : -s < y := hy.1
    have hyhigh : y < s := lt_of_le_of_ne hy.2 hys
    have hy2 : y ^ 2 < s ^ 2 := by
      nlinarith [sq_nonneg (y + s), sq_nonneg (s - y)]
    have hxy : x ^ 2 + y ^ 2 < a ^ 2 := by
      rw [hs2] at hy2
      linarith
    have hfactor := gap3 a x y ha hxy
    have hrad :
        a ^ 2 - x ^ 2 - y ^ 2 = s ^ 2 - y ^ 2 := by
      rw [hs2]
    have hheight :
        height a x y = Real.sqrt (s ^ 2 - y ^ 2) := by
      simp only [height, hrad]
    have hsqrt :
        Real.sqrt (s ^ 2 - y ^ 2) ≠ 0 := by
      exact Real.sqrt_ne_zero'.2 (by linarith)
    rw [hfactor, hrad, hheight]
    dsimp [b, q]
    field_simp [hsqrt]
  change
    (∫ y in -s..s,
      graphAreaFactor a x y * (x + y + height a x y)) =
      Real.pi * a * x + 2 * a * s
  rw [hpoint,
    intervalIntegral.integral_add (hxbInt.add hqInt) haInt,
    intervalIntegral.integral_add hxbInt hqInt,
    intervalIntegral.integral_const_mul, hbVal, hqVal,
    intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

theorem gap5 (a : ℝ) (ha : 0 < a) :
    hemisphereMoment a =
      ∫ x in -a..a,
        Real.pi * a * x +
          2 * a * Real.sqrt (a ^ 2 - x ^ 2) := by
  unfold hemisphereMoment
  apply intervalIntegral.integral_congr_ae
  filter_upwards [ae_real_ne a] with x hxa hx
  rw [Set.uIoc_of_le (by linarith : -a ≤ a)] at hx
  have hxa_lt : x < a := lt_of_le_of_ne hx.2 hxa
  have hx_sq : x ^ 2 < a ^ 2 := by
    nlinarith [hx.1]
  exact hemisphere_inner_slice a x ha hx_sq

private theorem symmetric_integral_odd_zero
    (f : ℝ → ℝ) (A : ℝ)
    (hodd : ∀ x : ℝ, f (-x) = -f x) :
    (∫ x in -A..A, f x) = 0 := by
  have hchange :
      (∫ x in -A..A, f (-x)) =
        ∫ x in -A..A, f x := by
    simpa using
      (intervalIntegral.integral_comp_neg
        (f := f) (a := -A) (b := A))
  have hoddint :
      (∫ x in -A..A, f (-x)) =
        -(∫ x in -A..A, f x) := by
    simp only [hodd, intervalIntegral.integral_neg]
  linarith

private theorem integral_even_neg_pos
    (f : ℝ → ℝ) (A : ℝ) (hA : 0 ≤ A)
    (hint : IntervalIntegrable f volume (-A) A)
    (heven : ∀ x : ℝ, f (-x) = f x) :
    (∫ x in -A..A, f x) =
      2 * ∫ x in (0 : ℝ)..A, f x := by
  have hleft : IntervalIntegrable f volume (-A) 0 :=
    hint.mono_set (by
      rw [Set.uIcc_of_le (neg_nonpos.2 hA),
        Set.uIcc_of_le (by linarith : -A ≤ A)]
      intro x hx
      exact ⟨hx.1, hx.2.trans hA⟩)
  have hright : IntervalIntegrable f volume 0 A :=
    hint.mono_set (by
      rw [Set.uIcc_of_le hA,
        Set.uIcc_of_le (by linarith : -A ≤ A)]
      intro x hx
      exact ⟨by linarith [hx.1], hx.2⟩)
  have hsplit :=
    intervalIntegral.integral_add_adjacent_intervals hleft hright
  have hreflect :
      (∫ x in -A..(0 : ℝ), f x) =
        ∫ x in (0 : ℝ)..A, f x := by
    calc
      (∫ x in -A..(0 : ℝ), f x) =
          ∫ x in (0 : ℝ)..A, f (-x) := by
        simpa using
          (intervalIntegral.integral_comp_neg
            (f := f) (a := (0 : ℝ)) (b := A)).symm
      _ = ∫ x in (0 : ℝ)..A, f x := by
        apply intervalIntegral.integral_congr
        intro x hx
        exact heven x
  rw [← hsplit, hreflect]
  ring

private theorem semicircle_integral (a : ℝ) (ha : 0 ≤ a) :
    (∫ x in -a..a, Real.sqrt (a ^ 2 - x ^ 2)) =
      Real.pi * a ^ 2 / 2 := by
  by_cases ha0 : a = 0
  · subst a
    simp
  let f := fun x : ℝ => Real.sqrt (a ^ 2 - x ^ 2)
  have hscaled :
      (∫ t in (-1 : ℝ)..1, f (a * t)) =
        a * (Real.pi / 2) := by
    calc
      (∫ t in (-1 : ℝ)..1, f (a * t)) =
          ∫ t in (-1 : ℝ)..1,
            a * Real.sqrt (1 - t ^ 2) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at ht
        have harg : 0 ≤ 1 - t ^ 2 := by
          nlinarith [mul_nonneg
            (by linarith [ht.1] : 0 ≤ t + 1)
            (by linarith [ht.2] : 0 ≤ 1 - t)]
        dsimp only [f]
        rw [show a ^ 2 - (a * t) ^ 2 =
          a ^ 2 * (1 - t ^ 2) by ring]
        rw [Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs,
          abs_of_nonneg ha]
      _ = a * ∫ t in (-1 : ℝ)..1,
          Real.sqrt (1 - t ^ 2) := by
        rw [intervalIntegral.integral_const_mul]
      _ = a * (Real.pi / 2) := by
        rw [integral_sqrt_one_sub_sq]
  calc
    (∫ x in -a..a, Real.sqrt (a ^ 2 - x ^ 2)) =
        a * intervalIntegral (fun t : ℝ => f (a * t)) (-1) 1 volume := by
      simpa [f, smul_eq_mul] using
        (intervalIntegral.smul_integral_comp_mul_left
          (f := f) (a := (-1 : ℝ)) (b := 1) a).symm
    _ = Real.pi * a ^ 2 / 2 := by
      rw [hscaled]
      ring

theorem gap6 (a : ℝ) (ha : 0 < a) :
    (∫ x in -a..a,
        Real.pi * a * x +
          2 * a * Real.sqrt (a ^ 2 - x ^ 2)) =
      4 * a *
        (∫ x in (0 : ℝ)..a,
          Real.sqrt (a ^ 2 - x ^ 2)) := by
  let f : ℝ → ℝ := fun x => Real.sqrt (a ^ 2 - x ^ 2)
  have hf : Continuous f := by
    dsimp [f]
    fun_prop
  have hfInt : IntervalIntegrable f volume (-a) a :=
    hf.intervalIntegrable _ _
  have heven : ∀ x : ℝ, f (-x) = f x := by
    intro x
    dsimp [f]
    congr 1
    ring
  have hsym :
      (∫ x in -a..a, f x) =
        2 * ∫ x in (0 : ℝ)..a, f x :=
    integral_even_neg_pos f a ha.le hfInt heven
  have hodd :
      (∫ x in -a..a, Real.pi * a * x) = 0 := by
    apply symmetric_integral_odd_zero
    intro x
    ring
  have hlinInt :
      IntervalIntegrable (fun x : ℝ => Real.pi * a * x)
        volume (-a) a := by
    exact
      (continuous_const.mul continuous_id).intervalIntegrable _ _
  have hrootInt :
      IntervalIntegrable
        (fun x : ℝ => 2 * a * Real.sqrt (a ^ 2 - x ^ 2))
        volume (-a) a := by
    simpa [f] using hfInt.const_mul (2 * a)
  rw [intervalIntegral.integral_add hlinInt hrootInt, hodd,
    intervalIntegral.integral_const_mul]
  dsimp [f] at hsym
  rw [hsym]
  ring

theorem gap7 (a : ℝ) (ha : 0 < a) :
    4 * a *
        (∫ x in (0 : ℝ)..a,
          Real.sqrt (a ^ 2 - x ^ 2)) =
      4 * a * (Real.pi * a ^ 2 / 4) := by
  let f : ℝ → ℝ := fun x => Real.sqrt (a ^ 2 - x ^ 2)
  have hf : Continuous f := by
    dsimp [f]
    fun_prop
  have hfInt : IntervalIntegrable f volume (-a) a :=
    hf.intervalIntegrable _ _
  have heven : ∀ x : ℝ, f (-x) = f x := by
    intro x
    dsimp [f]
    congr 1
    ring
  have hsym :
      (∫ x in -a..a, f x) =
        2 * ∫ x in (0 : ℝ)..a, f x :=
    integral_even_neg_pos f a ha.le hfInt heven
  have hfull := semicircle_integral a ha.le
  dsimp [f] at hsym
  have hhalf :
      (∫ x in (0 : ℝ)..a,
        Real.sqrt (a ^ 2 - x ^ 2)) =
          Real.pi * a ^ 2 / 4 := by
    linarith
  rw [hhalf]

theorem gap8 (a : ℝ) :
    4 * a * (Real.pi * a ^ 2 / 4) =
      Real.pi * a ^ 3 := by
  ring

theorem gap9 (a : ℝ) (ha : 0 < a) :
    hemisphereMoment a = Real.pi * a ^ 3 := by
  rw [gap5 a ha, gap6 a ha, gap7 a ha, gap8]

end

end ProofGap.Exercise4343
