import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open scoped Interval

namespace ProofGap.Exercise2478

noncomputable section

open Set

def OnCurve (a x y : ℝ) : Prop := x ^ 2 - x * y + y ^ 2 = a ^ 2

def discriminant (a x : ℝ) : ℝ := 4 * a ^ 2 - 3 * x ^ 2

def upper (a x : ℝ) : ℝ := (x + Real.sqrt (discriminant a x)) / 2

def lower (a x : ℝ) : ℝ := (x - Real.sqrt (discriminant a x)) / 2

def volume (a : ℝ) : ℝ :=
  2 * (Real.pi * (∫ x in 0..a, upper a x ^ 2) +
    Real.pi * (∫ x in a..(2 / Real.sqrt 3 * a),
      (upper a x ^ 2 - lower a x ^ 2)))

theorem gap1 (a x y : ℝ) (h : OnCurve a x y) :
    y ^ 2 - x * y + x ^ 2 - a ^ 2 = 0 := by
  unfold OnCurve at h
  linarith

theorem gap2 (a x y : ℝ) (hdisc : 0 ≤ discriminant a x) :
    OnCurve a x y ↔ y = upper a x ∨ y = lower a x := by
  have hsqrt :
      Real.sqrt (discriminant a x) ^ 2 = discriminant a x :=
    Real.sq_sqrt hdisc
  unfold discriminant at hsqrt
  constructor
  · intro h
    have hsq :
        (2 * y - x) ^ 2 = Real.sqrt (discriminant a x) ^ 2 := by
      unfold OnCurve at h
      unfold discriminant
      nlinarith
    rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hsq) with hp | hm
    · left
      unfold upper
      linarith
    · right
      unfold lower
      linarith
  · rintro (rfl | rfl)
    · unfold OnCurve upper
      unfold discriminant
      field_simp
      ring_nf at *
      nlinarith
    · unfold OnCurve lower
      unfold discriminant
      field_simp
      ring_nf at *
      nlinarith

private theorem outerEndpoint_sq (a : ℝ) :
    3 * (2 / Real.sqrt 3 * a) ^ 2 = 4 * a ^ 2 := by
  have hr : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hr2 : Real.sqrt (3 : ℝ) ^ 2 = 3 :=
    Real.sq_sqrt (by norm_num)
  field_simp [hr.ne']
  nlinarith

theorem gap3 (a x : ℝ) (ha : 0 ≤ a) (hdisc : 0 ≤ discriminant a x) :
    -(2 / Real.sqrt 3 * a) ≤ x := by
  let b : ℝ := 2 / Real.sqrt 3 * a
  have hr : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hb : 0 ≤ b := by
    dsimp [b]
    positivity
  have hbsq : 3 * b ^ 2 = 4 * a ^ 2 := by
    dsimp [b]
    exact outerEndpoint_sq a
  have hxsq : x ^ 2 ≤ b ^ 2 := by
    unfold discriminant at hdisc
    nlinarith
  exact (abs_le_of_sq_le_sq' hxsq hb).1

theorem gap4 (a x : ℝ) (ha : 0 ≤ a) (hdisc : 0 ≤ discriminant a x) :
    x ≤ 2 / Real.sqrt 3 * a := by
  let b : ℝ := 2 / Real.sqrt 3 * a
  have hr : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hb : 0 ≤ b := by
    dsimp [b]
    positivity
  have hbsq : 3 * b ^ 2 = 4 * a ^ 2 := by
    dsimp [b]
    exact outerEndpoint_sq a
  have hxsq : x ^ 2 ≤ b ^ 2 := by
    unfold discriminant at hdisc
    nlinarith
  exact (abs_le_of_sq_le_sq' hxsq hb).2

theorem gap5 (a x : ℝ) (ha : 0 ≤ a) :
    OnCurve a x 0 ↔ x = -a ∨ x = a := by
  constructor
  · intro h
    have hsq : x ^ 2 = a ^ 2 := by
      unfold OnCurve at h
      nlinarith
    rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hsq) with h | h
    · exact Or.inr h
    · exact Or.inl h
  · rintro (rfl | rfl) <;> simp [OnCurve]

theorem gap6 (a Vₓ : ℝ) (ha : 0 ≤ a) (hV : Vₓ = volume a) :
    Vₓ = 2 * (Real.pi * (∫ x in 0..a,
        1 / 4 * (x + Real.sqrt (4 * a ^ 2 - 3 * x ^ 2)) ^ 2) +
      Real.pi * (∫ x in a..(2 / Real.sqrt 3 * a),
        (1 / 4 * (x + Real.sqrt (4 * a ^ 2 - 3 * x ^ 2)) ^ 2 -
          1 / 4 * (x - Real.sqrt (4 * a ^ 2 - 3 * x ^ 2)) ^ 2))) := by
  have hI1 :
      (∫ x in 0..a, upper a x ^ 2) =
        ∫ x in 0..a,
          1 / 4 * (x + Real.sqrt (4 * a ^ 2 - 3 * x ^ 2)) ^ 2 := by
    apply intervalIntegral.integral_congr
    intro x hx
    unfold upper discriminant
    ring
  have hI2 :
      (∫ x in a..(2 / Real.sqrt 3 * a),
          (upper a x ^ 2 - lower a x ^ 2)) =
        ∫ x in a..(2 / Real.sqrt 3 * a),
          (1 / 4 * (x + Real.sqrt (4 * a ^ 2 - 3 * x ^ 2)) ^ 2 -
            1 / 4 * (x - Real.sqrt (4 * a ^ 2 - 3 * x ^ 2)) ^ 2) := by
    apply intervalIntegral.integral_congr
    intro x hx
    unfold upper lower discriminant
    ring
  rw [hV]
  unfold volume
  rw [hI1, hI2]

theorem gap7 (a Vₓ : ℝ) (ha : 0 ≤ a) (hV : Vₓ = volume a) :
    Vₓ =
      Real.pi / 2 * (∫ x in 0..a,
        (4 * a ^ 2 - 2 * x ^ 2 +
          2 * x * Real.sqrt (4 * a ^ 2 - 3 * x ^ 2))) +
      2 * Real.pi * (∫ x in a..(2 / Real.sqrt 3 * a),
        x * Real.sqrt (4 * a ^ 2 - 3 * x ^ 2)) := by
  have hI1 :
      (∫ x in 0..a, upper a x ^ 2) =
        (1 / 4 : ℝ) * ∫ x in 0..a,
          (4 * a ^ 2 - 2 * x ^ 2 +
            2 * x * Real.sqrt (4 * a ^ 2 - 3 * x ^ 2)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le ha] at hx
    have hfac : 0 ≤ (a - x) * (a + x) :=
      mul_nonneg (sub_nonneg.mpr hx.2) (by linarith [hx.1])
    have hdisc : 0 ≤ 4 * a ^ 2 - 3 * x ^ 2 := by
      nlinarith
    have hsqrt :
        Real.sqrt (4 * a ^ 2 - 3 * x ^ 2) ^ 2 =
          4 * a ^ 2 - 3 * x ^ 2 :=
      Real.sq_sqrt hdisc
    unfold upper discriminant
    nlinarith
  have hI2 :
      (∫ x in a..(2 / Real.sqrt 3 * a),
          (upper a x ^ 2 - lower a x ^ 2)) =
        ∫ x in a..(2 / Real.sqrt 3 * a),
          x * Real.sqrt (4 * a ^ 2 - 3 * x ^ 2) := by
    apply intervalIntegral.integral_congr
    intro x hx
    unfold upper lower discriminant
    ring
  rw [hV]
  unfold volume
  rw [hI1, hI2]
  ring

private def rootPrimitive (a x : ℝ) : ℝ :=
  -(discriminant a x * Real.sqrt (discriminant a x)) / 9

private theorem discriminant_hasDerivAt (a x : ℝ) :
    HasDerivAt (discriminant a) (-6 * x) x := by
  unfold discriminant
  convert
    (hasDerivAt_const x (4 * a ^ 2)).sub
      (((hasDerivAt_id x).pow 2).const_mul 3) using 1 <;>
    simp only [id_eq] <;> ring

private theorem rootPrimitive_hasDerivAt (a x : ℝ)
    (hdisc : 0 < discriminant a x) :
    HasDerivAt (rootPrimitive a)
      (x * Real.sqrt (discriminant a x)) x := by
  have hd := discriminant_hasDerivAt a x
  have hs := hd.sqrt hdisc.ne'
  have hspos : 0 < Real.sqrt (discriminant a x) :=
    Real.sqrt_pos.2 hdisc
  have hs_sq :
      Real.sqrt (discriminant a x) ^ 2 = discriminant a x :=
    Real.sq_sqrt hdisc.le
  have hcalc :
      -((-6 * x) * Real.sqrt (discriminant a x) +
          discriminant a x *
            ((-6 * x) / (2 * Real.sqrt (discriminant a x)))) / 9 =
        x * Real.sqrt (discriminant a x) := by
    field_simp [hspos.ne']
    rw [hs_sq]
    ring
  unfold rootPrimitive
  convert (hd.mul hs).neg.div_const 9 using 1
  exact hcalc.symm

private theorem rootPrimitive_continuous (a : ℝ) :
    Continuous (rootPrimitive a) := by
  unfold rootPrimitive discriminant
  fun_prop

private theorem rootIntegrand_continuous (a : ℝ) :
    Continuous (fun x : ℝ => x * Real.sqrt (discriminant a x)) := by
  unfold discriminant
  fun_prop

private theorem integral_root_eq (a u v : ℝ) (huv : u ≤ v)
    (hpos : ∀ x ∈ Set.Ioo u v, 0 < discriminant a x) :
    (∫ x in u..v, x * Real.sqrt (discriminant a x)) =
      rootPrimitive a v - rootPrimitive a u := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le huv
      (rootPrimitive_continuous a).continuousOn
  · intro x hx
    exact rootPrimitive_hasDerivAt a x (hpos x hx)
  · exact (rootIntegrand_continuous a).intervalIntegrable _ _

private def polynomialPrimitive (a x : ℝ) : ℝ :=
  4 * a ^ 2 * x - (2 / 3) * x ^ 3

private theorem polynomialPrimitive_hasDerivAt (a x : ℝ) :
    HasDerivAt (polynomialPrimitive a) (4 * a ^ 2 - 2 * x ^ 2) x := by
  unfold polynomialPrimitive
  convert
    ((hasDerivAt_id x).const_mul (4 * a ^ 2)).sub
      (((hasDerivAt_id x).pow 3).const_mul (2 / 3)) using 1 <;>
    simp only [id_eq] <;> ring

private theorem integral_polynomial_eq (a u v : ℝ) :
    (∫ x in u..v, (4 * a ^ 2 - 2 * x ^ 2)) =
      polynomialPrimitive a v - polynomialPrimitive a u := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    exact polynomialPrimitive_hasDerivAt a x
  · exact
      (by
        fun_prop :
        Continuous (fun x : ℝ => 4 * a ^ 2 - 2 * x ^ 2)).intervalIntegrable _ _

theorem gap8 (a Vₓ : ℝ) (ha : 0 ≤ a) (hV : Vₓ = volume a) :
    Vₓ = 8 / 3 * Real.pi * a ^ 3 := by
  rcases ha.eq_or_lt with hzero | ha
  · subst a
    simpa [volume, upper, lower, discriminant] using hV
  · let b : ℝ := 2 / Real.sqrt 3 * a
    have hr : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.2 (by norm_num)
    have hr2 : Real.sqrt (3 : ℝ) ^ 2 = 3 :=
      Real.sq_sqrt (by norm_num)
    have hrlt : Real.sqrt (3 : ℝ) < 2 := by
      nlinarith
    have hscale : 1 < 2 / Real.sqrt 3 := by
      rw [lt_div_iff₀ hr]
      linarith
    have hab : a < b := by
      dsimp [b]
      simpa only [one_mul] using mul_lt_mul_of_pos_right hscale ha
    have hpos1 : ∀ x ∈ Set.Ioo (0 : ℝ) a, 0 < discriminant a x := by
      intro x hx
      have hfac : 0 < (a - x) * (a + x) :=
        mul_pos (sub_pos.mpr hx.2) (by linarith [hx.1, ha])
      unfold discriminant
      nlinarith [sq_nonneg a]
    have hpos2 : ∀ x ∈ Set.Ioo a b, 0 < discriminant a x := by
      intro x hx
      have hfac : 0 < (b - x) * (b + x) :=
        mul_pos (sub_pos.mpr hx.2) (by linarith [hx.1, ha])
      have hxsq : x ^ 2 < b ^ 2 := by
        nlinarith
      have hbsq : 3 * b ^ 2 = 4 * a ^ 2 := by
        dsimp [b]
        exact outerEndpoint_sq a
      unfold discriminant
      nlinarith
    have hD0 : discriminant a 0 = 4 * a ^ 2 := by
      simp [discriminant]
    have hDa : discriminant a a = a ^ 2 := by
      unfold discriminant
      ring
    have hDb : discriminant a b = 0 := by
      have hbsq : 3 * b ^ 2 = 4 * a ^ 2 := by
        dsimp [b]
        exact outerEndpoint_sq a
      unfold discriminant
      linarith
    have hS0 : Real.sqrt (discriminant a 0) = 2 * a := by
      rw [hD0, show 4 * a ^ 2 = (2 * a) ^ 2 by ring,
        Real.sqrt_sq_eq_abs, abs_of_pos (mul_pos (by norm_num) ha)]
    have hSa : Real.sqrt (discriminant a a) = a := by
      rw [hDa, Real.sqrt_sq_eq_abs, abs_of_pos ha]
    have hF0 : rootPrimitive a 0 = -(8 / 9) * a ^ 3 := by
      unfold rootPrimitive
      rw [hS0, hD0]
      ring
    have hFa : rootPrimitive a a = -(1 / 9) * a ^ 3 := by
      unfold rootPrimitive
      rw [hSa, hDa]
      ring
    have hFb : rootPrimitive a b = 0 := by
      unfold rootPrimitive
      rw [hDb]
      simp
    have hI1 :
        (∫ x in 0..a, x * Real.sqrt (4 * a ^ 2 - 3 * x ^ 2)) =
          7 / 9 * a ^ 3 := by
      change
        (∫ x in 0..a, x * Real.sqrt (discriminant a x)) =
          7 / 9 * a ^ 3
      calc
        (∫ x in 0..a, x * Real.sqrt (discriminant a x)) =
            rootPrimitive a a - rootPrimitive a 0 :=
          integral_root_eq a 0 a ha.le hpos1
        _ = 7 / 9 * a ^ 3 := by
          rw [hFa, hF0]
          ring
    have hI2 :
        (∫ x in a..b, x * Real.sqrt (4 * a ^ 2 - 3 * x ^ 2)) =
          1 / 9 * a ^ 3 := by
      change
        (∫ x in a..b, x * Real.sqrt (discriminant a x)) =
          1 / 9 * a ^ 3
      calc
        (∫ x in a..b, x * Real.sqrt (discriminant a x)) =
            rootPrimitive a b - rootPrimitive a a :=
          integral_root_eq a a b hab.le hpos2
        _ = 1 / 9 * a ^ 3 := by
          rw [hFb, hFa]
          ring
    have hPoly :
        (∫ x in 0..a, (4 * a ^ 2 - 2 * x ^ 2)) =
          10 / 3 * a ^ 3 := by
      calc
        (∫ x in 0..a, (4 * a ^ 2 - 2 * x ^ 2)) =
            polynomialPrimitive a a - polynomialPrimitive a 0 :=
          integral_polynomial_eq a 0 a
        _ = 10 / 3 * a ^ 3 := by
          unfold polynomialPrimitive
          ring
    have hPolyInt :
        IntervalIntegrable (fun x : ℝ => 4 * a ^ 2 - 2 * x ^ 2)
          MeasureTheory.volume 0 a :=
      (by
        fun_prop :
        Continuous (fun x : ℝ => 4 * a ^ 2 - 2 * x ^ 2)).intervalIntegrable _ _
    have hRootInt :
        IntervalIntegrable
          (fun x : ℝ => 2 * x * Real.sqrt (4 * a ^ 2 - 3 * x ^ 2))
          MeasureTheory.volume 0 a :=
      (by
        fun_prop :
        Continuous
          (fun x : ℝ => 2 * x * Real.sqrt (4 * a ^ 2 - 3 * x ^ 2))).intervalIntegrable _ _
    have hSecond :
        (∫ x in 0..a, 2 * x * Real.sqrt (4 * a ^ 2 - 3 * x ^ 2)) =
          2 * (∫ x in 0..a,
            x * Real.sqrt (4 * a ^ 2 - 3 * x ^ 2)) := by
      simpa only [mul_assoc] using
        (intervalIntegral.integral_const_mul (a := 0) (b := a) (2 : ℝ)
          (fun x : ℝ => x * Real.sqrt (4 * a ^ 2 - 3 * x ^ 2)))
    have hFirst :
        (∫ x in 0..a,
          (4 * a ^ 2 - 2 * x ^ 2 +
            2 * x * Real.sqrt (4 * a ^ 2 - 3 * x ^ 2))) =
          44 / 9 * a ^ 3 := by
      calc
        (∫ x in 0..a,
            (4 * a ^ 2 - 2 * x ^ 2 +
              2 * x * Real.sqrt (4 * a ^ 2 - 3 * x ^ 2))) =
            (∫ x in 0..a, (4 * a ^ 2 - 2 * x ^ 2)) +
              (∫ x in 0..a,
                2 * x * Real.sqrt (4 * a ^ 2 - 3 * x ^ 2)) :=
          intervalIntegral.integral_add hPolyInt hRootInt
        _ = 44 / 9 * a ^ 3 := by
          rw [hPoly, hSecond, hI1]
          ring
    rw [gap7 a Vₓ ha.le hV, hFirst]
    change
      Real.pi / 2 * (44 / 9 * a ^ 3) +
          2 * Real.pi *
            (∫ x in a..b,
              x * Real.sqrt (4 * a ^ 2 - 3 * x ^ 2)) =
        8 / 3 * Real.pi * a ^ 3
    rw [hI2]
    ring

end

end ProofGap.Exercise2478
