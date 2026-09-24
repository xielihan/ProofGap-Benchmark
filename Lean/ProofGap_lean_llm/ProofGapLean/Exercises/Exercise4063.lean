import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4063

noncomputable section

open MeasureTheory
open scoped Interval

def PolarAdmissible (a phi r : ℝ) : Prop :=
  phi ∈ Set.Icc (-Real.pi) Real.pi ∧
    r ∈ Set.Icc 0 (a * (1 + Real.cos phi))

def Ix (a : ℝ) : ℝ :=
  ∫ phi in -Real.pi..Real.pi,
    ∫ r in (0 : ℝ)..a * (1 + Real.cos phi),
      r ^ 2 * Real.sin phi ^ 2 * r

def Iy (a : ℝ) : ℝ :=
  ∫ phi in -Real.pi..Real.pi,
    ∫ r in (0 : ℝ)..a * (1 + Real.cos phi),
      r ^ 2 * Real.cos phi ^ 2 * r

def cosinePowerIntegral (n : ℕ) : ℝ :=
  ∫ phi in (0 : ℝ)..Real.pi, Real.cos phi ^ n

private theorem cos_power_reflect (n : ℕ) :
    (∫ x in Real.pi / 2..Real.pi, Real.cos x ^ n) =
      (-1 : ℝ) ^ n *
        ∫ x in (0 : ℝ)..Real.pi / 2, Real.cos x ^ n := by
  have hsub :
      Real.pi - Real.pi / 2 = Real.pi / 2 := by ring
  calc
    (∫ x in Real.pi / 2..Real.pi, Real.cos x ^ n) =
        ∫ x in (0 : ℝ)..Real.pi / 2,
          Real.cos (Real.pi - x) ^ n := by
      have h := intervalIntegral.integral_comp_sub_left
        (fun x : ℝ => Real.cos x ^ n) (a := (0 : ℝ))
        (b := Real.pi / 2) Real.pi
      rw [hsub, sub_zero] at h
      exact h.symm
    _ = ∫ x in (0 : ℝ)..Real.pi / 2,
          (-1 : ℝ) ^ n * Real.cos x ^ n := by
      apply intervalIntegral.integral_congr
      intro x hx
      change Real.cos (Real.pi - x) ^ n =
        (-1 : ℝ) ^ n * Real.cos x ^ n
      rw [Real.cos_pi_sub, neg_pow]
    _ = (-1 : ℝ) ^ n *
          ∫ x in (0 : ℝ)..Real.pi / 2, Real.cos x ^ n := by
      rw [intervalIntegral.integral_const_mul]

private theorem cosine_power_parity (n : ℕ) :
    (Even n →
        cosinePowerIntegral n =
          2 * ∫ x in (0 : ℝ)..Real.pi / 2, Real.cos x ^ n) ∧
      (Odd n → cosinePowerIntegral n = 0) := by
  have hleft :
      IntervalIntegrable (fun x : ℝ => Real.cos x ^ n) volume
        0 (Real.pi / 2) :=
    (Real.continuous_cos.pow n).intervalIntegrable _ _
  have hright :
      IntervalIntegrable (fun x : ℝ => Real.cos x ^ n) volume
        (Real.pi / 2) Real.pi :=
    (Real.continuous_cos.pow n).intervalIntegrable _ _
  have hsplit :=
    intervalIntegral.integral_add_adjacent_intervals hleft hright
  constructor
  · intro hn
    unfold cosinePowerIntegral
    rw [← hsplit, cos_power_reflect n, hn.neg_one_pow]
    ring
  · intro hn
    unfold cosinePowerIntegral
    rw [← hsplit, cos_power_reflect n, hn.neg_one_pow]
    ring

private theorem half_cos_recurrence (n : ℕ) :
    (∫ x in (0 : ℝ)..Real.pi / 2, Real.cos x ^ (n + 2)) =
      (n + 1 : ℝ) / (n + 2 : ℝ) *
        ∫ x in (0 : ℝ)..Real.pi / 2, Real.cos x ^ n := by
  simpa [Real.cos_pi_div_two, Real.sin_pi_div_two, Real.cos_zero,
    Real.sin_zero] using
    (integral_cos_pow (a := (0 : ℝ)) (b := Real.pi / 2) (n := n))

private theorem half_cos_zero :
    (∫ x in (0 : ℝ)..Real.pi / 2, Real.cos x ^ 0) =
      Real.pi / 2 := by simp

private theorem half_cos_two :
    (∫ x in (0 : ℝ)..Real.pi / 2, Real.cos x ^ 2) =
      Real.pi / 4 := by
  rw [half_cos_recurrence 0, half_cos_zero]
  norm_num
  ring

private theorem half_cos_four :
    (∫ x in (0 : ℝ)..Real.pi / 2, Real.cos x ^ 4) =
      3 * Real.pi / 16 := by
  rw [half_cos_recurrence 2, half_cos_two]
  norm_num
  ring

private theorem half_cos_six :
    (∫ x in (0 : ℝ)..Real.pi / 2, Real.cos x ^ 6) =
      5 * Real.pi / 32 := by
  rw [half_cos_recurrence 4, half_cos_four]
  norm_num
  ring

private theorem half_cos_eight :
    (∫ x in (0 : ℝ)..Real.pi / 2, Real.cos x ^ 8) =
      35 * Real.pi / 256 := by
  rw [half_cos_recurrence 6, half_cos_six]
  norm_num
  ring

private theorem half_cos_ten :
    (∫ x in (0 : ℝ)..Real.pi / 2, Real.cos x ^ 10) =
      63 * Real.pi / 512 := by
  rw [half_cos_recurrence 8, half_cos_eight]
  norm_num
  ring

private theorem half_cos_twelve :
    (∫ x in (0 : ℝ)..Real.pi / 2, Real.cos x ^ 12) =
      231 * Real.pi / 2048 := by
  rw [half_cos_recurrence 10, half_cos_ten]
  norm_num
  ring

private theorem integral_r_cube (u : ℝ) :
    (∫ r in (0 : ℝ)..u, r ^ 3) = u ^ 4 / 4 := by
  have hd :
      ∀ r ∈ Set.uIcc (0 : ℝ) u,
        HasDerivAt (fun t : ℝ => t ^ 4 / 4) (r ^ 3) r := by
    intro r hr
    convert ((hasDerivAt_id r).pow 4).div_const 4 using 1 <;>
      norm_num <;> ring
  simpa using intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    ((continuous_id.pow 3).intervalIntegrable _ _)

private theorem integral_even_neg_pi_pi
    (f : ℝ → ℝ) (hf : Continuous f)
    (heven : ∀ x : ℝ, f (-x) = f x) :
    (∫ x in -Real.pi..Real.pi, f x) =
      2 * ∫ x in (0 : ℝ)..Real.pi, f x := by
  have hleft : IntervalIntegrable f volume (-Real.pi) 0 :=
    hf.intervalIntegrable _ _
  have hright : IntervalIntegrable f volume 0 Real.pi :=
    hf.intervalIntegrable _ _
  have hsplit :=
    intervalIntegral.integral_add_adjacent_intervals hleft hright
  have hreflect :
      (∫ x in -Real.pi..(0 : ℝ), f x) =
        ∫ x in (0 : ℝ)..Real.pi, f x := by
    calc
      (∫ x in -Real.pi..(0 : ℝ), f x) =
          ∫ x in (0 : ℝ)..Real.pi, f (-x) := by
        simpa using
          (intervalIntegral.integral_comp_neg
            (f := f) (a := (0 : ℝ)) (b := Real.pi)).symm
      _ = ∫ x in (0 : ℝ)..Real.pi, f x := by
        apply intervalIntegral.integral_congr
        intro x hx
        exact heven x
  rw [← hsplit, hreflect]
  ring

private theorem cosinePowerIntegral_zero :
    cosinePowerIntegral 0 = Real.pi := by
  calc
    cosinePowerIntegral 0 =
        2 * ∫ x in (0 : ℝ)..Real.pi / 2, Real.cos x ^ 0 :=
      (cosine_power_parity 0).1 (by decide)
    _ = Real.pi := by rw [half_cos_zero]; ring

private theorem cosinePowerIntegral_one :
    cosinePowerIntegral 1 = 0 :=
  (cosine_power_parity 1).2 (by decide)

private theorem cosinePowerIntegral_two :
    cosinePowerIntegral 2 = Real.pi / 2 := by
  calc
    cosinePowerIntegral 2 =
        2 * ∫ x in (0 : ℝ)..Real.pi / 2, Real.cos x ^ 2 :=
      (cosine_power_parity 2).1 (by decide)
    _ = Real.pi / 2 := by rw [half_cos_two]; ring

private theorem cosinePowerIntegral_three :
    cosinePowerIntegral 3 = 0 :=
  (cosine_power_parity 3).2 (by decide)

private theorem cosinePowerIntegral_four :
    cosinePowerIntegral 4 = 3 * Real.pi / 8 := by
  calc
    cosinePowerIntegral 4 =
        2 * ∫ x in (0 : ℝ)..Real.pi / 2, Real.cos x ^ 4 :=
      (cosine_power_parity 4).1 (by decide)
    _ = 3 * Real.pi / 8 := by rw [half_cos_four]; ring

private theorem cosinePowerIntegral_five :
    cosinePowerIntegral 5 = 0 :=
  (cosine_power_parity 5).2 (by decide)

private theorem cosinePowerIntegral_six :
    cosinePowerIntegral 6 = 5 * Real.pi / 16 := by
  calc
    cosinePowerIntegral 6 =
        2 * ∫ x in (0 : ℝ)..Real.pi / 2, Real.cos x ^ 6 :=
      (cosine_power_parity 6).1 (by decide)
    _ = 5 * Real.pi / 16 := by rw [half_cos_six]; ring

private theorem ix_angular_integral :
    (∫ phi in (0 : ℝ)..Real.pi,
        (1 + 4 * Real.cos phi + 6 * Real.cos phi ^ 2 +
            4 * Real.cos phi ^ 3 + Real.cos phi ^ 4) *
          Real.sin phi ^ 2) =
      21 / 16 * Real.pi := by
  have h0 : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 Real.pi :=
    continuous_const.intervalIntegrable _ _
  have h1 : IntervalIntegrable (fun x : ℝ => 4 * Real.cos x) volume 0 Real.pi :=
    (continuous_const.mul Real.continuous_cos).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun x : ℝ => 5 * Real.cos x ^ 2) volume 0 Real.pi :=
    (continuous_const.mul (Real.continuous_cos.pow 2)).intervalIntegrable _ _
  have h4 : IntervalIntegrable (fun x : ℝ => 5 * Real.cos x ^ 4) volume 0 Real.pi :=
    (continuous_const.mul (Real.continuous_cos.pow 4)).intervalIntegrable _ _
  have h5 : IntervalIntegrable (fun x : ℝ => 4 * Real.cos x ^ 5) volume 0 Real.pi :=
    (continuous_const.mul (Real.continuous_cos.pow 5)).intervalIntegrable _ _
  have h6 : IntervalIntegrable (fun x : ℝ => Real.cos x ^ 6) volume 0 Real.pi :=
    (Real.continuous_cos.pow 6).intervalIntegrable _ _
  calc
    (∫ phi in (0 : ℝ)..Real.pi,
        (1 + 4 * Real.cos phi + 6 * Real.cos phi ^ 2 +
            4 * Real.cos phi ^ 3 + Real.cos phi ^ 4) *
          Real.sin phi ^ 2) =
        ∫ phi in (0 : ℝ)..Real.pi,
          ((((1 + 4 * Real.cos phi) + 5 * Real.cos phi ^ 2) -
              5 * Real.cos phi ^ 4) -
            4 * Real.cos phi ^ 5) - Real.cos phi ^ 6 := by
      apply intervalIntegral.integral_congr
      intro phi hphi
      change
        (1 + 4 * Real.cos phi + 6 * Real.cos phi ^ 2 +
            4 * Real.cos phi ^ 3 + Real.cos phi ^ 4) *
              Real.sin phi ^ 2 =
          ((((1 + 4 * Real.cos phi) + 5 * Real.cos phi ^ 2) -
              5 * Real.cos phi ^ 4) -
            4 * Real.cos phi ^ 5) - Real.cos phi ^ 6
      have htrig := Real.sin_sq_add_cos_sq phi
      rw [show Real.sin phi ^ 2 = 1 - Real.cos phi ^ 2 by
        nlinarith]
      ring
    _ =
        (((((∫ _phi in (0 : ℝ)..Real.pi, (1 : ℝ)) +
              ∫ phi in (0 : ℝ)..Real.pi, 4 * Real.cos phi) +
            ∫ phi in (0 : ℝ)..Real.pi, 5 * Real.cos phi ^ 2) -
          ∫ phi in (0 : ℝ)..Real.pi, 5 * Real.cos phi ^ 4) -
        ∫ phi in (0 : ℝ)..Real.pi, 4 * Real.cos phi ^ 5) -
          ∫ phi in (0 : ℝ)..Real.pi, Real.cos phi ^ 6 := by
      rw [intervalIntegral.integral_sub
          ((((h0.add h1).add h2).sub h4).sub h5) h6,
        intervalIntegral.integral_sub (((h0.add h1).add h2).sub h4) h5,
        intervalIntegral.integral_sub ((h0.add h1).add h2) h4,
        intervalIntegral.integral_add (h0.add h1) h2,
        intervalIntegral.integral_add h0 h1]
    _ = 21 / 16 * Real.pi := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul]
      have hi1 :
          (∫ x in (0 : ℝ)..Real.pi, Real.cos x) = 0 := by
        simpa [cosinePowerIntegral] using cosinePowerIntegral_one
      have hi2 :
          (∫ x in (0 : ℝ)..Real.pi, Real.cos x ^ 2) = Real.pi / 2 := by
        simpa [cosinePowerIntegral] using cosinePowerIntegral_two
      have hi4 :
          (∫ x in (0 : ℝ)..Real.pi, Real.cos x ^ 4) =
            3 * Real.pi / 8 := by
        simpa [cosinePowerIntegral] using cosinePowerIntegral_four
      have hi5 :
          (∫ x in (0 : ℝ)..Real.pi, Real.cos x ^ 5) = 0 := by
        simpa [cosinePowerIntegral] using cosinePowerIntegral_five
      have hi6 :
          (∫ x in (0 : ℝ)..Real.pi, Real.cos x ^ 6) =
            5 * Real.pi / 16 := by
        simpa [cosinePowerIntegral] using cosinePowerIntegral_six
      rw [hi1, hi2, hi4, hi5, hi6]
      simp
      ring

private theorem iy_angular_integral :
    (∫ phi in (0 : ℝ)..Real.pi,
        (Real.cos phi ^ 2 + 4 * Real.cos phi ^ 3 +
          6 * Real.cos phi ^ 4 + 4 * Real.cos phi ^ 5 +
          Real.cos phi ^ 6)) =
      49 / 16 * Real.pi := by
  have h2 : IntervalIntegrable (fun x : ℝ => Real.cos x ^ 2) volume 0 Real.pi :=
    (Real.continuous_cos.pow 2).intervalIntegrable _ _
  have h3 : IntervalIntegrable (fun x : ℝ => 4 * Real.cos x ^ 3) volume 0 Real.pi :=
    (continuous_const.mul (Real.continuous_cos.pow 3)).intervalIntegrable _ _
  have h4 : IntervalIntegrable (fun x : ℝ => 6 * Real.cos x ^ 4) volume 0 Real.pi :=
    (continuous_const.mul (Real.continuous_cos.pow 4)).intervalIntegrable _ _
  have h5 : IntervalIntegrable (fun x : ℝ => 4 * Real.cos x ^ 5) volume 0 Real.pi :=
    (continuous_const.mul (Real.continuous_cos.pow 5)).intervalIntegrable _ _
  have h6 : IntervalIntegrable (fun x : ℝ => Real.cos x ^ 6) volume 0 Real.pi :=
    (Real.continuous_cos.pow 6).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (((h2.add h3).add h4).add h5) h6,
    intervalIntegral.integral_add ((h2.add h3).add h4) h5,
    intervalIntegral.integral_add (h2.add h3) h4,
    intervalIntegral.integral_add h2 h3,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  change
    cosinePowerIntegral 2 + 4 * cosinePowerIntegral 3 +
        6 * cosinePowerIntegral 4 + 4 * cosinePowerIntegral 5 +
        cosinePowerIntegral 6 =
      49 / 16 * Real.pi
  rw [cosinePowerIntegral_two, cosinePowerIntegral_three,
    cosinePowerIntegral_four, cosinePowerIntegral_five,
    cosinePowerIntegral_six]
  ring

theorem gap1 (a phi r : ℝ) (h : PolarAdmissible a phi r) :
    -Real.pi ≤ phi := by
  exact h.1.1

theorem gap2 (a phi r : ℝ) (h : PolarAdmissible a phi r) :
    phi ≤ Real.pi := by
  exact h.1.2

theorem gap3 (a phi r : ℝ) (h : PolarAdmissible a phi r) :
    0 ≤ r := by
  exact h.2.1

theorem gap4 (a phi r : ℝ) (h : PolarAdmissible a phi r) :
    r ≤ a * (1 + Real.cos phi) := by
  exact h.2.2

theorem gap5 (a : ℝ) (ha : 0 ≤ a) :
    Ix a =
      ∫ phi in -Real.pi..Real.pi,
        ∫ r in (0 : ℝ)..a * (1 + Real.cos phi),
          r ^ 2 * Real.sin phi ^ 2 * r := by
  rfl

theorem gap6 (a : ℝ) (ha : 0 ≤ a) :
    Ix a =
      ∫ phi in -Real.pi..Real.pi,
        1 / 4 * a ^ 4 * (1 + Real.cos phi) ^ 4 *
          Real.sin phi ^ 2 := by
  rw [gap5 a ha]
  apply intervalIntegral.integral_congr
  intro phi hphi
  calc
    (∫ r in (0 : ℝ)..a * (1 + Real.cos phi),
        r ^ 2 * Real.sin phi ^ 2 * r) =
        Real.sin phi ^ 2 *
          ∫ r in (0 : ℝ)..a * (1 + Real.cos phi), r ^ 3 := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro r hr
      ring
    _ = Real.sin phi ^ 2 *
        ((a * (1 + Real.cos phi)) ^ 4 / 4) := by
      rw [integral_r_cube]
    _ = 1 / 4 * a ^ 4 * (1 + Real.cos phi) ^ 4 *
        Real.sin phi ^ 2 := by ring

theorem gap7 (a : ℝ) (ha : 0 ≤ a) :
    Ix a =
      2 * (1 / 4 : ℝ) * a ^ 4 *
        ∫ phi in (0 : ℝ)..Real.pi,
          (1 + 4 * Real.cos phi + 6 * Real.cos phi ^ 2 +
              4 * Real.cos phi ^ 3 + Real.cos phi ^ 4) *
            Real.sin phi ^ 2 := by
  rw [gap6 a ha]
  have hfactor :
      (∫ phi in -Real.pi..Real.pi,
          1 / 4 * a ^ 4 * (1 + Real.cos phi) ^ 4 *
            Real.sin phi ^ 2) =
        (1 / 4 * a ^ 4) *
          ∫ phi in -Real.pi..Real.pi,
            (1 + Real.cos phi) ^ 4 * Real.sin phi ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro phi hphi
    ring
  rw [hfactor]
  let f : ℝ → ℝ :=
    fun phi => (1 + Real.cos phi) ^ 4 * Real.sin phi ^ 2
  have hf : Continuous f := by
    dsimp [f]
    fun_prop
  have heven : ∀ x : ℝ, f (-x) = f x := by
    intro x
    dsimp [f]
    rw [Real.cos_neg, Real.sin_neg]
    ring
  have hsym := integral_even_neg_pi_pi f hf heven
  have hexpand :
      (∫ phi in (0 : ℝ)..Real.pi, f phi) =
        ∫ phi in (0 : ℝ)..Real.pi,
          (1 + 4 * Real.cos phi + 6 * Real.cos phi ^ 2 +
              4 * Real.cos phi ^ 3 + Real.cos phi ^ 4) *
            Real.sin phi ^ 2 := by
    apply intervalIntegral.integral_congr
    intro phi hphi
    dsimp [f]
    ring
  change
    (1 / 4 * a ^ 4) *
        (∫ phi in -Real.pi..Real.pi, f phi) = _
  rw [hsym, hexpand]
  ring

theorem gap8 (a : ℝ) (ha : 0 ≤ a) :
    Ix a = 1 / 2 * Real.pi * a ^ 4 * (21 / 16 : ℝ) := by
  rw [gap7 a ha, ix_angular_integral]
  ring

theorem gap9 (a : ℝ) :
    1 / 2 * Real.pi * a ^ 4 * (21 / 16 : ℝ) =
      21 / 32 * Real.pi * a ^ 4 := by
  ring

theorem gap10 (a : ℝ) (ha : 0 ≤ a) :
    Ix a = 21 / 32 * Real.pi * a ^ 4 := by
  rw [gap8 a ha, gap9 a]

theorem gap11 (a : ℝ) (ha : 0 ≤ a) :
    Iy a =
      ∫ phi in -Real.pi..Real.pi,
        ∫ r in (0 : ℝ)..a * (1 + Real.cos phi),
          r ^ 2 * Real.cos phi ^ 2 * r := by
  rfl

theorem gap12 (a : ℝ) (ha : 0 ≤ a) :
    Iy a =
      1 / 2 * a ^ 4 *
        ∫ phi in (0 : ℝ)..Real.pi,
          (1 + Real.cos phi) ^ 4 * Real.cos phi ^ 2 := by
  rw [gap11 a ha]
  have hinner (phi : ℝ) :
      (∫ r in (0 : ℝ)..a * (1 + Real.cos phi),
          r ^ 2 * Real.cos phi ^ 2 * r) =
        1 / 4 * a ^ 4 * (1 + Real.cos phi) ^ 4 *
          Real.cos phi ^ 2 := by
    calc
      (∫ r in (0 : ℝ)..a * (1 + Real.cos phi),
          r ^ 2 * Real.cos phi ^ 2 * r) =
          Real.cos phi ^ 2 *
            ∫ r in (0 : ℝ)..a * (1 + Real.cos phi), r ^ 3 := by
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro r hr
        ring
      _ = Real.cos phi ^ 2 *
          ((a * (1 + Real.cos phi)) ^ 4 / 4) := by
        rw [integral_r_cube]
      _ = 1 / 4 * a ^ 4 * (1 + Real.cos phi) ^ 4 *
          Real.cos phi ^ 2 := by ring
  simp_rw [hinner]
  have hfactor :
      (∫ phi in -Real.pi..Real.pi,
          1 / 4 * a ^ 4 * (1 + Real.cos phi) ^ 4 *
            Real.cos phi ^ 2) =
        (1 / 4 * a ^ 4) *
          ∫ phi in -Real.pi..Real.pi,
            (1 + Real.cos phi) ^ 4 * Real.cos phi ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro phi hphi
    ring
  rw [hfactor]
  let f : ℝ → ℝ :=
    fun phi => (1 + Real.cos phi) ^ 4 * Real.cos phi ^ 2
  have hf : Continuous f := by
    dsimp [f]
    fun_prop
  have heven : ∀ x : ℝ, f (-x) = f x := by
    intro x
    dsimp [f]
    rw [Real.cos_neg]
  have hsym := integral_even_neg_pi_pi f hf heven
  change
    (1 / 4 * a ^ 4) *
        (∫ phi in -Real.pi..Real.pi, f phi) = _
  rw [hsym]
  ring

theorem gap13 (a : ℝ) (ha : 0 ≤ a) :
    Iy a =
      1 / 2 * a ^ 4 *
        ∫ phi in (0 : ℝ)..Real.pi,
          (Real.cos phi ^ 2 + 4 * Real.cos phi ^ 3 +
            6 * Real.cos phi ^ 4 + 4 * Real.cos phi ^ 5 +
            Real.cos phi ^ 6) := by
  rw [gap12 a ha]
  congr 1
  apply intervalIntegral.integral_congr
  intro phi hphi
  ring

theorem gap14 (a : ℝ) (ha : 0 ≤ a) :
    Iy a = 49 / 32 * Real.pi * a ^ 4 := by
  rw [gap13 a ha, iy_angular_integral]
  ring

theorem gap15 (n : ℕ) (hn : 0 < n) :
    (Even n →
        cosinePowerIntegral n =
          2 * ∫ phi in (0 : ℝ)..Real.pi / 2, Real.cos phi ^ n) ∧
      (Odd n → cosinePowerIntegral n = 0) := by
  exact cosine_power_parity n

theorem gap16 (a : ℝ) (ha : 0 ≤ a) :
    Ix a =
      a ^ 4 / 2 *
        ∫ phi in (0 : ℝ)..Real.pi,
          (1 + Real.cos phi) ^ 4 * Real.sin phi ^ 2 := by
  rw [gap6 a ha]
  have hfactor :
      (∫ phi in -Real.pi..Real.pi,
          1 / 4 * a ^ 4 * (1 + Real.cos phi) ^ 4 *
            Real.sin phi ^ 2) =
        (1 / 4 * a ^ 4) *
          ∫ phi in -Real.pi..Real.pi,
            (1 + Real.cos phi) ^ 4 * Real.sin phi ^ 2 := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro phi hphi
    ring
  rw [hfactor]
  let f : ℝ → ℝ :=
    fun phi => (1 + Real.cos phi) ^ 4 * Real.sin phi ^ 2
  have hf : Continuous f := by
    dsimp [f]
    fun_prop
  have heven : ∀ x : ℝ, f (-x) = f x := by
    intro x
    dsimp [f]
    rw [Real.cos_neg, Real.sin_neg]
    ring
  have hsym := integral_even_neg_pi_pi f hf heven
  change
    (1 / 4 * a ^ 4) *
        (∫ phi in -Real.pi..Real.pi, f phi) = _
  rw [hsym]
  ring

theorem gap17 (a : ℝ) (ha : 0 ≤ a) :
    Ix a =
      (2 : ℝ) ^ 6 * a ^ 4 *
        ∫ x in (0 : ℝ)..Real.pi / 2,
          Real.cos x ^ 10 * (1 - Real.cos x ^ 2) := by
  rw [gap16 a ha]
  let f : ℝ → ℝ :=
    fun phi => (1 + Real.cos phi) ^ 4 * Real.sin phi ^ 2
  have hscale :
      2 *
          (∫ x in (0 : ℝ)..Real.pi / 2, f (2 * x)) =
        ∫ phi in (0 : ℝ)..Real.pi, f phi := by
    have h := intervalIntegral.smul_integral_comp_mul_left
      (f := f) (a := (0 : ℝ)) (b := Real.pi / 2) (2 : ℝ)
    simpa only [smul_eq_mul, mul_zero] using
      (show
        2 * (∫ x in (0 : ℝ)..Real.pi / 2, f (2 * x)) =
          ∫ x in (0 : ℝ)..Real.pi, f x by
        convert h using 1 <;> ring)
  have hpoint :
      (∫ x in (0 : ℝ)..Real.pi / 2, f (2 * x)) =
        64 *
          ∫ x in (0 : ℝ)..Real.pi / 2,
            Real.cos x ^ 10 * (1 - Real.cos x ^ 2) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    dsimp [f]
    rw [Real.cos_two_mul, Real.sin_two_mul]
    have htrig := Real.sin_sq_add_cos_sq x
    rw [show 1 - Real.cos x ^ 2 = Real.sin x ^ 2 by nlinarith]
    ring
  change a ^ 4 / 2 * (∫ phi in (0 : ℝ)..Real.pi, f phi) = _
  rw [← hscale, hpoint]
  norm_num
  ring

theorem gap18 (a : ℝ) (ha : 0 ≤ a) :
    Ix a =
      (2 : ℝ) ^ 6 * a ^ 4 *
        ((9 * 7 * 5 * 3 * 1 : ℝ) / (10 * 8 * 6 * 4 * 2)) *
        (1 - (11 : ℝ) / 12) * (Real.pi / 2) := by
  rw [gap17 a ha]
  have h10 : IntervalIntegrable (fun x : ℝ => Real.cos x ^ 10)
      volume 0 (Real.pi / 2) :=
    (Real.continuous_cos.pow 10).intervalIntegrable _ _
  have h12 : IntervalIntegrable (fun x : ℝ => Real.cos x ^ 12)
      volume 0 (Real.pi / 2) :=
    (Real.continuous_cos.pow 12).intervalIntegrable _ _
  have hint :
      (∫ x in (0 : ℝ)..Real.pi / 2,
          Real.cos x ^ 10 * (1 - Real.cos x ^ 2)) =
        (∫ x in (0 : ℝ)..Real.pi / 2, Real.cos x ^ 10) -
          ∫ x in (0 : ℝ)..Real.pi / 2, Real.cos x ^ 12 := by
    calc
      (∫ x in (0 : ℝ)..Real.pi / 2,
          Real.cos x ^ 10 * (1 - Real.cos x ^ 2)) =
          ∫ x in (0 : ℝ)..Real.pi / 2,
            Real.cos x ^ 10 - Real.cos x ^ 12 := by
        apply intervalIntegral.integral_congr
        intro x hx
        ring
      _ = _ := intervalIntegral.integral_sub h10 h12
  rw [hint, half_cos_ten, half_cos_twelve]
  norm_num
  ring

theorem gap19 (a : ℝ) :
    (2 : ℝ) ^ 6 * a ^ 4 *
          ((9 * 7 * 5 * 3 * 1 : ℝ) / (10 * 8 * 6 * 4 * 2)) *
          (1 - (11 : ℝ) / 12) * (Real.pi / 2) =
      21 / 32 * Real.pi * a ^ 4 := by
  norm_num
  ring

theorem gap20 (a : ℝ) (ha : 0 ≤ a) :
    Ix a = 21 / 32 * Real.pi * a ^ 4 := by
  rw [gap18 a ha, gap19 a]

theorem gap21 (a : ℝ) (ha : 0 ≤ a) :
    Iy a =
      a ^ 4 / 2 *
        ∫ phi in (0 : ℝ)..Real.pi,
          (1 + Real.cos phi) ^ 4 * Real.cos phi ^ 2 := by
  rw [gap12 a ha]
  ring

theorem gap22 (a : ℝ) (ha : 0 ≤ a) :
    Iy a =
      (a ^ 4 / 2 *
          (∫ phi in (0 : ℝ)..Real.pi,
            (1 + Real.cos phi) ^ 4)) -
        21 / 32 * Real.pi * a ^ 4 := by
  rw [gap21 a ha]
  have htotal : IntervalIntegrable
      (fun phi : ℝ => (1 + Real.cos phi) ^ 4) volume 0 Real.pi :=
    ((continuous_const.add Real.continuous_cos).pow 4).intervalIntegrable _ _
  have hsin : IntervalIntegrable
      (fun phi : ℝ => (1 + Real.cos phi) ^ 4 * Real.sin phi ^ 2)
      volume 0 Real.pi :=
    (((continuous_const.add Real.continuous_cos).pow 4).mul
      (Real.continuous_sin.pow 2)).intervalIntegrable _ _
  have hdecomp :
      (∫ phi in (0 : ℝ)..Real.pi,
          (1 + Real.cos phi) ^ 4 * Real.cos phi ^ 2) =
        (∫ phi in (0 : ℝ)..Real.pi, (1 + Real.cos phi) ^ 4) -
          ∫ phi in (0 : ℝ)..Real.pi,
            (1 + Real.cos phi) ^ 4 * Real.sin phi ^ 2 := by
    calc
      (∫ phi in (0 : ℝ)..Real.pi,
          (1 + Real.cos phi) ^ 4 * Real.cos phi ^ 2) =
          ∫ phi in (0 : ℝ)..Real.pi,
            (1 + Real.cos phi) ^ 4 -
              (1 + Real.cos phi) ^ 4 * Real.sin phi ^ 2 := by
        apply intervalIntegral.integral_congr
        intro phi hphi
        change
          (1 + Real.cos phi) ^ 4 * Real.cos phi ^ 2 =
            (1 + Real.cos phi) ^ 4 -
              (1 + Real.cos phi) ^ 4 * Real.sin phi ^ 2
        have htrig := Real.sin_sq_add_cos_sq phi
        rw [show Real.cos phi ^ 2 = 1 - Real.sin phi ^ 2 by
          nlinarith]
        ring
      _ = _ := intervalIntegral.integral_sub htotal hsin
  have hix := gap16 a ha
  rw [gap10 a ha] at hix
  calc
    a ^ 4 / 2 *
          (∫ phi in (0 : ℝ)..Real.pi,
            (1 + Real.cos phi) ^ 4 * Real.cos phi ^ 2) =
        a ^ 4 / 2 *
          ((∫ phi in (0 : ℝ)..Real.pi, (1 + Real.cos phi) ^ 4) -
            (∫ phi in (0 : ℝ)..Real.pi,
              (1 + Real.cos phi) ^ 4 * Real.sin phi ^ 2)) := by
      rw [hdecomp]
    _ =
        (a ^ 4 / 2 *
            (∫ phi in (0 : ℝ)..Real.pi, (1 + Real.cos phi) ^ 4)) -
          (a ^ 4 / 2 *
            (∫ phi in (0 : ℝ)..Real.pi,
              (1 + Real.cos phi) ^ 4 * Real.sin phi ^ 2)) := by ring
    _ =
        (a ^ 4 / 2 *
          (∫ phi in (0 : ℝ)..Real.pi, (1 + Real.cos phi) ^ 4)) -
        21 / 32 * Real.pi * a ^ 4 := by
      rw [← hix]

theorem gap23 (a : ℝ) (ha : 0 ≤ a) :
    Iy a =
      ((2 : ℝ) ^ 4 * a ^ 4 *
          (∫ x in (0 : ℝ)..Real.pi / 2, Real.cos x ^ 8)) -
        21 / 32 * Real.pi * a ^ 4 := by
  rw [gap22 a ha]
  let f : ℝ → ℝ := fun phi => (1 + Real.cos phi) ^ 4
  have hscale :
      2 *
          (∫ x in (0 : ℝ)..Real.pi / 2, f (2 * x)) =
        ∫ phi in (0 : ℝ)..Real.pi, f phi := by
    have h := intervalIntegral.smul_integral_comp_mul_left
      (f := f) (a := (0 : ℝ)) (b := Real.pi / 2) (2 : ℝ)
    simpa only [smul_eq_mul, mul_zero] using
      (show
        2 * (∫ x in (0 : ℝ)..Real.pi / 2, f (2 * x)) =
          ∫ x in (0 : ℝ)..Real.pi, f x by
        convert h using 1 <;> ring)
  have hpoint :
      (∫ x in (0 : ℝ)..Real.pi / 2, f (2 * x)) =
        16 * ∫ x in (0 : ℝ)..Real.pi / 2, Real.cos x ^ 8 := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    dsimp [f]
    rw [Real.cos_two_mul]
    ring
  have hscaled :
      a ^ 4 / 2 * (∫ phi in (0 : ℝ)..Real.pi, f phi) =
        (2 : ℝ) ^ 4 * a ^ 4 *
          ∫ x in (0 : ℝ)..Real.pi / 2, Real.cos x ^ 8 := by
    rw [← hscale, hpoint]
    norm_num
    ring
  have hscaled' :
      a ^ 4 / 2 *
          (∫ phi in (0 : ℝ)..Real.pi, (1 + Real.cos phi) ^ 4) =
        (2 : ℝ) ^ 4 * a ^ 4 *
          ∫ x in (0 : ℝ)..Real.pi / 2, Real.cos x ^ 8 := by
    simpa [f] using hscaled
  simpa only [sub_eq_add_neg] using
    congrArg
      (fun z : ℝ => z - 21 / 32 * Real.pi * a ^ 4) hscaled'

theorem gap24 (a : ℝ) :
    ((2 : ℝ) ^ 4 * a ^ 4 *
          (∫ x in (0 : ℝ)..Real.pi / 2, Real.cos x ^ 8)) -
        21 / 32 * Real.pi * a ^ 4 =
      70 / 32 * Real.pi * a ^ 4 -
        21 / 32 * Real.pi * a ^ 4 := by
  have h := congrArg
    (fun z : ℝ =>
      (2 : ℝ) ^ 4 * a ^ 4 * z -
        21 / 32 * Real.pi * a ^ 4) half_cos_eight
  have h' :
      (2 : ℝ) ^ 4 * a ^ 4 *
            (∫ x in (0 : ℝ)..Real.pi / 2, Real.cos x ^ 8) -
          21 / 32 * Real.pi * a ^ 4 =
        (2 : ℝ) ^ 4 * a ^ 4 * (35 * Real.pi / 256) -
          21 / 32 * Real.pi * a ^ 4 := by
    simpa only [sub_eq_add_neg] using h
  rw [h']
  norm_num
  ring

theorem gap25 (a : ℝ) :
    70 / 32 * Real.pi * a ^ 4 -
        21 / 32 * Real.pi * a ^ 4 =
      49 / 32 * Real.pi * a ^ 4 := by
  ring

theorem gap26 (a : ℝ) (ha : 0 ≤ a) :
    Iy a = 49 / 32 * Real.pi * a ^ 4 := by
  rw [gap23 a ha, gap24 a, gap25 a]

end

end ProofGap.Exercise4063
