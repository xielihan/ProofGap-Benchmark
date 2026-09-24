import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise858

noncomputable section

/-- The real, sign-preserving cube root. -/
def signedCbrt (x : ℝ) : ℝ :=
  Real.sign x * Real.rpow |x| (1 / 3 : ℝ)

def q (x : ℝ) : ℝ :=
  (1 + x ^ 3) / (1 - x ^ 3)

def y (x : ℝ) : ℝ :=
  signedCbrt (q x)

/-- Exercise 858, gap 1.
Both the quotient denominator and cube-root argument must be nonzero. -/
private theorem rpowCbrtProduct (u : ℝ) (hu : 0 < u) :
    Real.rpow (u ^ 2) (1 / 3 : ℝ) * Real.rpow u (1 / 3 : ℝ) = u := by
  have hmul :
      Real.rpow (u * u) (1 / 3 : ℝ) =
        Real.rpow u (1 / 3 : ℝ) * Real.rpow u (1 / 3 : ℝ) :=
    Real.mul_rpow (le_of_lt hu) (le_of_lt hu)
  have hadd₁ :
      Real.rpow u ((1 / 3 : ℝ) + (1 / 3 : ℝ)) =
        Real.rpow u (1 / 3 : ℝ) * Real.rpow u (1 / 3 : ℝ) :=
    Real.rpow_add hu (1 / 3 : ℝ) (1 / 3 : ℝ)
  have hadd₂ :
      Real.rpow u (((1 / 3 : ℝ) + (1 / 3 : ℝ)) + (1 / 3 : ℝ)) =
        Real.rpow u ((1 / 3 : ℝ) + (1 / 3 : ℝ)) *
          Real.rpow u (1 / 3 : ℝ) :=
    Real.rpow_add hu ((1 / 3 : ℝ) + (1 / 3 : ℝ)) (1 / 3 : ℝ)
  calc
    Real.rpow (u ^ 2) (1 / 3 : ℝ) * Real.rpow u (1 / 3 : ℝ) =
        (Real.rpow u (1 / 3 : ℝ) * Real.rpow u (1 / 3 : ℝ)) *
          Real.rpow u (1 / 3 : ℝ) := by
      rw [pow_two]
      exact congrArg (fun t => t * Real.rpow u (1 / 3 : ℝ)) hmul
    _ = Real.rpow u ((1 / 3 : ℝ) + (1 / 3 : ℝ)) *
          Real.rpow u (1 / 3 : ℝ) := by
      exact congrArg (fun t => t * Real.rpow u (1 / 3 : ℝ)) hadd₁.symm
    _ = Real.rpow u (((1 / 3 : ℝ) + (1 / 3 : ℝ)) + (1 / 3 : ℝ)) :=
      hadd₂.symm
    _ = u := by
      convert Real.rpow_one u using 1 <;> norm_num

private theorem signedCbrtSqMul (z : ℝ) :
    signedCbrt (z ^ 2) * signedCbrt z = z := by
  rcases lt_trichotomy z 0 with hz | hz | hz
  · have hz2 : 0 < z ^ 2 := by
      rw [pow_two]
      exact mul_self_pos.mpr hz.ne
    have hu : 0 < -z := neg_pos.mpr hz
    have hp :
        Real.rpow (z ^ 2) (1 / 3 : ℝ) * Real.rpow (-z) (1 / 3 : ℝ) = -z := by
      rw [show z ^ 2 = (-z) ^ 2 by ring]
      exact rpowCbrtProduct (-z) hu
    have hsquare :
        signedCbrt (z ^ 2) = Real.rpow (z ^ 2) (1 / 3 : ℝ) := by
      simp [signedCbrt, Real.sign, hz2, not_lt_of_ge hz2.le,
        abs_of_pos hz2]
    have hroot :
        signedCbrt z = -Real.rpow (-z) (1 / 3 : ℝ) := by
      simp [signedCbrt, Real.sign, hz, abs_of_neg hz]
    rw [hsquare, hroot]
    calc
      Real.rpow (z ^ 2) (1 / 3 : ℝ) *
          -Real.rpow (-z) (1 / 3 : ℝ) =
        -(Real.rpow (z ^ 2) (1 / 3 : ℝ) *
          Real.rpow (-z) (1 / 3 : ℝ)) := by ring
      _ = -(-z) := by rw [hp]
      _ = z := by ring
  · subst z
    simp [signedCbrt, Real.sign]
  · have hz2 : 0 < z ^ 2 := pow_pos hz 2
    have hsquare :
        signedCbrt (z ^ 2) = Real.rpow (z ^ 2) (1 / 3 : ℝ) := by
      simp [signedCbrt, Real.sign, hz2, not_lt_of_ge hz2.le,
        abs_of_pos hz2]
    have hroot : signedCbrt z = Real.rpow z (1 / 3 : ℝ) := by
      simp [signedCbrt, Real.sign, hz, not_lt_of_ge hz.le, abs_of_pos hz]
    rw [hsquare, hroot]
    exact rpowCbrtProduct z hz

private theorem rpowCbrtDerivValue (u : ℝ) (hu : 0 < u) :
    (1 / 3 : ℝ) * Real.rpow u ((1 / 3 : ℝ) - 1) =
      1 / (3 * Real.rpow (u ^ 2) (1 / 3 : ℝ)) := by
  have hA : 0 < Real.rpow (u ^ 2) (1 / 3 : ℝ) :=
    Real.rpow_pos_of_pos (pow_pos hu 2) _
  have hrpowOne : Real.rpow u 1 = u := Real.rpow_one u
  have hadd :
      Real.rpow u (((1 / 3 : ℝ) - 1) + 1) =
        Real.rpow u ((1 / 3 : ℝ) - 1) * Real.rpow u 1 :=
    Real.rpow_add hu ((1 / 3 : ℝ) - 1) 1
  have hshift :
      Real.rpow u ((1 / 3 : ℝ) - 1) * u = Real.rpow u (1 / 3 : ℝ) := by
    calc
      Real.rpow u ((1 / 3 : ℝ) - 1) * u =
          Real.rpow u ((1 / 3 : ℝ) - 1) * Real.rpow u 1 := by
        exact congrArg
          (fun t => Real.rpow u ((1 / 3 : ℝ) - 1) * t) hrpowOne.symm
      _ = Real.rpow u (((1 / 3 : ℝ) - 1) + 1) := hadd.symm
      _ = Real.rpow u (1 / 3 : ℝ) := by congr 1 <;> ring
  have hAB :
      Real.rpow (u ^ 2) (1 / 3 : ℝ) *
          Real.rpow u ((1 / 3 : ℝ) - 1) = 1 := by
    apply mul_right_cancel₀ hu.ne'
    calc
      (Real.rpow (u ^ 2) (1 / 3 : ℝ) *
            Real.rpow u ((1 / 3 : ℝ) - 1)) * u =
          Real.rpow (u ^ 2) (1 / 3 : ℝ) *
            (Real.rpow u ((1 / 3 : ℝ) - 1) * u) := by ring
      _ = Real.rpow (u ^ 2) (1 / 3 : ℝ) * Real.rpow u (1 / 3 : ℝ) := by
        rw [hshift]
      _ = u := rpowCbrtProduct u hu
      _ = 1 * u := by ring
  have hBA :
      Real.rpow u ((1 / 3 : ℝ) - 1) *
          Real.rpow (u ^ 2) (1 / 3 : ℝ) = 1 := by
    simpa only [mul_comm] using hAB
  apply (eq_div_iff (mul_ne_zero (by norm_num) hA.ne')).2
  calc
    ((1 / 3 : ℝ) * Real.rpow u ((1 / 3 : ℝ) - 1)) *
        (3 * Real.rpow (u ^ 2) (1 / 3 : ℝ)) =
      Real.rpow u ((1 / 3 : ℝ) - 1) *
        Real.rpow (u ^ 2) (1 / 3 : ℝ) := by ring
    _ = 1 := hBA

private theorem hasDerivAtSignedCbrt {z : ℝ} (hz : z ≠ 0) :
    HasDerivAt signedCbrt (1 / (3 * signedCbrt (z ^ 2))) z := by
  rcases lt_or_gt_of_ne hz with hzneg | hzpos
  · have hu : 0 < -z := neg_pos.mpr hzneg
    have hp0 :
        HasDerivAt (fun w : ℝ => Real.rpow (-w) (1 / 3 : ℝ))
          (((1 / 3 : ℝ) * Real.rpow (-z) ((1 / 3 : ℝ) - 1)) * (-1)) z :=
      (Real.hasDerivAt_rpow_const (Or.inl hu.ne')).comp z
        (hasDerivAt_id z).neg
    have hp :
        HasDerivAt (fun w : ℝ => -Real.rpow (-w) (1 / 3 : ℝ))
          ((1 / 3 : ℝ) * Real.rpow (-z) ((1 / 3 : ℝ) - 1)) z := by
      convert hp0.neg using 1 <;> ring
    have heq :
        (fun w : ℝ => -Real.rpow (-w) (1 / 3 : ℝ)) =ᶠ[nhds z]
          signedCbrt := by
      filter_upwards [Iio_mem_nhds hzneg] with w hw
      change w < 0 at hw
      simp [signedCbrt, Real.sign, hw, abs_of_neg hw]
    have hroot :
        HasDerivAt signedCbrt
          ((1 / 3 : ℝ) * Real.rpow (-z) ((1 / 3 : ℝ) - 1)) z :=
      hp.congr_of_eventuallyEq heq.symm
    rw [rpowCbrtDerivValue (-z) hu] at hroot
    rw [show (-z) ^ 2 = z ^ 2 by ring] at hroot
    have hz2 : 0 < z ^ 2 := by
      rw [pow_two]
      exact mul_self_pos.mpr hz
    have hsquare :
        signedCbrt (z ^ 2) = Real.rpow (z ^ 2) (1 / 3 : ℝ) := by
      simp [signedCbrt, Real.sign, hz2, not_lt_of_ge hz2.le,
        abs_of_pos hz2]
    rw [hsquare]
    exact hroot
  · have hp :
        HasDerivAt (fun w : ℝ => Real.rpow w (1 / 3 : ℝ))
          ((1 / 3 : ℝ) * Real.rpow z ((1 / 3 : ℝ) - 1)) z :=
      Real.hasDerivAt_rpow_const (Or.inl hzpos.ne')
    have heq :
        (fun w : ℝ => Real.rpow w (1 / 3 : ℝ)) =ᶠ[nhds z]
          signedCbrt := by
      filter_upwards [Ioi_mem_nhds hzpos] with w hw
      change 0 < w at hw
      simp [signedCbrt, Real.sign, hw, not_lt_of_ge hw.le, abs_of_pos hw]
    have hroot :
        HasDerivAt signedCbrt
          ((1 / 3 : ℝ) * Real.rpow z ((1 / 3 : ℝ) - 1)) z :=
      hp.congr_of_eventuallyEq heq.symm
    rw [rpowCbrtDerivValue z hzpos] at hroot
    have hz2 : 0 < z ^ 2 := pow_pos hzpos 2
    have hsquare :
        signedCbrt (z ^ 2) = Real.rpow (z ^ 2) (1 / 3 : ℝ) := by
      simp [signedCbrt, Real.sign, hz2, not_lt_of_ge hz2.le,
        abs_of_pos hz2]
    rw [hsquare]
    exact hroot

theorem gap1 (x : ℝ) (hden : 1 - x ^ 3 ≠ 0) (hnum : 1 + x ^ 3 ≠ 0) :
    HasDerivAt y
      (1 / (3 * signedCbrt ((q x) ^ 2)) *
        ((3 * x ^ 2 * (1 - x ^ 3) + 3 * x ^ 2 * (1 + x ^ 3)) /
          (1 - x ^ 3) ^ 2)) x := by
  have hq0 : q x ≠ 0 := by
    unfold q
    exact div_ne_zero hnum hden
  have hcube :
      HasDerivAt (fun t : ℝ => t ^ 3) (3 * x ^ 2) x := by
    convert (hasDerivAt_id x).pow 3 using 1 <;> norm_num
  have hn :
      HasDerivAt (fun t : ℝ => 1 + t ^ 3) (3 * x ^ 2) x := by
    convert (hasDerivAt_const x (1 : ℝ)).add hcube using 1 <;> norm_num
  have hd :
      HasDerivAt (fun t : ℝ => 1 - t ^ 3) (-(3 * x ^ 2)) x := by
    convert (hasDerivAt_const x (1 : ℝ)).sub hcube using 1 <;> norm_num
  have hq :
      HasDerivAt q
        ((3 * x ^ 2 * (1 - x ^ 3) + 3 * x ^ 2 * (1 + x ^ 3)) /
          (1 - x ^ 3) ^ 2) x := by
    unfold q
    convert hn.div hd hden using 1
    ring
  exact (hasDerivAtSignedCbrt hq0).comp x hq

/-- Exercise 858, gap 2.
The omitted domain conditions are made explicit. -/
theorem gap2 (x : ℝ) (hden : 1 - x ^ 3 ≠ 0) (hnum : 1 + x ^ 3 ≠ 0) :
    1 / (3 * signedCbrt ((q x) ^ 2)) *
          ((3 * x ^ 2 * (1 - x ^ 3) + 3 * x ^ 2 * (1 + x ^ 3)) /
            (1 - x ^ 3) ^ 2) =
      2 * x ^ 2 / (1 - x ^ 6) * signedCbrt (q x) := by
  have hq0 : q x ≠ 0 := by
    unfold q
    exact div_ne_zero hnum hden
  have hprod :
      signedCbrt ((q x) ^ 2) * signedCbrt (q x) = q x :=
    signedCbrtSqMul (q x)
  have hprod0 :
      signedCbrt ((q x) ^ 2) * signedCbrt (q x) ≠ 0 := by
    rw [hprod]
    exact hq0
  have hsquare0 : signedCbrt ((q x) ^ 2) ≠ 0 :=
    (mul_ne_zero_iff.mp hprod0).1
  have hroot0 : signedCbrt (q x) ≠ 0 :=
    (mul_ne_zero_iff.mp hprod0).2
  have hfactor :
      1 - x ^ 6 = (1 - x ^ 3) * (1 + x ^ 3) := by
    ring
  have hrootDen :
      signedCbrt ((q x) ^ 2) * signedCbrt (q x) * (1 - x ^ 3) =
        1 + x ^ 3 := by
    rw [hprod]
    unfold q
    field_simp [hden]
  have hdenEq :
      signedCbrt ((q x) ^ 2) * signedCbrt (q x) * (1 - x ^ 3) ^ 2 =
        (1 + x ^ 3) * (1 - x ^ 3) := by
    calc
      signedCbrt ((q x) ^ 2) * signedCbrt (q x) * (1 - x ^ 3) ^ 2 =
          (signedCbrt ((q x) ^ 2) * signedCbrt (q x) * (1 - x ^ 3)) *
            (1 - x ^ 3) := by ring
      _ = (1 + x ^ 3) * (1 - x ^ 3) := by rw [hrootDen]
  rw [hfactor]
  calc
    1 / (3 * signedCbrt ((q x) ^ 2)) *
          ((3 * x ^ 2 * (1 - x ^ 3) + 3 * x ^ 2 * (1 + x ^ 3)) /
            (1 - x ^ 3) ^ 2) =
        2 * x ^ 2 /
          (signedCbrt ((q x) ^ 2) * (1 - x ^ 3) ^ 2) := by
      field_simp [hsquare0, hden] <;> ring
    _ =
        (2 * x ^ 2 * signedCbrt (q x)) /
          (signedCbrt ((q x) ^ 2) * signedCbrt (q x) *
            (1 - x ^ 3) ^ 2) := by
      field_simp [hsquare0, hroot0, hden] <;> ring
    _ =
        (2 * x ^ 2 * signedCbrt (q x)) /
          ((1 + x ^ 3) * (1 - x ^ 3)) := by
      rw [hdenEq]
    _ =
        2 * x ^ 2 / ((1 - x ^ 3) * (1 + x ^ 3)) * signedCbrt (q x) := by
      rw [mul_comm (1 + x ^ 3) (1 - x ^ 3)]
      ring

/-- Exercise 858, gap 3.
The omitted domain conditions are made explicit. -/
theorem gap3 (x : ℝ) (hden : 1 - x ^ 3 ≠ 0) (hnum : 1 + x ^ 3 ≠ 0) :
    HasDerivAt y
      (2 * x ^ 2 / (1 - x ^ 6) * signedCbrt (q x)) x := by
  rw [← gap2 x hden hnum]
  exact gap1 x hden hnum

end

end ProofGap.Exercise858
