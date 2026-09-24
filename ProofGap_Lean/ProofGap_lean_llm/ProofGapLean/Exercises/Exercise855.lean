import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise855

noncomputable section

/-- The real, sign-preserving cube root. -/
def signedCbrt (x : ℝ) : ℝ :=
  Real.sign x * Real.rpow |x| (1 / 3 : ℝ)

def y (x : ℝ) : ℝ :=
  (1 + x) * Real.sqrt (2 + x ^ 2) * signedCbrt (3 + x ^ 3)

/-- Exercise 855, gap 1.
The cube-root argument must be nonzero for the displayed derivative to exist. -/
private theorem _signedCbrtSquare (z : ℝ) (hz : z ≠ 0) :
    signedCbrt (z ^ 2) = Real.rpow |z| (2 / 3 : ℝ) := by
  have hz2 : 0 < z ^ 2 := sq_pos_of_ne_zero hz
  have ha : 0 < |z| := abs_pos.mpr hz
  calc
    signedCbrt (z ^ 2) = Real.rpow (|z| * |z|) (1 / 3 : ℝ) := by
      simp only [signedCbrt, Real.sign_of_pos hz2, one_mul, abs_of_pos hz2]
      rw [← sq_abs z, pow_two]
    _ = Real.rpow |z| (1 / 3 : ℝ) * Real.rpow |z| (1 / 3 : ℝ) := by
      exact Real.mul_rpow (le_of_lt ha) (le_of_lt ha)
    _ = Real.rpow |z| ((1 / 3 : ℝ) + 1 / 3) := by
      exact (Real.rpow_add ha (1 / 3 : ℝ) (1 / 3 : ℝ)).symm
    _ = Real.rpow |z| (2 / 3 : ℝ) := by
      norm_num

private theorem _signedCbrtMulSquare (z : ℝ) (hz : z ≠ 0) :
    signedCbrt z * signedCbrt (z ^ 2) = z := by
  rw [_signedCbrtSquare z hz, signedCbrt]
  have ha : 0 < |z| := abs_pos.mpr hz
  calc
    (Real.sign z * Real.rpow |z| (1 / 3 : ℝ)) *
          Real.rpow |z| (2 / 3 : ℝ) =
        Real.sign z *
          (Real.rpow |z| (1 / 3 : ℝ) *
            Real.rpow |z| (2 / 3 : ℝ)) := by
      ring
    _ = Real.sign z * Real.rpow |z| ((1 / 3 : ℝ) + 2 / 3) := by
      apply congrArg (fun w : ℝ => Real.sign z * w)
      exact (Real.rpow_add ha (1 / 3 : ℝ) (2 / 3 : ℝ)).symm
    _ = Real.sign z * |z| := by
      norm_num
    _ = z := by
      rcases lt_or_gt_of_ne hz with hzneg | hzpos
      · simp [Real.sign_of_neg hzneg, abs_of_neg hzneg]
      · simp [Real.sign_of_pos hzpos, abs_of_pos hzpos]

private theorem _hasDerivAtSqrtPos (z : ℝ) (hz : 0 < z) :
    HasDerivAt Real.sqrt (1 / (2 * Real.sqrt z)) z := by
  have hp :
      HasDerivAt (fun u : ℝ => Real.rpow u (1 / 2 : ℝ))
        ((1 / 2 : ℝ) * Real.rpow z ((1 / 2 : ℝ) - 1)) z :=
    Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hz))
  have hfun :
      Real.sqrt = (fun u : ℝ => u ^ (1 / 2 : ℝ)) := by
    funext u
    exact Real.sqrt_eq_rpow u
  have hp' :
      HasDerivAt Real.sqrt
        ((1 / 2 : ℝ) * Real.rpow z ((1 / 2 : ℝ) - 1)) z := by
    rw [hfun]
    exact hp
  convert hp' using 1
  rw [Real.sqrt_eq_rpow]
  change
    1 / (2 * Real.rpow z (1 / 2 : ℝ)) =
      (1 / 2 : ℝ) * Real.rpow z ((1 / 2 : ℝ) - 1)
  rw [show (1 / 2 : ℝ) - 1 = -(1 / 2 : ℝ) by norm_num]
  have hpne : Real.rpow z (1 / 2 : ℝ) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hz (1 / 2 : ℝ))
  have hmul :
      Real.rpow z (1 / 2 : ℝ) * Real.rpow z (-(1 / 2 : ℝ)) = 1 := by
    calc
      Real.rpow z (1 / 2 : ℝ) * Real.rpow z (-(1 / 2 : ℝ)) =
          Real.rpow z ((1 / 2 : ℝ) + -(1 / 2 : ℝ)) :=
        (Real.rpow_add hz (1 / 2 : ℝ) (-(1 / 2 : ℝ))).symm
      _ = 1 := by norm_num
  field_simp [hpne] <;> nlinarith [hmul]

private theorem _hasDerivAtSignedCbrt (z : ℝ) (hz : z ≠ 0) :
    HasDerivAt signedCbrt
      (1 / (3 * signedCbrt (z ^ 2))) z := by
  have hraw :
      HasDerivAt signedCbrt
        ((1 / 3 : ℝ) * Real.rpow |z| ((1 / 3 : ℝ) - 1)) z := by
    rcases lt_or_gt_of_ne hz with hzneg | hzpos
    · have hp :
          HasDerivAt (fun u : ℝ => Real.rpow u (1 / 3 : ℝ))
            ((1 / 3 : ℝ) * Real.rpow (-z) ((1 / 3 : ℝ) - 1)) (-z) :=
        Real.hasDerivAt_rpow_const
          (Or.inl (ne_of_gt (neg_pos.mpr hzneg)))
      have hn :
          HasDerivAt
            (fun u : ℝ => -Real.rpow (-u) (1 / 3 : ℝ))
            ((1 / 3 : ℝ) * Real.rpow (-z) ((1 / 3 : ℝ) - 1)) z := by
        convert (hp.comp z ((hasDerivAt_id z).neg)).neg using 1 <;>
          simp <;> ring
      have hn' :
          HasDerivAt
            (fun u : ℝ => -Real.rpow (-u) (1 / 3 : ℝ))
            ((1 / 3 : ℝ) * Real.rpow |z| ((1 / 3 : ℝ) - 1)) z := by
        simpa [abs_of_neg hzneg] using hn
      refine hn'.congr_of_eventuallyEq ?_
      filter_upwards [Iio_mem_nhds hzneg] with u hu
      change u < 0 at hu
      simp [signedCbrt, Real.sign_of_neg hu, abs_of_neg hu]
    · have hp :
          HasDerivAt (fun u : ℝ => Real.rpow u (1 / 3 : ℝ))
            ((1 / 3 : ℝ) * Real.rpow z ((1 / 3 : ℝ) - 1)) z :=
        Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hzpos))
      have hp' :
          HasDerivAt (fun u : ℝ => Real.rpow u (1 / 3 : ℝ))
            ((1 / 3 : ℝ) * Real.rpow |z| ((1 / 3 : ℝ) - 1)) z := by
        simpa [abs_of_pos hzpos] using hp
      refine hp'.congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds hzpos] with u hu
      change 0 < u at hu
      simp [signedCbrt, Real.sign_of_pos hu, abs_of_pos hu]
  convert hraw using 1
  rw [_signedCbrtSquare z hz]
  change
    1 / (3 * Real.rpow |z| (2 / 3 : ℝ)) =
      (1 / 3 : ℝ) * Real.rpow |z| ((1 / 3 : ℝ) - 1)
  rw [show (1 / 3 : ℝ) - 1 = -(2 / 3 : ℝ) by norm_num]
  have ha : 0 < |z| := abs_pos.mpr hz
  have hpne : Real.rpow |z| (2 / 3 : ℝ) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos ha (2 / 3 : ℝ))
  have hmul :
      Real.rpow |z| (2 / 3 : ℝ) *
          Real.rpow |z| (-(2 / 3 : ℝ)) = 1 := by
    calc
      Real.rpow |z| (2 / 3 : ℝ) *
            Real.rpow |z| (-(2 / 3 : ℝ)) =
          Real.rpow |z| ((2 / 3 : ℝ) + -(2 / 3 : ℝ)) :=
        (Real.rpow_add ha (2 / 3 : ℝ) (-(2 / 3 : ℝ))).symm
      _ = 1 := by norm_num
  field_simp [hpne] <;> nlinarith [hmul]

theorem gap1 (x : ℝ) (hcube : 3 + x ^ 3 ≠ 0) :
    HasDerivAt y
      (Real.sqrt (2 + x ^ 2) * signedCbrt (3 + x ^ 3) +
        (1 + x) *
          (x * signedCbrt (3 + x ^ 3) / Real.sqrt (2 + x ^ 2) +
            x ^ 2 * Real.sqrt (2 + x ^ 2) /
              signedCbrt ((3 + x ^ 3) ^ 2))) x := by
  have hq : 0 < 2 + x ^ 2 := by
    positivity
  have hsqrt0 : Real.sqrt (2 + x ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hq)
  have hinner :
      HasDerivAt (fun t : ℝ => 2 + t ^ 2) (2 * x) x := by
    convert
      (hasDerivAt_const x 2).add ((hasDerivAt_id x).pow 2) using 1 <;>
      simp [id] <;> ring
  have hs :
      HasDerivAt (fun t : ℝ => Real.sqrt (2 + t ^ 2))
        (x / Real.sqrt (2 + x ^ 2)) x := by
    convert (_hasDerivAtSqrtPos (2 + x ^ 2) hq).comp x hinner using 1 <;>
      field_simp [hsqrt0] <;> ring
  have hl : HasDerivAt (fun t : ℝ => 1 + t) 1 x := by
    convert (hasDerivAt_const x 1).add (hasDerivAt_id x) using 1 <;>
      simp [id]
  have hcinner :
      HasDerivAt (fun t : ℝ => 3 + t ^ 3) (3 * x ^ 2) x := by
    convert (hasDerivAt_const x 3).add ((hasDerivAt_id x).pow 3) using 1 <;>
      simp [id] <;> ring
  have hd0 : signedCbrt ((3 + x ^ 3) ^ 2) ≠ 0 := by
    rw [_signedCbrtSquare (3 + x ^ 3) hcube]
    exact ne_of_gt
      (Real.rpow_pos_of_pos (abs_pos.mpr hcube) (2 / 3 : ℝ))
  have hc :
      HasDerivAt (fun t : ℝ => signedCbrt (3 + t ^ 3))
        (x ^ 2 / signedCbrt ((3 + x ^ 3) ^ 2)) x := by
    convert
      (_hasDerivAtSignedCbrt (3 + x ^ 3) hcube).comp x hcinner using 1 <;>
      field_simp [hd0] <;> ring
  have hprod :
      HasDerivAt y
        ((1 * Real.sqrt (2 + x ^ 2) +
              (1 + x) * (x / Real.sqrt (2 + x ^ 2))) *
            signedCbrt (3 + x ^ 3) +
          ((1 + x) * Real.sqrt (2 + x ^ 2)) *
            (x ^ 2 / signedCbrt ((3 + x ^ 3) ^ 2))) x := by
    simpa only [y, Pi.mul_apply] using (hl.mul hs).mul hc
  convert hprod using 1
  field_simp [hsqrt0, hd0]
  ring

/-- Exercise 855, gap 2.
The same necessary nonzero condition is made explicit. -/
theorem gap2 (x : ℝ) (hcube : 3 + x ^ 3 ≠ 0) :
    HasDerivAt y
      ((6 + 3 * x + 8 * x ^ 2 + 4 * x ^ 3 + 2 * x ^ 4 + 3 * x ^ 5) /
        (Real.sqrt (2 + x ^ 2) * signedCbrt ((3 + x ^ 3) ^ 2))) x := by
  have hq : 0 < 2 + x ^ 2 := by
    positivity
  have hsqrt0 : Real.sqrt (2 + x ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hq)
  have hd0 : signedCbrt ((3 + x ^ 3) ^ 2) ≠ 0 := by
    rw [_signedCbrtSquare (3 + x ^ 3) hcube]
    exact ne_of_gt
      (Real.rpow_pos_of_pos (abs_pos.mpr hcube) (2 / 3 : ℝ))
  have hs2 :
      Real.sqrt (2 + x ^ 2) ^ 2 = 2 + x ^ 2 :=
    Real.sq_sqrt (le_of_lt hq)
  have hcd :
      signedCbrt (3 + x ^ 3) * signedCbrt ((3 + x ^ 3) ^ 2) =
        3 + x ^ 3 :=
    _signedCbrtMulSquare (3 + x ^ 3) hcube
  have heq :
      Real.sqrt (2 + x ^ 2) * signedCbrt (3 + x ^ 3) +
          (1 + x) *
            (x * signedCbrt (3 + x ^ 3) / Real.sqrt (2 + x ^ 2) +
              x ^ 2 * Real.sqrt (2 + x ^ 2) /
                signedCbrt ((3 + x ^ 3) ^ 2)) =
        (6 + 3 * x + 8 * x ^ 2 + 4 * x ^ 3 + 2 * x ^ 4 + 3 * x ^ 5) /
          (Real.sqrt (2 + x ^ 2) *
            signedCbrt ((3 + x ^ 3) ^ 2)) := by
    calc
      Real.sqrt (2 + x ^ 2) * signedCbrt (3 + x ^ 3) +
            (1 + x) *
              (x * signedCbrt (3 + x ^ 3) / Real.sqrt (2 + x ^ 2) +
                x ^ 2 * Real.sqrt (2 + x ^ 2) /
                  signedCbrt ((3 + x ^ 3) ^ 2)) =
          (Real.sqrt (2 + x ^ 2) ^ 2 *
                (signedCbrt (3 + x ^ 3) *
                  signedCbrt ((3 + x ^ 3) ^ 2)) +
              (1 + x) *
                (x *
                    (signedCbrt (3 + x ^ 3) *
                      signedCbrt ((3 + x ^ 3) ^ 2)) +
                  x ^ 2 * Real.sqrt (2 + x ^ 2) ^ 2)) /
            (Real.sqrt (2 + x ^ 2) *
              signedCbrt ((3 + x ^ 3) ^ 2)) := by
                field_simp [hsqrt0, hd0] <;> ring
      _ =
          (6 + 3 * x + 8 * x ^ 2 + 4 * x ^ 3 + 2 * x ^ 4 + 3 * x ^ 5) /
            (Real.sqrt (2 + x ^ 2) *
              signedCbrt ((3 + x ^ 3) ^ 2)) := by
                rw [hs2, hcd] <;> ring
  have h := gap1 x hcube
  rw [heq] at h
  exact h

end

end ProofGap.Exercise855
