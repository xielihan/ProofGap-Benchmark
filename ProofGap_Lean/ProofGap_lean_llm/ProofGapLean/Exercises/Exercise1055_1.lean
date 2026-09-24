import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1055_1

noncomputable section

def cbrt (x : ℝ) : ℝ := Real.sign x * Real.rpow |x| (1 / 3 : ℝ)
def y (x : ℝ) : ℝ := (x + 1) * cbrt (3 - x)
def tangentLine (x : ℝ) : ℝ := cbrt 4 * (x + 1)
def normalLine (x : ℝ) : ℝ := -(1 / cbrt 4) * (x + 1)

private theorem cbrt_pos {u : ℝ} (hu : 0 < u) : 0 < cbrt u := by
  simp [cbrt, Real.sign_of_pos hu, abs_of_pos hu,
    Real.rpow_pos_of_pos hu]

private theorem cbrt_mul_cbrt_sq {u : ℝ} (hu : 0 < u) :
    Real.rpow u (1 / 3 : ℝ) * cbrt (u ^ 2) = u := by
  have hs : 0 < u ^ 2 := sq_pos_of_pos hu
  have hlog : Real.log (u ^ 2) = (2 : ℝ) * Real.log u := by
    simpa using (Real.log_pow u 2)
  rw [cbrt, Real.sign_of_pos hs, abs_of_pos hs, one_mul]
  have hru :
      Real.rpow u (1 / 3 : ℝ) =
        Real.exp (Real.log u * (1 / 3 : ℝ)) :=
    Real.rpow_def_of_pos hu _
  have hrs :
      Real.rpow (u ^ 2) (1 / 3 : ℝ) =
        Real.exp (Real.log (u ^ 2) * (1 / 3 : ℝ)) :=
    Real.rpow_def_of_pos hs _
  rw [hru, hrs, hlog]
  calc
    Real.exp (Real.log u * (1 / 3 : ℝ)) *
          Real.exp (((2 : ℝ) * Real.log u) * (1 / 3 : ℝ)) =
        Real.exp (Real.log u) := by
          rw [← Real.exp_add]
          congr 1
          ring
    _ = u := Real.exp_log hu

private theorem rpow_third_deriv_coeff {u : ℝ} (hu : 0 < u) :
    Real.rpow u (1 / 3 : ℝ) * ((1 / u) * (1 / 3 : ℝ)) =
      1 / (3 * cbrt (u ^ 2)) := by
  have hb : 0 < cbrt (u ^ 2) := cbrt_pos (sq_pos_of_pos hu)
  have hrel := cbrt_mul_cbrt_sq hu
  field_simp [ne_of_gt hu, ne_of_gt hb]
  nlinarith [hrel]

private theorem hasDerivAt_rpow_third_of_pos {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun z : ℝ => Real.rpow z (1 / 3 : ℝ))
      (Real.rpow u (1 / 3 : ℝ) * ((1 / u) * (1 / 3 : ℝ))) u := by
  have h :=
    (Real.hasDerivAt_exp (Real.log u * (1 / 3 : ℝ))).comp u
      ((Real.hasDerivAt_log hu.ne').mul_const (1 / 3 : ℝ))
  have heq :
      Filter.EventuallyEq (nhds u)
        (fun z : ℝ => Real.exp (Real.log z * (1 / 3 : ℝ)))
        (fun z : ℝ => Real.rpow z (1 / 3 : ℝ)) := by
    filter_upwards [eventually_gt_nhds hu] with z hz
    symm
    exact Real.rpow_def_of_pos hz _
  have hlocal := h.congr_of_eventuallyEq (by
    simpa only [Function.comp_apply] using heq.symm)
  have hrpow :
      Real.rpow u (1 / 3 : ℝ) =
        Real.exp (Real.log u * (1 / 3 : ℝ)) :=
    Real.rpow_def_of_pos hu _
  rw [← hrpow] at hlocal
  simpa only [one_div] using hlocal

private theorem hasDerivAt_cbrt {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt cbrt (1 / (3 * cbrt (x ^ 2))) x := by
  rcases lt_or_gt_of_ne hx with hxneg | hxpos
  · have hu : 0 < -x := neg_pos.mpr hxneg
    have hp := hasDerivAt_rpow_third_of_pos hu
    have hc := (hp.comp x (hasDerivAt_neg x)).neg
    have heq :
        Filter.EventuallyEq (nhds x)
          (fun z : ℝ => -Real.rpow (-z) (1 / 3 : ℝ)) cbrt := by
      filter_upwards [eventually_lt_nhds hxneg] with z hz
      simp [cbrt, Real.sign_of_neg hz, abs_of_neg hz]
    have hlocal := hc.congr_of_eventuallyEq (by
      simpa only [Function.comp_apply] using heq.symm)
    convert hlocal using 1
    have hsq : (-x) ^ 2 = x ^ 2 := by ring
    have hcoeff := (rpow_third_deriv_coeff hu).symm
    rw [hsq] at hcoeff
    simpa only [mul_neg, mul_one, neg_neg] using hcoeff
  · have hp := hasDerivAt_rpow_third_of_pos hxpos
    have heq :
        Filter.EventuallyEq (nhds x)
          (fun z : ℝ => Real.rpow z (1 / 3 : ℝ)) cbrt := by
      filter_upwards [eventually_gt_nhds hxpos] with z hz
      simp [cbrt, Real.sign_of_pos hz, abs_of_pos hz]
    have hlocal := hp.congr_of_eventuallyEq heq.symm
    convert hlocal using 1
    exact (rpow_third_deriv_coeff hxpos).symm

theorem gap1 (x : ℝ) (hx : x ≠ 3) :
    deriv y x =
      cbrt (3 - x) - (x + 1) / (3 * cbrt ((3 - x) ^ 2)) := by
  have ht : 3 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  have hc :=
    (hasDerivAt_cbrt ht).comp x
      ((hasDerivAt_const x 3).sub (hasDerivAt_id x))
  have hp := ((hasDerivAt_id x).add_const 1).mul hc
  simpa [y, div_eq_mul_inv] using hp.deriv

theorem gap2 (x : ℝ) :
    tangentLine x = cbrt 4 * (x + 1) := by
  rfl

theorem gap3 (x : ℝ) :
    normalLine x = -(1 / cbrt 4) * (x + 1) := by
  rfl

theorem gap4 (x : ℝ) :
    -(1 / cbrt 4) * (x + 1) = -(cbrt 2 / 2) * (x + 1) := by
  have hrel := cbrt_mul_cbrt_sq (u := (2 : ℝ)) (by norm_num)
  have htwo : (0 : ℝ) < 2 := by norm_num
  have hc2 : cbrt 2 = Real.rpow 2 (1 / 3 : ℝ) := by
    simp [cbrt, Real.sign_of_pos htwo]
  have hsq : (2 : ℝ) ^ 2 = 4 := by norm_num
  have hrel' : cbrt 2 * cbrt 4 = 2 := by
    rw [hc2, ← hsq]
    exact hrel
  have h4 : 0 < cbrt 4 := cbrt_pos (by norm_num)
  have hcoef : 1 / cbrt 4 = cbrt 2 / 2 := by
    field_simp [ne_of_gt h4]
    simpa [mul_comm] using hrel'.symm
  rw [hcoef]

theorem gap5 (x : ℝ) :
    normalLine x = -(cbrt 2 / 2) * (x + 1) := by
  rw [gap3 x, gap4 x]

end

end ProofGap.Exercise1055_1
