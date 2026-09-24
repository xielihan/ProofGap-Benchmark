import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1000

open Filter

noncomputable section

def f (x : ℝ) : ℝ := |x|
def dq (g : ℝ → ℝ) (a h : ℝ) : ℝ := (g (a + h) - g a) / h
def HasLeftDerivAt (g : ℝ → ℝ) (g' a : ℝ) : Prop :=
  Tendsto (dq g a) (nhdsWithin 0 (Set.Iio 0)) (nhds g')
def HasRightDerivAt (g : ℝ → ℝ) (g' a : ℝ) : Prop :=
  Tendsto (dq g a) (nhdsWithin 0 (Set.Ioi 0)) (nhds g')

private theorem abs_div_self_eq_real_sign (x : ℝ) (hx : x ≠ 0) :
    |x| / x = Real.sign x := by
  rcases lt_or_gt_of_ne hx with hxneg | hxpos
  · rw [abs_of_neg hxneg]
    simp [Real.sign, hxneg, ne_of_lt hxneg]
  · have hnot : ¬ x < 0 := not_lt_of_ge hxpos.le
    rw [abs_of_pos hxpos]
    simp [Real.sign, hxpos, hnot, ne_of_gt hxpos]

private theorem dq_eq_real_sign_of_abs_lt
    (x h : ℝ) (hx : x ≠ 0) (hh : h ≠ 0) (hsmall : |h| < |x|) :
    dq f x h = Real.sign x := by
  rcases lt_or_gt_of_ne hx with hxneg | hxpos
  · have hxh : x + h < 0 := by
      rw [abs_of_neg hxneg] at hsmall
      have hh_le : h ≤ |h| := le_abs_self h
      linarith
    have hsign : Real.sign x = -1 := by
      simp [Real.sign, hxneg]
    rw [hsign]
    simp only [dq, f]
    rw [abs_of_neg hxh, abs_of_neg hxneg]
    field_simp [hh] <;> ring
  · have hxh : 0 < x + h := by
      rw [abs_of_pos hxpos] at hsmall
      have hh_le : -|h| ≤ h := neg_abs_le h
      linarith
    have hnot : ¬ x < 0 := not_lt_of_ge hxpos.le
    have hsign : Real.sign x = 1 := by
      simp [Real.sign, hxpos, hnot]
    rw [hsign]
    simp only [dq, f]
    rw [abs_of_pos hxh, abs_of_pos hxpos]
    field_simp [hh] <;> ring

theorem gap1 (x : ℝ) (hx : x ≠ 0) :
    HasLeftDerivAt f (Real.sign x) x ∧
      HasRightDerivAt f (Real.sign x) x := by
  constructor
  · unfold HasLeftDerivAt
    refine (tendsto_const_nhds :
      Tendsto (fun _ : ℝ => Real.sign x)
        (nhdsWithin 0 (Set.Iio 0)) (nhds (Real.sign x))).congr' ?_
    filter_upwards [
      mem_nhdsWithin_of_mem_nhds
        (Metric.ball_mem_nhds (0 : ℝ) (abs_pos.mpr hx)),
      self_mem_nhdsWithin] with h hsmall hside
    have hhneg : h < 0 := hside
    have habs : |h| < |x| := by
      simpa [Real.dist_eq] using hsmall
    symm
    exact dq_eq_real_sign_of_abs_lt x h hx (ne_of_lt hhneg) habs
  · unfold HasRightDerivAt
    refine (tendsto_const_nhds :
      Tendsto (fun _ : ℝ => Real.sign x)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.sign x))).congr' ?_
    filter_upwards [
      mem_nhdsWithin_of_mem_nhds
        (Metric.ball_mem_nhds (0 : ℝ) (abs_pos.mpr hx)),
      self_mem_nhdsWithin] with h hsmall hside
    have hhpos : 0 < h := hside
    have habs : |h| < |x| := by
      simpa [Real.dist_eq] using hsmall
    symm
    exact dq_eq_real_sign_of_abs_lt x h hx (ne_of_gt hhpos) habs

theorem gap2 (x : ℝ) (hx : x ≠ 0) :
    HasLeftDerivAt f (|x| / x) x := by
  rw [abs_div_self_eq_real_sign x hx]
  exact (gap1 x hx).1

theorem gap3 (x : ℝ) (hx : x ≠ 0) :
    |x| / x = Real.sign x := by
  exact abs_div_self_eq_real_sign x hx

theorem gap4 (x : ℝ) (hx : x ≠ 0) :
    HasRightDerivAt f (Real.sign x) x := by
  exact (gap1 x hx).2

theorem gap5 (h : ℝ) (hh : h ≠ 0) :
    dq f 0 h = if h < 0 then -1 else 1 := by
  by_cases hneg : h < 0
  · simp [dq, f, hneg, abs_of_neg hneg, hh]
  · have hpos : 0 < h :=
      lt_of_le_of_ne (le_of_not_gt hneg) (Ne.symm hh)
    simp [dq, f, hneg, abs_of_pos hpos, hh]

theorem gap6 :
    HasRightDerivAt f 1 0 := by
  unfold HasRightDerivAt
  refine (tendsto_const_nhds :
    Tendsto (fun _ : ℝ => (1 : ℝ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1)).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hhpos : 0 < h := hh
  symm
  rw [gap5 h (ne_of_gt hhpos), if_neg (not_lt_of_ge hhpos.le)]

theorem gap7 :
    HasLeftDerivAt f (-1) 0 := by
  unfold HasLeftDerivAt
  refine (tendsto_const_nhds :
    Tendsto (fun _ : ℝ => (-1 : ℝ))
      (nhdsWithin 0 (Set.Iio 0)) (nhds (-1))).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hhneg : h < 0 := hh
  symm
  rw [gap5 h (ne_of_lt hhneg), if_pos hhneg]

end

end ProofGap.Exercise1000
