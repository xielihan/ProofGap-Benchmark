import ProofGapLean.Prelude.Sequences
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow

namespace ProofGap.Exercise1078_3

noncomputable section

open scoped Topology

def x (t : ℝ) : ℝ := (2 * t + t ^ 2) / (1 + t ^ 3)
def y (t : ℝ) : ℝ := (2 * t - t ^ 2) / (1 + t ^ 3)
def slope (t : ℝ) : ℝ := deriv y t / deriv x t

def regular (t : ℝ) : Prop :=
  1 + t ^ 3 ≠ 0 ∧ 2 + 2 * t - 4 * t ^ 3 - t ^ 4 ≠ 0

def tangent : Set (ℝ × ℝ) := {p | p.2 = -p.1}
def normal : Set (ℝ × ℝ) := {p | p.2 = p.1}

theorem gap1 (t : ℝ) (ht : regular t) :
    slope t =
      (2 - 2 * t - 4 * t ^ 3 + t ^ 4) /
        (2 + 2 * t - 4 * t ^ 3 - t ^ 4) := by
  have hden :
      HasDerivAt (fun z : ℝ => 1 + z ^ 3) (3 * t ^ 2) t := by
    have hpow :
        HasDerivAt (fun z : ℝ => z ^ 3) (3 * t ^ 2) t := by
      convert (hasDerivAt_id t).pow 3 using 1 <;>
        simp only [Pi.pow_apply, id_eq] <;> ring
    exact hpow.const_add 1
  have hnumx :
      HasDerivAt (fun z : ℝ => 2 * z + z ^ 2) (2 + 2 * t) t := by
    have hlin : HasDerivAt (fun z : ℝ => 2 * z) 2 t := by
      simpa using (hasDerivAt_id t).const_mul 2
    have hpow :
        HasDerivAt (fun z : ℝ => z ^ 2) (2 * t) t := by
      convert (hasDerivAt_id t).pow 2 using 1 <;>
        simp only [Pi.pow_apply, id_eq] <;> ring
    simpa only [Pi.add_apply] using HasDerivAt.add hlin hpow
  have hnumy :
      HasDerivAt (fun z : ℝ => 2 * z - z ^ 2) (2 - 2 * t) t := by
    have hlin : HasDerivAt (fun z : ℝ => 2 * z) 2 t := by
      simpa using (hasDerivAt_id t).const_mul 2
    have hpow :
        HasDerivAt (fun z : ℝ => z ^ 2) (2 * t) t := by
      convert (hasDerivAt_id t).pow 2 using 1 <;>
        simp only [Pi.pow_apply, id_eq] <;> ring
    simpa only [Pi.sub_apply] using HasDerivAt.sub hlin hpow
  have hx :
      HasDerivAt x
        ((2 + 2 * t - 4 * t ^ 3 - t ^ 4) / (1 + t ^ 3) ^ 2) t := by
    unfold x
    convert hnumx.div hden ht.1 using 1 <;> ring
  have hy :
      HasDerivAt y
        ((2 - 2 * t - 4 * t ^ 3 + t ^ 4) / (1 + t ^ 3) ^ 2) t := by
    unfold y
    convert hnumy.div hden ht.1 using 1 <;> ring
  unfold slope
  rw [hx.deriv, hy.deriv]
  field_simp [ht.1, ht.2]

theorem gap2 : Tendsto x atTop (𝓝 0) := by
  have hinv :
      Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero
  have hnum :
      Tendsto (fun t : ℝ => 2 * (t⁻¹) ^ 2 + t⁻¹) atTop (𝓝 0) := by
    convert (tendsto_const_nhds.mul (hinv.pow 2)).add hinv using 1 <;>
      norm_num
  have hden :
      Tendsto (fun t : ℝ => (t⁻¹) ^ 3 + 1) atTop (𝓝 1) := by
    convert (hinv.pow 3).add tendsto_const_nhds using 1 <;> norm_num
  have hquot :=
    hnum.div hden (by norm_num : (1 : ℝ) ≠ 0)
  have hquot' :
      Tendsto
        ((fun t : ℝ => 2 * (t⁻¹) ^ 2 + t⁻¹) /
          (fun t : ℝ => (t⁻¹) ^ 3 + 1)) atTop (𝓝 0) := by
    simpa using hquot
  apply hquot'.congr'
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hd1 : 1 + t ^ 3 ≠ 0 := by positivity
  have hd2 : (t⁻¹) ^ 3 + 1 ≠ 0 := by positivity
  simp only [Pi.div_apply]
  unfold x
  field_simp [ht0, hd1, hd2] <;> ring

theorem gap3 : Tendsto y atTop (𝓝 0) := by
  have hinv :
      Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero
  have hnum :
      Tendsto (fun t : ℝ => 2 * (t⁻¹) ^ 2 - t⁻¹) atTop (𝓝 0) := by
    convert (tendsto_const_nhds.mul (hinv.pow 2)).sub hinv using 1 <;>
      norm_num
  have hden :
      Tendsto (fun t : ℝ => (t⁻¹) ^ 3 + 1) atTop (𝓝 1) := by
    convert (hinv.pow 3).add tendsto_const_nhds using 1 <;> norm_num
  have hquot :=
    hnum.div hden (by norm_num : (1 : ℝ) ≠ 0)
  have hquot' :
      Tendsto
        ((fun t : ℝ => 2 * (t⁻¹) ^ 2 - t⁻¹) /
          (fun t : ℝ => (t⁻¹) ^ 3 + 1)) atTop (𝓝 0) := by
    simpa using hquot
  apply hquot'.congr'
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hd1 : 1 + t ^ 3 ≠ 0 := by positivity
  have hd2 : (t⁻¹) ^ 3 + 1 ≠ 0 := by positivity
  simp only [Pi.div_apply]
  unfold y
  field_simp [ht0, hd1, hd2] <;> ring

theorem gap4 : Tendsto slope atTop (𝓝 (-1)) := by
  have hinv :
      Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero
  have hnum :
      Tendsto
        (fun t : ℝ =>
          2 * (t⁻¹) ^ 4 - 2 * (t⁻¹) ^ 3 -
            4 * t⁻¹ + 1) atTop (𝓝 1) := by
    convert
      (((tendsto_const_nhds.mul (hinv.pow 4)).sub
        (tendsto_const_nhds.mul (hinv.pow 3))).sub
        (tendsto_const_nhds.mul hinv)).add tendsto_const_nhds using 1 <;>
      norm_num
  have hden :
      Tendsto
        (fun t : ℝ =>
          2 * (t⁻¹) ^ 4 + 2 * (t⁻¹) ^ 3 -
            4 * t⁻¹ - 1) atTop (𝓝 (-1)) := by
    convert
      (((tendsto_const_nhds.mul (hinv.pow 4)).add
        (tendsto_const_nhds.mul (hinv.pow 3))).sub
        (tendsto_const_nhds.mul hinv)).sub tendsto_const_nhds using 1 <;>
      norm_num
  have hquot :=
    hnum.div hden (by norm_num : (-1 : ℝ) ≠ 0)
  have hquot' :
      Tendsto
        ((fun t : ℝ =>
            2 * (t⁻¹) ^ 4 - 2 * (t⁻¹) ^ 3 - 4 * t⁻¹ + 1) /
          (fun t : ℝ =>
            2 * (t⁻¹) ^ 4 + 2 * (t⁻¹) ^ 3 - 4 * t⁻¹ - 1))
        atTop (𝓝 (-1)) := by
    simpa using hquot
  apply hquot'.congr'
  filter_upwards [Filter.eventually_gt_atTop (2 : ℝ)] with t ht
  have ht0 : t ≠ 0 := ne_of_gt (lt_trans (by norm_num) ht)
  have htpos : 0 < t := lt_trans (by norm_num) ht
  have ht2 : 1 < t ^ 2 := by nlinarith [sq_nonneg (t - 1)]
  have ht3 : t < t ^ 3 := by
    nlinarith [mul_pos htpos (sub_pos.mpr ht2)]
  have hreg : regular t := by
    constructor
    · nlinarith [pow_pos htpos 3]
    · have ht4 : 0 < t ^ 4 := pow_pos htpos 4
      nlinarith
  have hdtrans :
      2 * (t⁻¹) ^ 4 + 2 * (t⁻¹) ^ 3 - 4 * t⁻¹ - 1 ≠ 0 := by
    have hscale :
        2 * (t⁻¹) ^ 4 + 2 * (t⁻¹) ^ 3 - 4 * t⁻¹ - 1 =
          (2 + 2 * t - 4 * t ^ 3 - t ^ 4) * (t⁻¹) ^ 4 := by
      field_simp [ht0] <;> ring
    rw [hscale]
    exact mul_ne_zero hreg.2 (pow_ne_zero 4 (inv_ne_zero ht0))
  simp only [Pi.div_apply]
  rw [gap1 t hreg]
  field_simp [ht0, hreg.2, hdtrans] <;> ring

theorem gap5 :
    tangent = {p : ℝ × ℝ | p.2 = -p.1} := by rfl

theorem gap6 :
    normal = {p : ℝ × ℝ | p.2 = p.1} := by rfl

end

end ProofGap.Exercise1078_3
