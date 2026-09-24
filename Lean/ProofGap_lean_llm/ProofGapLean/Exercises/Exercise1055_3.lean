import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import ProofGapLean.Exercises.Exercise1055_2
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace ProofGap.Exercise1055_3

noncomputable section

open Filter
open scoped Topology

def cbrt (x : ℝ) : ℝ := Real.sign x * Real.rpow |x| (1 / 3 : ℝ)
def y (x : ℝ) : ℝ := (x + 1) * cbrt (3 - x)
def verticalLine (c : ℝ) : Set (ℝ × ℝ) := {p | p.1 = c}
def horizontalLine (c : ℝ) : Set (ℝ × ℝ) := {p | p.2 = c}

theorem gap1 (x : ℝ) (hx : x ≠ 3) :
    deriv y x =
      cbrt (3 - x) - (x + 1) / (3 * cbrt ((3 - x) ^ 2)) := by
  simpa [y, cbrt, ProofGap.Exercise1055_2.y,
    ProofGap.Exercise1055_2.cbrt] using
      ProofGap.Exercise1055_2.gap1 x hx

theorem gap2 :
    Tendsto (fun x => deriv y x)
      (nhdsWithin 3 ({3} : Set ℝ)ᶜ) atBot := by
  let L := nhdsWithin (3 : ℝ) ({3} : Set ℝ)ᶜ
  have habs0 :
      Tendsto (fun x : ℝ => |3 - x|) L (𝓝 0) := by
    have hfull :
        Tendsto (fun x : ℝ => |3 - x|) (𝓝 3) (𝓝 0) := by
      have hconst :
          Tendsto (fun _ : ℝ => (3 : ℝ)) (𝓝 3) (𝓝 3) :=
        tendsto_const_nhds
      have hsub :
          Tendsto (fun x : ℝ => 3 - x) (𝓝 3) (𝓝 0) := by
        simpa only [id_eq, sub_self] using
          hconst.sub
            (tendsto_id : Tendsto (fun x : ℝ => x) (𝓝 3) (𝓝 3))
      simpa [Function.comp_def] using
        (continuous_abs.tendsto (0 : ℝ)).comp hsub
    exact hfull.mono_left inf_le_left
  have habsRight :
      Tendsto (fun x : ℝ => |3 - x|) L (nhdsWithin 0 (Set.Ioi 0)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨habs0, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx3 : x ≠ 3 := by simpa using hx
    exact abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hx3))
  have hblow :
      Tendsto (fun x : ℝ => Real.rpow |3 - x| (-(2 / 3 : ℝ)))
        L atTop :=
    (tendsto_rpow_neg_nhdsGT_zero
      (show (-(2 / 3 : ℝ)) < 0 by norm_num)).comp habsRight
  have hcoef :
      Tendsto (fun x : ℝ => -(x + 1) / 3) L (𝓝 (-(4 : ℝ) / 3)) := by
    have hfull :
        Tendsto (fun x : ℝ => -(x + 1) / 3) (𝓝 3)
          (𝓝 (-(4 : ℝ) / 3)) := by
      have hid :
          Tendsto (fun x : ℝ => x) (𝓝 3) (𝓝 3) :=
        tendsto_id
      convert ((hid.add_const 1).neg.div_const 3) using 1 <;> norm_num
    exact hfull.mono_left inf_le_left
  have hprod :
      Tendsto
        (fun x : ℝ => (-(x + 1) / 3) *
          Real.rpow |3 - x| (-(2 / 3 : ℝ))) L atBot :=
    hcoef.neg_mul_atTop (by norm_num) hblow
  have hrpow0 :
      Tendsto (fun x : ℝ => Real.rpow |3 - x| (1 / 3 : ℝ))
        L (𝓝 0) := by
    have hr :=
      (Real.continuous_rpow_const
        (show (0 : ℝ) ≤ (1 / 3 : ℝ) by norm_num)).tendsto 0
    simpa using hr.comp habs0
  have hcbrt0 :
      Tendsto (fun x : ℝ => cbrt (3 - x)) L (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply hrpow0.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx3 : x ≠ 3 := by simpa using hx
    have hu : 3 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx3)
    rcases lt_or_gt_of_ne hu with hu_neg | hu_pos
    · simp [cbrt, Real.sign_of_neg hu_neg, abs_of_neg hu_neg]
      have hxpos : 0 < x - 3 := by linarith
      rw [abs_of_pos (Real.rpow_pos_of_pos hxpos _)]
    · simp [cbrt, Real.sign_of_pos hu_pos, abs_of_pos hu_pos,
        abs_of_pos (Real.rpow_pos_of_pos hu_pos _)]
  have hsum := hprod.atBot_add hcbrt0
  apply hsum.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx3 : x ≠ 3 := by simpa using hx
  have hu : 3 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx3)
  have huabs : 0 < |3 - x| := abs_pos.mpr hu
  have hsquare : (|3 - x| : ℝ) ^ 2 = (3 - x) ^ 2 := sq_abs (3 - x)
  have hcbsq :
      cbrt ((3 - x) ^ 2) = Real.rpow |3 - x| (2 / 3 : ℝ) := by
    have hu2 : 0 < (3 - x) ^ 2 := sq_pos_of_ne_zero hu
    unfold cbrt
    rw [Real.sign_of_pos hu2, abs_of_pos hu2, one_mul, ← hsquare]
    have hmul :
        Real.rpow |3 - x| ((2 : ℝ) * (1 / 3 : ℝ)) =
          Real.rpow (|3 - x| ^ 2) (1 / 3 : ℝ) :=
      Real.rpow_natCast_mul (abs_nonneg _) 2 (1 / 3 : ℝ)
    calc
      Real.rpow (|3 - x| ^ 2) (1 / 3 : ℝ) =
          Real.rpow |3 - x| ((2 : ℝ) * (1 / 3 : ℝ)) := hmul.symm
      _ = Real.rpow |3 - x| (2 / 3 : ℝ) := by congr 1 <;> ring
  have hpow_ne : Real.rpow |3 - x| (2 / 3 : ℝ) ≠ 0 :=
    (Real.rpow_pos_of_pos huabs _).ne'
  have hneg :
      Real.rpow |3 - x| (-(2 / 3 : ℝ)) =
        (Real.rpow |3 - x| (2 / 3 : ℝ))⁻¹ :=
    Real.rpow_neg (abs_nonneg _) (2 / 3 : ℝ)
  rw [gap1 x hx3, hcbsq, hneg]
  field_simp [hpow_ne]
  <;> ring

theorem gap3 :
    verticalLine 3 = {p : ℝ × ℝ | p.1 = 3} := by
  rfl

theorem gap4 :
    horizontalLine 0 = {p : ℝ × ℝ | p.2 = 0} := by
  rfl

end

end ProofGap.Exercise1055_3
