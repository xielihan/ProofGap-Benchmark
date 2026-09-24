import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope

namespace ProofGap.Exercise1047

noncomputable section

open Filter
open scoped Topology

def xCoord (t : ℝ) : ℝ := 2 * t + |t|
def yCoord (t : ℝ) : ℝ := 5 * t ^ 2 + 4 * t * |t|
def deltaX (t Δt : ℝ) : ℝ := xCoord (t + Δt) - xCoord t
def deltaY (t Δt : ℝ) : ℝ := yCoord (t + Δt) - yCoord t
def quotient (Δt : ℝ) : ℝ := deltaY 0 Δt / deltaX 0 Δt

def ParametricDifferentiableAtZero : Prop :=
  ∃ L : ℝ, Tendsto quotient (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (𝓝 L)

theorem gap1 (Δt : ℝ) :
    deltaX 0 Δt = 2 * Δt + |Δt| := by
  simp [deltaX, xCoord]

theorem gap2 (Δt : ℝ) :
    deltaY 0 Δt = 5 * Δt ^ 2 + 4 * Δt * |Δt| := by
  simp [deltaY, yCoord]

theorem gap3 (Δt : ℝ) (hΔ : Δt ≠ 0) :
    quotient Δt =
      (5 * Δt ^ 2 + 4 * Δt * |Δt|) / (2 * Δt + |Δt|) := by
  unfold quotient
  rw [gap1, gap2]

theorem gap4 (Δt : ℝ) (hΔ : Δt ≠ 0) :
    (5 * Δt ^ 2 + 4 * Δt * |Δt|) / (2 * Δt + |Δt|) =
      if 0 < Δt then 3 * Δt else Δt := by
  split_ifs with hpos
  · rw [abs_of_pos hpos]
    field_simp [hΔ]
    ring
  · have hneg : Δt < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hΔ
    rw [abs_of_neg hneg]
    field_simp [hΔ]
    ring

theorem gap5 (Δt : ℝ) (hΔ : Δt ≠ 0) :
    quotient Δt = if 0 < Δt then 3 * Δt else Δt := by
  rw [gap3 Δt hΔ, gap4 Δt hΔ]

theorem gap6 :
    Tendsto quotient (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (𝓝 0) := by
  have hid :
      Tendsto (fun t : ℝ => t) (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (𝓝 0) :=
    tendsto_id.mono_left inf_le_left
  have hthree :
      Tendsto (fun t : ℝ => 3 * t) (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hid
  have hmodel :
      Tendsto (fun t : ℝ => if 0 < t then 3 * t else t)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (𝓝 0) :=
    hthree.if' hid
  apply hmodel.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : t ≠ 0 := by simpa using ht
  exact (gap5 t ht0).symm

theorem gap7 : ParametricDifferentiableAtZero := by
  exact ⟨0, gap6⟩

theorem gap8 :
    ¬DifferentiableAt ℝ (fun t : ℝ => |t|) 0 := by
  exact not_differentiableAt_abs_zero

theorem gap9 :
    ¬DifferentiableAt ℝ xCoord 0 := by
  intro hx
  apply gap8
  have habs :
      DifferentiableAt ℝ (fun t : ℝ => xCoord t - 2 * t) 0 :=
    hx.sub (differentiableAt_id.const_mul 2)
  convert habs using 1
  funext t
  simp [xCoord]

theorem gap10 :
    DifferentiableAt ℝ yCoord 0 := by
  have habs :
      Tendsto (fun h : ℝ => |h|) (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (𝓝 0) := by
    simpa using (continuous_abs.tendsto (0 : ℝ)).mono_left inf_le_left
  have hmul : HasDerivAt (fun t : ℝ => t * |t|) 0 0 := by
    rw [hasDerivAt_iff_tendsto_slope_zero]
    apply habs.congr'
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hh0 : h ≠ 0 := by simpa using hh
    simp only [zero_add, zero_mul, sub_zero, smul_eq_mul]
    field_simp [hh0]
  have hsquare : HasDerivAt (fun t : ℝ => t ^ 2) 0 0 := by
    convert (hasDerivAt_id (0 : ℝ)).pow 2 using 1 <;> norm_num
  unfold yCoord
  simpa only [Pi.add_apply, Pi.mul_apply, mul_assoc] using
    ((hsquare.const_mul 5).add (hmul.const_mul 4)).differentiableAt

theorem gap11 :
    ParametricDifferentiableAtZero ∧
      ¬DifferentiableAt ℝ xCoord 0 ∧ DifferentiableAt ℝ yCoord 0 := by
  exact ⟨gap7, gap9, gap10⟩

end

end ProofGap.Exercise1047
