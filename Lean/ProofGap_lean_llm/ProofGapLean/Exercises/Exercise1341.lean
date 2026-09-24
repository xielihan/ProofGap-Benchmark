import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

namespace ProofGap.Exercise1341

noncomputable section

def HasRightLimitAtZero (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin 0 (Set.Ioi 0)) (nhds L)

def f₀ (ε x : ℝ) : ℝ := Real.rpow x ε * Real.log x
def f₁ (ε x : ℝ) : ℝ := Real.log x / Real.rpow x (-ε)
def f₂ (ε x : ℝ) : ℝ :=
  (1 / x) / (-ε * Real.rpow x (-ε - 1))
def f₃ (ε x : ℝ) : ℝ := -(Real.rpow x ε / ε)

private theorem f₀_limit (ε : ℝ) (hε : 0 < ε) :
    HasRightLimitAtZero (f₀ ε) 0 := by
  unfold HasRightLimitAtZero
  apply (tendsto_log_mul_rpow_nhdsGT_zero hε).congr'
  filter_upwards with x
  change Real.log x * Real.rpow x ε = Real.rpow x ε * Real.log x
  ring

private theorem f₁_limit (ε : ℝ) (hε : 0 < ε) :
    HasRightLimitAtZero (f₁ ε) 0 := by
  simpa [HasRightLimitAtZero, f₁] using
    (tendsto_log_div_rpow_nhdsGT_zero (neg_lt_zero.mpr hε))

private theorem f₃_limit (ε : ℝ) (hε : 0 < ε) :
    HasRightLimitAtZero (f₃ ε) 0 := by
  have hp : Filter.Tendsto (fun x : ℝ => Real.rpow x ε)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hc := Real.continuousAt_rpow_const 0 ε (Or.inr hε.le)
    simpa [Real.zero_rpow hε.ne'] using hc.tendsto.mono_left inf_le_left
  unfold HasRightLimitAtZero
  convert (hp.div_const ε).neg using 1 <;> norm_num [f₃]

private theorem f₂_limit (ε : ℝ) (hε : 0 < ε) :
    HasRightLimitAtZero (f₂ ε) 0 := by
  apply (f₃_limit ε hε).congr'
  filter_upwards [eventually_mem_nhdsWithin] with x hx
  have hxpos : 0 < x := hx
  have hrpos : Real.rpow x ε ≠ 0 := (Real.rpow_pos_of_pos hxpos ε).ne'
  simp only [f₂, f₃]
  have hrsub : Real.rpow x (-ε - 1) = Real.rpow x (-ε) / x :=
    Real.rpow_sub_one hxpos.ne' (-ε)
  have hrneg : Real.rpow x (-ε) = (Real.rpow x ε)⁻¹ :=
    Real.rpow_neg hxpos.le ε
  rw [hrsub, hrneg]
  field_simp [hxpos.ne', hε.ne', hrpos]

theorem gap1 (ε : ℝ) (hε : 0 < ε) :
    HasRightLimitAtZero (f₀ ε) 0 ↔ HasRightLimitAtZero (f₁ ε) 0 := by
  constructor <;> intro _
  · exact f₁_limit ε hε
  · exact f₀_limit ε hε

theorem gap2 (ε : ℝ) (hε : 0 < ε) :
    HasRightLimitAtZero (f₁ ε) 0 ↔ HasRightLimitAtZero (f₂ ε) 0 := by
  constructor <;> intro _
  · exact f₂_limit ε hε
  · exact f₁_limit ε hε

theorem gap3 (ε : ℝ) (hε : 0 < ε) :
    HasRightLimitAtZero (f₂ ε) 0 ↔ HasRightLimitAtZero (f₃ ε) 0 := by
  constructor <;> intro _
  · exact f₃_limit ε hε
  · exact f₂_limit ε hε

theorem gap4 (ε : ℝ) (hε : 0 < ε) :
    HasRightLimitAtZero (f₃ ε) 0 := by exact f₃_limit ε hε

theorem gap5 (ε : ℝ) (hε : 0 < ε) :
    HasRightLimitAtZero (f₀ ε) 0 := by exact f₀_limit ε hε

end

end ProofGap.Exercise1341
