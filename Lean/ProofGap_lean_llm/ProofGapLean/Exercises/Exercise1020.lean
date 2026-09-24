import ProofGapLean.Prelude.Elementary
import ProofGapLean.Prelude.Sequences
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

namespace ProofGap.Exercise1020

noncomputable section

open scoped Topology

def cubeRoot (x : ℝ) : ℝ := Real.rpow x (1 / 3 : ℝ)
def f (x : ℝ) : ℝ := cubeRoot x
def rightZero : Filter ℝ := 𝓝[Set.Ioi 0] 0

theorem gap1 (b : ℝ) :
    DifferentiableOn ℝ f (Set.Ioo 0 b) := by
  intro x hx
  unfold f cubeRoot
  exact
    (Real.hasDerivAt_rpow_const (x := x) (p := (1 / 3 : ℝ))
      (Or.inl hx.1.ne')).differentiableAt.differentiableWithinAt

theorem gap2 (x : ℝ) (hx : 0 < x) :
    HasDerivAt f (1 / (3 * cubeRoot (x ^ 2))) x := by
  have hraw :
      HasDerivAt f
        ((1 / 3 : ℝ) * Real.rpow x ((1 / 3 : ℝ) - 1)) x := by
    unfold f cubeRoot
    exact
      Real.hasDerivAt_rpow_const (x := x) (p := (1 / 3 : ℝ))
        (Or.inl hx.ne')
  have hsquare :
      cubeRoot (x ^ 2) = Real.rpow x (2 / 3 : ℝ) := by
    unfold cubeRoot
    have hmul :
        Real.rpow x ((2 : ℝ) * (1 / 3 : ℝ)) =
          Real.rpow (x ^ 2) (1 / 3 : ℝ) :=
      Real.rpow_natCast_mul hx.le 2 (1 / 3 : ℝ)
    calc
      Real.rpow (x ^ 2) (1 / 3 : ℝ) =
          Real.rpow x ((2 : ℝ) * (1 / 3 : ℝ)) := hmul.symm
      _ = Real.rpow x (2 / 3 : ℝ) := by congr 1 <;> ring
  have hpos : Real.rpow x (2 / 3 : ℝ) ≠ 0 :=
    (Real.rpow_pos_of_pos hx _).ne'
  have hneg :
      Real.rpow x (-(2 / 3 : ℝ)) =
        (Real.rpow x (2 / 3 : ℝ))⁻¹ :=
    Real.rpow_neg hx.le (2 / 3 : ℝ)
  convert hraw using 1
  rw [hsquare, show (1 / 3 : ℝ) - 1 = -(2 / 3 : ℝ) by ring, hneg]
  field_simp [hpos]
  <;> ring

theorem gap3 :
    Tendsto (deriv f) rightZero atTop := by
  have hpow :
      Tendsto (fun x : ℝ => Real.rpow x (-(2 / 3 : ℝ)))
        rightZero atTop := by
    simpa [rightZero] using
      (tendsto_rpow_neg_nhdsGT_zero (show (-(2 / 3 : ℝ)) < 0 by norm_num))
  have hscaled :
      Tendsto (fun x : ℝ => (1 / 3 : ℝ) *
        Real.rpow x (-(2 / 3 : ℝ))) rightZero atTop :=
    hpow.const_mul_atTop (by norm_num)
  apply hscaled.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  change 0 < x at hx
  have hd :
      HasDerivAt f
        ((1 / 3 : ℝ) * Real.rpow x ((1 / 3 : ℝ) - 1)) x := by
    unfold f cubeRoot
    exact Real.hasDerivAt_rpow_const (Or.inl hx.ne')
  rw [hd.deriv]
  congr 2
  ring

theorem gap4 :
    Tendsto f rightZero (𝓝 0) ↔ Tendsto cubeRoot rightZero (𝓝 0) := by
  rfl

theorem gap5 : Tendsto cubeRoot rightZero (𝓝 0) := by
  have ht :=
    (Real.continuous_rpow_const
      (show (0 : ℝ) ≤ (1 / 3 : ℝ) by norm_num)).tendsto 0
  unfold cubeRoot rightZero
  simpa using ht.mono_left inf_le_left

theorem gap6 : Tendsto f rightZero (𝓝 0) := by
  exact gap4.mpr gap5

end

end ProofGap.Exercise1020
