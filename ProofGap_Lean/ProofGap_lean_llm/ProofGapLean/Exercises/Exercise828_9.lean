import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise828_9

noncomputable section

def y (x : ℝ) : ℝ := Real.arccos x
def quotient (x h : ℝ) : ℝ := (Real.arccos (x + h) - Real.arccos x) / h
def t (x h : ℝ) : ℝ :=
  (x + h) * Real.sqrt (1 - x ^ 2) - x * Real.sqrt (1 - (x + h) ^ 2)
def target (x : ℝ) : ℝ := -(1 / Real.sqrt (1 - x ^ 2))

theorem gap1 (x h Δy : ℝ) (hΔy : Δy = y (x + h) - y x) :
    Δy / h = quotient x h := by
  simpa [quotient, y, hΔy]
theorem gap2 (x h : ℝ) (hx : x ∈ Set.Ioo (-1) 1)
    (hxh : x + h ∈ Set.Ioo (-1) 1)
    (hrange : Real.arccos (x + h) - Real.arccos x ∈
      Set.Icc (-(Real.pi / 2)) (Real.pi / 2)) :
    quotient x h =
      Real.arcsin (x * Real.sqrt (1 - (x + h) ^ 2) -
        (x + h) * Real.sqrt (1 - x ^ 2)) / h := by
  have hsin :
      Real.sin (Real.arccos (x + h) - Real.arccos x) =
        x * Real.sqrt (1 - (x + h) ^ 2) -
          (x + h) * Real.sqrt (1 - x ^ 2) := by
    rw [Real.sin_sub, Real.sin_arccos, Real.sin_arccos,
      Real.cos_arccos hxh.1.le hxh.2.le, Real.cos_arccos hx.1.le hx.2.le]
    ring
  have harc := Real.arcsin_sin hrange.1 hrange.2
  unfold quotient
  congr 1
  calc
    Real.arccos (x + h) - Real.arccos x =
        Real.arcsin (Real.sin (Real.arccos (x + h) - Real.arccos x)) := harc.symm
    _ = _ := by rw [hsin]
theorem gap3 (x h Δy : ℝ) (hΔy : Δy = y (x + h) - y x)
    (hx : x ∈ Set.Ioo (-1) 1) (hxh : x + h ∈ Set.Ioo (-1) 1)
    (hrange : Real.arccos (x + h) - Real.arccos x ∈
      Set.Icc (-(Real.pi / 2)) (Real.pi / 2)) :
    Δy / h =
      Real.arcsin (x * Real.sqrt (1 - (x + h) ^ 2) -
        (x + h) * Real.sqrt (1 - x ^ 2)) / h := by
  rw [gap1 x h Δy hΔy]
  exact gap2 x h hx hxh hrange
theorem gap4 (x h Δy : ℝ) (hΔy : Δy = y (x + h) - y x)
    (hh : h ≠ 0) (hx : x ∈ Set.Ioo (-1) 1)
    (hxh : x + h ∈ Set.Ioo (-1) 1)
    (hrange : Real.arccos (x + h) - Real.arccos x ∈
      Set.Icc (-(Real.pi / 2)) (Real.pi / 2))
    (ht : t x h ≠ 0)
    (hden :
      (x + h) * Real.sqrt (1 - x ^ 2) +
        x * Real.sqrt (1 - (x + h) ^ 2) ≠ 0) :
    Δy / h = Real.arcsin (-(t x h)) / (-(t x h)) *
      (-(2 * x + h) /
        ((x + h) * Real.sqrt (1 - x ^ 2) +
          x * Real.sqrt (1 - (x + h) ^ 2))) := by
  have hsx : (Real.sqrt (1 - x ^ 2)) ^ 2 = 1 - x ^ 2 :=
    Real.sq_sqrt (by nlinarith [hx.1, hx.2])
  have hss : (Real.sqrt (1 - (x + h) ^ 2)) ^ 2 =
      1 - (x + h) ^ 2 := Real.sq_sqrt (by nlinarith [hxh.1, hxh.2])
  have hratio :
      -(t x h) / h =
        -(2 * x + h) /
          ((x + h) * Real.sqrt (1 - x ^ 2) +
            x * Real.sqrt (1 - (x + h) ^ 2)) := by
    unfold t
    field_simp [hh, hden]
    nlinarith
  have hq := gap3 x h Δy hΔy hx hxh hrange
  have hnum :
      x * Real.sqrt (1 - (x + h) ^ 2) -
          (x + h) * Real.sqrt (1 - x ^ 2) = -(t x h) := by
    unfold t
    ring
  rw [hnum] at hq
  have hneg : -(t x h) ≠ 0 := neg_ne_zero.mpr ht
  rw [hq]
  calc
    Real.arcsin (-(t x h)) / h =
        Real.arcsin (-(t x h)) / (-(t x h)) * (-(t x h) / h) := by
      field_simp [hh, hneg]
    _ = _ := by rw [hratio]
theorem gap5 (x : ℝ) :
    Filter.Tendsto (t x) (nhds 0) (nhds 0) := by
  have hcont : Continuous (t x) := by
    unfold t
    exact
      ((continuous_const.add continuous_id).mul continuous_const).sub
        (continuous_const.mul
          (Real.continuous_sqrt.comp
            (continuous_const.sub
              ((continuous_const.add continuous_id).pow 2))))
  have hcont0 : ContinuousAt (t x) 0 := hcont.continuousAt
  change Filter.Tendsto (t x) (nhds 0) (nhds (t x 0)) at hcont0
  have ht0 : t x 0 = 0 := by
    simp [t]
  rw [ht0] at hcont0
  exact hcont0
theorem gap6 (x : ℝ) (hx : x ∈ Set.Ioo (-1) 1) :
    HasDerivAt y (target x) x := by
  change HasDerivAt (fun z : ℝ => Real.arccos z)
    (-(1 / Real.sqrt (1 - x ^ 2))) x
  have hxm1 : x ≠ -1 := ne_of_gt hx.1
  have hx1 : x ≠ 1 := ne_of_lt hx.2
  have harcsin :
      HasDerivAt Real.arcsin (1 / Real.sqrt (1 - x ^ 2)) x :=
    Real.hasDerivAt_arcsin hxm1 hx1
  simpa only [Real.arccos_eq_pi_div_two_sub_arcsin, zero_sub] using
    (hasDerivAt_const x (Real.pi / 2)).sub harcsin
theorem gap7 (x : ℝ) (hx : x ∈ Set.Ioo (-1) 1) :
    Filter.Tendsto (quotient x) (nhdsWithin 0 {0}ᶜ) (nhds (target x)) := by
  have hinner : HasDerivAt (fun h : ℝ => x + h) 1 0 := by
    simpa using (hasDerivAt_id (𝕜 := ℝ) 0).const_add x
  have hout : HasDerivAt y (target x) (x + 0) := by
    simpa using gap6 x hx
  have hd0 : HasDerivAt (fun h : ℝ => y (x + h)) (target x) 0 := by
    simpa [Function.comp_def] using hout.comp 0 hinner
  rw [hasDerivAt_iff_tendsto_slope] at hd0
  have heq : quotient x = slope (fun h : ℝ => y (x + h)) 0 := by
    funext h
    change
      (Real.arccos (x + h) - Real.arccos x) / h =
        (h - 0)⁻¹ *
          (Real.arccos (x + h) - Real.arccos (x + 0))
    simp only [sub_zero, add_zero, div_eq_mul_inv]
    exact mul_comm _ _
  rw [heq]
  exact hd0
theorem gap8 (x : ℝ) (hx : x ∈ Set.Ioo (-1) 1) :
    target x = -(1 / Real.sqrt (1 - x ^ 2)) := by
  rfl
theorem gap9 (x : ℝ) (hx : x ∈ Set.Ioo (-1) 1) :
    HasDerivAt y (-(1 / Real.sqrt (1 - x ^ 2))) x := by
  simpa [target] using gap6 x hx

end
end ProofGap.Exercise828_9
