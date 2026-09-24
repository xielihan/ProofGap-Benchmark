import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise828_1

noncomputable section

def y (x : ℝ) : ℝ := x ^ 2
def Δy (x Δx : ℝ) : ℝ := y (x + Δx) - y x

private theorem hasDerivAt_y (x : ℝ) : HasDerivAt y (2 * x) x := by
  have h := (hasDerivAt_id x).mul (hasDerivAt_id x)
  have hfun : (id * id : ℝ → ℝ) = (fun z : ℝ => z ^ 2) := by
    funext z
    simp [pow_two]
  rw [hfun] at h
  simpa [y, two_mul] using h

private theorem tendsto_linear (x : ℝ) :
    Filter.Tendsto (fun Δx : ℝ => 2 * x + Δx)
      (nhds 0) (nhds (2 * x)) := by
  have h :=
    (continuousAt_const.add continuousAt_id :
      ContinuousAt ((fun _ : ℝ => 2 * x) + (id : ℝ → ℝ)) 0)
  have hfun :
      ((fun _ : ℝ => 2 * x) + (id : ℝ → ℝ)) =
        (fun Δx : ℝ => 2 * x + Δx) := by
    funext Δx
    rfl
  rw [hfun] at h
  change Filter.Tendsto (fun Δx : ℝ => 2 * x + Δx)
    (nhds 0) (nhds ((fun Δx : ℝ => 2 * x + Δx) 0)) at h
  simpa using h

private theorem tendsto_slope_y (x : ℝ) :
    Filter.Tendsto (fun Δx => Δy x Δx / Δx)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (2 * x)) := by
  have hlin :
      Filter.Tendsto (fun Δx : ℝ => 2 * x + Δx)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (2 * x)) :=
    (tendsto_linear x).mono_left inf_le_left
  apply hlin.congr'
  filter_upwards [self_mem_nhdsWithin] with Δx hΔ
  have hΔ0 : Δx ≠ 0 := by
    simpa using hΔ
  simp only [Δy, y]
  symm
  apply (div_eq_iff hΔ0).2
  ring

theorem gap1 (x Δx : ℝ) :
    Δy x Δx / Δx = ((x + Δx) ^ 2 - x ^ 2) / Δx := by
  rfl
theorem gap2 (x Δx : ℝ) (hΔ : Δx ≠ 0) :
    ((x + Δx) ^ 2 - x ^ 2) / Δx = 2 * x + Δx := by
  apply (div_eq_iff hΔ).2
  ring
theorem gap3 (x Δx : ℝ) (hΔ : Δx ≠ 0) :
    Δy x Δx / Δx = 2 * x + Δx := by
  rw [gap1 x Δx, gap2 x Δx hΔ]
theorem gap4 (x : ℝ) :
    HasDerivAt y (deriv y x) x ↔
      Filter.Tendsto (fun Δx => Δy x Δx / Δx)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (deriv y x)) := by
  constructor
  · intro _
    rw [(hasDerivAt_y x).deriv]
    exact tendsto_slope_y x
  · intro _
    rw [(hasDerivAt_y x).deriv]
    exact hasDerivAt_y x
theorem gap5 (x : ℝ) :
    Filter.Tendsto (fun Δx => Δy x Δx / Δx)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (2 * x)) := by
  exact tendsto_slope_y x
theorem gap6 (x : ℝ) :
    Filter.Tendsto (fun Δx : ℝ => 2 * x + Δx) (nhds 0) (nhds (2 * x)) := by
  exact tendsto_linear x
theorem gap7 (x : ℝ) : deriv y x = 2 * x := by
  exact (hasDerivAt_y x).deriv

end

end ProofGap.Exercise828_1
