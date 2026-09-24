import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Order.Filter.Tendsto
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise1403

noncomputable section
open Filter
open scoped Topology

def rightPunctured (x₀ : ℝ) := nhdsWithin x₀ (Set.Ioi x₀)
def original (a x : ℝ) :=
  (Real.rpow a x + Real.rpow a (-x) - 2) / x ^ 2
def exponentialStage (a x : ℝ) :=
  (Real.exp (x * Real.log a) + Real.exp (-x * Real.log a) - 2) / x ^ 2
def leadingStage (a x : ℝ) := Real.log a ^ 2 + x

private theorem exponentialStage_limit (a : ℝ) :
    Tendsto (exponentialStage a) (rightPunctured 0)
      (nhds (Real.log a ^ 2)) := by
  let L : ℝ := Real.log a
  have hinner : HasDerivAt (fun x : ℝ => x * L) L 0 := by
    simpa using (hasDerivAt_id (𝕜 := ℝ) (0 : ℝ)).mul_const L
  have hderiv : HasDerivAt (fun x : ℝ => Real.exp (x * L)) L 0 := by
    simpa using (Real.hasDerivAt_exp (0 * L)).comp 0 hinner
  have hfilter : rightPunctured 0 ≤ 𝓝[≠] (0 : ℝ) := by
    unfold rightPunctured
    apply nhdsWithin_mono
    intro x hx
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using (ne_of_gt hx)
  have hq0 := hderiv.tendsto_slope.mono_left hfilter
  change
    Tendsto
      (fun x : ℝ => (x - 0)⁻¹ •
        (Real.exp (x * L) - Real.exp (0 * L)))
      (rightPunctured 0) (nhds L) at hq0
  have hq :
      Tendsto (fun x : ℝ => (Real.exp (x * L) - 1) / x)
        (rightPunctured 0) (nhds L) := by
    simpa [div_eq_mul_inv, mul_comm] using hq0
  have hx : Tendsto (fun x : ℝ => x) (rightPunctured 0) (nhds 0) := by
    apply tendsto_id.mono_left
    unfold rightPunctured
    exact inf_le_left
  have ht : Tendsto (fun x : ℝ => x * L) (rightPunctured 0) (nhds 0) := by
    simpa using hx.mul_const L
  have he :
      Tendsto (fun x : ℝ => Real.exp (x * L)) (rightPunctured 0) (nhds 1) := by
    simpa using (Real.continuous_exp.tendsto 0).comp ht
  have hmain :
      Tendsto
        (fun x : ℝ => ((Real.exp (x * L) - 1) / x) ^ 2 / Real.exp (x * L))
        (rightPunctured 0) (nhds (L ^ 2)) := by
    simpa using (hq.pow 2).div he (one_ne_zero : (1 : ℝ) ≠ 0)
  have hfun :
      exponentialStage a =
        (fun x : ℝ => ((Real.exp (x * L) - 1) / x) ^ 2 / Real.exp (x * L)) := by
    funext x
    rcases eq_or_ne x 0 with rfl | hx0
    · simp [exponentialStage]
    · unfold exponentialStage
      rw [show -x * L = -(x * L) by ring, Real.exp_neg]
      field_simp [hx0, Real.exp_ne_zero] <;> ring
  rw [hfun]
  simpa [L] using hmain

theorem gap1 (a : ℝ) (ha : 0 < a) :
    Tendsto (original a) (rightPunctured 0) (nhds (Real.log a ^ 2)) := by
  have hpow (y : ℝ) :
      Real.rpow a y = Real.exp (y * Real.log a) := by
    calc
      Real.rpow a y = Real.exp (Real.log a * y) :=
        Real.rpow_def_of_pos ha y
      _ = Real.exp (y * Real.log a) := by rw [mul_comm]
  have hstage : original a = exponentialStage a := by
    funext x
    unfold original exponentialStage
    rw [hpow x, hpow (-x)]
  rw [hstage]
  exact exponentialStage_limit a
theorem gap2 (a : ℝ) (ha : 0 < a) :
    Tendsto (exponentialStage a) (rightPunctured 0)
      (nhds (Real.log a ^ 2)) := by
  exact exponentialStage_limit a
theorem gap3 (a : ℝ) (ha : 0 < a) :
    Tendsto (leadingStage a) (rightPunctured 0)
      (nhds (Real.log a ^ 2)) := by
  have hx : Tendsto (fun x : ℝ => x) (rightPunctured 0) (nhds 0) := by
    apply tendsto_id.mono_left
    unfold rightPunctured
    exact inf_le_left
  have hc :
      Tendsto (fun _ : ℝ => Real.log a ^ 2) (rightPunctured 0)
        (nhds (Real.log a ^ 2)) := tendsto_const_nhds
  simpa [leadingStage] using hc.add hx
theorem gap4 (a : ℝ) (ha : 0 < a) :
    Tendsto (leadingStage a) (rightPunctured 0)
      (nhds (Real.log a ^ 2)) := by
  exact gap3 a ha
theorem gap5 (a : ℝ) (ha : 0 < a) :
    Tendsto (original a) (rightPunctured 0) (nhds (Real.log a ^ 2)) := by
  exact gap1 a ha

end
end ProofGap.Exercise1403
