import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise1319

noncomputable section
open Filter
open scoped Topology

def punctured (x₀ : ℝ) := nhdsWithin x₀ ({x₀} : Set ℝ)ᶜ
def original (x : ℝ) := (Real.cosh x - Real.cos x) / x ^ 2
def firstStage (x : ℝ) := (Real.sinh x + Real.sin x) / (2 * x)
def secondStage (x : ℝ) := (Real.cosh x + Real.cos x) / 2

private theorem derivativeQuotientLimit
    {f : ℝ → ℝ} {a : ℝ} (h : HasDerivAt f a 0) (h0 : f 0 = 0) :
    Tendsto (fun x : ℝ => f x / x) (punctured 0) (nhds a) := by
  simpa [punctured, h0, div_eq_mul_inv, mul_comm] using h.tendsto_slope_zero

theorem gap1 : Tendsto original (punctured 0) (nhds 1) := by
  have hsinhDeriv :
      HasDerivAt (fun x : ℝ => Real.sinh (x / 2)) (1 / 2) 0 := by
    have hinner : HasDerivAt (fun x : ℝ => x / 2) (1 / 2) 0 := by
      simpa using (hasDerivAt_id (𝕜 := ℝ) 0).div_const 2
    simpa using (Real.hasDerivAt_sinh (0 / 2)).comp 0 hinner
  have hsinDeriv :
      HasDerivAt (fun x : ℝ => Real.sin (x / 2)) (1 / 2) 0 := by
    have hinner : HasDerivAt (fun x : ℝ => x / 2) (1 / 2) 0 := by
      simpa using (hasDerivAt_id (𝕜 := ℝ) 0).div_const 2
    simpa using (Real.hasDerivAt_sin (0 / 2)).comp 0 hinner
  have hsinh := derivativeQuotientLimit hsinhDeriv (by norm_num)
  have hsin := derivativeQuotientLimit hsinDeriv (by norm_num)
  have hcoshDouble (y : ℝ) :
      Real.cosh (y + y) - 1 = 2 * Real.sinh y ^ 2 := by
    rw [Real.cosh_add]
    nlinarith [Real.cosh_sq_sub_sinh_sq y]
  have hcosDouble (y : ℝ) :
      1 - Real.cos (y + y) = 2 * Real.sin y ^ 2 := by
    rw [Real.cos_add]
    nlinarith [Real.sin_sq_add_cos_sq y]
  have hcosh (x : ℝ) :
      Real.cosh x - 1 = 2 * Real.sinh (x / 2) ^ 2 := by
    have hx : x = x / 2 + x / 2 := by ring
    calc
      Real.cosh x - 1 = Real.cosh (x / 2 + x / 2) - 1 :=
        congrArg (fun z : ℝ => Real.cosh z - 1) hx
      _ = 2 * Real.sinh (x / 2) ^ 2 := hcoshDouble (x / 2)
  have hcos (x : ℝ) :
      1 - Real.cos x = 2 * Real.sin (x / 2) ^ 2 := by
    have hx : x = x / 2 + x / 2 := by ring
    calc
      1 - Real.cos x = 1 - Real.cos (x / 2 + x / 2) :=
        congrArg (fun z : ℝ => 1 - Real.cos z) hx
      _ = 2 * Real.sin (x / 2) ^ 2 := hcosDouble (x / 2)
  have hmem : ∀ᶠ x : ℝ in punctured 0, x ∈ ({0} : Set ℝ)ᶜ := by
    rw [punctured]
    exact self_mem_nhdsWithin
  have hlim : Tendsto
      (fun x : ℝ =>
        2 * (Real.sinh (x / 2) / x) ^ 2 +
          2 * (Real.sin (x / 2) / x) ^ 2)
      (punctured 0) (nhds 1) := by
    convert
      ((tendsto_const_nhds.mul (hsinh.pow 2)).add
        (tendsto_const_nhds.mul (hsin.pow 2))) using 1 <;> norm_num
  refine hlim.congr' ?_
  filter_upwards [hmem] with x hx
  have hx0 : x ≠ 0 := by simpa using hx
  symm
  unfold original
  rw [show Real.cosh x - Real.cos x =
    (Real.cosh x - 1) + (1 - Real.cos x) by ring, hcosh x, hcos x]
  field_simp [hx0]
  <;> ring
theorem gap2 : Tendsto firstStage (punctured 0) (nhds 1) := by
  have hderiv :
      HasDerivAt (fun x : ℝ => Real.sinh x + Real.sin x) 2 0 := by
    convert (Real.hasDerivAt_sinh 0).add (Real.hasDerivAt_sin 0) using 1 <;>
      norm_num
  have hquot := derivativeQuotientLimit hderiv (by norm_num)
  have hlim : Tendsto
      (fun x : ℝ => ((Real.sinh x + Real.sin x) / x) / 2)
      (punctured 0) (nhds 1) := by
    convert hquot.div tendsto_const_nhds (by norm_num : (2 : ℝ) ≠ 0) using 1
    <;> norm_num
  have hmem : ∀ᶠ x : ℝ in punctured 0, x ∈ ({0} : Set ℝ)ᶜ := by
    rw [punctured]
    exact self_mem_nhdsWithin
  refine hlim.congr' ?_
  filter_upwards [hmem] with x hx
  have hx0 : x ≠ 0 := by simpa using hx
  symm
  unfold firstStage
  field_simp [hx0]
  <;> ring
theorem gap3 : Tendsto secondStage (punctured 0) (nhds 1) := by
  have hcont : ContinuousAt secondStage 0 := by
    unfold secondStage
    exact ((Real.continuous_cosh.add Real.continuous_cos).div_const 2).continuousAt
  have h : Tendsto secondStage (nhds 0) (nhds (secondStage 0)) := hcont
  have hvalue : secondStage 0 = 1 := by
    norm_num [secondStage]
  rw [hvalue] at h
  rw [punctured]
  exact h.mono_left inf_le_left
theorem gap4 : Tendsto original (punctured 0) (nhds 1) := by
  exact gap1

end
end ProofGap.Exercise1319
