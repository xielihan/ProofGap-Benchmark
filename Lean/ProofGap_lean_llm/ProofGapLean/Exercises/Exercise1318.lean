import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1318

noncomputable section
open Filter
open scoped Topology

def punctured (x₀ : ℝ) := nhdsWithin x₀ ({x₀} : Set ℝ)ᶜ
def original (a b x : ℝ) := Real.sin (a * x) / Real.sin (b * x)
def firstDerivatives (a b x : ℝ) :=
  (a * Real.cos (a * x)) / (b * Real.cos (b * x))

private theorem sin_eq_arg_mul_sinc (x : ℝ) :
    Real.sin x = x * Real.sinc x := by
  by_cases hx : x = 0
  · subst x
    simp
  · rw [Real.sinc_of_ne_zero hx]
    field_simp [hx]

theorem gap1 (a b : ℝ) (hb : b ≠ 0) :
    Tendsto (original a b) (punctured 0) (nhds (a / b)) := by
  have hlin_a : Continuous (fun x : ℝ => a * x) :=
    continuous_const.mul continuous_id
  have hlin_b : Continuous (fun x : ℝ => b * x) :=
    continuous_const.mul continuous_id
  have hnum : ContinuousAt (fun x : ℝ => a * Real.sinc (a * x)) 0 :=
    (continuous_const.mul (Real.continuous_sinc.comp hlin_a)).continuousAt
  have hden : ContinuousAt (fun x : ℝ => b * Real.sinc (b * x)) 0 :=
    (continuous_const.mul (Real.continuous_sinc.comp hlin_b)).continuousAt
  have hden0 : b * Real.sinc (b * (0 : ℝ)) ≠ 0 := by
    simpa [Real.sinc] using hb
  have hquot :
      ContinuousAt
        (fun x : ℝ =>
          (a * Real.sinc (a * x)) / (b * Real.sinc (b * x))) 0 :=
    hnum.div hden hden0
  have hle : punctured 0 ≤ nhds 0 := by
    unfold punctured nhdsWithin
    exact inf_le_left
  have ht :
      Tendsto
        (fun x : ℝ =>
          (a * Real.sinc (a * x)) / (b * Real.sinc (b * x)))
        (punctured 0) (nhds (a / b)) := by
    simpa [Real.sinc] using hquot.tendsto.mono_left hle
  have hx_ne : ∀ᶠ x in punctured 0, x ≠ 0 := by
    change ∀ᶠ x in nhdsWithin 0 (({0} : Set ℝ)ᶜ), x ≠ 0
    filter_upwards [self_mem_nhdsWithin] with x hx
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hx
  apply ht.congr'
  filter_upwards [hx_ne] with x hx
  unfold original
  rw [sin_eq_arg_mul_sinc, sin_eq_arg_mul_sinc]
  field_simp [hx, hb]
  <;> ring
theorem gap2 (a b : ℝ) (hb : b ≠ 0) :
    Tendsto (firstDerivatives a b) (punctured 0) (nhds (a / b)) := by
  have hlin_a : Continuous (fun x : ℝ => a * x) :=
    continuous_const.mul continuous_id
  have hlin_b : Continuous (fun x : ℝ => b * x) :=
    continuous_const.mul continuous_id
  have hnum :
      ContinuousAt (fun x : ℝ => a * Real.cos (a * x)) 0 :=
    (continuous_const.mul (Real.continuous_cos.comp hlin_a)).continuousAt
  have hden :
      ContinuousAt (fun x : ℝ => b * Real.cos (b * x)) 0 :=
    (continuous_const.mul (Real.continuous_cos.comp hlin_b)).continuousAt
  have hden0 : b * Real.cos (b * (0 : ℝ)) ≠ 0 := by
    simpa using hb
  have hquot : ContinuousAt (firstDerivatives a b) 0 := by
    simpa [firstDerivatives] using hnum.div hden hden0
  have hle : punctured 0 ≤ nhds 0 := by
    unfold punctured nhdsWithin
    exact inf_le_left
  simpa [firstDerivatives] using hquot.tendsto.mono_left hle
theorem gap3 (a b : ℝ) (hb : b ≠ 0) :
    Tendsto (original a b) (punctured 0) (nhds (a / b)) := by
  exact gap1 a b hb

end
end ProofGap.Exercise1318
