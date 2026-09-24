import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace ProofGap.Exercise1326

noncomputable section
open Filter
open scoped Topology

def punctured (x₀ : ℝ) := nhdsWithin x₀ ({x₀} : Set ℝ)ᶜ
def original (x : ℝ) :=
  (1 - Real.cos (x ^ 2)) / (x ^ 2 * Real.sin (x ^ 2))
def substituted (t : ℝ) := (1 - Real.cos t) / (t * Real.sin t)
def derivativeStage (t : ℝ) := Real.sin t / (Real.sin t + t * Real.cos t)
def normalized (t : ℝ) := 1 / (1 + (t / Real.sin t) * Real.cos t)

private theorem sinc_tendsto_zero :
    Tendsto Real.sinc (nhds 0) (nhds (1 : ℝ)) := by
  have h : ContinuousAt Real.sinc (0 : ℝ) :=
    Real.continuous_sinc.continuousAt
  change Tendsto Real.sinc (nhds 0) (nhds (Real.sinc 0)) at h
  simpa [Real.sinc] using h

private theorem id_tendsto_zero_punctured :
    Tendsto (fun x : ℝ => x) (punctured 0) (nhds 0) := by
  apply tendsto_id.mono_left
  unfold punctured
  exact inf_le_left

private theorem sinc_tendsto_zero_punctured :
    Tendsto Real.sinc (punctured 0) (nhds (1 : ℝ)) := by
  apply sinc_tendsto_zero.mono_left
  unfold punctured
  exact inf_le_left

private theorem cos_tendsto_zero_punctured :
    Tendsto Real.cos (punctured 0) (nhds (1 : ℝ)) := by
  have h : ContinuousAt Real.cos (0 : ℝ) :=
    Real.continuous_cos.continuousAt
  change Tendsto Real.cos (nhds 0) (nhds (Real.cos 0)) at h
  have h' : Tendsto Real.cos (nhds 0) (nhds (1 : ℝ)) := by
    simpa using h
  apply h'.mono_left
  unfold punctured
  exact inf_le_left

private theorem eventually_ne_zero :
    ∀ᶠ x : ℝ in punctured 0, x ≠ 0 := by
  change ∀ᶠ x : ℝ in nhdsWithin 0 ({0} : Set ℝ)ᶜ, x ≠ 0
  filter_upwards [self_mem_nhdsWithin] with x hx
  simpa using hx

private theorem substituted_eq_sinc {t : ℝ} (ht : t ≠ 0) :
    substituted t =
      (1 / 2 : ℝ) * Real.sinc (t / 2) ^ 2 / Real.sinc t := by
  have ht2 : t / 2 ≠ 0 := div_ne_zero ht (by norm_num)
  have hcos :
      Real.cos t = 1 - 2 * Real.sin (t / 2) ^ 2 := by
    calc
      Real.cos t = Real.cos (2 * (t / 2)) := by congr 1 <;> ring
      _ = Real.cos (t / 2) ^ 2 - Real.sin (t / 2) ^ 2 :=
        Real.cos_two_mul' (t / 2)
      _ = 1 - 2 * Real.sin (t / 2) ^ 2 := by
        nlinarith [Real.sin_sq_add_cos_sq (t / 2)]
  unfold substituted
  rw [hcos]
  simp only [Real.sinc, if_neg ht, if_neg ht2]
  by_cases hs : Real.sin t = 0
  · simp [hs]
  · field_simp [ht, ht2, hs]
    <;> ring

private theorem substituted_tendsto :
    Tendsto substituted (punctured 0) (nhds (1 / 2 : ℝ)) := by
  have hhalfArg :
      Tendsto (fun t : ℝ => t / 2) (punctured 0) (nhds 0) := by
    convert id_tendsto_zero_punctured.mul_const (1 / 2 : ℝ) using 1 <;> ring
  have hhalf :
      Tendsto (fun t : ℝ => Real.sinc (t / 2))
        (punctured 0) (nhds (1 : ℝ)) :=
    sinc_tendsto_zero.comp hhalfArg
  have hc :
      Tendsto (fun _ : ℝ => (1 / 2 : ℝ))
        (punctured 0) (nhds (1 / 2 : ℝ)) :=
    tendsto_const_nhds
  have hform :
      Tendsto
        (fun t : ℝ =>
          (1 / 2 : ℝ) * Real.sinc (t / 2) ^ 2 / Real.sinc t)
        (punctured 0) (nhds (1 / 2 : ℝ)) := by
    convert (hc.mul (hhalf.pow 2)).div sinc_tendsto_zero_punctured
      (by norm_num) using 1 <;> norm_num
  refine hform.congr' ?_
  filter_upwards [eventually_ne_zero] with t ht
  exact (substituted_eq_sinc ht).symm

private theorem derivativeStage_eq_sinc {t : ℝ} (ht : t ≠ 0) :
    derivativeStage t =
      Real.sinc t / (Real.sinc t + Real.cos t) := by
  unfold derivativeStage
  simp only [Real.sinc, if_neg ht]
  have hrewrite :
      Real.sin t / t + Real.cos t =
        (Real.sin t + t * Real.cos t) / t := by
    field_simp [ht]
    <;> ring
  rw [hrewrite]
  by_cases hd : Real.sin t + t * Real.cos t = 0
  · simp [hd]
  · have hdt :
        (Real.sin t + t * Real.cos t) / t ≠ 0 :=
      div_ne_zero hd ht
    field_simp [ht, hd, hdt]
    <;> ring

private theorem derivativeStage_tendsto :
    Tendsto derivativeStage (punctured 0) (nhds (1 / 2 : ℝ)) := by
  have hform :
      Tendsto
        (fun t : ℝ =>
          Real.sinc t / (Real.sinc t + Real.cos t))
        (punctured 0) (nhds (1 / 2 : ℝ)) := by
    convert sinc_tendsto_zero_punctured.div
      (sinc_tendsto_zero_punctured.add cos_tendsto_zero_punctured)
      (by norm_num) using 1 <;> norm_num
  refine hform.congr' ?_
  filter_upwards [eventually_ne_zero] with t ht
  exact (derivativeStage_eq_sinc ht).symm

private theorem normalized_eq_sinc {t : ℝ} (ht : t ≠ 0) :
    normalized t =
      1 / (1 + (Real.sinc t)⁻¹ * Real.cos t) := by
  unfold normalized
  simp only [Real.sinc, if_neg ht, inv_div]

private theorem normalized_tendsto :
    Tendsto normalized (punctured 0) (nhds (1 / 2 : ℝ)) := by
  have hinv :
      Tendsto (fun t : ℝ => (Real.sinc t)⁻¹)
        (punctured 0) (nhds (1 : ℝ)) := by
    simpa using sinc_tendsto_zero_punctured.inv₀ (by norm_num)
  have hone :
      Tendsto (fun _ : ℝ => (1 : ℝ))
        (punctured 0) (nhds (1 : ℝ)) :=
    tendsto_const_nhds
  have hden :
      Tendsto
        (fun t : ℝ => 1 + (Real.sinc t)⁻¹ * Real.cos t)
        (punctured 0) (nhds (2 : ℝ)) := by
    convert hone.add (hinv.mul cos_tendsto_zero_punctured) using 1 <;> norm_num
  have hform :
      Tendsto
        (fun t : ℝ => 1 / (1 + (Real.sinc t)⁻¹ * Real.cos t))
        (punctured 0) (nhds (1 / 2 : ℝ)) := by
    exact hone.div hden (by norm_num)
  refine hform.congr' ?_
  filter_upwards [eventually_ne_zero] with t ht
  exact (normalized_eq_sinc ht).symm

private theorem sq_tendsto_punctured :
    Tendsto (fun x : ℝ => x ^ 2) (punctured 0) (punctured 0) := by
  have hnhds :
      Tendsto (fun x : ℝ => x ^ 2) (punctured 0) (nhds 0) := by
    simpa using id_tendsto_zero_punctured.pow 2
  have hmem :
      Tendsto (fun x : ℝ => x ^ 2) (punctured 0)
        (principal (({0} : Set ℝ)ᶜ)) := by
    rw [tendsto_principal]
    filter_upwards [eventually_ne_zero] with x hx
    simpa using (pow_ne_zero 2 hx)
  change Tendsto (fun x : ℝ => x ^ 2) (punctured 0)
    (nhds 0 ⊓ principal (({0} : Set ℝ)ᶜ))
  simpa only [inf_idem] using hnhds.inf hmem

theorem gap1 : Tendsto original (punctured 0) (nhds (1 / 2 : ℝ)) := by
  simpa [original, substituted] using
    substituted_tendsto.comp sq_tendsto_punctured
theorem gap2 : Tendsto substituted (punctured 0) (nhds (1 / 2 : ℝ)) := by
  exact substituted_tendsto
theorem gap3 : Tendsto derivativeStage (punctured 0) (nhds (1 / 2 : ℝ)) := by
  exact derivativeStage_tendsto
theorem gap4 : Tendsto normalized (punctured 0) (nhds (1 / 2 : ℝ)) := by
  exact normalized_tendsto
theorem gap5 : Tendsto original (punctured 0) (nhds (1 / 2 : ℝ)) := by
  exact gap1

end
end ProofGap.Exercise1326
