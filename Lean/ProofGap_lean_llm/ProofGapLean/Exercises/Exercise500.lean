import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise500

noncomputable section

def original (x : ℝ) : ℝ :=
  x ^ 2 / (Real.sqrt (1 + x * Real.sin x) - Real.sqrt (Real.cos x))
def rationalized (x : ℝ) : ℝ :=
  x ^ 2 * (Real.sqrt (1 + x * Real.sin x) + Real.sqrt (Real.cos x)) /
    (1 + x * Real.sin x - Real.cos x)
def normalized (x : ℝ) : ℝ :=
  (Real.sqrt (1 + x * Real.sin x) + Real.sqrt (Real.cos x)) /
    (Real.sin x / x + 2 * Real.sin (x / 2) ^ 2 / x ^ 2)
def HasLimitAtZero (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds L)

/-- Source: `proof_gap/exercise_500/1.txt`. -/
private theorem limit_data :
    (original =ᶠ[nhdsWithin 0 ({0} : Set ℝ)ᶜ] rationalized) ∧
      (rationalized =ᶠ[nhdsWithin 0 ({0} : Set ℝ)ᶜ] normalized) ∧
        Filter.Tendsto normalized (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
          (nhds (4 / 3 : ℝ)) := by
  have hx_full : Filter.Tendsto (fun x : ℝ => x) (nhds 0) (nhds 0) := by
    simpa using (continuousAt_id : ContinuousAt (fun x : ℝ => x) 0)
  have hx : Filter.Tendsto (fun x : ℝ => x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) :=
    hx_full.mono_left inf_le_left
  have hsin_div : Filter.Tendsto (fun x : ℝ => Real.sin x / x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    have hslope := (Real.hasDerivAt_sin 0).tendsto_slope
    have heq : slope Real.sin 0 =ᶠ[nhdsWithin 0 ({0} : Set ℝ)ᶜ]
        (fun x : ℝ => Real.sin x / x) := by
      refine Filter.Eventually.of_forall ?_
      intro x
      change (x - 0)⁻¹ * (Real.sin x - Real.sin 0) = Real.sin x / x
      simp [div_eq_mul_inv, mul_comm]
    have h := (Filter.tendsto_congr' heq).1 hslope
    simpa using h
  have hsin : Filter.Tendsto (fun x : ℝ => Real.sin x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
    simpa using (Real.continuous_sin.continuousAt.tendsto.comp hx)
  have hcos : Filter.Tendsto (fun x : ℝ => Real.cos x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    simpa using (Real.continuous_cos.continuousAt.tendsto.comp hx)
  have hA : Filter.Tendsto (fun x : ℝ => 1 + x * Real.sin x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    have hone : Filter.Tendsto (fun _ : ℝ => (1 : ℝ))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := tendsto_const_nhds
    convert hone.add (hx.mul hsin) using 1 <;> norm_num
  have hsqrtA : Filter.Tendsto
      (fun x : ℝ => Real.sqrt (1 + x * Real.sin x))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    simpa using (Real.continuous_sqrt.continuousAt.tendsto.comp hA)
  have hsqrtC : Filter.Tendsto (fun x : ℝ => Real.sqrt (Real.cos x))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    simpa using (Real.continuous_sqrt.continuousAt.tendsto.comp hcos)
  have htwo : Filter.Tendsto (fun _ : ℝ => (2 : ℝ))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 2) := tendsto_const_nhds
  have hscale_nhds : Filter.Tendsto (fun x : ℝ => x / 2)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
    convert hx.div htwo (by norm_num : (2 : ℝ) ≠ 0) using 1 <;> norm_num
  have hscale : Filter.Tendsto (fun x : ℝ => x / 2)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hscale_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with x hx0
    have hxne : x ≠ 0 := by simpa using hx0
    simpa using (div_ne_zero hxne (by norm_num : (2 : ℝ) ≠ 0))
  have hq : Filter.Tendsto
      (fun x : ℝ => Real.sin (x / 2) / (x / 2))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) :=
    hsin_div.comp hscale
  have hhalf : Filter.Tendsto (fun _ : ℝ => (1 / 2 : ℝ))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (1 / 2 : ℝ)) :=
    tendsto_const_nhds
  have hsecond_model : Filter.Tendsto
      (fun x : ℝ => (1 / 2 : ℝ) *
        (Real.sin (x / 2) / (x / 2)) ^ 2)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (1 / 2 : ℝ)) := by
    convert hhalf.mul (hq.pow 2) using 1 <;> norm_num
  have hsecond_eq :
      (fun x : ℝ => 2 * Real.sin (x / 2) ^ 2 / x ^ 2) =ᶠ[
        nhdsWithin 0 ({0} : Set ℝ)ᶜ]
      (fun x : ℝ => (1 / 2 : ℝ) *
        (Real.sin (x / 2) / (x / 2)) ^ 2) := by
    filter_upwards [self_mem_nhdsWithin] with x hx0
    have hxne : x ≠ 0 := by simpa using hx0
    field_simp [hxne] <;> ring
  have hsecond : Filter.Tendsto
      (fun x : ℝ => 2 * Real.sin (x / 2) ^ 2 / x ^ 2)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (1 / 2 : ℝ)) :=
    (Filter.tendsto_congr' hsecond_eq).2 hsecond_model
  have hden : Filter.Tendsto
      (fun x : ℝ => Real.sin x / x +
        2 * Real.sin (x / 2) ^ 2 / x ^ 2)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (3 / 2 : ℝ)) := by
    convert hsin_div.add hsecond using 1 <;> norm_num
  have hnum : Filter.Tendsto
      (fun x : ℝ => Real.sqrt (1 + x * Real.sin x) +
        Real.sqrt (Real.cos x))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 2) := by
    convert hsqrtA.add hsqrtC using 1 <;> norm_num
  have hnormalized : Filter.Tendsto normalized
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (4 / 3 : ℝ)) := by
    unfold normalized
    convert hnum.div hden (by norm_num : (3 / 2 : ℝ) ≠ 0) using 1 <;>
      norm_num
  have hden_pos : ∀ᶠ x in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
      0 < Real.sin x / x + 2 * Real.sin (x / 2) ^ 2 / x ^ 2 :=
    (tendsto_order.1 hden).1 0 (by norm_num)
  have hA_pos : ∀ᶠ x in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
      0 < 1 + x * Real.sin x :=
    (tendsto_order.1 hA).1 0 (by norm_num)
  have hC_pos : ∀ᶠ x in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
      0 < Real.cos x :=
    (tendsto_order.1 hcos).1 0 (by norm_num)
  have htrig (x : ℝ) :
      1 - Real.cos x = 2 * Real.sin (x / 2) ^ 2 := by
    calc
      1 - Real.cos x = 1 - Real.cos (2 * (x / 2)) := by
        have h : (2 : ℝ) * (x / 2) = x := by ring
        rw [h]
      _ = 2 * Real.sin (x / 2) ^ 2 := by
        rw [Real.cos_two_mul]
        nlinarith [Real.sin_sq_add_cos_sq (x / 2)]
  have hden_formula (x : ℝ) (hxne : x ≠ 0) :
      1 + x * Real.sin x - Real.cos x =
        x ^ 2 * (Real.sin x / x +
          2 * Real.sin (x / 2) ^ 2 / x ^ 2) := by
    calc
      1 + x * Real.sin x - Real.cos x =
          x * Real.sin x + (1 - Real.cos x) := by ring
      _ = x * Real.sin x + 2 * Real.sin (x / 2) ^ 2 := by
        rw [htrig]
      _ = x ^ 2 * (Real.sin x / x +
          2 * Real.sin (x / 2) ^ 2 / x ^ 2) := by
        field_simp [hxne] <;> ring
  have heq_rn : rationalized =ᶠ[nhdsWithin 0 ({0} : Set ℝ)ᶜ]
      normalized := by
    filter_upwards [self_mem_nhdsWithin, hden_pos] with x hx0 hd
    have hxne : x ≠ 0 := by simpa using hx0
    unfold rationalized normalized
    rw [hden_formula x hxne]
    field_simp [hxne, ne_of_gt hd] <;> ring
  have heq_or : original =ᶠ[nhdsWithin 0 ({0} : Set ℝ)ᶜ]
      rationalized := by
    filter_upwards [self_mem_nhdsWithin, hden_pos, hA_pos, hC_pos]
      with x hx0 hd hapos hcpos
    have hxne : x ≠ 0 := by simpa using hx0
    have hactual_ne : 1 + x * Real.sin x - Real.cos x ≠ 0 := by
      rw [hden_formula x hxne]
      exact mul_ne_zero (pow_ne_zero 2 hxne) (ne_of_gt hd)
    have hsA : Real.sqrt (1 + x * Real.sin x) ^ 2 =
        1 + x * Real.sin x := Real.sq_sqrt (le_of_lt hapos)
    have hsC : Real.sqrt (Real.cos x) ^ 2 = Real.cos x :=
      Real.sq_sqrt (le_of_lt hcpos)
    have hfactor :
        (Real.sqrt (1 + x * Real.sin x) - Real.sqrt (Real.cos x)) *
          (Real.sqrt (1 + x * Real.sin x) + Real.sqrt (Real.cos x)) =
            1 + x * Real.sin x - Real.cos x := by
      calc
        _ = Real.sqrt (1 + x * Real.sin x) ^ 2 -
            Real.sqrt (Real.cos x) ^ 2 := by ring
        _ = (1 + x * Real.sin x) - Real.cos x := by rw [hsA, hsC]
        _ = 1 + x * Real.sin x - Real.cos x := by ring
    have hprod_ne :
        (Real.sqrt (1 + x * Real.sin x) - Real.sqrt (Real.cos x)) *
          (Real.sqrt (1 + x * Real.sin x) + Real.sqrt (Real.cos x)) ≠ 0 := by
      rw [hfactor]
      exact hactual_ne
    have hdiff_ne :
        Real.sqrt (1 + x * Real.sin x) - Real.sqrt (Real.cos x) ≠ 0 :=
      (mul_ne_zero_iff.mp hprod_ne).1
    have hsum_ne :
        Real.sqrt (1 + x * Real.sin x) + Real.sqrt (Real.cos x) ≠ 0 :=
      (mul_ne_zero_iff.mp hprod_ne).2
    unfold original rationalized
    rw [← hfactor]
    field_simp [hdiff_ne, hsum_ne] <;> ring
  exact ⟨heq_or, heq_rn, hnormalized⟩

theorem gap1 (L : ℝ) :
    HasLimitAtZero original L ↔ HasLimitAtZero rationalized L := by
  unfold HasLimitAtZero
  exact Filter.tendsto_congr' limit_data.1

/-- Source: `proof_gap/exercise_500/2.txt`. -/
theorem gap2 (L : ℝ) :
    HasLimitAtZero rationalized L ↔ HasLimitAtZero normalized L := by
  unfold HasLimitAtZero
  exact Filter.tendsto_congr' limit_data.2.1

/-- Source: `proof_gap/exercise_500/3.txt`. -/
theorem gap3 : HasLimitAtZero normalized (4 / 3) := by
  unfold HasLimitAtZero
  exact limit_data.2.2

/-- Source: `proof_gap/exercise_500/4.txt`. -/
theorem gap4 : HasLimitAtZero original (4 / 3) := by
  exact (gap1 (4 / 3)).2 ((gap2 (4 / 3)).2 gap3)

end

end ProofGap.Exercise500
