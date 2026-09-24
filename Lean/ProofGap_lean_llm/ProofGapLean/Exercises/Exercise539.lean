import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise539

noncomputable section

def original (a b x : ℝ) : ℝ :=
  Real.log (Real.cos (a * x)) / Real.log (Real.cos (b * x))
def factored (a b x : ℝ) : ℝ :=
  (Real.log (Real.cos (a * x)) / (Real.cos (a * x) - 1)) *
    ((Real.cos (b * x) - 1) / Real.log (Real.cos (b * x))) *
    ((Real.cos (a * x) - 1) / (Real.cos (b * x) - 1))
def sineRatio (a b x : ℝ) : ℝ :=
  (2 * Real.sin (a * x / 2) ^ 2) / (2 * Real.sin (b * x / 2) ^ 2)
def HasLimitAtZero (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds L)

/-- Exercise 539, gap 1; require the denominator parameter `b≠0`. -/
theorem gap1 (a b : ℝ) (hb : b ≠ 0) (L : ℝ) :
    HasLimitAtZero (original a b) L ↔ HasLimitAtZero (factored a b) L := by
  have hcancel (A B C D : ℝ) (hB : B ≠ 0) (hC : C ≠ 0) (hD : D ≠ 0) :
      A / B = (A / C) * (D / B) * (C / D) := by
    field_simp [hB, hC, hD] <;> ring
  have hfun : original a b = factored a b := by
    funext x
    rw [original, factored]
    by_cases hA : Real.cos (a * x) - 1 = 0
    · have hcosA : Real.cos (a * x) = 1 := sub_eq_zero.mp hA
      simp [hcosA]
    · by_cases hB : Real.log (Real.cos (b * x)) = 0
      · simp [hB]
      · by_cases hD : Real.cos (b * x) - 1 = 0
        · have hcosB : Real.cos (b * x) = 1 := sub_eq_zero.mp hD
          exact (hB (by simp [hcosB])).elim
        · exact hcancel _ _ _ _ hB hA hD
  rw [hfun]

/-- Exercise 539, gap 2; require `b≠0`. -/
theorem gap2 (a b : ℝ) (hb : b ≠ 0) :
    HasLimitAtZero (sineRatio a b) (a ^ 2 / b ^ 2) := by
  unfold HasLimitAtZero
  rcases eq_or_ne a 0 with rfl | ha
  · have hzero : sineRatio 0 b = fun _ : ℝ => 0 := by
      funext x
      simp [sineRatio]
    have hz :
        Filter.Tendsto (fun _ : ℝ => 0)
          (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) :=
      tendsto_const_nhds
    rw [hzero]
    convert hz using 1 <;> norm_num
  have hsinc :
      Filter.Tendsto (fun x : ℝ => Real.sin x / x)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    simpa only [zero_add, Real.sin_zero, sub_zero, Real.cos_zero,
      smul_eq_mul, div_eq_mul_inv, mul_comm] using
      (Real.hasDerivAt_sin 0).tendsto_slope_zero
  have hscale (c : ℝ) (hc : c ≠ 0) :
      Filter.Tendsto (fun x : ℝ => c * x / 2)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) := by
    have hxfull :
        Filter.Tendsto (fun x : ℝ => x) (nhds 0) (nhds 0) :=
      continuousAt_id
    have hx :
        Filter.Tendsto (fun x : ℝ => x)
          (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) :=
      hxfull.mono_left inf_le_left
    have hfull :
        Filter.Tendsto (fun x : ℝ => c * x / 2)
          (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
      simpa using (tendsto_const_nhds.mul hx).div_const (2 : ℝ)
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hfull, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with x hxmem
    have hx0 : x ≠ 0 := by
      simpa using hxmem
    have hcx : c * x / 2 ≠ 0 :=
      div_ne_zero (mul_ne_zero hc hx0) (by norm_num)
    simpa using hcx
  have hsa :
      Filter.Tendsto
        (fun x : ℝ => Real.sin (a * x / 2) / (a * x / 2))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    simpa only [Function.comp_apply] using hsinc.comp (hscale a ha)
  have hsb :
      Filter.Tendsto
        (fun x : ℝ => Real.sin (b * x / 2) / (b * x / 2))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    simpa only [Function.comp_apply] using hsinc.comp (hscale b hb)
  have hmain :
      Filter.Tendsto
        (fun x : ℝ =>
          (a ^ 2 / b ^ 2) *
            ((Real.sin (a * x / 2) / (a * x / 2)) ^ 2 /
              (Real.sin (b * x / 2) / (b * x / 2)) ^ 2))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (a ^ 2 / b ^ 2)) := by
    have hc :
        Filter.Tendsto (fun _ : ℝ => a ^ 2 / b ^ 2)
          (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (a ^ 2 / b ^ 2)) :=
      tendsto_const_nhds
    simpa using
      hc.mul ((hsa.pow 2).div (hsb.pow 2)
        (by norm_num : (1 : ℝ) ^ 2 ≠ 0))
  have hsincb :
      ∀ᶠ x in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
        Real.sin (b * x / 2) / (b * x / 2) ≠ 0 :=
    hsb.eventually (eventually_ne_nhds (by norm_num : (1 : ℝ) ≠ 0))
  have hratio (A B α β x : ℝ)
      (hB : B ≠ 0) (hα : α ≠ 0) (hβ : β ≠ 0) (hx : x ≠ 0) :
      (2 * A ^ 2) / (2 * B ^ 2) =
        (α ^ 2 / β ^ 2) *
          ((A / (α * x / 2)) ^ 2 / (B / (β * x / 2)) ^ 2) := by
    field_simp [hB, hα, hβ, hx] <;> ring
  have heq :
      (fun x : ℝ => sineRatio a b x) =ᶠ[nhdsWithin 0 ({0} : Set ℝ)ᶜ]
        (fun x : ℝ =>
          (a ^ 2 / b ^ 2) *
            ((Real.sin (a * x / 2) / (a * x / 2)) ^ 2 /
              (Real.sin (b * x / 2) / (b * x / 2)) ^ 2)) := by
    filter_upwards [self_mem_nhdsWithin, hsincb] with x hx hsinc
    have hx0 : x ≠ 0 := by simpa using hx
    have hsinb : Real.sin (b * x / 2) ≠ 0 :=
      (div_ne_zero_iff.mp hsinc).1
    unfold sineRatio
    exact hratio _ _ _ _ _ hsinb ha hb hx0
  exact hmain.congr' heq.symm

end

end ProofGap.Exercise539
