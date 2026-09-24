import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise738

noncomputable section

def core (x : ℝ) : ℝ := (1 - Real.cos x) / x ^ 2

/-- Source: `proof_gap/exercise_738/1.txt`; the source's equivalence with
`ContinuousAt f 0` is false because the displayed limit is independent of
`f 0`; isolate the actual limit computation. -/
theorem gap1 :
    Filter.Tendsto core (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
      (nhds (1 / 2 : ℝ)) := by
  have hscale_nhds :
      Filter.Tendsto (fun x : ℝ => x / 2) (nhds 0) (nhds 0) := by
    have hcont : ContinuousAt (fun x : ℝ => x / 2) 0 := by
      simpa only [id_eq] using
        (continuousAt_id.div
          (continuousAt_const : ContinuousAt (fun _ : ℝ => (2 : ℝ)) 0)
          (by norm_num : (2 : ℝ) ≠ 0))
    simpa only [ContinuousAt, zero_div] using hcont
  have hscale :
      Filter.Tendsto (fun x : ℝ => x / 2)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · exact hscale_nhds.mono_left inf_le_left
    · filter_upwards [self_mem_nhdsWithin] with x hx
      have hx0 : x ≠ 0 := by simpa using hx
      exact div_ne_zero hx0 (by norm_num)
  have hsin :
      Filter.Tendsto (fun x : ℝ => Real.sin x / x)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    simpa [Real.sin_zero, Real.cos_zero, div_eq_mul_inv, mul_comm] using
      (Real.hasDerivAt_sin 0).tendsto_slope_zero
  have hscaled :
      Filter.Tendsto (fun x : ℝ => Real.sin (x / 2) / (x / 2))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    simpa [Function.comp_def] using hsin.comp hscale
  have hmodel :
      Filter.Tendsto
        (fun x : ℝ => (1 / 2 : ℝ) *
          (Real.sin (x / 2) / (x / 2)) ^ 2)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (1 / 2 : ℝ)) := by
    have hc :
        Filter.Tendsto (fun _ : ℝ => (1 / 2 : ℝ))
          (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (1 / 2 : ℝ)) :=
      tendsto_const_nhds
    simpa using hc.mul (hscaled.pow 2)
  have htrig (x : ℝ) :
      1 - Real.cos x = 2 * (Real.sin (x / 2)) ^ 2 := by
    have hcos :
        Real.cos x = 2 * (Real.cos (x / 2)) ^ 2 - 1 := by
      convert Real.cos_two_mul (x / 2) using 1 <;> ring
    nlinarith [hcos, Real.sin_sq_add_cos_sq (x / 2)]
  refine hmodel.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := by simpa using hx
  rw [core, htrig]
  field_simp [hx0] <;> ring

/-- Source: `proof_gap/exercise_738/2.txt`; include the punctured definition
of `f` needed for the removable-extension criterion. -/
theorem gap2 (f : ℝ → ℝ)
    (hf : ∀ x : ℝ, x ≠ 0 → f x = core x) :
    ContinuousAt f 0 ↔ f 0 = (1 / 2 : ℝ) := by
  have hfeq :
      f =ᶠ[nhdsWithin 0 ({0} : Set ℝ)ᶜ] core := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact hf x (by simpa using hx)
  constructor
  · intro hcont
    have hcore :
        Filter.Tendsto core (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
          (nhds (f 0)) :=
      (hcont.mono_left inf_le_left).congr' hfeq
    exact tendsto_nhds_unique hcore gap1
  · intro h0
    have hpunct :
        Filter.Tendsto f (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
          (nhds (1 / 2 : ℝ)) :=
      gap1.congr' hfeq.symm
    change Filter.Tendsto f (nhds 0) (nhds (f 0))
    rw [h0, Filter.tendsto_def]
    intro s hs
    have hp : f ⁻¹' s ∈ nhdsWithin 0 ({0} : Set ℝ)ᶜ := hpunct hs
    rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hp with
      ⟨u, hu, hu_sub⟩
    refine Filter.mem_of_superset hu ?_
    intro x hx
    by_cases hx0 : x = 0
    · subst x
      simpa [h0] using (mem_of_mem_nhds hs)
    · exact hu_sub ⟨hx, by simpa using hx0⟩

/-- Source: `proof_gap/exercise_738/3.txt`. -/
theorem gap3 (f : ℝ → ℝ)
    (hf : ∀ x : ℝ, x ≠ 0 → f x = core x)
    (h0 : f 0 ∈ ({(1 / 2 : ℝ)} : Set ℝ)) :
    ContinuousAt f 0 := by
  apply (gap2 f hf).2
  simpa using h0

end

end ProofGap.Exercise738
