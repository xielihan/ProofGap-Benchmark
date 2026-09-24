import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise478

noncomputable section

def original (p x : ℝ) : ℝ :=
  (1 + Real.sin x - Real.cos x) /
    (1 + Real.sin (p * x) - Real.cos (p * x))
def halfAngle (p x : ℝ) : ℝ :=
  (2 * Real.sin (x / 2) ^ 2 + Real.sin x) /
    (2 * Real.sin (p * x / 2) ^ 2 + Real.sin (p * x))
def factored (p x : ℝ) : ℝ :=
  (Real.sin (x / 2) * (Real.sin (x / 2) + Real.cos (x / 2))) /
    (Real.sin (p * x / 2) *
      (Real.sin (p * x / 2) + Real.cos (p * x / 2)))
def normalized (p x : ℝ) : ℝ :=
  (Real.sin (x / 2) / (x / 2)) *
    ((p * x / 2) / Real.sin (p * x / 2)) * (1 / p) *
    ((Real.sin (x / 2) + Real.cos (x / 2)) /
      (Real.sin (p * x / 2) + Real.cos (p * x / 2)))
def HasLimitAtZero (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds L)

/-- Exercise 478, gap 1; require the omitted parameter condition `p≠0`. -/
private theorem original_half_numerator (x : ℝ) :
    1 + Real.sin x - Real.cos x =
      2 * Real.sin (x / 2) ^ 2 + Real.sin x := by
  have hcos : Real.cos x = 2 * Real.cos (x / 2) ^ 2 - 1 := by
    convert Real.cos_two_mul (x / 2) using 1 <;> ring_nf
  have htrig := Real.sin_sq_add_cos_sq (x / 2)
  have hhalf : 1 - Real.cos x = 2 * Real.sin (x / 2) ^ 2 := by
    nlinarith
  calc
    1 + Real.sin x - Real.cos x =
        (1 - Real.cos x) + Real.sin x := by ring
    _ = 2 * Real.sin (x / 2) ^ 2 + Real.sin x := by rw [hhalf]

private theorem sin_factor_identity (x : ℝ) :
    2 * Real.sin (x / 2) ^ 2 + Real.sin x =
      2 * (Real.sin (x / 2) *
        (Real.sin (x / 2) + Real.cos (x / 2))) := by
  have hsin : Real.sin x =
      2 * Real.sin (x / 2) * Real.cos (x / 2) := by
    convert Real.sin_two_mul (x / 2) using 1 <;> ring_nf
  rw [hsin]
  ring

private theorem tendsto_mul_punctured (a : ℝ) (ha : a ≠ 0) :
    Filter.Tendsto (fun x : ℝ => a * x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) := by
  refine Filter.tendsto_inf.2 ⟨?_, ?_⟩
  · have hconst : Filter.Tendsto (fun _ : ℝ => a)
        (nhds 0) (nhds a) := tendsto_const_nhds
    have hid : Filter.Tendsto (fun x : ℝ => x)
        (nhds 0) (nhds 0) := continuousAt_id
    simpa using (hconst.mul hid).mono_left inf_le_left
  · rw [Filter.tendsto_principal]
    have hmem : ∀ᶠ x : ℝ in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
        x ∈ ({0} : Set ℝ)ᶜ := self_mem_nhdsWithin
    filter_upwards [hmem] with x hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx ⊢
    exact mul_ne_zero ha hx

private theorem tendsto_sin_div_self :
    Filter.Tendsto (fun y : ℝ => Real.sin y / y)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
  have hsincFull : Filter.Tendsto Real.sinc
      (nhds 0) (nhds (Real.sinc 0)) :=
    Real.continuous_sinc.continuousAt
  have hsinc : Filter.Tendsto Real.sinc
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    simpa [Real.sinc] using hsincFull.mono_left inf_le_left
  have heq : Real.sinc =ᶠ[nhdsWithin 0 ({0} : Set ℝ)ᶜ]
      (fun y : ℝ => Real.sin y / y) := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hy0 : y ≠ 0 := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hy
    simp [Real.sinc, hy0]
  exact hsinc.congr' heq

private theorem tendsto_sin_div_scale (a : ℝ) (ha : a ≠ 0) :
    Filter.Tendsto (fun x : ℝ => Real.sin (a * x) / (a * x))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
  simpa [Function.comp_def] using
    tendsto_sin_div_self.comp (tendsto_mul_punctured a ha)

private theorem tendsto_sin_add_cos_scale (a : ℝ) (ha : a ≠ 0) :
    Filter.Tendsto
      (fun x : ℝ => Real.sin (a * x) + Real.cos (a * x))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
  have harg : Filter.Tendsto (fun x : ℝ => a * x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) :=
    (tendsto_mul_punctured a ha).mono_right inf_le_left
  have hs := (Real.continuous_sin.tendsto 0).comp harg
  have hc := (Real.continuous_cos.tendsto 0).comp harg
  simpa using hs.add hc

private theorem eventually_ne_zero_of_tendsto_one
    {l : Filter ℝ} {f : ℝ → ℝ}
    (h : Filter.Tendsto f l (nhds 1)) :
    ∀ᶠ x in l, f x ≠ 0 := by
  exact h.eventually
    (eventually_ne_nhds (by norm_num : (1 : ℝ) ≠ 0))

private theorem eventually_sin_scale_ne_zero (a : ℝ) (ha : a ≠ 0) :
    ∀ᶠ x in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
      Real.sin (a * x) ≠ 0 := by
  filter_upwards
      [eventually_ne_zero_of_tendsto_one
        (tendsto_sin_div_scale a ha)] with x hx
  intro hs
  apply hx
  simp [hs]

theorem gap1 (p : ℝ) (hp : p ≠ 0) (L : ℝ) :
    HasLimitAtZero (original p) L ↔ HasLimitAtZero (halfAngle p) L := by
  have heq : original p = halfAngle p := by
    funext x
    unfold original halfAngle
    rw [original_half_numerator x, original_half_numerator (p * x)]
  unfold HasLimitAtZero
  simpa [heq]

/-- Exercise 478, gap 2; require `p≠0`. -/
theorem gap2 (p : ℝ) (hp : p ≠ 0) (L : ℝ) :
    HasLimitAtZero (halfAngle p) L ↔ HasLimitAtZero (factored p) L := by
  have ha : p / 2 ≠ 0 := div_ne_zero hp (by norm_num)
  have hsin : ∀ᶠ x in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
      Real.sin (p * x / 2) ≠ 0 := by
    simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
      (eventually_sin_scale_ne_zero (p / 2) ha)
  have hsum : ∀ᶠ x in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
      Real.sin (p * x / 2) + Real.cos (p * x / 2) ≠ 0 := by
    simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
      (eventually_ne_zero_of_tendsto_one
        (tendsto_sin_add_cos_scale (p / 2) ha))
  have heq : halfAngle p =ᶠ[nhdsWithin 0 ({0} : Set ℝ)ᶜ] factored p := by
    filter_upwards [hsin, hsum] with x hs hc
    unfold halfAngle factored
    rw [sin_factor_identity x, sin_factor_identity (p * x)]
    field_simp [hs, hc]
  have heq' : factored p =ᶠ[nhdsWithin 0 ({0} : Set ℝ)ᶜ] halfAngle p := by
    filter_upwards [heq] with x hx
    exact hx.symm
  unfold HasLimitAtZero
  constructor
  · intro h
    exact h.congr' heq
  · intro h
    exact h.congr' heq'

/-- Exercise 478, gap 3; require `p≠0`. -/
theorem gap3 (p : ℝ) (hp : p ≠ 0) (L : ℝ) :
    HasLimitAtZero (original p) L ↔ HasLimitAtZero (factored p) L := by
  exact (gap1 p hp L).trans (gap2 p hp L)

/-- Exercise 478, gap 4; require `p≠0`. -/
theorem gap4 (p : ℝ) (hp : p ≠ 0) (L : ℝ) :
    HasLimitAtZero (original p) L ↔ HasLimitAtZero (normalized p) L := by
  have ha : p / 2 ≠ 0 := div_ne_zero hp (by norm_num)
  have hsin : ∀ᶠ x in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
      Real.sin (p * x / 2) ≠ 0 := by
    simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
      (eventually_sin_scale_ne_zero (p / 2) ha)
  have hsum : ∀ᶠ x in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
      Real.sin (p * x / 2) + Real.cos (p * x / 2) ≠ 0 := by
    simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
      (eventually_ne_zero_of_tendsto_one
        (tendsto_sin_add_cos_scale (p / 2) ha))
  have heq : factored p =ᶠ[nhdsWithin 0 ({0} : Set ℝ)ᶜ] normalized p := by
    filter_upwards [self_mem_nhdsWithin, hsin, hsum] with x hx hs hc
    have hx0 : x ≠ 0 := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hx
    unfold factored normalized
    field_simp [hp, hx0, hs, hc]
  have heq' : normalized p =ᶠ[nhdsWithin 0 ({0} : Set ℝ)ᶜ] factored p := by
    filter_upwards [heq] with x hx
    exact hx.symm
  have hlim :
      HasLimitAtZero (factored p) L ↔ HasLimitAtZero (normalized p) L := by
    unfold HasLimitAtZero
    constructor
    · intro h
      exact h.congr' heq
    · intro h
      exact h.congr' heq'
  exact (gap3 p hp L).trans hlim

/-- Exercise 478, gap 5; require `p≠0`. -/
theorem gap5 (p : ℝ) (hp : p ≠ 0) :
    HasLimitAtZero (normalized p) (1 / p) := by
  unfold HasLimitAtZero
  have hfirst : Filter.Tendsto
      (fun x : ℝ => Real.sin (x / 2) / (x / 2))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
      (tendsto_sin_div_scale (1 / 2) (by norm_num))
  have ha : p / 2 ≠ 0 := div_ne_zero hp (by norm_num)
  have hscaled := tendsto_sin_div_scale (p / 2) ha
  have hsecond : Filter.Tendsto
      (fun x : ℝ => (p * x / 2) / Real.sin (p * x / 2))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    simpa [inv_div, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
      hscaled.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have hnum : Filter.Tendsto
      (fun x : ℝ => Real.sin (x / 2) + Real.cos (x / 2))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
      (tendsto_sin_add_cos_scale (1 / 2) (by norm_num))
  have hden : Filter.Tendsto
      (fun x : ℝ => Real.sin (p * x / 2) + Real.cos (p * x / 2))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using
      (tendsto_sin_add_cos_scale (p / 2) ha)
  have hfour : Filter.Tendsto
      (fun x : ℝ =>
        (Real.sin (x / 2) + Real.cos (x / 2)) /
          (Real.sin (p * x / 2) + Real.cos (p * x / 2)))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    simpa using hnum.div hden (by norm_num : (1 : ℝ) ≠ 0)
  have hconst : Filter.Tendsto (fun _ : ℝ => 1 / p)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (1 / p)) :=
    tendsto_const_nhds
  have hprod := (((hfirst.mul hsecond).mul hconst).mul hfour)
  change Filter.Tendsto
    (fun x : ℝ =>
      (Real.sin (x / 2) / (x / 2)) *
        ((p * x / 2) / Real.sin (p * x / 2)) * (1 / p) *
        ((Real.sin (x / 2) + Real.cos (x / 2)) /
          (Real.sin (p * x / 2) + Real.cos (p * x / 2))))
    (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (1 / p))
  convert hprod using 1 <;> norm_num

/-- Exercise 478, gap 6; require `p≠0`. -/
theorem gap6 (p : ℝ) (hp : p ≠ 0) :
    HasLimitAtZero (original p) (1 / p) := by
  exact (gap4 p hp (1 / p)).mpr (gap5 p hp)

end

end ProofGap.Exercise478
