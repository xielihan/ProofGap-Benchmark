import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ProofGap.Exercise1354

noncomputable section

def HasLimitAtZero (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds L)

def f₀ (x : ℝ) : ℝ := 1 / x - 1 / (Real.exp x - 1)
def f₁ (x : ℝ) : ℝ := (Real.exp x - 1 - x) / (x * (Real.exp x - 1))
def f₂ (x : ℝ) : ℝ := (Real.exp x - 1) / (Real.exp x - 1 + x * Real.exp x)
def f₃ (x : ℝ) : ℝ := Real.exp x / (Real.exp x * (x + 2))

private theorem exercise1354_lhopital_at_zero
    (u v du dv : ℝ → ℝ)
    (hu : ∀ x, HasDerivAt u (du x) x)
    (hv : ∀ x, HasDerivAt v (dv x) x)
    (hu0 : u 0 = 0)
    (hv0 : v 0 = 0)
    (hdv : ∀ᶠ x in nhdsWithin 0 ({0} : Set ℝ)ᶜ, dv x ≠ 0)
    {L : ℝ}
    (hlim : Filter.Tendsto (fun x => du x / dv x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds L)) :
    Filter.Tendsto (fun x => u x / v x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds L) := by
  have hR : nhdsWithin 0 (Set.Ioi 0) ≤
      nhdsWithin 0 ({0} : Set ℝ)ᶜ :=
    nhdsWithin_mono 0 (by
      intro x hx
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact ne_of_gt hx)
  have hL : nhdsWithin 0 (Set.Iio 0) ≤
      nhdsWithin 0 ({0} : Set ℝ)ᶜ :=
    nhdsWithin_mono 0 (by
      intro x hx
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact ne_of_lt hx)
  have hright : Filter.Tendsto (fun x => u x / v x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds L) := by
    apply HasDerivAt.lhopital_zero_nhdsGT (f' := du) (g' := dv)
    · filter_upwards with x
      exact hu x
    · filter_upwards with x
      exact hv x
    · exact hdv.filter_mono hR
    · have h := (hu 0).continuousAt.tendsto.mono_left
        (show nhdsWithin 0 (Set.Ioi 0) ≤ nhds 0 from inf_le_left)
      simpa [hu0] using h
    · have h := (hv 0).continuousAt.tendsto.mono_left
        (show nhdsWithin 0 (Set.Ioi 0) ≤ nhds 0 from inf_le_left)
      simpa [hv0] using h
    · exact hlim.mono_left hR
  have hleft : Filter.Tendsto (fun x => u x / v x)
      (nhdsWithin 0 (Set.Iio 0)) (nhds L) := by
    apply HasDerivAt.lhopital_zero_nhdsLT (f' := du) (g' := dv)
    · filter_upwards with x
      exact hu x
    · filter_upwards with x
      exact hv x
    · exact hdv.filter_mono hL
    · have h := (hu 0).continuousAt.tendsto.mono_left
        (show nhdsWithin 0 (Set.Iio 0) ≤ nhds 0 from inf_le_left)
      simpa [hu0] using h
    · have h := (hv 0).continuousAt.tendsto.mono_left
        (show nhdsWithin 0 (Set.Iio 0) ≤ nhds 0 from inf_le_left)
      simpa [hv0] using h
    · exact hlim.mono_left hL
  have hset : ({0} : Set ℝ)ᶜ = Set.Iio 0 ∪ Set.Ioi 0 := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_union,
      Set.mem_Iio, Set.mem_Ioi]
    constructor
    · intro hx
      exact lt_or_gt_of_ne hx
    · intro hx
      cases hx with
      | inl hlt => exact ne_of_lt hlt
      | inr hgt => exact ne_of_gt hgt
  rw [hset, nhdsWithin_union]
  change Filter.map (fun x => u x / v x)
      (nhdsWithin 0 (Set.Iio 0) ⊔ nhdsWithin 0 (Set.Ioi 0)) ≤ nhds L
  rw [Filter.map_sup]
  exact sup_le hleft hright

private theorem exercise1354_limit_f3 : HasLimitAtZero f₃ (1 / 2) := by
  unfold HasLimitAtZero
  have hcont : ContinuousAt (fun x : ℝ => 1 / (x + 2)) 0 := by
    exact continuousAt_const.div
      (continuousAt_id.add continuousAt_const) (by norm_num)
  have hlim : Filter.Tendsto (fun x : ℝ => 1 / (x + 2))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (1 / 2)) := by
    have h := hcont.tendsto.mono_left
      (show nhdsWithin 0 ({0} : Set ℝ)ᶜ ≤ nhds 0 from inf_le_left)
    norm_num at h ⊢
    exact h
  apply hlim.congr'
  filter_upwards with x
  change 1 / (x + 2) = Real.exp x / (Real.exp x * (x + 2))
  by_cases hx : x + 2 = 0
  · simp [hx]
  · field_simp [hx, Real.exp_ne_zero x]

private theorem exercise1354_limit_f2 : HasLimitAtZero f₂ (1 / 2) := by
  let u : ℝ → ℝ := fun x => Real.exp x - 1
  let v : ℝ → ℝ := fun x => Real.exp x - 1 + x * Real.exp x
  let du : ℝ → ℝ := fun x => Real.exp x
  let dv : ℝ → ℝ := fun x => Real.exp x * (x + 2)
  have hu : ∀ x, HasDerivAt u (du x) x := by
    intro x
    simpa [u, du] using (Real.hasDerivAt_exp x).sub_const 1
  have hv : ∀ x, HasDerivAt v (dv x) x := by
    intro x
    convert ((Real.hasDerivAt_exp x).sub_const 1).add
      ((hasDerivAt_id x).mul (Real.hasDerivAt_exp x)) using 1 <;>
      simp [v, dv] <;> ring
  have hu0 : u 0 = 0 := by simp [u]
  have hv0 : v 0 = 0 := by simp [v]
  have hdv : ∀ᶠ x in nhdsWithin 0 ({0} : Set ℝ)ᶜ, dv x ≠ 0 := by
    have hc : ContinuousAt dv 0 := by
      dsimp [dv]
      fun_prop
    have hne : dv 0 ≠ 0 := by norm_num [dv]
    have h := hc.eventually_ne hne
    exact h.filter_mono
      (show nhdsWithin 0 ({0} : Set ℝ)ᶜ ≤ nhds 0 from inf_le_left)
  have hr := exercise1354_lhopital_at_zero u v du dv hu hv hu0 hv0 hdv
    (show Filter.Tendsto (fun x => du x / dv x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (1 / 2)) by
      simpa [du, dv, f₃] using exercise1354_limit_f3)
  simpa [HasLimitAtZero, u, v, f₂] using hr

private theorem exercise1354_limit_f1 : HasLimitAtZero f₁ (1 / 2) := by
  let u : ℝ → ℝ := fun x => Real.exp x - 1 - x
  let v : ℝ → ℝ := fun x => x * (Real.exp x - 1)
  let du : ℝ → ℝ := fun x => Real.exp x - 1
  let dv : ℝ → ℝ := fun x => Real.exp x - 1 + x * Real.exp x
  have hu : ∀ x, HasDerivAt u (du x) x := by
    intro x
    convert ((Real.hasDerivAt_exp x).sub_const 1).sub (hasDerivAt_id x) using 1 <;>
      simp [u, du]
  have hv : ∀ x, HasDerivAt v (dv x) x := by
    intro x
    convert (hasDerivAt_id x).mul ((Real.hasDerivAt_exp x).sub_const 1) using 1 <;>
      simp [v, dv] <;> ring
  have hu0 : u 0 = 0 := by simp [u]
  have hv0 : v 0 = 0 := by simp [v]
  have hdv : ∀ᶠ x in nhdsWithin 0 ({0} : Set ℝ)ᶜ, dv x ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := by simpa using hx
    have hexp : 0 < Real.exp x := Real.exp_pos x
    by_cases hxp : 0 < x
    · have he : 1 < Real.exp x := by
        simpa using (Real.exp_lt_exp.mpr hxp)
      have hp : 0 < x * Real.exp x := mul_pos hxp hexp
      dsimp [dv]
      linarith
    · have hxn : x < 0 := lt_of_le_of_ne (le_of_not_gt hxp) hx0
      have he : Real.exp x < 1 := by
        simpa using (Real.exp_lt_exp.mpr hxn)
      have hp : x * Real.exp x < 0 := mul_neg_of_neg_of_pos hxn hexp
      dsimp [dv]
      linarith
  have hr := exercise1354_lhopital_at_zero u v du dv hu hv hu0 hv0 hdv
    (show Filter.Tendsto (fun x => du x / dv x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (1 / 2)) by
      simpa [du, dv, f₂] using exercise1354_limit_f2)
  simpa [HasLimitAtZero, u, v, f₁] using hr

private theorem exercise1354_limit_f0 : HasLimitAtZero f₀ (1 / 2) := by
  unfold HasLimitAtZero
  have h := exercise1354_limit_f1
  unfold HasLimitAtZero at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := by simpa using hx
  have he0 : Real.exp x - 1 ≠ 0 := by
    intro he
    have hexp1 : Real.exp x = 1 := sub_eq_zero.mp he
    have hexp0 : Real.exp x = Real.exp 0 := by simpa using hexp1
    exact hx0 (Real.exp_injective hexp0)
  dsimp only [f₁, f₀]
  field_simp [hx0, he0]

theorem gap1 : HasLimitAtZero f₀ (1 / 2) ↔ HasLimitAtZero f₁ (1 / 2) := by
  constructor
  · intro _
    exact exercise1354_limit_f1
  · intro _
    exact exercise1354_limit_f0
theorem gap2 : HasLimitAtZero f₁ (1 / 2) ↔ HasLimitAtZero f₂ (1 / 2) := by
  constructor
  · intro _
    exact exercise1354_limit_f2
  · intro _
    exact exercise1354_limit_f1
theorem gap3 : HasLimitAtZero f₂ (1 / 2) ↔ HasLimitAtZero f₃ (1 / 2) := by
  constructor
  · intro _
    exact exercise1354_limit_f3
  · intro _
    exact exercise1354_limit_f2
theorem gap4 : HasLimitAtZero f₃ (1 / 2) := by
  exact exercise1354_limit_f3
theorem gap5 : HasLimitAtZero f₀ (1 / 2) := by
  exact exercise1354_limit_f0

end

end ProofGap.Exercise1354
