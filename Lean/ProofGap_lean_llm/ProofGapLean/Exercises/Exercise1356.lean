import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

namespace ProofGap.Exercise1356

noncomputable section

def HasLimitAtZero (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds L)

def cot (x : ℝ) : ℝ := Real.cos x / Real.sin x
def f₀ (x : ℝ) : ℝ := cot x - 1 / x
def f₁ (x : ℝ) : ℝ := (x * Real.cos x - Real.sin x) / (x * Real.sin x)
def f₂ (x : ℝ) : ℝ :=
  (Real.cos x - x * Real.sin x - Real.cos x) / (Real.sin x + x * Real.cos x)
def f₃ (x : ℝ) : ℝ := -Real.sin x / (Real.sin x / x + Real.cos x)

private theorem tendsto_id_punctured :
    Tendsto (fun x : ℝ => x) (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) :=
  Filter.tendsto_id.mono_left inf_le_left

private theorem sin_div_limit :
    Tendsto (fun x : ℝ => Real.sin x / x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
  have hs : HasDerivAt Real.sin 1 0 := by
    simpa using Real.hasDerivAt_sin 0
  have hsl := hasDerivAt_iff_tendsto_slope.mp hs
  apply hsl.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := by simpa using hx
  simp [slope_def_field, hx0]

private theorem bracket_limit :
    Tendsto (fun x : ℝ => Real.sin x / x + Real.cos x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 2) := by
  have hc : Tendsto Real.cos (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    simpa using
      ((Real.continuous_cos.continuousAt : ContinuousAt Real.cos 0).tendsto).mono_left
        inf_le_left
  convert sin_div_limit.add hc using 1 <;> norm_num

private theorem f₃_limit : HasLimitAtZero f₃ 0 := by
  have hs : Tendsto Real.sin (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
    simpa using
      ((Real.continuous_sin.continuousAt : ContinuousAt Real.sin 0).tendsto).mono_left
        inf_le_left
  unfold HasLimitAtZero
  convert hs.neg.div bracket_limit (by norm_num) using 1 <;> norm_num [f₃]

private theorem f₂_limit : HasLimitAtZero f₂ 0 := by
  apply f₃_limit.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := by simpa using hx
  simp only [f₂, f₃]
  field_simp [hx0]
  ring

private theorem f₁_limit : HasLimitAtZero f₁ 0 := by
  let A : ℝ → ℝ := fun x => x * Real.cos x - Real.sin x
  let B : ℝ → ℝ := fun x => x * Real.sin x
  have hA :
      ∀ᶠ x : ℝ in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
        HasDerivAt A (Real.cos x - x * Real.sin x - Real.cos x) x := by
    filter_upwards with x
    dsimp [A]
    convert ((hasDerivAt_id x).mul (Real.hasDerivAt_cos x)).sub
      (Real.hasDerivAt_sin x) using 1 <;> simp [id] <;> ring
  have hB :
      ∀ᶠ x : ℝ in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
        HasDerivAt B (Real.sin x + x * Real.cos x) x := by
    filter_upwards with x
    dsimp [B]
    convert (hasDerivAt_id x).mul (Real.hasDerivAt_sin x) using 1 <;>
      simp [id] <;> ring
  have hbr_ne :
      ∀ᶠ x : ℝ in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
        Real.sin x / x + Real.cos x ≠ 0 :=
    bracket_limit.eventually_ne (by norm_num)
  have hB_ne :
      ∀ᶠ x : ℝ in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
        Real.sin x + x * Real.cos x ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin, hbr_ne] with x hx hbr
    have hx0 : x ≠ 0 := by simpa using hx
    have heq : Real.sin x + x * Real.cos x =
        x * (Real.sin x / x + Real.cos x) := by
      field_simp [hx0]
    rw [heq]
    exact mul_ne_zero hx0 hbr
  have hzeroA : Tendsto A (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
    have hc : Tendsto Real.cos (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
      simpa using
        ((Real.continuous_cos.continuousAt : ContinuousAt Real.cos 0).tendsto).mono_left
          inf_le_left
    have hs : Tendsto Real.sin (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
      simpa using
        ((Real.continuous_sin.continuousAt : ContinuousAt Real.sin 0).tendsto).mono_left
          inf_le_left
    convert (tendsto_id_punctured.mul hc).sub hs using 1 <;> norm_num [A]
  have hzeroB : Tendsto B (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
    have hs : Tendsto Real.sin (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
      simpa using
        ((Real.continuous_sin.continuousAt : ContinuousAt Real.sin 0).tendsto).mono_left
          inf_le_left
    convert tendsto_id_punctured.mul hs using 1 <;> norm_num [B]
  apply HasDerivAt.lhopital_zero_nhdsNE hA hB hB_ne hzeroA hzeroB
  change Tendsto f₂ (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0)
  exact f₂_limit

private theorem eventually_sin_ne :
    ∀ᶠ x : ℝ in nhdsWithin 0 ({0} : Set ℝ)ᶜ, Real.sin x ≠ 0 := by
  have hsmall : ∀ᶠ x : ℝ in nhds 0, |x| < Real.pi := by
    apply Metric.eventually_nhds_iff.mpr
    refine ⟨Real.pi, Real.pi_pos, ?_⟩
    intro y hy
    simpa [Real.dist_eq] using hy
  filter_upwards [hsmall.filter_mono inf_le_left, self_mem_nhdsWithin] with x hx hne
  have hx0 : x ≠ 0 := by simpa using hne
  rw [abs_lt] at hx
  exact (Real.sin_eq_zero_iff_of_lt_of_lt hx.1 hx.2).not.mpr hx0

private theorem f₀_limit : HasLimitAtZero f₀ 0 := by
  apply f₁_limit.congr'
  filter_upwards [self_mem_nhdsWithin, eventually_sin_ne] with x hx hs
  have hx0 : x ≠ 0 := by simpa using hx
  simp only [f₀, f₁, cot]
  field_simp [hx0, hs]

theorem gap1 : HasLimitAtZero f₀ 0 ↔ HasLimitAtZero f₁ 0 := by
  constructor <;> intro _
  · exact f₁_limit
  · exact f₀_limit
theorem gap2 : HasLimitAtZero f₁ 0 ↔ HasLimitAtZero f₂ 0 := by
  constructor <;> intro _
  · exact f₂_limit
  · exact f₁_limit
theorem gap3 : HasLimitAtZero f₂ 0 ↔ HasLimitAtZero f₃ 0 := by
  constructor <;> intro _
  · exact f₃_limit
  · exact f₂_limit
theorem gap4 : HasLimitAtZero f₃ 0 := by exact f₃_limit
theorem gap5 : HasLimitAtZero f₀ 0 := by exact f₀_limit

end

end ProofGap.Exercise1356
