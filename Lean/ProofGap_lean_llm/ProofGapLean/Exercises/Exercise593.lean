import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise593

noncomputable section

def original (x : ℝ) : ℝ := Real.sqrt (x ^ 2 + x) - x
def rationalized (x : ℝ) : ℝ := x / (Real.sqrt (x ^ 2 + x) + x)
def HasLimitAtPosInfinity (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f Filter.atTop (nhds L)

/-- Source: `proof_gap/exercise_593/1.txt`. -/
theorem gap1 : Filter.Tendsto original Filter.atBot Filter.atTop := by
  refine Filter.tendsto_atTop.2 ?_
  intro b
  filter_upwards [Filter.eventually_le_atBot (-b)] with x hx
  have hsqrt : 0 ≤ Real.sqrt (x ^ 2 + x) := Real.sqrt_nonneg _
  unfold original
  linarith

/-- Source: `proof_gap/exercise_593/2.txt`. -/
theorem gap2 (L : ℝ) :
    HasLimitAtPosInfinity original L ↔ HasLimitAtPosInfinity rationalized L := by
  have heq : original =ᶠ[Filter.atTop] rationalized := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
    have hrad : 0 ≤ x ^ 2 + x := by
      nlinarith [sq_nonneg x]
    have hden : Real.sqrt (x ^ 2 + x) + x ≠ 0 := by
      have hsqrt := Real.sqrt_nonneg (x ^ 2 + x)
      nlinarith
    unfold original rationalized
    apply (eq_div_iff hden).2
    nlinarith [Real.sq_sqrt hrad]
  constructor
  · intro h
    exact h.congr' heq
  · intro h
    exact h.congr' heq.symm

/-- Source: `proof_gap/exercise_593/3.txt`. -/
theorem gap3 : HasLimitAtPosInfinity rationalized (1 / 2) := by
  unfold HasLimitAtPosInfinity
  have hinv :
      Filter.Tendsto (fun x : ℝ => x⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  have hone :
      Filter.Tendsto (fun _ : ℝ => (1 : ℝ)) Filter.atTop (nhds 1) :=
    tendsto_const_nhds
  have hinside :
      Filter.Tendsto (fun x : ℝ => 1 + x⁻¹) Filter.atTop (nhds 1) := by
    simpa using hone.add hinv
  have hsqrt :
      Filter.Tendsto (fun x : ℝ => Real.sqrt (1 + x⁻¹))
        Filter.atTop (nhds 1) := by
    simpa using (Real.continuous_sqrt.tendsto (1 : ℝ)).comp hinside
  have hden :
      Filter.Tendsto (fun x : ℝ => Real.sqrt (1 + x⁻¹) + 1)
        Filter.atTop (nhds 2) := by
    have h := hsqrt.add hone
    norm_num at h
    exact h
  have hrecip :
      Filter.Tendsto (fun x : ℝ => (Real.sqrt (1 + x⁻¹) + 1)⁻¹)
        Filter.atTop (nhds ((2 : ℝ)⁻¹)) :=
    hden.inv₀ (by norm_num)
  have heq :
      rationalized =ᶠ[Filter.atTop]
        (fun x : ℝ => (Real.sqrt (1 + x⁻¹) + 1)⁻¹) := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
    have hx0 : x ≠ 0 := ne_of_gt hx
    have hxinv : 0 < x⁻¹ := inv_pos.mpr hx
    have hrad₁ : 0 ≤ x ^ 2 + x := by
      nlinarith [sq_nonneg x]
    have hrad₂ : 0 ≤ 1 + x⁻¹ := by
      linarith
    have hrel : x ^ 2 * (1 + x⁻¹) = x ^ 2 + x := by
      field_simp [hx0] <;> ring
    have hsquares :
        (Real.sqrt (x ^ 2 + x)) ^ 2 =
          (x * Real.sqrt (1 + x⁻¹)) ^ 2 := by
      rw [Real.sq_sqrt hrad₁, mul_pow, Real.sq_sqrt hrad₂]
      exact hrel.symm
    have hscale :
        Real.sqrt (x ^ 2 + x) = x * Real.sqrt (1 + x⁻¹) := by
      have hleft := Real.sqrt_nonneg (x ^ 2 + x)
      have hright : 0 ≤ x * Real.sqrt (1 + x⁻¹) :=
        mul_nonneg (le_of_lt hx) (Real.sqrt_nonneg _)
      nlinarith
    have hunit : Real.sqrt (1 + x⁻¹) + 1 ≠ 0 := by
      have hs := Real.sqrt_nonneg (1 + x⁻¹)
      nlinarith
    unfold rationalized
    rw [hscale]
    field_simp [hx0, hunit] <;> ring
  have hrat :
      Filter.Tendsto rationalized Filter.atTop (nhds ((2 : ℝ)⁻¹)) :=
    hrecip.congr' heq.symm
  simpa [one_div] using hrat

/-- Source: `proof_gap/exercise_593/4.txt`. -/
theorem gap4 : HasLimitAtPosInfinity original (1 / 2) := by
  exact (gap2 (1 / 2)).mpr gap3

end

end ProofGap.Exercise593
