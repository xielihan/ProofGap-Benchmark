import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise505

noncomputable section

def difference (x : ℝ) : ℝ :=
  Real.sin (Real.sqrt (x + 1)) - Real.sin (Real.sqrt x)
def rootDifference (x : ℝ) : ℝ := Real.sqrt (x + 1) - Real.sqrt x
def productForm (x : ℝ) : ℝ :=
  2 * Real.sin (rootDifference x / 2) *
    Real.cos ((Real.sqrt (x + 1) + Real.sqrt x) / 2)
def HasLimitAtPosInfinity (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f Filter.atTop (nhds L)

/-- Source: `proof_gap/exercise_505/1.txt`; restrict the square roots to `x≥0`. -/
theorem gap1 (x : ℝ) (hx : 0 ≤ x) : difference x = productForm x := by
  let a : ℝ := Real.sqrt (x + 1)
  let b : ℝ := Real.sqrt x
  change
    Real.sin a - Real.sin b =
      2 * Real.sin ((a - b) / 2) * Real.cos ((a + b) / 2)
  calc
    Real.sin a - Real.sin b =
        Real.sin ((a - b) / 2 + (a + b) / 2) -
          Real.sin ((a + b) / 2 - (a - b) / 2) := by
      apply congrArg₂ (fun u v : ℝ => u - v)
      · apply congrArg Real.sin
        ring
      · apply congrArg Real.sin
        ring
    _ = 2 * Real.sin ((a - b) / 2) * Real.cos ((a + b) / 2) := by
      rw [Real.sin_add, Real.sin_sub]
      ring

/-- Source: `proof_gap/exercise_505/2.txt`; restrict the square roots to `x≥0`. -/
theorem gap2 (x : ℝ) (hx : 0 ≤ x) :
    rootDifference x = 1 / (Real.sqrt (x + 1) + Real.sqrt x) := by
  unfold rootDifference
  have hx1 : 0 ≤ x + 1 := by
    linarith
  have hpos : 0 < Real.sqrt (x + 1) + Real.sqrt x := by
    have hspos : 0 < Real.sqrt (x + 1) :=
      Real.sqrt_pos.2 (by linarith)
    nlinarith [Real.sqrt_nonneg x]
  have hne : Real.sqrt (x + 1) + Real.sqrt x ≠ 0 := ne_of_gt hpos
  apply (eq_div_iff hne).2
  nlinarith [Real.sq_sqrt hx1, Real.sq_sqrt hx]

/-- Source: `proof_gap/exercise_505/3.txt`. -/
theorem gap3 :
    HasLimitAtPosInfinity
      (fun x => 1 / (Real.sqrt (x + 1) + Real.sqrt x)) 0 := by
  unfold HasLimitAtPosInfinity
  have hden :
      Filter.Tendsto
        (fun x : ℝ => Real.sqrt (x + 1) + Real.sqrt x)
        Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop.2 ?_
    intro b
    filter_upwards [
      (Filter.tendsto_atTop.1 Real.tendsto_sqrt_atTop) b
    ] with x hx
    nlinarith [Real.sqrt_nonneg (x + 1)]
  have hinv :
      Filter.Tendsto (fun y : ℝ => y⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  simpa [one_div] using hinv.comp hden

/-- Source: `proof_gap/exercise_505/4.txt`. -/
theorem gap4 : HasLimitAtPosInfinity rootDifference 0 := by
  unfold HasLimitAtPosInfinity
  have heq :
      (fun x : ℝ => 1 / (Real.sqrt (x + 1) + Real.sqrt x)) =ᶠ[Filter.atTop]
        rootDifference := by
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with x hx
    exact (gap2 x hx).symm
  exact gap3.congr' heq

/-- Source: `proof_gap/exercise_505/5.txt`. -/
theorem gap5 :
    HasLimitAtPosInfinity (fun x => Real.sin (rootDifference x / 2)) 0 := by
  unfold HasLimitAtPosInfinity
  have hhalf :
      Filter.Tendsto
        (fun x : ℝ => rootDifference x * (2 : ℝ)⁻¹)
        Filter.atTop (nhds 0) := by
    simpa using gap4.mul_const ((2 : ℝ)⁻¹)
  simpa [div_eq_mul_inv] using
    (Real.continuous_sin.tendsto 0).comp hhalf

/-- Source: `proof_gap/exercise_505/6.txt`; restrict the square roots to `x≥0`. -/
theorem gap6 (x : ℝ) (hx : 0 ≤ x) :
    |Real.cos ((Real.sqrt (x + 1) + Real.sqrt x) / 2)| ≤ 1 := by
  exact Real.abs_cos_le_one _

/-- Source: `proof_gap/exercise_505/7.txt`. -/
theorem gap7 : HasLimitAtPosInfinity difference 0 := by
  unfold HasLimitAtPosInfinity
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hs :
      ∀ᶠ x : ℝ in Filter.atTop,
        dist (Real.sin (rootDifference x / 2)) 0 < ε / 2 :=
    (Metric.tendsto_nhds.1 gap5) (ε / 2) (by linarith)
  filter_upwards [hs, Filter.eventually_ge_atTop (0 : ℝ)] with x hsx hx
  have hsx' : |Real.sin (rootDifference x / 2)| < ε / 2 := by
    simpa [Real.dist_eq] using hsx
  have hc :
      |Real.cos ((Real.sqrt (x + 1) + Real.sqrt x) / 2)| ≤ 1 :=
    gap6 x hx
  rw [gap1 x hx]
  simp only [Real.dist_eq, sub_zero]
  calc
    |productForm x| =
        2 * |Real.sin (rootDifference x / 2)| *
          |Real.cos ((Real.sqrt (x + 1) + Real.sqrt x) / 2)| := by
      simp [productForm, abs_mul]
    _ ≤ (2 * |Real.sin (rootDifference x / 2)|) * 1 := by
      exact mul_le_mul_of_nonneg_left hc
        (mul_nonneg (by norm_num) (abs_nonneg _))
    _ = 2 * |Real.sin (rootDifference x / 2)| := by
      ring
    _ < ε := by
      linarith

end

end ProofGap.Exercise505
