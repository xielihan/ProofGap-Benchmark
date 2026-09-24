import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise532

noncomputable section

def difference (x : ℝ) : ℝ := Real.sin (Real.log (x + 1)) - Real.sin (Real.log x)
def productForm (x : ℝ) : ℝ :=
  2 * Real.cos ((Real.log (x + 1) + Real.log x) / 2) *
    Real.sin ((Real.log (x + 1) - Real.log x) / 2)
def logDifference (x : ℝ) : ℝ := Real.log (x + 1) - Real.log x
def normalizedLog (x : ℝ) : ℝ := Real.log (1 + 1 / x)
def HasLimitAtPosInfinity (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f Filter.atTop (nhds L)

/-- Exercise 532, gap 1; restrict logarithms to `x>0`. -/
private theorem cosineFactor_abs_le_one (x : ℝ) :
    |Real.cos ((Real.log (x + 1) + Real.log x) / 2)| ≤ 1 := by
  apply abs_le.mpr
  exact ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩

theorem gap1 (x : ℝ) (hx : 0 < x) : difference x = productForm x := by
  unfold difference productForm
  let a : ℝ := Real.log (x + 1)
  let b : ℝ := Real.log x
  let u : ℝ := (a + b) / 2
  let v : ℝ := (a - b) / 2
  change Real.sin a - Real.sin b = 2 * Real.cos u * Real.sin v
  have ha : Real.sin a = Real.sin (u + v) := by
    apply congrArg Real.sin
    dsimp [u, v]
    ring
  have hb : Real.sin b = Real.sin (u - v) := by
    apply congrArg Real.sin
    dsimp [u, v]
    ring
  rw [ha, hb, Real.sin_add, Real.sin_sub]
  ring

/-- Exercise 532, gap 2; restrict logarithms to `x>0`. -/
theorem gap2 (x : ℝ) (hx : 0 < x) : logDifference x = normalizedLog x := by
  unfold logDifference normalizedLog
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hx1 : x + 1 ≠ 0 := by linarith
  calc
    Real.log (x + 1) - Real.log x = Real.log ((x + 1) / x) :=
      (Real.log_div hx1 hx0).symm
    _ = Real.log (1 + 1 / x) := by
      apply congrArg Real.log
      field_simp [hx0]

/-- Exercise 532, gap 3. -/
theorem gap3 : HasLimitAtPosInfinity normalizedLog 0 := by
  unfold HasLimitAtPosInfinity normalizedLog
  have hinv :
      Filter.Tendsto (fun x : ℝ => x⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  have hinner :
      Filter.Tendsto (fun x : ℝ => 1 + 1 / x) Filter.atTop (nhds 1) := by
    simpa [one_div] using tendsto_const_nhds.add hinv
  simpa using
    ((Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hinner)

/-- Exercise 532, gap 4. -/
theorem gap4 : HasLimitAtPosInfinity logDifference 0 := by
  unfold HasLimitAtPosInfinity
  apply gap3.congr'
  refine Filter.eventually_atTop.2 ?_
  refine ⟨1, ?_⟩
  intro x hx
  exact (gap2 x (lt_of_lt_of_le zero_lt_one hx)).symm

/-- Exercise 532, gap 5. -/
theorem gap5 :
    HasLimitAtPosInfinity (fun x => Real.sin (logDifference x / 2)) 0 := by
  unfold HasLimitAtPosInfinity
  simpa using
    (Real.continuous_sin.continuousAt.tendsto.comp
      (gap4.div_const (2 : ℝ)))

/-- Exercise 532, gap 6; express boundedness explicitly. -/
theorem gap6 :
    ∃ M : ℝ, ∀ x : ℝ,
      |Real.cos ((Real.log (x + 1) + Real.log x) / 2)| ≤ M := by
  refine ⟨1, ?_⟩
  intro x
  exact cosineFactor_abs_le_one x

/-- Exercise 532, gap 7. -/
theorem gap7 : HasLimitAtPosInfinity difference 0 := by
  unfold HasLimitAtPosInfinity
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ :=
    (Metric.tendsto_atTop.1 gap5) (ε / 2) (by linarith)
  refine ⟨max N 1, ?_⟩
  intro x hx
  have hxN : N ≤ x := le_trans (le_max_left N 1) hx
  have hx1 : 1 ≤ x := le_trans (le_max_right N 1) hx
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have hs : |Real.sin (logDifference x / 2)| < ε / 2 := by
    simpa [Real.dist_eq] using hN x hxN
  rw [Real.dist_eq, sub_zero, gap1 x hxpos]
  unfold productForm
  rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have hc2 :
      2 * |Real.cos ((Real.log (x + 1) + Real.log x) / 2)| ≤ 2 := by
    linarith [cosineFactor_abs_le_one x]
  have hprod :
      2 * |Real.cos ((Real.log (x + 1) + Real.log x) / 2)| *
          |Real.sin ((Real.log (x + 1) - Real.log x) / 2)| ≤
        2 * |Real.sin ((Real.log (x + 1) - Real.log x) / 2)| :=
    mul_le_mul_of_nonneg_right hc2 (abs_nonneg _)
  have hs' :
      |Real.sin ((Real.log (x + 1) - Real.log x) / 2)| < ε / 2 := by
    exact hs
  exact lt_of_le_of_lt hprod (by linarith)

end

end ProofGap.Exercise532
