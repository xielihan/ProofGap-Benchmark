import ProofGapLean.Prelude.Sequences
import ProofGapLean.Prelude.Discrete
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise603

noncomputable section

def f (x : ℝ) : ℝ := x * (Int.floor (1 / x) : ℝ)
def HasLimitAtZero (g : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto g (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds L)

/-- Exercise 603, gap 1; exclude `x=0`. -/
theorem gap1 (x : ℝ) (hx : x ≠ 0) :
    1 / x - 1 < (Int.floor (1 / x) : ℝ) := by
  have h : 1 / x < (Int.floor (1 / x) : ℝ) + 1 :=
    Int.lt_floor_add_one _
  linarith

/-- Exercise 603, gap 2; exclude `x=0`. -/
theorem gap2 (x : ℝ) (hx : x ≠ 0) :
    (Int.floor (1 / x) : ℝ) ≤ 1 / x := by
  exact Int.floor_le _

/-- Exercise 603, gap 3; exclude `x=0`. -/
theorem gap3 (x : ℝ) (hx : x ≠ 0) : 1 / x - 1 < 1 / x := by
  linarith

/-- Exercise 603, gap 4. -/
theorem gap4 (x : ℝ) (hx : 0 < x) : 1 - x < f x := by
  calc
    1 - x = x * (1 / x - 1) := by
      field_simp [ne_of_gt hx]
    _ < x * (Int.floor (1 / x) : ℝ) :=
      mul_lt_mul_of_pos_left (gap1 x (ne_of_gt hx)) hx
    _ = f x := rfl

/-- Exercise 603, gap 5. -/
theorem gap5 (x : ℝ) (hx : 0 < x) : f x ≤ 1 := by
  calc
    f x = x * (Int.floor (1 / x) : ℝ) := rfl
    _ ≤ x * (1 / x) :=
      mul_le_mul_of_nonneg_left (gap2 x (ne_of_gt hx)) hx.le
    _ = 1 := by
      field_simp [ne_of_gt hx]

/-- Exercise 603, gap 6. -/
theorem gap6 (x : ℝ) (hx : 0 < x) : 1 - x < (1 : ℝ) := by
  linarith

/-- Exercise 603, gap 7. -/
theorem gap7 (x : ℝ) (hx : x < 0) : f x < 1 - x := by
  calc
    f x = x * (Int.floor (1 / x) : ℝ) := rfl
    _ < x * (1 / x - 1) :=
      mul_lt_mul_of_neg_left (gap1 x (ne_of_lt hx)) hx
    _ = 1 - x := by
      field_simp [ne_of_lt hx]

/-- Exercise 603, gap 8. -/
theorem gap8 (x : ℝ) (hx : x < 0) : 1 ≤ f x := by
  calc
    1 = x * (1 / x) := by
      field_simp [ne_of_lt hx]
    _ ≤ x * (Int.floor (1 / x) : ℝ) :=
      mul_le_mul_of_nonpos_left (gap2 x (ne_of_lt hx)) hx.le
    _ = f x := rfl

/-- Exercise 603, gap 9. -/
theorem gap9 (x : ℝ) (hx : x < 0) : (1 : ℝ) < 1 - x := by
  linarith

/-- Exercise 603, gap 10. -/
theorem gap10 : HasLimitAtZero f 1 := by
  unfold HasLimitAtZero
  rw [Metric.tendsto_nhds]
  intro ε hε
  have heps_ball : ∀ᶠ x : ℝ in nhds 0, x ∈ Metric.ball 0 ε :=
    Metric.ball_mem_nhds 0 hε
  have heps : ∀ᶠ x : ℝ in nhdsWithin 0 ({0} : Set ℝ)ᶜ, dist x 0 < ε := by
    filter_upwards [heps_ball.filter_mono inf_le_left] with x hx
    simpa [Metric.mem_ball] using hx
  filter_upwards [heps, self_mem_nhdsWithin] with x hdist hxmem
  have hx0 : x ≠ 0 := by
    simpa using hxmem
  rcases lt_or_gt_of_ne hx0 with hxneg | hxpos
  · have hdist' : -x < ε := by
      simpa [Real.dist_eq, abs_of_neg hxneg] using hdist
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (gap8 x hxneg))]
    linarith [gap7 x hxneg]
  · have hdist' : x < ε := by
      simpa [Real.dist_eq, abs_of_pos hxpos] using hdist
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr (gap5 x hxpos))]
    linarith [gap4 x hxpos]

end

end ProofGap.Exercise603
