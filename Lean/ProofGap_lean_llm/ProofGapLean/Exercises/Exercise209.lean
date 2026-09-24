import ProofGapLean.Prelude.Elementary
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise209

noncomputable section

def base (x : ℝ) : ℝ := x / Real.sqrt (1 + x ^ 2)
def iter (n : ℕ) (x : ℝ) : ℝ := (base^[n]) x
def closedForm (n : ℕ) (x : ℝ) : ℝ := x / Real.sqrt (1 + (n : ℝ) * x ^ 2)

private theorem closedForm_step (k : ℕ) (x : ℝ) :
    (x / Real.sqrt (1 + (k : ℝ) * x ^ 2)) /
        Real.sqrt (1 + x ^ 2 / (1 + (k : ℝ) * x ^ 2)) =
      closedForm (k + 1) x := by
  unfold closedForm
  have hA : 0 < 1 + (k : ℝ) * x ^ 2 := by positivity
  have hprod :
      (1 + (k : ℝ) * x ^ 2) *
          (1 + x ^ 2 / (1 + (k : ℝ) * x ^ 2)) =
        1 + ((k + 1 : ℕ) : ℝ) * x ^ 2 := by
    rw [Nat.cast_add, Nat.cast_one]
    field_simp [ne_of_gt hA]
    ring
  rw [div_div, ← Real.sqrt_mul hA.le, hprod]

private theorem iter_eq_closedForm (n : ℕ) (x : ℝ) :
    iter n x = closedForm n x := by
  induction n with
  | zero =>
      simp [iter, closedForm]
  | succ k ih =>
      rw [iter, Function.iterate_succ_apply']
      change base (iter k x) = closedForm (k + 1) x
      rw [ih]
      unfold base closedForm
      have hA : 0 < 1 + (k : ℝ) * x ^ 2 := by positivity
      have hsquare :
          (x / Real.sqrt (1 + (k : ℝ) * x ^ 2)) ^ 2 =
            x ^ 2 / (1 + (k : ℝ) * x ^ 2) := by
        rw [div_pow, Real.sq_sqrt hA.le]
      rw [hsquare]
      exact closedForm_step k x

/-- Source: `proof_gap/exercise_209/1.txt`; make the previously overloaded `f(n,x)` an iterate. -/
theorem gap1 : ∀ x, iter 2 x = closedForm 2 x := by
  intro x
  exact iter_eq_closedForm 2 x

/-- Source: `proof_gap/exercise_209/2.txt`. -/
theorem gap2 : ∀ k x, iter k x = closedForm k x →
    iter (k + 1) x =
      (x / Real.sqrt (1 + (k : ℝ) * x ^ 2)) /
        Real.sqrt (1 + x ^ 2 / (1 + (k : ℝ) * x ^ 2)) := by
  intro k x h
  rw [iter, Function.iterate_succ_apply']
  change base (iter k x) = _
  rw [h]
  unfold base closedForm
  have hA : 0 < 1 + (k : ℝ) * x ^ 2 := by positivity
  have hsquare :
      (x / Real.sqrt (1 + (k : ℝ) * x ^ 2)) ^ 2 =
        x ^ 2 / (1 + (k : ℝ) * x ^ 2) := by
    rw [div_pow, Real.sq_sqrt hA.le]
  rw [hsquare]

/-- Source: `proof_gap/exercise_209/3.txt`. -/
theorem gap3 : ∀ (k : ℕ) (x : ℝ),
    (x / Real.sqrt (1 + (k : ℝ) * x ^ 2)) /
        Real.sqrt (1 + x ^ 2 / (1 + (k : ℝ) * x ^ 2)) =
      closedForm (k + 1) x := by
  exact closedForm_step

/-- Source: `proof_gap/exercise_209/4.txt`. -/
theorem gap4 : ∀ k x, iter k x = closedForm k x →
    iter (k + 1) x = closedForm (k + 1) x := by
  intro k x h
  rw [gap2 k x h, gap3 k x]

/-- Source: `proof_gap/exercise_209/5.txt`. -/
theorem gap5 : ∀ n x, 0 < n → iter n x = closedForm n x := by
  intro n x _
  exact iter_eq_closedForm n x

end

end ProofGap.Exercise209
