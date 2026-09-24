import ProofGapLean.Prelude.Analysis

namespace ProofGap.Exercise659

def monomial (n : ℕ) (x : ℝ) : ℝ := x ^ n

/-- Source: `proof_gap/exercise_659/1.txt`; add `n≥1` before using `n-1`. -/
theorem gap1 (x : ℝ) (n : ℕ) (hn : 1 ≤ n) (hx : x ≠ 0) :
    monomial n x / monomial (n - 1) x = x := by
  cases n with
  | zero => simp at hn
  | succ n => simp [monomial, pow_succ, hx]

/-- Source: `proof_gap/exercise_659/2.txt`; express `+∞` by `Tendsto ... atTop`. -/
theorem gap2 (n : ℕ) (hn : 1 ≤ n) :
    Filter.Tendsto (fun x : ℝ => monomial n x / monomial (n - 1) x)
      Filter.atTop Filter.atTop := by
  refine Filter.tendsto_id.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
  exact (gap1 x n hn (ne_of_gt hx)).symm

/-- Source: `proof_gap/exercise_659/3.txt`. -/
theorem gap3 (n : ℕ) (hn : 1 ≤ n) :
    Filter.Tendsto (fun x : ℝ => Real.exp x / x ^ n)
      Filter.atTop Filter.atTop := by
  simpa using Real.tendsto_exp_div_pow_atTop n

/-- Source: `proof_gap/exercise_659/4.txt`. -/
theorem gap4 :
    (∀ n ≥ 1, Filter.Tendsto
      (fun x : ℝ => monomial n x / monomial (n - 1) x)
      Filter.atTop Filter.atTop) ∧
    (∀ n ≥ 1, Filter.Tendsto
      (fun x : ℝ => Real.exp x / x ^ n)
      Filter.atTop Filter.atTop) := by
  exact ⟨(fun n hn => gap2 n hn), (fun n hn => gap3 n hn)⟩

end ProofGap.Exercise659
