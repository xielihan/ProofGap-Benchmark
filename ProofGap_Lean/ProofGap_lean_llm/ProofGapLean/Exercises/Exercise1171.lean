import ProofGapLean.Prelude.Discrete
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1171

noncomputable section

def nthDeriv : ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0, f => f
  | n + 1, f => deriv (nthDeriv n f)

def y (x : ℝ) : ℝ := x ^ 5
def differential (n : ℕ) (f : ℝ → ℝ) (x dx : ℝ) : ℝ :=
  nthDeriv n f x * dx ^ n

private theorem nthDeriv_y_five_value (x : ℝ) : nthDeriv 5 y x = 120 := by
  have hp2 (z : ℝ) : HasDerivAt (fun t : ℝ => t ^ 2) (2 * z) z := by
    simpa [id_eq, pow_two, two_mul] using
      (hasDerivAt_id z).mul (hasDerivAt_id z)
  have hp3 (z : ℝ) : HasDerivAt (fun t : ℝ => t ^ 3) (3 * z ^ 2) z := by
    convert (hp2 z).mul (hasDerivAt_id z) using 1 <;>
      simp [id_eq] <;> ring
  have hp4 (z : ℝ) : HasDerivAt (fun t : ℝ => t ^ 4) (4 * z ^ 3) z := by
    convert (hp3 z).mul (hasDerivAt_id z) using 1 <;>
      simp [id_eq] <;> ring
  have hp5 (z : ℝ) : HasDerivAt (fun t : ℝ => t ^ 5) (5 * z ^ 4) z := by
    convert (hp4 z).mul (hasDerivAt_id z) using 1 <;>
      simp [id_eq] <;> ring
  have h1 : nthDeriv 1 y = fun z : ℝ => 5 * z ^ 4 := by
    funext z
    change deriv y z = 5 * z ^ 4
    simpa [y] using (hp5 z).deriv
  have h2 : nthDeriv 2 y = fun z : ℝ => 20 * z ^ 3 := by
    funext z
    change deriv (nthDeriv 1 y) z = 20 * z ^ 3
    rw [h1]
    convert ((hp4 z).const_mul (5 : ℝ)).deriv using 1 <;>
      norm_num <;> ring
  have h3 : nthDeriv 3 y = fun z : ℝ => 60 * z ^ 2 := by
    funext z
    change deriv (nthDeriv 2 y) z = 60 * z ^ 2
    rw [h2]
    convert ((hp3 z).const_mul (20 : ℝ)).deriv using 1 <;>
      norm_num <;> ring
  have h4 : nthDeriv 4 y = fun z : ℝ => 120 * z := by
    funext z
    change deriv (nthDeriv 3 y) z = 120 * z
    rw [h3]
    convert ((hp2 z).const_mul (60 : ℝ)).deriv using 1 <;>
      norm_num <;> ring
  change deriv (nthDeriv 4 y) x = 120
  rw [h4]
  convert ((hasDerivAt_id x).const_mul (120 : ℝ)).deriv using 1 <;>
    norm_num

theorem gap1 (x dx : ℝ) :
    differential 5 y x dx =
      ((Nat.factorial 5 : ℕ) : ℝ) * dx ^ 5 := by
  unfold differential
  rw [nthDeriv_y_five_value]
  norm_num [Nat.factorial]

theorem gap2 (x dx : ℝ) :
    ((Nat.factorial 5 : ℕ) : ℝ) * dx ^ 5 =
      120 * dx ^ 5 := by
  norm_num [Nat.factorial]

theorem gap3 (x dx : ℝ) :
    differential 5 y x dx = 120 * dx ^ 5 := by
  unfold differential
  rw [nthDeriv_y_five_value]

end

end ProofGap.Exercise1171
