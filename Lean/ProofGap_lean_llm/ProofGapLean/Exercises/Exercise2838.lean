import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

namespace ProofGap.Exercise2838

noncomputable section

def f (x : ℝ) : ℝ := x ^ 3

private theorem deriv_f_eq :
    deriv f = fun x : ℝ => 3 * x ^ 2 := by
  funext x
  change deriv (fun y : ℝ => y ^ 3) x = 3 * x ^ 2
  have hx : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
  have hsq :
      HasDerivAt (fun y : ℝ => y * y) (1 * x + x * 1) x :=
    hx.mul hx
  have hcub :
      HasDerivAt (fun y : ℝ => (y * y) * y)
        ((1 * x + x * 1) * x + (x * x) * 1) x :=
    hsq.mul hx
  have hf :
      HasDerivAt (fun y : ℝ => y ^ 3)
        ((1 * x + x * 1) * x + (x * x) * 1) x := by
    simpa only [pow_three, mul_assoc] using hcub
  calc
    deriv (fun y : ℝ => y ^ 3) x =
        (1 * x + x * 1) * x + (x * x) * 1 := hf.deriv
    _ = 3 * x ^ 2 := by ring

private theorem deriv_three_sq_eq :
    deriv (fun x : ℝ => 3 * x ^ 2) = fun x : ℝ => 6 * x := by
  funext x
  have hx : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
  have hsq :
      HasDerivAt (fun y : ℝ => y * y) (1 * x + x * 1) x :=
    hx.mul hx
  have hscaled :
      HasDerivAt (fun y : ℝ => 3 * (y * y))
        (3 * (1 * x + x * 1)) x :=
    hsq.const_mul (3 : ℝ)
  have h :
      HasDerivAt (fun y : ℝ => 3 * y ^ 2)
        (3 * (1 * x + x * 1)) x := by
    simpa only [pow_two] using hscaled
  calc
    deriv (fun y : ℝ => 3 * y ^ 2) x = 3 * (1 * x + x * 1) := h.deriv
    _ = 6 * x := by ring

private theorem deriv_six_mul_eq :
    deriv (fun x : ℝ => 6 * x) = fun _ : ℝ => 6 := by
  funext x
  convert ((hasDerivAt_id x).const_mul (6 : ℝ)).deriv using 1 <;> ring

private theorem deriv_const_six_eq :
    deriv (fun _ : ℝ => (6 : ℝ)) = fun _ : ℝ => (0 : ℝ) := by
  funext x
  exact (hasDerivAt_const (x : ℝ) (6 : ℝ)).deriv

private theorem deriv_zero_fun_eq :
    deriv (fun _ : ℝ => (0 : ℝ)) = fun _ : ℝ => (0 : ℝ) := by
  funext x
  exact (hasDerivAt_const (x : ℝ) (0 : ℝ)).deriv

private theorem iteratedDeriv_one_f_eq :
    iteratedDeriv 1 f = fun x : ℝ => 3 * x ^ 2 := by
  funext x
  norm_num [iteratedDeriv, deriv_f_eq]

private theorem iteratedDeriv_two_f_eq :
    iteratedDeriv 2 f = fun x : ℝ => 6 * x := by
  funext x
  rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
    iteratedDeriv_one_f_eq, deriv_three_sq_eq]

private theorem iteratedDeriv_three_f_eq :
    iteratedDeriv 3 f = fun _ : ℝ => 6 := by
  funext x
  rw [show (3 : ℕ) = 2 + 1 by norm_num, iteratedDeriv_succ,
    iteratedDeriv_two_f_eq, deriv_six_mul_eq]

private theorem iteratedDeriv_four_f_eq :
    iteratedDeriv 4 f = fun _ : ℝ => 0 := by
  funext x
  rw [show (4 : ℕ) = 3 + 1 by norm_num, iteratedDeriv_succ,
    iteratedDeriv_three_f_eq, deriv_const_six_eq]

private theorem iteratedDeriv_five_f_eq :
    iteratedDeriv 5 f = fun _ : ℝ => 0 := by
  funext x
  rw [show (5 : ℕ) = 4 + 1 by norm_num, iteratedDeriv_succ,
    iteratedDeriv_four_f_eq, deriv_zero_fun_eq]

theorem gap1 :
    ∀ x : ℝ, f x = (x + 1 - 1) ^ 3 := by
  intro x
  simp [f]

theorem gap2 :
    ∀ x : ℝ,
      (x + 1 - 1) ^ 3 =
        (x + 1) ^ 3 - 3 * (x + 1) ^ 2 + 3 * (x + 1) - 1 := by
  intro x
  ring

theorem gap3 :
    ∀ x : ℝ,
      f x = (x + 1) ^ 3 - 3 * (x + 1) ^ 2 + 3 * (x + 1) - 1 := by
  intro x
  calc
    f x = (x + 1 - 1) ^ 3 := gap1 x
    _ = (x + 1) ^ 3 - 3 * (x + 1) ^ 2 + 3 * (x + 1) - 1 := gap2 x

theorem gap4 :
    f (-1) = -1 := by
  norm_num [f]

theorem gap5 :
    iteratedDeriv 1 f (-1) = 3 := by
  norm_num [iteratedDeriv, deriv_f_eq]

theorem gap6 :
    iteratedDeriv 2 f (-1) = -6 := by
  rw [iteratedDeriv_two_f_eq]
  norm_num

theorem gap7 :
    iteratedDeriv 3 f (-1) = 6 := by
  exact congrFun iteratedDeriv_three_f_eq (-1)

theorem gap8 :
    iteratedDeriv 4 f (-1) = iteratedDeriv 5 f (-1) := by
  calc
    iteratedDeriv 4 f (-1) = 0 := congrFun iteratedDeriv_four_f_eq (-1)
    _ = iteratedDeriv 5 f (-1) := (congrFun iteratedDeriv_five_f_eq (-1)).symm

theorem gap9 :
    iteratedDeriv 5 f (-1) = 0 := by
  exact congrFun iteratedDeriv_five_f_eq (-1)

theorem gap10 :
    (0 : ℝ) = 0 := by
  rfl

theorem gap11 :
    iteratedDeriv 4 f (-1) = 0 := by
  rw [gap8, gap9]

theorem gap12 :
    ∀ x : ℝ,
      f x =
        -1 + 3 * (x + 1) - (6 / 2) * (x + 1) ^ 2 +
          (6 / 6) * (x + 1) ^ 3 := by
  intro x
  norm_num [f] <;> ring

theorem gap13 :
    ∀ x : ℝ,
      -1 + 3 * (x + 1) - (6 / 2) * (x + 1) ^ 2 +
          (6 / 6) * (x + 1) ^ 3 =
        -1 + 3 * (x + 1) - 3 * (x + 1) ^ 2 + (x + 1) ^ 3 := by
  intro x
  norm_num

theorem gap14 :
    ∀ x : ℝ,
      f x = -1 + 3 * (x + 1) - 3 * (x + 1) ^ 2 + (x + 1) ^ 3 := by
  intro x
  calc
    f x =
        -1 + 3 * (x + 1) - (6 / 2) * (x + 1) ^ 2 +
          (6 / 6) * (x + 1) ^ 3 := gap12 x
    _ = -1 + 3 * (x + 1) - 3 * (x + 1) ^ 2 + (x + 1) ^ 3 := gap13 x

end

end ProofGap.Exercise2838
