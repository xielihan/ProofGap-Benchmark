import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise1459

noncomputable section

def f (x : ℝ) : ℝ := x ^ 2
def g (x : ℝ) : ℝ := x ^ 3
def difference (x : ℝ) : ℝ := f x - g x

def IsMaximizerOn (u : ℝ → ℝ) (s : Set ℝ) (x₀ : ℝ) : Prop :=
  x₀ ∈ s ∧ ∀ x ∈ s, u x ≤ u x₀

def uniformDifference : ℝ :=
  sSup {y : ℝ | ∃ x ∈ Set.Icc (0 : ℝ) 1, y = |difference x|}

private theorem deriv_f_formula (x : ℝ) : deriv f x = 2 * x := by
  unfold f
  convert ((hasDerivAt_id x).pow 2).deriv using 1 <;>
    norm_num <;> ring

private theorem deriv_g_formula (x : ℝ) : deriv g x = 3 * x ^ 2 := by
  unfold g
  convert ((hasDerivAt_id x).pow 3).deriv using 1 <;>
    norm_num <;> ring

theorem gap1 (x : ℝ) :
    difference x = x ^ 2 - x ^ 3 := by
  rfl

theorem gap2 (x : ℝ) :
    deriv f x - deriv g x = 2 * x - 3 * x ^ 2 := by
  rw [deriv_f_formula, deriv_g_formula]

theorem gap3 (x : ℝ) (hzero : deriv f x - deriv g x = 0) :
    x = 0 ∨ x = (2 / 3 : ℝ) := by
  rw [gap2 x] at hzero
  have hfactor : x * (2 - 3 * x) = 0 := by
    nlinarith [hzero]
  rcases mul_eq_zero.mp hfactor with hx | hx
  · exact Or.inl hx
  · right
    linarith

theorem gap4 (x : ℝ) :
    deriv (deriv f) x - deriv (deriv g) x = 2 - 6 * x := by
  have hf : deriv f = fun y : ℝ => 2 * y := funext deriv_f_formula
  have hg : deriv g = fun y : ℝ => 3 * y ^ 2 := funext deriv_g_formula
  rw [hf, hg]
  have hdf : deriv (fun y : ℝ => 2 * y) x = 2 := by
    have hfun : (fun y : ℝ => 2 * y) = id + id := by
      funext y
      change 2 * y = y + y
      ring
    rw [hfun]
    convert ((hasDerivAt_id x).add (hasDerivAt_id x)).deriv using 1 <;>
      norm_num
  have hdg : deriv (fun y : ℝ => 3 * y ^ 2) x = 6 * x := by
    have hp := (hasDerivAt_id x).pow 2
    have hfun : (fun y : ℝ => 3 * y ^ 2) = (id ^ 2 + id ^ 2) + id ^ 2 := by
      funext y
      change 3 * y ^ 2 = (y ^ 2 + y ^ 2) + y ^ 2
      ring
    rw [hfun]
    convert ((hp.add hp).add hp).deriv using 1 <;>
      norm_num <;> ring
  rw [hdf, hdg]

theorem gap5 :
    deriv (deriv f) (2 / 3 : ℝ) - deriv (deriv g) (2 / 3 : ℝ) = 2 - 4 := by
  rw [gap4]
  norm_num

theorem gap6 :
    (2 : ℝ) - 4 = -2 := by
  norm_num

theorem gap7 :
    (-2 : ℝ) < 0 := by
  norm_num

theorem gap8 :
    deriv (deriv f) (2 / 3 : ℝ) - deriv (deriv g) (2 / 3 : ℝ) < 0 := by
  rw [gap5, gap6]
  exact gap7

theorem gap9 :
    IsMaximizerOn difference (Set.Icc 0 1) (2 / 3 : ℝ) := by
  constructor
  · constructor <;> norm_num
  · intro x hx
    have hlinear : 0 ≤ 3 * x + 1 := by
      nlinarith [hx.1]
    have hfactor : 0 ≤ (3 * x - 2) ^ 2 * (3 * x + 1) :=
      mul_nonneg (sq_nonneg (3 * x - 2)) hlinear
    rw [gap1 x, gap1 (2 / 3 : ℝ)]
    nlinarith [hfactor]

theorem gap10 (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ difference x := by
  rw [gap1]
  have hone : 0 ≤ 1 - x := by
    linarith [hx.2]
  have hproduct : 0 ≤ x ^ 2 * (1 - x) :=
    mul_nonneg (sq_nonneg x) hone
  nlinarith [hproduct]

theorem gap11 :
    uniformDifference = difference (2 / 3 : ℝ) := by
  unfold uniformDifference
  apply le_antisymm
  · apply csSup_le
    · refine ⟨|difference (2 / 3 : ℝ)|, ?_⟩
      exact ⟨2 / 3, (gap9).1, rfl⟩
    · intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      rw [abs_of_nonneg (gap10 x hx)]
      exact (gap9).2 x hx
  · apply le_csSup
    · refine ⟨difference (2 / 3 : ℝ), ?_⟩
      intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      rw [abs_of_nonneg (gap10 x hx)]
      exact (gap9).2 x hx
    · refine ⟨2 / 3, (gap9).1, ?_⟩
      exact (abs_of_nonneg (gap10 (2 / 3 : ℝ) (gap9).1)).symm

theorem gap12 :
    difference (2 / 3 : ℝ) = (4 / 27 : ℝ) := by
  norm_num [difference, f, g]

theorem gap13 :
    uniformDifference = (4 / 27 : ℝ) := by
  exact gap11.trans gap12

end

end ProofGap.Exercise1459
