import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

namespace ProofGap.Exercise3598

noncomputable section

open scoped BigOperators

def f (x y : ℝ) : ℝ :=
  Real.cos x * Real.cosh y

def cosineTerm (x : ℝ) (m : ℕ) : ℝ :=
  (-1 : ℝ) ^ m * x ^ (2 * m) / (Nat.factorial (2 * m) : ℝ)

def coshTerm (y : ℝ) (n : ℕ) : ℝ :=
  y ^ (2 * n) / (Nat.factorial (2 * n) : ℝ)

def doubleTerm (x y : ℝ) (m n : ℕ) : ℝ :=
  (-1 : ℝ) ^ m * (x ^ (2 * m) * y ^ (2 * n)) /
    ((Nat.factorial (2 * m) : ℝ) * (Nat.factorial (2 * n) : ℝ))

private theorem product_terms (x y : ℝ) (m n : ℕ) :
    cosineTerm x m * coshTerm y n = doubleTerm x y m n := by
  simp only [cosineTerm, coshTerm, doubleTerm]
  rw [div_mul_div_comm]
  rw [mul_assoc]

theorem gap1 :
    ∀ y : ℝ, Real.cosh y = (Real.exp y + Real.exp (-y)) / 2 := by
  intro y
  exact Real.cosh_eq y

theorem gap2 :
    ∀ y : ℝ,
      (Real.exp y + Real.exp (-y)) / 2 = ∑' n, coshTerm y n := by
  intro y
  calc
    (Real.exp y + Real.exp (-y)) / 2 = Real.cosh y := (gap1 y).symm
    _ = ∑' n, coshTerm y n := by
      simpa [coshTerm] using (Real.hasSum_cosh y).tsum_eq.symm

theorem gap3 :
    ∀ y : ℝ, Real.cosh y = ∑' n, coshTerm y n := by
  intro y
  simpa [coshTerm] using (Real.hasSum_cosh y).tsum_eq.symm

theorem gap4 :
    ∀ x y : ℝ,
      f x y = (∑' m, cosineTerm x m) * (∑' n, coshTerm y n) := by
  intro x y
  have hx : Real.cos x = ∑' m, cosineTerm x m := by
    simpa [cosineTerm] using (Real.hasSum_cos x).tsum_eq.symm
  calc
    f x y = Real.cos x * Real.cosh y := rfl
    _ = (∑' m, cosineTerm x m) * (∑' n, coshTerm y n) :=
      congrArg₂ (fun a b : ℝ => a * b) hx (gap3 y)

theorem gap5 :
    ∀ x y : ℝ,
      (∑' m, cosineTerm x m) * (∑' n, coshTerm y n) =
        ∑' m, ∑' n, doubleTerm x y m n := by
  intro x y
  have hx : HasSum (cosineTerm x) (Real.cos x) := by
    simpa [cosineTerm] using Real.hasSum_cos x
  have hy : HasSum (coshTerm y) (Real.cosh y) := by
    simpa [coshTerm] using Real.hasSum_cosh y
  have houter :
      HasSum (fun m => cosineTerm x m * Real.cosh y)
        (Real.cos x * Real.cosh y) :=
    hx.mul_right (Real.cosh y)
  calc
    (∑' m, cosineTerm x m) * (∑' n, coshTerm y n) =
        Real.cos x * Real.cosh y := by
      rw [hx.tsum_eq, hy.tsum_eq]
    _ = ∑' m, cosineTerm x m * Real.cosh y := houter.tsum_eq.symm
    _ = ∑' m, ∑' n, cosineTerm x m * coshTerm y n := by
      apply tsum_congr
      intro m
      exact (hy.mul_left (cosineTerm x m)).tsum_eq.symm
    _ = ∑' m, ∑' n, doubleTerm x y m n := by
      apply tsum_congr
      intro m
      apply tsum_congr
      intro n
      exact product_terms x y m n

theorem gap6 :
    ∀ x y : ℝ, f x y = ∑' m, ∑' n, doubleTerm x y m n := by
  intro x y
  exact (gap4 x y).trans (gap5 x y)

end

end ProofGap.Exercise3598
