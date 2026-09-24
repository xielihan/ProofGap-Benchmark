import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace ProofGap.Exercise2842

noncomputable section

def evenExpTerm (x : ℝ) (n : ℕ) : ℝ :=
  x ^ (2 * n) / (Nat.factorial (2 * n) : ℝ)

theorem gap1 (f : ℝ → ℝ) (hf : ∀ x, f x = Real.cosh x) :
    ∀ x, f x = (Real.exp x + Real.exp (-x)) / 2 := by
  intro x
  rw [hf x]
  exact Real.cosh_eq x

theorem gap2
    (f : ℝ → ℝ)
    (hf : ∀ x, f x = Real.cosh x)
    (hexp : ∀ x, f x = (Real.exp x + Real.exp (-x)) / 2) :
    ∀ x, (Real.exp x + Real.exp (-x)) / 2 = ∑' n, evenExpTerm x n := by
  intro x
  rw [← Real.cosh_eq x]
  simpa [evenExpTerm] using Real.cosh_eq_tsum x

theorem gap3
    (f : ℝ → ℝ)
    (hf : ∀ x, f x = Real.cosh x)
    (hexp : ∀ x, f x = (Real.exp x + Real.exp (-x)) / 2)
    (hseries :
      ∀ x, (Real.exp x + Real.exp (-x)) / 2 = ∑' n, evenExpTerm x n) :
    ∀ x, f x = ∑' n, evenExpTerm x n := by
  intro x
  calc
    f x = (Real.exp x + Real.exp (-x)) / 2 := hexp x
    _ = ∑' n, evenExpTerm x n := hseries x

theorem gap4
    (f : ℝ → ℝ)
    (hf : ∀ x, f x = Real.cosh x)
    (hexp : ∀ x, f x = (Real.exp x + Real.exp (-x)) / 2)
    (hseries :
      ∀ x, (Real.exp x + Real.exp (-x)) / 2 = ∑' n, evenExpTerm x n)
    (hfseries : ∀ x, f x = ∑' n, evenExpTerm x n) :
    ∀ x, Summable (evenExpTerm x) := by
  intro x
  simpa [evenExpTerm] using (Real.hasSum_cosh x).summable

end

end ProofGap.Exercise2842
