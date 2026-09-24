import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

namespace ProofGap.Exercise2914

noncomputable section

open scoped BigOperators

def seriesTerm (x : ℝ) (n : ℕ) : ℝ :=
  x ^ (4 * n) / (Nat.factorial (4 * n) : ℝ)

def firstDerivativeTerm (x : ℝ) (n : ℕ) : ℝ :=
  x ^ (4 * n + 3) / (Nat.factorial (4 * n + 3) : ℝ)

def secondDerivativeTerm (x : ℝ) (n : ℕ) : ℝ :=
  x ^ (4 * n + 2) / (Nat.factorial (4 * n + 2) : ℝ)

def thirdDerivativeTerm (x : ℝ) (n : ℕ) : ℝ :=
  x ^ (4 * n + 1) / (Nat.factorial (4 * n + 1) : ℝ)

def fourthDerivativeTerm (x : ℝ) (n : ℕ) : ℝ :=
  x ^ (4 * n) / (Nat.factorial (4 * n) : ℝ)

def y (x : ℝ) : ℝ :=
  ∑' n, seriesTerm x n

private theorem analyticFacts :
    (∀ x : ℝ,
      (∑' n, seriesTerm x n) = (Real.cosh x + Real.cos x) / 2 ∧
      (∑' n, firstDerivativeTerm x n) = (Real.sinh x - Real.sin x) / 2 ∧
      (∑' n, secondDerivativeTerm x n) = (Real.cosh x - Real.cos x) / 2 ∧
      (∑' n, thirdDerivativeTerm x n) = (Real.sinh x + Real.sin x) / 2) ∧
    deriv (fun x : ℝ => (Real.cosh x + Real.cos x) / 2) =
      (fun x : ℝ => (Real.sinh x - Real.sin x) / 2) ∧
    deriv (fun x : ℝ => (Real.sinh x - Real.sin x) / 2) =
      (fun x : ℝ => (Real.cosh x - Real.cos x) / 2) ∧
    deriv (fun x : ℝ => (Real.cosh x - Real.cos x) / 2) =
      (fun x : ℝ => (Real.sinh x + Real.sin x) / 2) ∧
    deriv (fun x : ℝ => (Real.sinh x + Real.sin x) / 2) =
      (fun x : ℝ => (Real.cosh x + Real.cos x) / 2) := by
  constructor
  · intro x
    have hcosh := (Real.hasSum_cosh x).tsum_eq
    have hcos := (Real.hasSum_cos x).tsum_eq
    have hsinh := (Real.hasSum_sinh x).tsum_eq
    have hsin := (Real.hasSum_sin x).tsum_eq
    have hcoshEven : Summable (fun k : ℕ =>
        x ^ (2 * (2 * k)) /
          (Nat.factorial (2 * (2 * k)) : ℝ)) :=
      (Real.hasSum_cosh x).summable.comp_injective (by
        intro a b hab
        omega)
    have hcoshOdd : Summable (fun k : ℕ =>
        x ^ (2 * (2 * k + 1)) /
          (Nat.factorial (2 * (2 * k + 1)) : ℝ)) :=
      (Real.hasSum_cosh x).summable.comp_injective (by
        intro a b hab
        change 2 * a + 1 = 2 * b + 1 at hab
        omega)
    have hcosEven : Summable (fun k : ℕ =>
        (-1) ^ (2 * k) * x ^ (2 * (2 * k)) /
          (Nat.factorial (2 * (2 * k)) : ℝ)) :=
      (Real.hasSum_cos x).summable.comp_injective (by
        intro a b hab
        omega)
    have hcosOdd : Summable (fun k : ℕ =>
        (-1) ^ (2 * k + 1) * x ^ (2 * (2 * k + 1)) /
          (Nat.factorial (2 * (2 * k + 1)) : ℝ)) :=
      (Real.hasSum_cos x).summable.comp_injective (by
        intro a b hab
        change 2 * a + 1 = 2 * b + 1 at hab
        omega)
    have hsinhEven : Summable (fun k : ℕ =>
        x ^ (2 * (2 * k) + 1) /
          (Nat.factorial (2 * (2 * k) + 1) : ℝ)) :=
      (Real.hasSum_sinh x).summable.comp_injective (by
        intro a b hab
        omega)
    have hsinhOdd : Summable (fun k : ℕ =>
        x ^ (2 * (2 * k + 1) + 1) /
          (Nat.factorial (2 * (2 * k + 1) + 1) : ℝ)) :=
      (Real.hasSum_sinh x).summable.comp_injective (by
        intro a b hab
        change 2 * a + 1 = 2 * b + 1 at hab
        omega)
    have hsinEven : Summable (fun k : ℕ =>
        (-1) ^ (2 * k) * x ^ (2 * (2 * k) + 1) /
          (Nat.factorial (2 * (2 * k) + 1) : ℝ)) :=
      (Real.hasSum_sin x).summable.comp_injective (by
        intro a b hab
        omega)
    have hsinOdd : Summable (fun k : ℕ =>
        (-1) ^ (2 * k + 1) * x ^ (2 * (2 * k + 1) + 1) /
          (Nat.factorial (2 * (2 * k + 1) + 1) : ℝ)) :=
      (Real.hasSum_sin x).summable.comp_injective (by
        intro a b hab
        change 2 * a + 1 = 2 * b + 1 at hab
        omega)
    rw [← tsum_even_add_odd] at hcosh hcos hsinh hsin <;> try assumption
    simp [pow_mul, pow_succ, mul_add, ← mul_assoc] at hcosh hcos hsinh hsin
    simp only [neg_div, tsum_neg] at hcos hsin
    have h0 :
        (∑' k : ℕ, (x * x * x * x) ^ k /
          (Nat.factorial (4 * k) : ℝ)) =
          (Real.cosh x + Real.cos x) / 2 := by
      linarith [hcosh, hcos]
    have h3 :
        (∑' k : ℕ, (x * x * x * x) ^ k * x * x * x /
          (Nat.factorial (4 * k + 2 + 1) : ℝ)) =
          (Real.sinh x - Real.sin x) / 2 := by
      linarith [hsinh, hsin]
    have h2 :
        (∑' k : ℕ, (x * x * x * x) ^ k * x * x /
          (Nat.factorial (4 * k + 2) : ℝ)) =
          (Real.cosh x - Real.cos x) / 2 := by
      linarith [hcosh, hcos]
    have h1 :
        (∑' k : ℕ, (x * x * x * x) ^ k * x /
          (Nat.factorial (4 * k + 1) : ℝ)) =
          (Real.sinh x + Real.sin x) / 2 := by
      linarith [hsinh, hsin]
    constructor
    · simpa [seriesTerm, pow_mul, pow_succ, mul_add, ← mul_assoc] using h0
    constructor
    · simpa [firstDerivativeTerm, pow_mul, pow_succ, mul_add, ← mul_assoc] using h3
    constructor
    · simpa [secondDerivativeTerm, pow_mul, pow_succ, mul_add, ← mul_assoc] using h2
    · simpa [thirdDerivativeTerm, pow_mul, pow_succ, mul_add, ← mul_assoc] using h1
  constructor
  · funext x
    convert (((Real.hasDerivAt_cosh x).add
      (Real.hasDerivAt_cos x)).div_const 2).deriv using 1 <;> ring
  constructor
  · funext x
    convert (((Real.hasDerivAt_sinh x).sub
      (Real.hasDerivAt_sin x)).div_const 2).deriv using 1 <;> ring
  constructor
  · funext x
    convert (((Real.hasDerivAt_cosh x).sub
      (Real.hasDerivAt_cos x)).div_const 2).deriv using 1 <;> ring
  · funext x
    convert (((Real.hasDerivAt_sinh x).add
      (Real.hasDerivAt_sin x)).div_const 2).deriv using 1 <;> ring

theorem gap1 :
    {x : ℝ | Summable (fun n => seriesTerm x n)} = Set.univ := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
  have h : Summable (fun n : ℕ =>
      x ^ (2 * (2 * n)) / (Nat.factorial (2 * (2 * n)) : ℝ)) :=
    (Real.hasSum_cosh x).summable.comp_injective (by
      intro a b hab
      omega)
  simpa [seriesTerm, ← mul_assoc] using h

theorem gap2 :
    ∀ x : ℝ, iteratedDeriv 1 y x =
      ∑' n, firstDerivativeTerm x n := by
  intro x
  simp only [iteratedDeriv_succ, iteratedDeriv_zero]
  have hy : y = fun t : ℝ => (Real.cosh t + Real.cos t) / 2 := by
    funext t
    simpa [y] using (analyticFacts.1 t).1
  rw [hy, analyticFacts.2.1, (analyticFacts.1 x).2.1]

theorem gap3 :
    ∀ x : ℝ, iteratedDeriv 2 y x =
      ∑' n, secondDerivativeTerm x n := by
  intro x
  simp only [iteratedDeriv_succ, iteratedDeriv_zero]
  have hy : y = fun t : ℝ => (Real.cosh t + Real.cos t) / 2 := by
    funext t
    simpa [y] using (analyticFacts.1 t).1
  rw [hy, analyticFacts.2.1, analyticFacts.2.2.1,
    (analyticFacts.1 x).2.2.1]

theorem gap4 :
    ∀ x : ℝ, iteratedDeriv 3 y x =
      ∑' n, thirdDerivativeTerm x n := by
  intro x
  simp only [iteratedDeriv_succ, iteratedDeriv_zero]
  have hy : y = fun t : ℝ => (Real.cosh t + Real.cos t) / 2 := by
    funext t
    simpa [y] using (analyticFacts.1 t).1
  rw [hy, analyticFacts.2.1, analyticFacts.2.2.1,
    analyticFacts.2.2.2.1, (analyticFacts.1 x).2.2.2]

theorem gap5 :
    ∀ x : ℝ, iteratedDeriv 4 y x =
      ∑' n, fourthDerivativeTerm x n := by
  intro x
  simp only [iteratedDeriv_succ, iteratedDeriv_zero]
  have hy : y = fun t : ℝ => (Real.cosh t + Real.cos t) / 2 := by
    funext t
    simpa [y] using (analyticFacts.1 t).1
  rw [hy, analyticFacts.2.1, analyticFacts.2.2.1,
    analyticFacts.2.2.2.1, analyticFacts.2.2.2.2]
  simpa [fourthDerivativeTerm, seriesTerm] using (analyticFacts.1 x).1.symm

theorem gap6 :
    ∀ x : ℝ, iteratedDeriv 4 y x =
      ∑' n, seriesTerm x n := by
  intro x
  simpa [fourthDerivativeTerm, seriesTerm] using gap5 x

theorem gap7 :
    ∀ x : ℝ, (∑' n, seriesTerm x n) = y x := by
  intro x
  rfl

theorem gap8 :
    ∀ x : ℝ, iteratedDeriv 4 y x = y x := by
  intro x
  exact (gap6 x).trans (gap7 x)

theorem gap9 :
    ∀ x : ℝ, iteratedDeriv 4 y x = y x := by
  exact gap8

end

end ProofGap.Exercise2914
