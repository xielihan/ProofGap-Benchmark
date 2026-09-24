import ProofGapLean.Prelude.Analysis

namespace ProofGap.Exercise3065_2

noncomputable section

open Filter
open scoped BigOperators Topology

def partialProduct (p : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.Icc 1 n, p i

def HasProduct (p : ℕ → ℝ) (P : ℝ) : Prop :=
  Tendsto (partialProduct p) atTop (𝓝 P)

def ConvergentProduct (p : ℕ → ℝ) : Prop :=
  ∃ P : ℝ, HasProduct p P

def squarePartialProduct (p : ℕ → ℝ) (n : ℕ) : ℝ :=
  partialProduct (fun i => (p i) ^ 2) n

/-- Exercise 3065_2, gap 1; replace both ellipses by exact products. -/
theorem gap1 (p : ℕ → ℝ) (Q : ℕ → ℝ)
    (hQ : ∀ n, Q n = squarePartialProduct p n) :
    ∀ n, Q n = (partialProduct p n) ^ 2 := by
  intro n
  rw [hQ n]
  simp only [squarePartialProduct, partialProduct, Finset.prod_pow]

/-- Exercise 3065_2, gap 2. -/
theorem gap2 (p : ℕ → ℝ) (P : ℝ) (hP : HasProduct p P)
    (hP0 : P ≠ 0) (Q : ℕ → ℝ)
    (hQ : ∀ n, Q n = squarePartialProduct p n) :
    Tendsto Q atTop (𝓝 (P ^ 2)) := by
  unfold HasProduct at hP
  have hQ' : Q = fun n => (partialProduct p n) ^ 2 := by
    funext n
    exact gap1 p Q hQ n
  rw [hQ']
  simpa [pow_two] using hP.mul hP

/-- Exercise 3065_2, gap 3. -/
theorem gap3 (p : ℕ → ℝ) (P : ℝ) (hP : HasProduct p P)
    (hP0 : P ≠ 0) :
    ConvergentProduct (fun n => (p n) ^ 2) := by
  refine ⟨P ^ 2, ?_⟩
  exact gap2 p P hP hP0
    (partialProduct (fun n => (p n) ^ 2)) (fun n => rfl)

/-- Exercise 3065_2, gap 4. -/
theorem gap4 (p : ℕ → ℝ) (P : ℝ) (hP : HasProduct p P)
    (hP0 : P ≠ 0) :
    HasProduct (fun n => (p n) ^ 2) (P ^ 2) := by
  exact gap2 p P hP hP0
    (partialProduct (fun n => (p n) ^ 2)) (fun n => rfl)

/-- Exercise 3065_2, gap 5. -/
theorem gap5 (p : ℕ → ℝ) (P : ℝ) (hP : HasProduct p P)
    (hP0 : P ≠ 0) :
    HasProduct (fun n => (p n) ^ 2) (P ^ 2) := by
  exact gap4 p P hP hP0

end

end ProofGap.Exercise3065_2
