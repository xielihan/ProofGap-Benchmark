import ProofGapLean.Prelude.Analysis

namespace ProofGap.Exercise3065_3

noncomputable section

open Filter
open scoped BigOperators Topology

def partialProduct (p : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.Icc 1 n, p i

def HasProduct (p : ℕ → ℝ) (P : ℝ) : Prop :=
  Tendsto (partialProduct p) atTop (𝓝 P)

def ConvergentProduct (p : ℕ → ℝ) : Prop :=
  ∃ P : ℝ, HasProduct p P

/-- Exercise 3065_3, gap 1; replace both product ellipses exactly. -/
theorem gap1 (p q : ℕ → ℝ) (P Q : ℝ)
    (hp : HasProduct p P) (hq : HasProduct q Q)
    (hP0 : P ≠ 0) (hQ0 : Q ≠ 0)
    (R : ℕ → ℝ)
    (hR : ∀ n, R n = partialProduct p n * partialProduct q n) :
    Tendsto R atTop (𝓝 (P * Q)) := by
  have hReq : R = fun n => partialProduct p n * partialProduct q n := funext hR
  rw [hReq]
  exact hp.mul hq

/-- Exercise 3065_3, gap 2. -/
theorem gap2 (p q : ℕ → ℝ) (P Q : ℝ)
    (hp : HasProduct p P) (hq : HasProduct q Q)
    (hP0 : P ≠ 0) (hQ0 : Q ≠ 0) :
    ConvergentProduct (fun n => p n * q n) := by
  refine ⟨P * Q, ?_⟩
  unfold HasProduct
  apply gap1 p q P Q hp hq hP0 hQ0
  intro n
  simp only [partialProduct, Finset.prod_mul_distrib]

/-- Exercise 3065_3, gap 3. -/
theorem gap3 (p q : ℕ → ℝ) (P Q : ℝ)
    (hp : HasProduct p P) (hq : HasProduct q Q)
    (hP0 : P ≠ 0) (hQ0 : Q ≠ 0) :
    HasProduct (fun n => p n * q n) (P * Q) := by
  unfold HasProduct
  apply gap1 p q P Q hp hq hP0 hQ0
  intro n
  simp only [partialProduct, Finset.prod_mul_distrib]

/-- Exercise 3065_3, gap 4. -/
theorem gap4 (p q : ℕ → ℝ) (P Q : ℝ)
    (hp : HasProduct p P) (hq : HasProduct q Q)
    (hP0 : P ≠ 0) (hQ0 : Q ≠ 0) :
    HasProduct (fun n => p n * q n) (P * Q) := by
  exact gap3 p q P Q hp hq hP0 hQ0

end

end ProofGap.Exercise3065_3
