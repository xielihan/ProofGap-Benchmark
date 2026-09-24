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

/-- Source: `proof_gap/exercise_3065_3/1.txt`; replace both product ellipses exactly. -/
theorem gap1 (p q : ℕ → ℝ) (P Q : ℝ)
    (hp : HasProduct p P) (hq : HasProduct q Q)
    (hP0 : P ≠ 0) (hQ0 : Q ≠ 0)
    (R : ℕ → ℝ)
    (hR : ∀ n, R n = partialProduct p n * partialProduct q n) :
    Tendsto R atTop (𝓝 (P * Q)) := by
  have hReq : R = fun n => partialProduct p n * partialProduct q n := funext hR
  rw [hReq]
  exact hp.mul hq

/-- Source: `proof_gap/exercise_3065_3/2.txt`. -/
theorem gap2 (p q : ℕ → ℝ) (P Q : ℝ)
    (hp : HasProduct p P) (hq : HasProduct q Q)
    (hP0 : P ≠ 0) (hQ0 : Q ≠ 0) :
    ConvergentProduct (fun n => p n * q n) := by
  refine ⟨P * Q, ?_⟩
  unfold HasProduct
  apply gap1 p q P Q hp hq hP0 hQ0
  intro n
  simp only [partialProduct, Finset.prod_mul_distrib]

/-- Source: `proof_gap/exercise_3065_3/3.txt`. -/
theorem gap3 (p q : ℕ → ℝ) (P Q : ℝ)
    (hp : HasProduct p P) (hq : HasProduct q Q)
    (hP0 : P ≠ 0) (hQ0 : Q ≠ 0) :
    HasProduct (fun n => p n * q n) (P * Q) := by
  unfold HasProduct
  apply gap1 p q P Q hp hq hP0 hQ0
  intro n
  simp only [partialProduct, Finset.prod_mul_distrib]

/-- Source: `proof_gap/exercise_3065_3/4.txt`. -/
theorem gap4 (p q : ℕ → ℝ) (P Q : ℝ)
    (hp : HasProduct p P) (hq : HasProduct q Q)
    (hP0 : P ≠ 0) (hQ0 : Q ≠ 0) :
    HasProduct (fun n => p n * q n) (P * Q) := by
  exact gap3 p q P Q hp hq hP0 hQ0

end

end ProofGap.Exercise3065_3
