import ProofGapLean.Prelude.Analysis

namespace ProofGap.Exercise3065_4

noncomputable section

open Filter
open scoped BigOperators Topology

def partialProduct (p : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.Icc 1 n, p i

def HasProduct (p : ℕ → ℝ) (P : ℝ) : Prop :=
  Tendsto (partialProduct p) atTop (𝓝 P)

def ConvergentProduct (p : ℕ → ℝ) : Prop :=
  ∃ P : ℝ, HasProduct p P

def quotientPartialProduct (p q : ℕ → ℝ) (n : ℕ) : ℝ :=
  partialProduct p n / partialProduct q n

/-- Source: `proof_gap/exercise_3065_4/1.txt`; replace both product ellipses exactly. -/
theorem gap1 (p q : ℕ → ℝ) (P Q : ℝ)
    (hp : HasProduct p P) (hq : HasProduct q Q)
    (hP0 : P ≠ 0) (hQ0 : Q ≠ 0)
    (R : ℕ → ℝ)
    (hR : ∀ n, R n = quotientPartialProduct p q n) :
    ∀ n, R n = quotientPartialProduct p q n := by
  exact hR

/-- Source: `proof_gap/exercise_3065_4/2.txt`; the denominator limit is nonzero. -/
theorem gap2 (p q : ℕ → ℝ) (P Q : ℝ)
    (hp : HasProduct p P) (hq : HasProduct q Q)
    (hP0 : P ≠ 0) (hQ0 : Q ≠ 0)
    (R : ℕ → ℝ)
    (hR : ∀ n, R n = quotientPartialProduct p q n) :
    Tendsto R atTop (𝓝 (P / Q)) := by
  have hReq : R = quotientPartialProduct p q := funext hR
  subst R
  unfold HasProduct at hp hq
  simpa only [quotientPartialProduct] using hp.div hq hQ0

/-- Source: `proof_gap/exercise_3065_4/3.txt`; retain `Q ≠ 0` for division. -/
theorem gap3 (p q : ℕ → ℝ) (P Q : ℝ)
    (hp : HasProduct p P) (hq : HasProduct q Q)
    (hP0 : P ≠ 0) (hQ0 : Q ≠ 0) :
    ConvergentProduct (fun n => p n / q n) := by
  refine ⟨P / Q, ?_⟩
  unfold HasProduct
  exact gap2 p q P Q hp hq hP0 hQ0
    (partialProduct (fun n => p n / q n))
    (by
      intro n
      simp only [quotientPartialProduct, partialProduct,
        Finset.prod_div_distrib])

/-- Source: `proof_gap/exercise_3065_4/4.txt`; retain `Q ≠ 0` for division. -/
theorem gap4 (p q : ℕ → ℝ) (P Q : ℝ)
    (hp : HasProduct p P) (hq : HasProduct q Q)
    (hP0 : P ≠ 0) (hQ0 : Q ≠ 0) :
    HasProduct (fun n => p n / q n) (P / Q) := by
  unfold HasProduct
  exact gap2 p q P Q hp hq hP0 hQ0
    (partialProduct (fun n => p n / q n))
    (by
      intro n
      simp only [quotientPartialProduct, partialProduct,
        Finset.prod_div_distrib])

/-- Source: `proof_gap/exercise_3065_4/5.txt`; retain `Q ≠ 0` for division. -/
theorem gap5 (p q : ℕ → ℝ) (P Q : ℝ)
    (hp : HasProduct p P) (hq : HasProduct q Q)
    (hP0 : P ≠ 0) (hQ0 : Q ≠ 0) :
    HasProduct (fun n => p n / q n) (P / Q) := by
  exact gap4 p q P Q hp hq hP0 hQ0

end

end ProofGap.Exercise3065_4
