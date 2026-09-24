import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

namespace ProofGap.Exercise3074

noncomputable section

open Filter
open scoped BigOperators Topology

def term (n : ℕ) : ℝ :=
  (n : ℝ) / Real.sqrt ((n : ℝ) ^ 2 + 1)

def normalizedTerm (n : ℕ) : ℝ :=
  1 / Real.sqrt (1 + 1 / (n : ℝ) ^ 2)

def logarithmicTerm (n : ℕ) : ℝ :=
  Real.log (1 + 1 / (n : ℝ) ^ 2)

def sumFromOne (f : ℕ → ℝ) : ℝ :=
  ∑' k : ℕ, f (k + 1)

def SummableFromOne (f : ℕ → ℝ) : Prop :=
  Summable (fun k : ℕ => f (k + 1))

def partialProduct (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.Icc 1 n, term i

def NonzeroConvergentProduct : Prop :=
  ∃ P : ℝ, P ≠ 0 ∧ Tendsto partialProduct atTop (𝓝 P)

private lemma partialProduct_eq_prod_range (n : ℕ) :
    partialProduct n = ∏ k ∈ Finset.range n, term (k + 1) := by
  unfold partialProduct
  symm
  have h := Finset.prod_Ico_add' term 0 n 1
  rw [Nat.Ico_zero_eq_range, zero_add,
    Finset.Ico_add_one_right_eq_Icc] at h
  exact h

/-- Exercise 3074, gap 1; the rewrite requires `n ≥ 1`. -/
theorem gap1 (p : ℕ → ℝ) (hp : ∀ n, p n = term n) :
    ∀ n : ℕ, 1 ≤ n → p n = normalizedTerm n := by
  intro n hn
  rw [hp n]
  unfold term normalizedTerm
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hfac :
      (n : ℝ) ^ 2 + 1 =
        (n : ℝ) ^ 2 * (1 + 1 / (n : ℝ) ^ 2) := by
    field_simp
  rw [hfac, Real.sqrt_mul (sq_nonneg (n : ℝ)), Real.sqrt_sq hnpos.le]
  have hspos : 0 < Real.sqrt (1 + 1 / (n : ℝ) ^ 2) := by
    positivity
  field_simp

/-- Exercise 3074, gap 2; the logarithmic rewrite starts at one. -/
theorem gap2 (p : ℕ → ℝ) (hp : ∀ n, p n = term n) :
    ∀ n : ℕ, 1 ≤ n →
      Real.log (p n) = -(1 / 2 : ℝ) * logarithmicTerm n := by
  intro n hn
  rw [gap1 p hp n hn]
  unfold normalizedTerm logarithmicTerm
  rw [one_div, Real.log_inv, Real.log_sqrt (by positivity)]
  ring

/-- Exercise 3074, gap 3; use exact sums from index one. -/
theorem gap3 (p : ℕ → ℝ) (hp : ∀ n, p n = term n) :
    sumFromOne (fun n => Real.log (p n)) =
      -(1 / 2 : ℝ) * sumFromOne logarithmicTerm := by
  unfold sumFromOne
  rw [← tsum_mul_left]
  apply tsum_congr
  intro k
  exact gap2 p hp (k + 1) (by omega)

/-- Exercise 3074, gap 4. -/
theorem gap4 :
    SummableFromOne (fun n => 1 / (n : ℝ) ^ 2) := by
  unfold SummableFromOne
  have hs :
      Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  exact (summable_nat_add_iff 1).2 hs

/-- Exercise 3074, gap 5. -/
theorem gap5 : SummableFromOne logarithmicTerm := by
  simpa [SummableFromOne, logarithmicTerm] using
    Real.summable_log_one_add_of_summable gap4

/-- Exercise 3074, gap 6; retain the definition of arbitrary `p`. -/
theorem gap6 (p : ℕ → ℝ) (hp : ∀ n, p n = term n) :
    SummableFromOne (fun n => Real.log (p n)) := by
  unfold SummableFromOne
  refine (gap5.mul_left (-(1 / 2 : ℝ))).congr ?_
  intro k
  exact (gap2 p hp (k + 1) (by omega)).symm

/-- Exercise 3074, gap 7. -/
theorem gap7 : NonzeroConvergentProduct := by
  let f : ℕ → ℝ := fun k => term (k + 1)
  have hfpos : ∀ k, 0 < f k := by
    intro k
    dsimp [f, term]
    positivity
  have hfsum : Summable (fun k => Real.log (f k)) := by
    simpa [f, SummableFromOne] using
      (gap6 term fun _ => rfl)
  have hfprod :
      HasProd f (Real.exp (∑' k, Real.log (f k))) :=
    Real.hasProd_of_hasSum_log hfpos hfsum.hasSum
  refine ⟨Real.exp (∑' k, Real.log (f k)), Real.exp_ne_zero _, ?_⟩
  have heq :
      partialProduct =
        fun n => ∏ k ∈ Finset.range n, term (k + 1) := by
    funext n
    exact partialProduct_eq_prod_range n
  rw [heq]
  simpa only [f] using hfprod.tendsto_prod_nat

end

end ProofGap.Exercise3074
