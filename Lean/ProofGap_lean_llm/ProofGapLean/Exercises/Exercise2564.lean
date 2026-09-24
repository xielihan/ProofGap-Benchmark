import ProofGapLean.Prelude.Sequences
import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace ProofGap.Exercise2564

noncomputable section

def radicalTerm (n : ℕ) : ℝ :=
  1 / Real.sqrt ((2 * (n : ℝ) - 1) * (2 * (n : ℝ) + 1))

def halfHarmonicTerm (n : ℕ) : ℝ := 1 / (2 * (n : ℝ))

theorem gap1 :
    ∀ n : ℕ, 1 ≤ n → radicalTerm n > halfHarmonicTerm n := by
  intro n hn
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hleft : 0 < 2 * (n : ℝ) - 1 := by linarith
  have hright : 0 < 2 * (n : ℝ) + 1 := by linarith
  have hprod : 0 < (2 * (n : ℝ) - 1) * (2 * (n : ℝ) + 1) :=
    mul_pos hleft hright
  have hsqrt_pos :
      0 < Real.sqrt ((2 * (n : ℝ) - 1) * (2 * (n : ℝ) + 1)) :=
    Real.sqrt_pos.2 hprod
  have hsqrt_sq :
      Real.sqrt ((2 * (n : ℝ) - 1) * (2 * (n : ℝ) + 1)) ^ 2 =
        (2 * (n : ℝ) - 1) * (2 * (n : ℝ) + 1) :=
    Real.sq_sqrt hprod.le
  have hsqrt_lt :
      Real.sqrt ((2 * (n : ℝ) - 1) * (2 * (n : ℝ) + 1)) < 2 * (n : ℝ) := by
    nlinarith [Real.sqrt_nonneg ((2 * (n : ℝ) - 1) * (2 * (n : ℝ) + 1))]
  exact one_div_lt_one_div_of_lt hsqrt_pos hsqrt_lt

theorem gap2
    (hcompare : ∀ n : ℕ, 1 ≤ n →
      radicalTerm n > halfHarmonicTerm n) :
    ∀ n : ℕ, 1 ≤ n → halfHarmonicTerm n > 0 := by
  intro n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  unfold halfHarmonicTerm
  positivity

theorem gap3
    (hcompare : ∀ n : ℕ, 1 ≤ n →
      radicalTerm n > halfHarmonicTerm n)
    (hhalf : ∀ n : ℕ, 1 ≤ n → halfHarmonicTerm n > 0) :
    ∀ n : ℕ, 1 ≤ n → radicalTerm n > 0 := by
  intro n hn
  exact (hhalf n hn).trans (hcompare n hn)

theorem gap4
    (hcompare : ∀ n : ℕ, 1 ≤ n →
      radicalTerm n > halfHarmonicTerm n)
    (hhalf : ∀ n : ℕ, 1 ≤ n → halfHarmonicTerm n > 0)
    (hradical : ∀ n : ℕ, 1 ≤ n → radicalTerm n > 0) :
    ¬ Summable halfHarmonicTerm := by
  intro hsummable
  apply Real.not_summable_one_div_natCast
  exact (hsummable.mul_left (2 : ℝ)).congr fun n => by
    simp only [halfHarmonicTerm, one_div, mul_inv_rev]
    ring_nf

theorem gap5
    (hcompare : ∀ n : ℕ, 1 ≤ n →
      radicalTerm n > halfHarmonicTerm n)
    (hhalf : ∀ n : ℕ, 1 ≤ n → halfHarmonicTerm n > 0)
    (hradical : ∀ n : ℕ, 1 ≤ n → radicalTerm n > 0)
    (hdiv : ¬ Summable halfHarmonicTerm) :
    ¬ Summable radicalTerm := by
  intro hsummable
  apply hdiv
  refine Summable.of_nonneg_of_le ?_ ?_ hsummable
  · intro n
    unfold halfHarmonicTerm
    positivity
  · intro n
    by_cases hn : n = 0
    · subst n
      simp [halfHarmonicTerm, radicalTerm]
    · exact (hcompare n (Nat.one_le_iff_ne_zero.2 hn)).le

end

end ProofGap.Exercise2564
