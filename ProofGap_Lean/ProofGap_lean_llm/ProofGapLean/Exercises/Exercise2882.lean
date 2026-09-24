import ProofGapLean.Prelude.Analysis
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise2882

noncomputable section

open scoped BigOperators

def negativeExpTerm (x : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * x ^ n / (Nat.factorial n : ℝ)

def expandedTailTerm (x : ℝ) (k : ℕ) : ℝ :=
  let n := k + 2
  (((-1 : ℝ) ^ n / (Nat.factorial n : ℝ)) +
      ((-1 : ℝ) ^ (k + 1) / (Nat.factorial (k + 1) : ℝ))) *
    x ^ n

def simplifiedTailTerm (x : ℝ) (k : ℕ) : ℝ :=
  let n := k + 2
  (-1 : ℝ) ^ (k + 1) * ((k + 1 : ℝ) / (Nat.factorial n : ℝ)) *
    x ^ n

private theorem negativeExpTerm_hasSum_exp (x : ℝ) :
    HasSum (negativeExpTerm x) (Real.exp (-x)) := by
  have hfun :
      (fun n : ℕ => (-x) ^ n / (Nat.factorial n : ℝ)) =
        negativeExpTerm x := by
    funext n
    unfold negativeExpTerm
    rw [show -x = (-1 : ℝ) * x by ring, mul_pow]
  simpa only [hfun, Real.exp_eq_exp_ℝ] using
    (NormedSpace.expSeries_div_hasSum_exp (-x))

theorem gap1 :
    ∀ x : ℝ, (1 + x) * Real.exp (-x) =
      (1 + x) * (∑' n, negativeExpTerm x n) := by
  intro x
  have h : Real.exp (-x) = ∑' n, negativeExpTerm x n :=
    (negativeExpTerm_hasSum_exp x).tsum_eq.symm
  exact congrArg (fun y : ℝ => (1 + x) * y) h

theorem gap2 :
    ∀ x : ℝ, (1 + x) * Real.exp (-x) =
      1 + ∑' k, expandedTailTerm x k := by
  intro x
  let a : ℕ → ℝ := negativeExpTerm x
  have ha : Summable a := by
    simpa [a] using (negativeExpTerm_hasSum_exp x).summable
  have hs1 :
      a 0 + ∑' k : ℕ, a (k + 1) = ∑' n : ℕ, a n := by
    simpa [Finset.sum_range_succ, Nat.add_comm] using
      (ha.sum_add_tsum_nat_add 1)
  have hs2 :
      (a 0 + a 1) + ∑' k : ℕ, a (k + 2) = ∑' n : ℕ, a n := by
    simpa [Finset.sum_range_succ, Nat.add_comm, add_assoc] using
      (ha.sum_add_tsum_nat_add 2)
  have htail1 :
      (∑' k : ℕ, a (k + 1)) = (∑' n : ℕ, a n) - a 0 := by
    rw [← hs1]
    ring
  have htail2 :
      (∑' k : ℕ, a (k + 2)) =
        (∑' n : ℕ, a n) - (a 0 + a 1) := by
    rw [← hs2]
    ring
  have hshift_injective (c : ℕ) :
      Function.Injective (fun k : ℕ => k + c) := by
    intro m n hmn
    exact Nat.add_right_cancel hmn
  have ha1 : Summable (fun k : ℕ => a (k + 1)) := by
    simpa only [Function.comp_apply] using
      ha.comp_injective (hshift_injective 1)
  have ha2 : Summable (fun k : ℕ => a (k + 2)) := by
    simpa only [Function.comp_apply] using
      ha.comp_injective (hshift_injective 2)
  have hraw :
      (∑' k : ℕ, (a (k + 2) + x * a (k + 1))) =
        (∑' k : ℕ, a (k + 2)) + x * (∑' k : ℕ, a (k + 1)) :=
    (ha2.hasSum.add (ha1.hasSum.mul_left x)).tsum_eq
  have hterm (k : ℕ) :
      expandedTailTerm x k = a (k + 2) + x * a (k + 1) := by
    have hk : k + 2 = (k + 1) + 1 := by omega
    have hx : x ^ (k + 2) = x ^ (k + 1) * x := by
      rw [hk, pow_succ]
    dsimp [expandedTailTerm, a, negativeExpTerm]
    simp only [hx]
    ring
  have hseries :
      (∑' k : ℕ, expandedTailTerm x k) =
        ((∑' n : ℕ, a n) - (a 0 + a 1)) +
          x * ((∑' n : ℕ, a n) - a 0) := by
    calc
      (∑' k : ℕ, expandedTailTerm x k) =
          ∑' k : ℕ, (a (k + 2) + x * a (k + 1)) :=
        tsum_congr hterm
      _ = (∑' k : ℕ, a (k + 2)) +
          x * (∑' k : ℕ, a (k + 1)) := hraw
      _ = ((∑' n : ℕ, a n) - (a 0 + a 1)) +
          x * ((∑' n : ℕ, a n) - a 0) := by
        rw [htail2, htail1]
  calc
    (1 + x) * Real.exp (-x) =
        (1 + x) * (∑' n : ℕ, a n) := by
      simpa [a] using (gap1 x)
    _ = 1 + ∑' k : ℕ, expandedTailTerm x k := by
      rw [hseries]
      simp [a, negativeExpTerm]
      ring

theorem gap3 :
    ∀ x : ℝ, (1 + x) * Real.exp (-x) =
      1 + ∑' k, simplifiedTailTerm x k := by
  intro x
  calc
    (1 + x) * Real.exp (-x) =
        1 + ∑' k, expandedTailTerm x k := gap2 x
    _ = 1 + ∑' k, simplifiedTailTerm x k := by
      have ht :
          (∑' k, expandedTailTerm x k) =
            ∑' k, simplifiedTailTerm x k := by
        apply tsum_congr
        intro k
        have hidx : k + 2 = (k + 1) + 1 := by omega
        have hpow :
            (-1 : ℝ) ^ (k + 2) = -((-1 : ℝ) ^ (k + 1)) := by
          rw [hidx, pow_succ]
          ring
        have hfac :
            (Nat.factorial (k + 2) : ℝ) =
              ((k + 1 : ℝ) + 1) *
                (Nat.factorial (k + 1) : ℝ) := by
          rw [hidx, Nat.factorial_succ]
          norm_num [Nat.cast_mul, Nat.cast_add]
        unfold expandedTailTerm simplifiedTailTerm
        dsimp only
        simp only [hpow, hfac]
        have hfac_ne :
            (Nat.factorial (k + 1) : ℝ) ≠ 0 := by positivity
        have hk_ne : (k + 1 : ℝ) + 1 ≠ 0 := by positivity
        field_simp [hfac_ne, hk_ne]
        all_goals ring
      exact congrArg (fun y : ℝ => 1 + y) ht

end

end ProofGap.Exercise2882
