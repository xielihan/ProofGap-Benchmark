import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise3065_1

noncomputable section

open Filter
open scoped BigOperators Topology

def pTerm (n : ℕ) : ℝ :=
  1 - 1 / (n : ℝ) ^ 2

def qTerm (n : ℕ) : ℝ :=
  1 + 1 / (n : ℝ) ^ 2

def partialProduct (u : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.Icc 1 n, u i

def ConvergentProduct (u : ℕ → ℝ) : Prop :=
  ∃ L : ℝ, Tendsto (partialProduct u) atTop (𝓝 L)

def DivergentProduct (u : ℕ → ℝ) : Prop :=
  ¬ConvergentProduct u

/-- Source: `proof_gap/exercise_3065_1/1.txt`. -/
theorem gap1 : ConvergentProduct pTerm := by
  refine ⟨0, (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)).congr' ?_⟩
  filter_upwards [eventually_ge_atTop 1] with n hn
  symm
  unfold partialProduct
  apply Finset.prod_eq_zero (show 1 ∈ Finset.Icc 1 n by simp [hn])
  norm_num [pTerm]

/-- Source: `proof_gap/exercise_3065_1/2.txt`. -/
theorem gap2 : ConvergentProduct qTerm := by
  have hq_one_le (n : ℕ) : 1 ≤ qTerm n := by
    unfold qTerm
    have hnonneg : 0 ≤ 1 / (n : ℝ) ^ 2 :=
      div_nonneg (by norm_num) (sq_nonneg (n : ℝ))
    linarith
  have hq_nonneg (n : ℕ) : 0 ≤ qTerm n :=
    le_trans (by norm_num) (hq_one_le n)
  have hprod_nonneg (n : ℕ) : 0 ≤ partialProduct qTerm n := by
    unfold partialProduct
    apply Finset.prod_nonneg
    intro i hi
    exact hq_nonneg i
  have hrec (n : ℕ) :
      partialProduct qTerm (n + 1) =
        partialProduct qTerm n * qTerm (n + 1) := by
    have hIcc :
        Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
      ext i
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    unfold partialProduct
    rw [hIcc, Finset.prod_insert (by simp)]
    ring
  have hmono : Monotone (partialProduct qTerm) := by
    apply monotone_nat_of_le_succ
    intro n
    rw [hrec n]
    calc
      partialProduct qTerm n = partialProduct qTerm n * 1 := by ring
      _ ≤ partialProduct qTerm n * qTerm (n + 1) :=
        mul_le_mul_of_nonneg_left (hq_one_le (n + 1)) (hprod_nonneg n)
  have hbound_aux :
      ∀ n : ℕ, 1 ≤ n →
        partialProduct qTerm n ≤
          4 * (n : ℝ) / ((n : ℝ) + 1) := by
    intro n
    induction n with
    | zero =>
        intro hn
        omega
    | succ n ih =>
        intro hn
        by_cases hzero : n = 0
        · subst n
          norm_num [partialProduct, qTerm]
        · have hn1 : 1 ≤ n := by omega
          have hih := ih hn1
          have hnpos : (0 : ℝ) < (n : ℝ) :=
            Nat.cast_pos.mpr (by omega)
          have hn1pos : 0 < (n : ℝ) + 1 := by linarith
          have hn2pos : 0 < (n : ℝ) + 2 := by linarith
          have hqform :
              qTerm (n + 1) =
                (((n : ℝ) + 1) ^ 2 + 1) / (((n : ℝ) + 1) ^ 2) := by
            unfold qTerm
            simp only [Nat.cast_add, Nat.cast_one]
            field_simp [ne_of_gt hn1pos] <;> ring
          have hdenleft : 0 < ((n : ℝ) + 1) ^ 2 :=
            pow_pos hn1pos 2
          have hdenright :
              0 < (n : ℝ) * ((n : ℝ) + 2) :=
            mul_pos hnpos hn2pos
          have hq_upper :
              qTerm (n + 1) ≤
                ((n : ℝ) + 1) ^ 2 /
                  ((n : ℝ) * ((n : ℝ) + 2)) := by
            rw [hqform]
            apply (div_le_div_iff₀ hdenleft hdenright).2
            nlinarith
          have hcoef_nonneg :
              0 ≤ 4 * (n : ℝ) / ((n : ℝ) + 1) :=
            div_nonneg
              (mul_nonneg (by norm_num) (le_of_lt hnpos))
              (le_of_lt hn1pos)
          rw [hrec n]
          calc
            partialProduct qTerm n * qTerm (n + 1)
                ≤ (4 * (n : ℝ) / ((n : ℝ) + 1)) * qTerm (n + 1) :=
              mul_le_mul_of_nonneg_right hih (hq_nonneg (n + 1))
            _ ≤ (4 * (n : ℝ) / ((n : ℝ) + 1)) *
                  (((n : ℝ) + 1) ^ 2 /
                    ((n : ℝ) * ((n : ℝ) + 2))) :=
              mul_le_mul_of_nonneg_left hq_upper hcoef_nonneg
            _ = 4 * ((n : ℝ) + 1) / ((n : ℝ) + 2) := by
              field_simp [ne_of_gt hnpos, ne_of_gt hn1pos, ne_of_gt hn2pos] <;>
                ring
            _ = 4 * ((n + 1 : ℕ) : ℝ) /
                  (((n + 1 : ℕ) : ℝ) + 1) := by
              norm_num [Nat.cast_add, add_assoc]
  have hbound (n : ℕ) : partialProduct qTerm n ≤ 4 := by
    by_cases hn : n = 0
    · subst n
      norm_num [partialProduct]
    · have hn1 : 1 ≤ n := by omega
      have haux := hbound_aux n hn1
      have hncast : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      have hden : 0 < (n : ℝ) + 1 := by linarith
      have hfrac : 4 * (n : ℝ) / ((n : ℝ) + 1) ≤ 4 := by
        apply (div_le_iff₀ hden).2
        nlinarith
      exact haux.trans hfrac
  have hbdd : BddAbove (Set.range (partialProduct qTerm)) := by
    refine ⟨4, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact hbound n
  refine ⟨⨆ n : ℕ, partialProduct qTerm n, ?_⟩
  apply tendsto_atTop_ciSup
  all_goals assumption

/--
Source: `proof_gap/exercise_3065_1/3.txt`; the two divergent infinite products
are replaced by equality of every finite partial product.
-/
theorem gap3 :
    ∀ n,
      partialProduct (fun k => pTerm k + qTerm k) n =
        partialProduct (fun _ => (2 : ℝ)) n := by
  intro n
  unfold partialProduct
  apply Finset.prod_congr rfl
  intro i hi
  simp only [pTerm, qTerm]
  ring

/-- Source: `proof_gap/exercise_3065_1/4.txt`. -/
theorem gap4 : DivergentProduct (fun _ => (2 : ℝ)) := by
  rintro ⟨L, hL⟩
  have hpartial (n : ℕ) :
      partialProduct (fun _ => (2 : ℝ)) n = (2 : ℝ) ^ n := by
    simp [partialProduct]
  have hpow : Tendsto (fun n : ℕ => (2 : ℝ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hsmall :
      ∀ᶠ n in atTop, partialProduct (fun _ => (2 : ℝ)) n < L + 1 :=
    hL.eventually (Iio_mem_nhds (by linarith))
  have hlarge : ∀ᶠ n in atTop, L + 1 < (2 : ℝ) ^ n :=
    hpow.eventually (eventually_gt_atTop (L + 1))
  rcases eventually_atTop.1 hsmall with ⟨N1, hN1⟩
  rcases eventually_atTop.1 hlarge with ⟨N2, hN2⟩
  have hs := hN1 (max N1 N2) (Nat.le_max_left N1 N2)
  have hl := hN2 (max N1 N2) (Nat.le_max_right N1 N2)
  rw [hpartial (max N1 N2)] at hs
  linarith

/-- Source: `proof_gap/exercise_3065_1/5.txt`; retain definitions of arbitrary `p` and `q`. -/
theorem gap5 (p q : ℕ → ℝ)
    (hp : ∀ n, p n = pTerm n) (hq : ∀ n, q n = qTerm n) :
    ¬ConvergentProduct (fun n => p n + q n) := by
  intro hconv
  have hfun : (fun n => p n + q n) = (fun _ => (2 : ℝ)) := by
    funext n
    rw [hp n, hq n]
    simp only [pTerm, qTerm]
    ring
  exact gap4 (hfun ▸ hconv)

/-- Source: `proof_gap/exercise_3065_1/6.txt`. -/
theorem gap6 :
    ∃ p q : ℕ → ℝ,
      ¬(ConvergentProduct p ∧ ConvergentProduct q →
        ConvergentProduct (fun n => p n + q n)) := by
  refine ⟨pTerm, qTerm, ?_⟩
  intro h
  exact gap5 pTerm qTerm (fun _ => rfl) (fun _ => rfl) (h ⟨gap1, gap2⟩)

end

end ProofGap.Exercise3065_1
