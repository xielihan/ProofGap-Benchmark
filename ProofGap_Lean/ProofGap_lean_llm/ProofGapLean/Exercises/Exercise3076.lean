import ProofGapLean.Prelude.Analysis
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.PSeries
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3076

noncomputable section

open Filter
open scoped BigOperators Topology

def term (n : ℕ) : ℝ :=
  Real.rpow (n : ℝ) (1 / (n : ℝ) ^ 2)

def logarithmicTerm (n : ℕ) : ℝ :=
  Real.log (n : ℝ) / (n : ℝ) ^ 2

def comparisonTerm (ε : ℝ) (n : ℕ) : ℝ :=
  1 / Real.rpow (n : ℝ) (1 + ε)

def sumFromOne (f : ℕ → ℝ) : ℝ :=
  ∑' k : ℕ, f (k + 1)

def SummableFromOne (f : ℕ → ℝ) : Prop :=
  Summable (fun k : ℕ => f (k + 1))

def partialProduct (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.Icc 1 n, term i

def NonzeroConvergentProduct : Prop :=
  ∃ P : ℝ, P ≠ 0 ∧ Tendsto partialProduct atTop (𝓝 P)

/-- Exercise 3076, gap 1; use `Real.rpow` and start at one. -/
private theorem logarithmicTerm_norm_le_half (n : ℕ) (hn : 1 ≤ n) :
    ‖logarithmicTerm n‖ ≤
      2 * ‖comparisonTerm (1 / 2 : ℝ) n‖ := by
  have hnposNat : 0 < n := by omega
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnposNat
  have hnone : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlognonneg : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnone
  have hhalfpos : 0 < Real.rpow (n : ℝ) (1 / 2 : ℝ) :=
    Real.rpow_pos_of_pos hnpos _
  have hcompPos : 0 < Real.rpow (n : ℝ) (1 + (1 / 2 : ℝ)) :=
    Real.rpow_pos_of_pos hnpos _
  have hlogHalf :
      Real.log (Real.rpow (n : ℝ) (1 / 2 : ℝ)) =
        (1 / 2 : ℝ) * Real.log (n : ℝ) := by
    simpa [mul_comm] using Real.log_rpow hnpos (1 / 2 : ℝ)
  have hlogBound0 := Real.log_le_sub_one_of_pos hhalfpos
  have hlogBound :
      Real.log (n : ℝ) ≤ 2 * Real.rpow (n : ℝ) (1 / 2 : ℝ) := by
    nlinarith
  have hmul :
      Real.rpow (n : ℝ) (1 + (1 / 2 : ℝ)) *
          Real.rpow (n : ℝ) (1 / 2 : ℝ) =
        (n : ℝ) ^ 2 := by
    change
      ((n : ℝ) ^ (1 + (1 / 2 : ℝ))) *
          ((n : ℝ) ^ (1 / 2 : ℝ)) = (n : ℝ) ^ 2
    calc
      ((n : ℝ) ^ (1 + (1 / 2 : ℝ))) *
          ((n : ℝ) ^ (1 / 2 : ℝ)) =
          (n : ℝ) ^ ((1 + (1 / 2 : ℝ)) + (1 / 2 : ℝ)) :=
        (Real.rpow_add hnpos (1 + (1 / 2 : ℝ)) (1 / 2 : ℝ)).symm
      _ = (n : ℝ) ^ ((1 : ℝ) + 1) := by norm_num
      _ = ((n : ℝ) ^ (1 : ℝ)) * ((n : ℝ) ^ (1 : ℝ)) :=
        Real.rpow_add hnpos (1 : ℝ) (1 : ℝ)
      _ = (n : ℝ) ^ 2 := by rw [Real.rpow_one]; ring
  have hsquarePos : 0 < (n : ℝ) ^ 2 := pow_pos hnpos _
  have hcompNe : Real.rpow (n : ℝ) (1 + (1 / 2 : ℝ)) ≠ 0 :=
    ne_of_gt hcompPos
  have hinv :
      (1 / Real.rpow (n : ℝ) (1 + (1 / 2 : ℝ))) *
          Real.rpow (n : ℝ) (1 + (1 / 2 : ℝ)) = 1 := by
    simpa using (div_mul_cancel₀ (1 : ℝ) hcompNe)
  change ‖Real.log (n : ℝ) / (n : ℝ) ^ 2‖ ≤
    2 * ‖1 / Real.rpow (n : ℝ) (1 + (1 / 2 : ℝ))‖
  simp only [Real.norm_eq_abs]
  rw [abs_of_nonneg (div_nonneg hlognonneg (le_of_lt hsquarePos)),
    abs_of_pos (one_div_pos.mpr hcompPos)]
  apply (div_le_iff₀ hsquarePos).2
  calc
    Real.log (n : ℝ) ≤
        2 * Real.rpow (n : ℝ) (1 / 2 : ℝ) := hlogBound
    _ = (2 * (1 / Real.rpow (n : ℝ) (1 + (1 / 2 : ℝ)))) *
          (n : ℝ) ^ 2 := by
      rw [← hmul]
      calc
        2 * Real.rpow (n : ℝ) (1 / 2 : ℝ) =
            2 * ((1 / Real.rpow (n : ℝ) (1 + (1 / 2 : ℝ))) *
              Real.rpow (n : ℝ) (1 + (1 / 2 : ℝ))) *
              Real.rpow (n : ℝ) (1 / 2 : ℝ) := by rw [hinv]; ring
        _ = (2 * (1 / Real.rpow (n : ℝ) (1 + (1 / 2 : ℝ)))) *
              (Real.rpow (n : ℝ) (1 + (1 / 2 : ℝ)) *
                Real.rpow (n : ℝ) (1 / 2 : ℝ)) := by ring

private theorem logarithmicTerm_isBigOHalf :
    logarithmicTerm =O[atTop] comparisonTerm (1 / 2 : ℝ) := by
  refine Asymptotics.IsBigO.of_bound 2 ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  exact logarithmicTerm_norm_le_half n hn

private theorem comparisonHalf_summable :
    SummableFromOne (comparisonTerm (1 / 2 : ℝ)) := by
  have hs : Summable
      (fun n : ℕ =>
        Real.rpow (n : ℝ) (-(1 + (1 / 2 : ℝ)))) := by
    exact Real.summable_nat_rpow.2 (by norm_num)
  unfold SummableFromOne
  have heq :
      (fun k : ℕ => comparisonTerm (1 / 2 : ℝ) (k + 1)) =
        ((fun n : ℕ =>
          Real.rpow (n : ℝ) (-(1 + (1 / 2 : ℝ)))) ∘ Nat.succ) := by
    funext k
    simp only [Function.comp_apply, Nat.succ_eq_add_one]
    unfold comparisonTerm
    simp only [one_div]
    have hkposNat : 0 < k + 1 := by omega
    have hkpos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by
      exact_mod_cast hkposNat
    have hmul :
        Real.rpow ((k + 1 : ℕ) : ℝ) (1 + (2 : ℝ)⁻¹) *
            Real.rpow ((k + 1 : ℕ) : ℝ) (-(1 + (2 : ℝ)⁻¹)) = 1 := by
      calc
        Real.rpow ((k + 1 : ℕ) : ℝ) (1 + (2 : ℝ)⁻¹) *
            Real.rpow ((k + 1 : ℕ) : ℝ) (-(1 + (2 : ℝ)⁻¹)) =
            Real.rpow ((k + 1 : ℕ) : ℝ)
              ((1 + (2 : ℝ)⁻¹) + -(1 + (2 : ℝ)⁻¹)) :=
          (Real.rpow_add hkpos (1 + (2 : ℝ)⁻¹)
            (-(1 + (2 : ℝ)⁻¹))).symm
        _ = 1 := by simp
    have hpowNe :
        Real.rpow ((k + 1 : ℕ) : ℝ) (1 + (2 : ℝ)⁻¹) ≠ 0 :=
      ne_of_gt (Real.rpow_pos_of_pos hkpos _)
    calc
      (Real.rpow ((k + 1 : ℕ) : ℝ) (1 + (2 : ℝ)⁻¹))⁻¹ =
          (Real.rpow ((k + 1 : ℕ) : ℝ) (1 + (2 : ℝ)⁻¹))⁻¹ *
            (Real.rpow ((k + 1 : ℕ) : ℝ) (1 + (2 : ℝ)⁻¹) *
              Real.rpow ((k + 1 : ℕ) : ℝ) (-(1 + (2 : ℝ)⁻¹))) := by
        rw [hmul, mul_one]
      _ = Real.rpow ((k + 1 : ℕ) : ℝ) (-(1 + (2 : ℝ)⁻¹)) := by
        rw [← mul_assoc, inv_mul_cancel₀ hpowNe, one_mul]
  rw [heq]
  exact hs.comp_injective Nat.succ_injective

theorem gap1 (p : ℕ → ℝ) (hp : ∀ n, p n = term n) :
    ∀ n : ℕ, 1 ≤ n → Real.log (p n) = logarithmicTerm n := by
  intro n hn
  have hnposNat : 0 < n := by omega
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnposNat
  rw [hp n]
  unfold term logarithmicTerm
  change Real.log ((n : ℝ) ^ (1 / (n : ℝ) ^ 2 : ℝ)) =
    Real.log (n : ℝ) / (n : ℝ) ^ 2
  rw [Real.log_rpow hnpos]
  ring

/-- Exercise 3076, gap 2; use exact sums from index one. -/
theorem gap2 (p : ℕ → ℝ) (hp : ∀ n, p n = term n) :
    sumFromOne (fun n => Real.log (p n)) =
      sumFromOne logarithmicTerm := by
  unfold sumFromOne
  apply tsum_congr
  intro k
  apply gap1 p hp
  omega

/-- Exercise 3076, gap 3; quantify the functions and a valid `ε`. -/
theorem gap3 :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
      (logarithmicTerm =O[atTop] comparisonTerm ε) := by
  refine ⟨(1 / 2 : ℝ), by norm_num, by norm_num, ?_⟩
  exact logarithmicTerm_isBigOHalf

/-- Exercise 3076, gap 4; the comparison exponent needs `ε > 0`. -/
theorem gap4 :
    ∃ ε : ℝ, 0 < ε ∧ SummableFromOne (comparisonTerm ε) := by
  refine ⟨(1 / 2 : ℝ), by norm_num, ?_⟩
  exact comparisonHalf_summable

/--
Exercise 3076, gap 5; apply convergence to the sequence of
finite partial products, not to each scalar product.
-/
theorem gap5 : NonzeroConvergentProduct := by
  have hcomp : Summable
      (fun k : ℕ => comparisonTerm (1 / 2 : ℝ) (k + 1)) :=
    comparisonHalf_summable
  have hcompNonneg : ∀ k : ℕ,
      0 ≤ comparisonTerm (1 / 2 : ℝ) (k + 1) := by
    intro k
    have hkposNat : 0 < k + 1 := by omega
    have hkpos : (0 : ℝ) < (((k + 1 : ℕ) : ℝ)) := by
      exact_mod_cast hkposNat
    unfold comparisonTerm
    exact le_of_lt (one_div_pos.mpr (Real.rpow_pos_of_pos hkpos _))
  have hscaled : Summable
      (fun k : ℕ => 2 * comparisonTerm (1 / 2 : ℝ) (k + 1)) :=
    hcomp.mul_left 2
  have hmajorEq :
      (fun k : ℕ => 2 * ‖comparisonTerm (1 / 2 : ℝ) (k + 1)‖) =
        (fun k : ℕ => 2 * comparisonTerm (1 / 2 : ℝ) (k + 1)) := by
    funext k
    rw [Real.norm_eq_abs, abs_of_nonneg (hcompNonneg k)]
  have hmajor : Summable
      (fun k : ℕ => 2 * ‖comparisonTerm (1 / 2 : ℝ) (k + 1)‖) := by
    rw [hmajorEq]
    exact hscaled
  have hf : Summable (fun k : ℕ => logarithmicTerm (k + 1)) := by
    refine Summable.of_norm_bounded hmajor ?_
    intro k
    exact logarithmicTerm_norm_le_half (k + 1) (by omega)
  have hterm_exp : ∀ i : ℕ, 1 ≤ i →
      term i = Real.exp (logarithmicTerm i) := by
    intro i hi
    have hiposNat : 0 < i := by omega
    have hipos : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hiposNat
    unfold term logarithmicTerm
    change ((i : ℝ) ^ (1 / (i : ℝ) ^ 2 : ℝ)) =
      Real.exp (Real.log (i : ℝ) / (i : ℝ) ^ 2)
    rw [Real.rpow_def_of_pos hipos]
    congr 1
    ring
  have hpartial : ∀ n : ℕ,
      partialProduct n =
        Real.exp (∑ k ∈ Finset.range n, logarithmicTerm (k + 1)) := by
    intro n
    induction n with
    | zero =>
        simp [partialProduct]
    | succ n ih =>
        have hIcc : Finset.Icc 1 (n + 1) =
            insert (n + 1) (Finset.Icc 1 n) := by
          ext i
          simp only [Finset.mem_Icc, Finset.mem_insert]
          omega
        rw [partialProduct, hIcc,
          Finset.prod_insert (by simp [Finset.mem_Icc])]
        change term (n + 1) * partialProduct n =
          Real.exp (∑ k ∈ Finset.range (n + 1), logarithmicTerm (k + 1))
        rw [hterm_exp (n + 1) (by omega), ih, Finset.sum_range_succ,
          Real.exp_add]
        ring
  refine ⟨Real.exp (sumFromOne logarithmicTerm), Real.exp_ne_zero _, ?_⟩
  have hsums : Tendsto
      (fun n : ℕ => ∑ k ∈ Finset.range n, logarithmicTerm (k + 1))
      atTop (nhds (sumFromOne logarithmicTerm)) := by
    simpa [sumFromOne] using hf.hasSum.tendsto_sum_nat
  have hexp : Tendsto
      (fun n : ℕ =>
        Real.exp (∑ k ∈ Finset.range n, logarithmicTerm (k + 1)))
      atTop (nhds (Real.exp (sumFromOne logarithmicTerm))) := by
    simpa only [Function.comp_apply] using
      Real.continuous_exp.continuousAt.tendsto.comp hsums
  have hpartial_fun :
      partialProduct =
        (fun n : ℕ =>
          Real.exp (∑ k ∈ Finset.range n, logarithmicTerm (k + 1))) := by
    funext n
    exact hpartial n
  rw [hpartial_fun]
  exact hexp

end

end ProofGap.Exercise3076
