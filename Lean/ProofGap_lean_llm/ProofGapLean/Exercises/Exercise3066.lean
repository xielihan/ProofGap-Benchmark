import ProofGapLean.Prelude.Analysis
import ProofGapLean.Prelude.Discrete
import Lean.Elab.Tactic.Omega
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3066

noncomputable section

open Filter
open scoped BigOperators Topology

def reciprocalTerm (n : ℕ) : ℝ :=
  1 / (n : ℝ)

def factorialReciprocal (n : ℕ) : ℝ :=
  1 / (Nat.factorial n : ℝ)

def partialProduct (p : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.Icc 1 n, p i

def NonzeroConvergentProduct (p : ℕ → ℝ) : Prop :=
  ∃ P : ℝ, P ≠ 0 ∧ Tendsto (partialProduct p) atTop (𝓝 P)

def DivergentProduct (p : ℕ → ℝ) : Prop :=
  ¬NonzeroConvergentProduct p

/-- Source: `proof_gap/exercise_3066/1.txt`. -/
private theorem partialProduct_reciprocalTerm_eq_factorialReciprocal (n : ℕ) :
    partialProduct reciprocalTerm n = factorialReciprocal n := by
  have hfac : ∀ m : ℕ, ∏ i ∈ Finset.Icc 1 m, i = Nat.factorial m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        have hset :
            Finset.Icc 1 (Nat.succ m) =
              insert (Nat.succ m) (Finset.Icc 1 m) := by
          ext i
          simp only [Finset.mem_Icc, Finset.mem_insert]
          omega
        have hnot : Nat.succ m ∉ Finset.Icc 1 m := by
          simp
        rw [hset, Finset.prod_insert hnot, ih, Nat.factorial_succ]
  have hcast :
      (∏ i ∈ Finset.Icc 1 n, (i : ℝ)) = (Nat.factorial n : ℝ) := by
    simpa only [Nat.cast_prod] using
      congrArg (fun m : ℕ => (m : ℝ)) (hfac n)
  simp only [partialProduct, reciprocalTerm, factorialReciprocal, one_div]
  rw [Finset.prod_inv_distrib, hcast]

theorem gap1 (p : ℕ → ℝ) (hp : ∀ n, p n = reciprocalTerm n) :
    Tendsto p atTop (𝓝 0) := by
  have hcast :
      Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hinv :
      Tendsto (fun n : ℕ => ((n : ℝ)⁻¹)) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hcast
  have hp_inv : p = fun n : ℕ => ((n : ℝ)⁻¹) := by
    funext n
    rw [hp n]
    simp only [reciprocalTerm, one_div]
  rw [hp_inv]
  exact hinv

/-- Source: `proof_gap/exercise_3066/2.txt`. -/
theorem gap2 (p : ℕ → ℝ) (hp : ∀ n, p n = reciprocalTerm n) :
    ¬Tendsto p atTop (𝓝 1) := by
  intro h1
  have h0 : Tendsto p atTop (𝓝 0) := gap1 p hp
  have hEq : (0 : ℝ) = 1 := tendsto_nhds_unique h0 h1
  exact zero_ne_one hEq

/-- Source: `proof_gap/exercise_3066/3.txt`; retain the definition of arbitrary `P`. -/
theorem gap3 (P : ℕ → ℝ) (hP : ∀ n, P n = factorialReciprocal n) :
    Tendsto P atTop (𝓝 0) := by
  have hfac_ge : ∀ n : ℕ, n ≤ Nat.factorial n := by
    intro n
    cases n with
    | zero => simp
    | succ n =>
        rw [Nat.factorial_succ]
        have hone : 1 ≤ Nat.factorial n := Nat.factorial_pos n
        simpa using Nat.mul_le_mul_left (Nat.succ n) hone
  have hcast :
      Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hfactorial :
      Tendsto (fun n : ℕ => (Nat.factorial n : ℝ)) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    filter_upwards [tendsto_atTop.1 hcast b] with n hn
    exact hn.trans (Nat.cast_le.2 (hfac_ge n))
  have hinv :
      Tendsto (fun n : ℕ => (Nat.factorial n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hfactorial
  have hP_inv : P = fun n : ℕ => (Nat.factorial n : ℝ)⁻¹ := by
    funext n
    rw [hP n]
    simp only [factorialReciprocal, one_div]
  rw [hP_inv]
  exact hinv

/-- Source: `proof_gap/exercise_3066/4.txt`; spell out the positive-integer domain. -/
theorem gap4 :
    ∀ n : ℕ, 0 < n → (1 / (n : ℝ)) ≠ 0 := by
  intro n hn
  exact one_div_ne_zero (Nat.cast_ne_zero.mpr (ne_of_gt hn))

/--
Source: `proof_gap/exercise_3066/5.txt`; divergence means failure to converge
to a nonzero product value.
-/
theorem gap5 : DivergentProduct reciprocalTerm := by
  rw [DivergentProduct]
  rintro ⟨P, hP, hlim⟩
  have heq : partialProduct reciprocalTerm = factorialReciprocal := by
    funext n
    exact partialProduct_reciprocalTerm_eq_factorialReciprocal n
  have hzero : Tendsto (partialProduct reciprocalTerm) atTop (𝓝 0) := by
    rw [heq]
    exact gap3 factorialReciprocal (fun n => rfl)
  apply hP
  exact tendsto_nhds_unique hlim hzero

end

end ProofGap.Exercise3066
