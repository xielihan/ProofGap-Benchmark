import ProofGapLean.Prelude.Analysis
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Analysis.SpecificLimits.Normed

namespace ProofGap.Exercise3069

noncomputable section

open Filter
open scoped BigOperators Topology

def factor (n : ℕ) : ℝ :=
  1 - 1 / (n : ℝ)

def harmonicTerm (n : ℕ) : ℝ :=
  -(1 / (n : ℝ))

def partialProduct (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.Icc 2 n, factor i

def NonzeroConvergentProduct : Prop :=
  ∃ P : ℝ, P ≠ 0 ∧ Tendsto partialProduct atTop (𝓝 P)

def DivergentProduct : Prop :=
  ¬NonzeroConvergentProduct

/-- Exercise 3069, gap 1; retain the definition of arbitrary `p`. -/
private theorem partialProduct_formula :
    (∀ n : ℕ, 2 ≤ n → partialProduct n = 1 / (n : ℝ)) ∧
      Tendsto partialProduct atTop (𝓝 0) := by
  have hformula : ∀ n : ℕ, 2 ≤ n → partialProduct n = 1 / (n : ℝ) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
        norm_num [partialProduct, factor]
    | succ n hn ih =>
        have hnot : n + 1 ∉ Finset.Icc 2 n := by
          simp
        have hset :
            Finset.Icc 2 (n + 1) =
              insert (n + 1) (Finset.Icc 2 n) := by
          ext i
          simp only [Finset.mem_Icc, Finset.mem_insert]
          omega
        have ih' :
            (∏ i ∈ Finset.Icc 2 n, factor i) = 1 / (n : ℝ) := by
          simpa [partialProduct] using ih
        rw [partialProduct, hset, Finset.prod_insert hnot, ih', factor]
        have hn0 : (n : ℝ) ≠ 0 := by
          have : (0 : ℝ) < (n : ℝ) := by
            exact_mod_cast (show 0 < n by omega)
          exact ne_of_gt this
        have hsucc0 : ((n + 1 : ℕ) : ℝ) ≠ 0 := by
          have : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by
            exact_mod_cast (show 0 < n + 1 by omega)
          exact ne_of_gt this
        have hcastsucc : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by
          norm_num
        rw [hcastsucc] at hsucc0 ⊢
        field_simp [hn0, hsucc0]
        ring
  have hcast :
      Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hinv :
      Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) := by
    simpa [one_div] using
      ((tendsto_inv_atTop_zero :
          Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0)).comp hcast)
  refine ⟨hformula, ?_⟩
  apply hinv.congr'
  filter_upwards [eventually_ge_atTop 2] with n hn
  exact (hformula n hn).symm

theorem gap1 (p : ℕ → ℝ) (hp : ∀ n, p n = factor n) :
    ∀ n, p n - 1 = harmonicTerm n := by
  intro n
  rw [hp n]
  simp only [factor, harmonicTerm]
  ring

/-- Exercise 3069, gap 2. -/
theorem gap2 : ¬Summable harmonicTerm := by
  intro hs
  rcases hs with ⟨a, ha⟩
  have ht :
      Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, harmonicTerm i)
        atTop (𝓝 a) :=
    ha.tendsto_sum_nat
  rw [Metric.tendsto_atTop] at ht
  obtain ⟨N, hN⟩ := ht (1 / 8 : ℝ) (by norm_num)
  let m : ℕ := N + 1
  have hmN : N ≤ m := by
    simp [m]
  have htwomN : N ≤ 2 * m := by
    omega
  have hmclose := hN m hmN
  have htwomclose := hN (2 * m) htwomN
  have hmclose' :
      |(∑ i ∈ Finset.range m, harmonicTerm i) - a| < (1 / 8 : ℝ) := by
    simpa only [Real.dist_eq] using hmclose
  have htwomclose' :
      |(∑ i ∈ Finset.range (2 * m), harmonicTerm i) - a| <
        (1 / 8 : ℝ) := by
    simpa only [Real.dist_eq] using htwomclose
  have hdiff :
      -(1 / 4 : ℝ) <
        (∑ i ∈ Finset.range (2 * m), harmonicTerm i) -
          ∑ i ∈ Finset.range m, harmonicTerm i := by
    have hlow := (abs_lt.mp htwomclose').1
    have hupp := (abs_lt.mp hmclose').2
    linarith
  have hmpos : 0 < m := by
    simp [m]
  have hterm :
      ∀ i ∈ Finset.Ico m (2 * m),
        harmonicTerm i ≤ -(1 / (((2 * m : ℕ) : ℝ))) := by
    intro i hi
    have him : m ≤ i := (Finset.mem_Ico.mp hi).1
    have hiupper : i ≤ 2 * m := Nat.le_of_lt (Finset.mem_Ico.mp hi).2
    have hipos : 0 < i := lt_of_lt_of_le hmpos him
    have hiRpos : (0 : ℝ) < (i : ℝ) := by
      exact_mod_cast hipos
    have hiRupper : (i : ℝ) ≤ ((2 * m : ℕ) : ℝ) := by
      exact_mod_cast hiupper
    have hrecip :
        1 / (((2 * m : ℕ) : ℝ)) ≤ 1 / (i : ℝ) :=
      one_div_le_one_div_of_le hiRpos hiRupper
    unfold harmonicTerm
    exact neg_le_neg hrecip
  have hblock :
      (∑ i ∈ Finset.Ico m (2 * m), harmonicTerm i) ≤
        ∑ _i ∈ Finset.Ico m (2 * m),
          -(1 / (((2 * m : ℕ) : ℝ))) := by
    apply Finset.sum_le_sum
    intro i hi
    exact hterm i hi
  have hcard : (Finset.Ico m (2 * m)).card = m := by
    simp <;> omega
  have hm0 : (m : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hmpos)
  have hcasttwo : (((2 * m : ℕ) : ℝ)) = 2 * (m : ℝ) := by
    norm_num
  have hconst :
      (∑ _i ∈ Finset.Ico m (2 * m),
          -(1 / (((2 * m : ℕ) : ℝ)))) = -(1 / 2 : ℝ) := by
    rw [Finset.sum_const, hcard]
    simp only [nsmul_eq_mul]
    rw [hcasttwo]
    field_simp [hm0] <;> ring
  have hupper :
      (∑ i ∈ Finset.Ico m (2 * m), harmonicTerm i) ≤ -(1 / 2 : ℝ) := by
    calc
      (∑ i ∈ Finset.Ico m (2 * m), harmonicTerm i) ≤
          ∑ _i ∈ Finset.Ico m (2 * m),
            -(1 / (((2 * m : ℕ) : ℝ))) := hblock
      _ = -(1 / 2 : ℝ) := hconst
  have hsplit :
      (∑ i ∈ Finset.range (2 * m), harmonicTerm i) -
          ∑ i ∈ Finset.range m, harmonicTerm i =
        ∑ i ∈ Finset.Ico m (2 * m), harmonicTerm i := by
    rw [Finset.sum_Ico_eq_sub _ (by omega)]
  rw [hsplit] at hdiff
  linarith

/--
Exercise 3069, gap 3; divergence means failure to converge
to a nonzero product value.
-/
theorem gap3 : DivergentProduct := by
  unfold DivergentProduct NonzeroConvergentProduct
  rintro ⟨P, hP, hlim⟩
  have hPzero : P = 0 :=
    tendsto_nhds_unique hlim partialProduct_formula.2
  exact hP hPzero

/-- Exercise 3069, gap 4; replace the ellipsis and require `n ≥ 2`. -/
theorem gap4 (P : ℕ → ℝ) (hP : ∀ n, P n = partialProduct n) :
    ∀ n : ℕ, 2 ≤ n → P n = 1 / (n : ℝ) := by
  intro n hn
  calc
    P n = partialProduct n := hP n
    _ = 1 / (n : ℝ) := partialProduct_formula.1 n hn

/-- Exercise 3069, gap 5. -/
theorem gap5 (P : ℕ → ℝ) (hP : ∀ n, P n = partialProduct n) :
    Tendsto P atTop (𝓝 0) := by
  apply partialProduct_formula.2.congr'
  exact Filter.Eventually.of_forall (fun n => (hP n).symm)

/-- Exercise 3069, gap 6. -/
theorem gap6 :
    ∀ n : ℕ, 2 ≤ n → factor n ≠ 0 := by
  intro n hn
  unfold factor
  intro hzero
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by
    nlinarith
  field_simp [hn0] at hzero
  nlinarith

/-- Exercise 3069, gap 7. -/
theorem gap7 : DivergentProduct := by
  exact gap3

end

end ProofGap.Exercise3069
