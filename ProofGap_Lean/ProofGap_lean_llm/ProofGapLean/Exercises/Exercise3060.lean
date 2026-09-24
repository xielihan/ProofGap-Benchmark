import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd

namespace ProofGap.Exercise3060

noncomputable section

open Filter
open scoped BigOperators Topology

def normalizedSinc (x : ℝ) : ℝ :=
  if x = 0 then 1 else Real.sin x / x

def sineFactor (x : ℝ) (n : ℕ) : ℝ :=
  1 - x ^ 2 / ((n : ℝ) ^ 2 * Real.pi ^ 2)

def sinePartialProduct (x : ℝ) (N : ℕ) : ℝ :=
  ∏ n ∈ Finset.Icc 1 N, sineFactor x n

def factorA (n : ℕ) : ℝ :=
  1 - 1 / ((3 * n : ℕ) : ℝ) ^ 2

def factorB (n : ℕ) : ℝ :=
  (((3 * n : ℕ) : ℝ) - 1) * (((3 * n : ℕ) : ℝ) + 1) /
    (((3 * n : ℕ) : ℝ) ^ 2)

def factorC (n : ℕ) : ℝ :=
  (((3 * n : ℕ) : ℝ) / (((3 * n : ℕ) : ℝ) - 1)) *
    (((3 * n : ℕ) : ℝ) / (((3 * n : ℕ) : ℝ) + 1))

def partialA (N : ℕ) : ℝ := ∏ n ∈ Finset.Icc 1 N, factorA n
def partialB (N : ℕ) : ℝ := ∏ n ∈ Finset.Icc 1 N, factorB n
def partialC (N : ℕ) : ℝ := ∏ n ∈ Finset.Icc 1 N, factorC n

def HasProductA (L : ℝ) : Prop := Tendsto partialA atTop (𝓝 L)
def HasProductB (L : ℝ) : Prop := Tendsto partialB atTop (𝓝 L)
def HasProductC (L : ℝ) : Prop := Tendsto partialC atTop (𝓝 L)

private theorem sinePartialProduct_eq_range (x : ℝ) (N : ℕ) :
    sinePartialProduct x N =
      ∏ j ∈ Finset.range N,
        (1 - (x / Real.pi) ^ 2 / (((j : ℝ) + 1) ^ 2)) := by
  unfold sinePartialProduct
  rw [show Finset.Icc 1 N = Finset.Ico 1 (N + 1) by
    ext n
    simp]
  rw [Finset.prod_Ico_eq_prod_range]
  apply Finset.prod_congr rfl
  intro j hj
  unfold sineFactor
  push_cast
  field_simp [Real.pi_ne_zero, Nat.cast_add_one_ne_zero]
  <;> ring

private theorem factorA_eq_sineFactor (n : ℕ) (hn : 1 ≤ n) :
    factorA n = sineFactor (Real.pi / 3) n := by
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  unfold factorA sineFactor
  push_cast
  field_simp [Real.pi_ne_zero, hn0]

private theorem partialA_eq_sinePartialProduct (N : ℕ) :
    partialA N = sinePartialProduct (Real.pi / 3) N := by
  unfold partialA sinePartialProduct
  apply Finset.prod_congr rfl
  intro n hn
  exact factorA_eq_sineFactor n (Finset.mem_Icc.mp hn).1

private theorem factorA_eq_factorB (n : ℕ) (hn : 1 ≤ n) :
    factorA n = factorB n := by
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  unfold factorA factorB
  push_cast
  field_simp [hn0]
  ring

private theorem partialB_eq_partialA (N : ℕ) : partialB N = partialA N := by
  unfold partialB partialA
  apply Finset.prod_congr rfl
  intro n hn
  exact (factorA_eq_factorB n (Finset.mem_Icc.mp hn).1).symm

private theorem factorC_eq_inv_factorB (n : ℕ) (hn : 1 ≤ n) :
    factorC n = (factorB n)⁻¹ := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hzero : (3 * (n : ℝ)) ≠ 0 := by nlinarith
  have hminus : (3 * (n : ℝ) - 1) ≠ 0 := by nlinarith
  have hplus : (3 * (n : ℝ) + 1) ≠ 0 := by nlinarith
  unfold factorC factorB
  push_cast
  field_simp [hzero, hminus, hplus]

private theorem partialC_eq_inv_partialB (N : ℕ) :
    partialC N = (partialB N)⁻¹ := by
  unfold partialC partialB
  calc
    (∏ n ∈ Finset.Icc 1 N, factorC n) =
        ∏ n ∈ Finset.Icc 1 N, (factorB n)⁻¹ := by
      apply Finset.prod_congr rfl
      intro n hn
      exact factorC_eq_inv_factorB n (Finset.mem_Icc.mp hn).1
    _ = (∏ n ∈ Finset.Icc 1 N, factorB n)⁻¹ :=
      Finset.prod_inv_distrib _

theorem gap1 (x : ℝ) :
    Real.sin x = x * normalizedSinc x ∧
      Tendsto (sinePartialProduct x) atTop (𝓝 (normalizedSinc x)) := by
  constructor
  · by_cases hx : x = 0
    · simp [hx, normalizedSinc]
    · rw [normalizedSinc, if_neg hx]
      field_simp
  · by_cases hx : x = 0
    · subst x
      have heq : sinePartialProduct 0 = fun _ : ℕ => (1 : ℝ) := by
        funext N
        simp [sinePartialProduct, sineFactor]
      rw [heq]
      simpa [normalizedSinc] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
    · have h := Real.tendsto_euler_sin_prod (x / Real.pi)
      have hscale : Real.pi * (x / Real.pi) = x := by
        field_simp [Real.pi_ne_zero]
      have h' :
          Tendsto
            (fun N : ℕ => x *
              ∏ j ∈ Finset.range N,
                (1 - (x / Real.pi) ^ 2 / (((j : ℝ) + 1) ^ 2)))
            atTop (𝓝 (Real.sin x)) := by
        simpa only [hscale] using h
      have hinv := h'.const_mul x⁻¹
      rw [show sinePartialProduct x = fun N : ℕ =>
          ∏ j ∈ Finset.range N,
            (1 - (x / Real.pi) ^ 2 / (((j : ℝ) + 1) ^ 2)) by
        funext N
        exact sinePartialProduct_eq_range x N]
      simpa [normalizedSinc, hx, div_eq_mul_inv, mul_assoc, mul_comm] using hinv

theorem gap2 :
    Real.sin (Real.pi / 3) =
      Real.pi / 3 * (Real.sin (Real.pi / 3) / (Real.pi / 3)) ∧
      HasProductA (Real.sin (Real.pi / 3) / (Real.pi / 3)) := by
  constructor
  · field_simp [Real.pi_ne_zero]
  · unfold HasProductA
    rw [show partialA = sinePartialProduct (Real.pi / 3) by
      funext N
      exact partialA_eq_sinePartialProduct N]
    have h := (gap1 (Real.pi / 3)).2
    simpa [normalizedSinc, Real.pi_ne_zero] using h

theorem gap3 :
    (∀ n : ℕ, 1 ≤ n → factorA n = factorB n) ∧
      HasProductA (Real.sin (Real.pi / 3) / (Real.pi / 3)) ∧
      HasProductB (Real.sin (Real.pi / 3) / (Real.pi / 3)) := by
  refine ⟨factorA_eq_factorB, gap2.2, ?_⟩
  unfold HasProductB
  rw [show partialB = partialA by
    funext N
    exact partialB_eq_partialA N]
  exact gap2.2

theorem gap4 :
    Real.sin (Real.pi / 3) =
      Real.pi / 3 * (Real.sin (Real.pi / 3) / (Real.pi / 3)) ∧
      HasProductB (Real.sin (Real.pi / 3) / (Real.pi / 3)) := by
  exact ⟨gap2.1, gap3.2.2⟩

theorem gap5 :
    HasProductC ((Real.pi / 3) / Real.sin (Real.pi / 3)) := by
  have hsin : Real.sin (Real.pi / 3) ≠ 0 := by
    rw [Real.sin_pi_div_three]
    positivity
  have hpi : Real.pi / 3 ≠ 0 := div_ne_zero Real.pi_ne_zero (by norm_num)
  have hlim : Real.sin (Real.pi / 3) / (Real.pi / 3) ≠ 0 :=
    div_ne_zero hsin hpi
  have hinv := gap4.2.inv₀ hlim
  unfold HasProductC
  rw [show partialC = fun N : ℕ => (partialB N)⁻¹ by
    funext N
    exact partialC_eq_inv_partialB N]
  convert hinv using 1
  field_simp [hsin, hpi]

theorem gap6 :
    (Real.pi / 3) / Real.sin (Real.pi / 3) =
      2 * Real.pi / (3 * Real.sqrt 3) := by
  rw [Real.sin_pi_div_three]
  have hsqrt : Real.sqrt 3 ≠ 0 := by positivity
  field_simp [hsqrt]

theorem gap7 :
    HasProductC (2 * Real.pi / (3 * Real.sqrt 3)) := by
  rw [← gap6]
  exact gap5

theorem gap8 :
    HasProductC (2 * Real.pi / (3 * Real.sqrt 3)) := by
  exact gap7

end

end ProofGap.Exercise3060
