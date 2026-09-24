import ProofGapLean.Prelude.Elementary
import ProofGapLean.Prelude.Finite
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise1026

noncomputable section

open scoped BigOperators

def dyadic (k : ℕ) : ℝ := (2 : ℝ) ^ k

def product (n : ℕ) (x : ℝ) : ℝ :=
  ∏ k ∈ Finset.Icc 1 n, Real.cos (x / dyadic k)

def quotientForm (n : ℕ) (x : ℝ) : ℝ :=
  Real.sin x / (dyadic n * Real.sin (x / dyadic n))

def productDerivative (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n,
    (-(1 / dyadic k) * Real.sin (x / dyadic k)) *
      ∏ j ∈ (Finset.Icc 1 n).erase k, Real.cos (x / dyadic j)

def quotientDerivative (n : ℕ) (x : ℝ) : ℝ :=
  (Real.cos x * Real.sin (x / dyadic n) -
      (1 / dyadic n) * Real.sin x * Real.cos (x / dyadic n)) /
    (dyadic n * Real.sin (x / dyadic n) ^ 2)

def weightedTanSum (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n, (1 / dyadic k) * Real.tan (x / dyadic k)

def cot (x : ℝ) : ℝ := Real.cos x / Real.sin x

def regular (n : ℕ) (x : ℝ) : Prop :=
  1 ≤ n ∧ Real.sin x ≠ 0 ∧ Real.sin (x / dyadic n) ≠ 0 ∧
    ∀ k ∈ Finset.Icc 1 n, Real.cos (x / dyadic k) ≠ 0

private theorem exercise1026_dyadic_ne_zero (n : ℕ) : dyadic n ≠ 0 := by
  unfold dyadic
  exact pow_ne_zero n (by norm_num)

private theorem exercise1026_dyadic_succ (n : ℕ) :
    dyadic (n + 1) = 2 * dyadic n := by
  simp [dyadic, pow_succ, mul_comm]

private theorem exercise1026_product_succ (n : ℕ) (x : ℝ) :
    product (n + 1) x =
      product n x * Real.cos (x / dyadic (n + 1)) := by
  have hset :
      Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hnot : n + 1 ∉ Finset.Icc 1 n := by
    simp
  unfold product
  rw [hset, Finset.prod_insert hnot]
  ring

private theorem exercise1026_weighted_succ (n : ℕ) (x : ℝ) :
    weightedTanSum (n + 1) x =
      weightedTanSum n x +
        (1 / dyadic (n + 1)) * Real.tan (x / dyadic (n + 1)) := by
  have hset :
      Finset.Icc 1 (n + 1) = insert (n + 1) (Finset.Icc 1 n) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hnot : n + 1 ∉ Finset.Icc 1 n := by
    simp
  unfold weightedTanSum
  rw [hset, Finset.sum_insert hnot]
  ring

private theorem exercise1026_sine_product_identity (n : ℕ) (x : ℝ) :
    Real.sin x =
      dyadic n * Real.sin (x / dyadic n) * product n x := by
  induction n with
  | zero =>
      simp [product, dyadic]
  | succ n ih =>
      let u : ℝ := x / dyadic (n + 1)
      have harg : x / dyadic n = 2 * u := by
        dsimp [u]
        rw [exercise1026_dyadic_succ]
        field_simp [exercise1026_dyadic_ne_zero n] <;> ring
      have hdouble : Real.sin (2 * u) = 2 * Real.sin u * Real.cos u :=
        Real.sin_two_mul u
      calc
        Real.sin x =
            dyadic n * Real.sin (x / dyadic n) * product n x := ih
        _ = dyadic n * Real.sin (2 * u) * product n x := by rw [harg]
        _ = (2 * dyadic n) * Real.sin u *
              (product n x * Real.cos u) := by
            rw [hdouble]
            ring
        _ = dyadic (n + 1) * Real.sin (x / dyadic (n + 1)) *
              product (n + 1) x := by
            dsimp [u]
            rw [exercise1026_product_succ]
            rw [exercise1026_dyadic_succ]

private theorem exercise1026_tan_cot_double (t : ℝ)
    (hs : Real.sin t ≠ 0) (hc : Real.cos t ≠ 0) :
    Real.tan t = cot t - 2 * cot (2 * t) := by
  have hcos :
      Real.cos (2 * t) =
        Real.cos t * Real.cos t - Real.sin t * Real.sin t := by
    rw [show 2 * t = t + t by ring, Real.cos_add]
  have hsin :
      Real.sin (2 * t) = 2 * Real.sin t * Real.cos t := by
    simpa using Real.sin_two_mul t
  rw [Real.tan_eq_sin_div_cos]
  unfold cot
  rw [hcos, hsin]
  field_simp [hs, hc] <;> ring

private theorem exercise1026_weighted_telescope (n : ℕ) (x : ℝ)
    (hsx : Real.sin x ≠ 0)
    (hsn : Real.sin (x / dyadic n) ≠ 0)
    (hc : ∀ k ∈ Finset.Icc 1 n,
      Real.cos (x / dyadic k) ≠ 0) :
    weightedTanSum n x =
      (1 / dyadic n) * cot (x / dyadic n) - cot x := by
  revert x
  induction n with
  | zero =>
      intro x hsx hsn hc
      simp [weightedTanSum, dyadic]
  | succ n ih =>
      intro x hsx hsn hc
      have hlast_mem : n + 1 ∈ Finset.Icc 1 (n + 1) := by
        simp
      have hlast : Real.cos (x / dyadic (n + 1)) ≠ 0 :=
        hc (n + 1) hlast_mem
      have harg :
          x / dyadic n = 2 * (x / dyadic (n + 1)) := by
        rw [exercise1026_dyadic_succ]
        field_simp [exercise1026_dyadic_ne_zero n] <;> ring
      have hsn_prev : Real.sin (x / dyadic n) ≠ 0 := by
        rw [harg, Real.sin_two_mul]
        exact mul_ne_zero (mul_ne_zero (by norm_num) hsn) hlast
      have hc_prev :
          ∀ k ∈ Finset.Icc 1 n,
            Real.cos (x / dyadic k) ≠ 0 := by
        intro k hk
        apply hc k
        simp only [Finset.mem_Icc] at hk ⊢
        omega
      rw [exercise1026_weighted_succ]
      rw [ih x hsx hsn_prev hc_prev]
      rw [harg]
      rw [exercise1026_tan_cot_double
        (x / dyadic (n + 1)) hsn hlast]
      rw [exercise1026_dyadic_succ]
      field_simp [exercise1026_dyadic_ne_zero n] <;> ring

private theorem exercise1026_product_derivative_factor (n : ℕ) (x : ℝ)
    (hc : ∀ k ∈ Finset.Icc 1 n,
      Real.cos (x / dyadic k) ≠ 0) :
    productDerivative n x =
      -weightedTanSum n x * product n x := by
  unfold productDerivative weightedTanSum
  calc
    (∑ k ∈ Finset.Icc 1 n,
        (-(1 / dyadic k) * Real.sin (x / dyadic k)) *
          ∏ j ∈ (Finset.Icc 1 n).erase k,
            Real.cos (x / dyadic j)) =
      ∑ k ∈ Finset.Icc 1 n,
        (-((1 / dyadic k) * Real.tan (x / dyadic k))) *
          product n x := by
            apply Finset.sum_congr rfl
            intro k hk
            have hprod :
                product n x =
                  Real.cos (x / dyadic k) *
                    ∏ j ∈ (Finset.Icc 1 n).erase k,
                      Real.cos (x / dyadic j) := by
              unfold product
              rw [← Finset.insert_erase hk]
              simp
            rw [hprod, Real.tan_eq_sin_div_cos]
            field_simp [exercise1026_dyadic_ne_zero k, hc k hk] <;> ring
    _ = (∑ k ∈ Finset.Icc 1 n,
          -((1 / dyadic k) * Real.tan (x / dyadic k))) *
          product n x := by
            rw [Finset.sum_mul]
    _ = -(∑ k ∈ Finset.Icc 1 n,
          (1 / dyadic k) * Real.tan (x / dyadic k)) *
          product n x := by
            rw [Finset.sum_neg_distrib]

theorem gap1 (n : ℕ) (x : ℝ) (h : regular n x) :
    productDerivative n x = quotientDerivative n x := by
  rcases h with ⟨_, hsx, hsn, hc⟩
  have hden : dyadic n * Real.sin (x / dyadic n) ≠ 0 :=
    mul_ne_zero (exercise1026_dyadic_ne_zero n) hsn
  have hp :
      product n x = Real.sin x / (dyadic n * Real.sin (x / dyadic n)) := by
    apply (eq_div_iff hden).2
    rw [exercise1026_sine_product_identity n x]
    ring
  rw [exercise1026_product_derivative_factor n x hc]
  rw [exercise1026_weighted_telescope n x hsx hsn hc]
  rw [hp]
  unfold quotientDerivative cot
  field_simp [exercise1026_dyadic_ne_zero n, hsx, hsn] <;> ring

theorem gap2 (n : ℕ) (x : ℝ) (h : regular n x) :
    -weightedTanSum n x =
      cot x - (1 / dyadic n) * cot (x / dyadic n) := by
  rcases h with ⟨_, hsx, hsn, hc⟩
  rw [exercise1026_weighted_telescope n x hsx hsn hc]
  ring

theorem gap3 (n : ℕ) (x : ℝ) (h : regular n x) :
    weightedTanSum n x =
      (1 / dyadic n) * cot (x / dyadic n) - cot x := by
  rcases h with ⟨_, hsx, hsn, hc⟩
  exact exercise1026_weighted_telescope n x hsx hsn hc

end

end ProofGap.Exercise1026
