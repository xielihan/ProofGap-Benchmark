import ProofGapLean.Prelude.Analysis
import ProofGapLean.Prelude.Discrete
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Choose.Cast

open scoped Topology

/-!
# Exercise 64

Semantic formalization of Exercise 64, gaps 1,...,14.
-/

namespace ProofGap.Exercise64

noncomputable section

def nthRootN (n : ℕ) : ℝ :=
  Real.rpow (n : ℝ) (1 / (n : ℝ))

def logBase (a x : ℝ) : ℝ :=
  Real.log x / Real.log a

def u (a : ℝ) (n : ℕ) : ℝ :=
  logBase a n / (n : ℝ)

private theorem binomial_quadratic_lower {x : ℝ} (hx : 0 < x) (n : ℕ) :
    (1 + x) ^ n >
      ((n : ℝ) * ((n : ℝ) - 1) / 2) * x ^ 2 := by
  by_cases hn : n < 2
  · interval_cases n <;>
      simp [Finset.sum_range_succ] <;> positivity
  · let f : ℕ → ℝ := fun j => (Nat.choose n j : ℝ) * x ^ j
    have hzero : 0 ∈ Finset.range (n + 1) := by simp
    have htwo : 2 ∈ (Finset.range (n + 1)).erase 0 := by
      simp
      omega
    have hle : f 2 ≤ ∑ j ∈ (Finset.range (n + 1)).erase 0, f j :=
      Finset.single_le_sum
        (f := f) (fun j hj => by
          unfold f
          positivity) htwo
    have hsum :=
      Finset.sum_erase_add (Finset.range (n + 1)) f hzero
    have hfzero : f 0 = 1 := by simp [f]
    rw [hfzero] at hsum
    have hftwo :
        f 2 = ((n : ℝ) * ((n : ℝ) - 1) / 2) * x ^ 2 := by
      unfold f
      rw [Nat.cast_choose_two ℝ n]
    have hbin :
        (1 + x) ^ n = ∑ j ∈ Finset.range (n + 1), f j := by
      unfold f
      rw [add_comm]
      simpa [mul_comm] using (add_pow x 1 n)
    rw [hbin, ← hftwo]
    linarith

/-- Exercise 64, gap 1; the valid range is restored. -/
theorem gap1 :
    ∀ n : ℕ, 1 < n → 1 < nthRootN n := by
  intro n hn
  unfold nthRootN
  exact Real.one_lt_rpow
    (by exact_mod_cast hn)
    (one_div_pos.mpr (by positivity))

/-- Exercise 64, gap 2; the estimate is eventual. -/
theorem gap2 :
    ∀ n : ℕ, 2 < n →
      (nthRootN n) ^ n >
        ((n : ℝ) ^ 2 / 4) * (nthRootN n - 1) ^ 2 := by
  intro n hn
  have hroot : 1 < nthRootN n := gap1 n (by omega)
  have hquad :=
    binomial_quadratic_lower (sub_pos.mpr hroot) n
  rw [show 1 + (nthRootN n - 1) = nthRootN n by ring] at hquad
  have hncast : (2 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hcoef :
      (n : ℝ) ^ 2 / 4 <
        (n : ℝ) * ((n : ℝ) - 1) / 2 := by
    nlinarith
  have hmul :
      (n : ℝ) ^ 2 / 4 * (nthRootN n - 1) ^ 2 <
        ((n : ℝ) * ((n : ℝ) - 1) / 2) *
          (nthRootN n - 1) ^ 2 :=
    mul_lt_mul_of_pos_right hcoef (sq_pos_of_pos (sub_pos.mpr hroot))
  exact hmul.trans hquad

/-- Exercise 64, gap 3. -/
theorem gap3
    (h2 : ∀ n : ℕ, 2 < n →
      (nthRootN n) ^ n >
        ((n : ℝ) ^ 2 / 4) * (nthRootN n - 1) ^ 2) :
    ∀ n : ℕ, 2 < n →
      (n : ℝ) >
        ((n : ℝ) ^ 2 / 4) * (nthRootN n - 1) ^ 2 := by
  intro n hn
  have hnzero : n ≠ 0 := by omega
  have heq : (nthRootN n) ^ n = (n : ℝ) := by
    unfold nthRootN
    simpa [one_div] using
      (Real.rpow_inv_natCast_pow (Nat.cast_nonneg n) hnzero)
  simpa [heq] using h2 n hn

/-- Exercise 64, gap 4. -/
theorem gap4 :
    ∀ n : ℕ, 1 < n → 0 < nthRootN n - 1 := by
  intro n hn
  exact sub_pos.mpr (gap1 n hn)

/-- Exercise 64, gap 5. -/
theorem gap5
    (h3 : ∀ n : ℕ, 2 < n →
      (n : ℝ) >
        ((n : ℝ) ^ 2 / 4) * (nthRootN n - 1) ^ 2)
    (h4 : ∀ n : ℕ, 1 < n → 0 < nthRootN n - 1) :
    ∀ n : ℕ, 2 < n →
      nthRootN n - 1 < 2 / Real.sqrt n := by
  intro n hn
  have hnpos : 0 < (n : ℝ) := by positivity
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnpos
  have hsquare : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) :=
    Real.sq_sqrt hnpos.le
  have hx : 0 < nthRootN n - 1 := h4 n (by omega)
  have hineq := h3 n hn
  have hfact :
      0 < (n : ℝ) * (4 - (n : ℝ) * (nthRootN n - 1) ^ 2) := by
    nlinarith
  have hsmall : (n : ℝ) * (nthRootN n - 1) ^ 2 < 4 := by
    rcases (mul_pos_iff.mp hfact) with hpos | hneg
    · nlinarith [hpos.2]
    · linarith
  have hsqprod :
      ((nthRootN n - 1) * Real.sqrt (n : ℝ)) ^ 2 =
        (n : ℝ) * (nthRootN n - 1) ^ 2 := by
    rw [mul_pow, hsquare]
    ring
  have hprod :
      (nthRootN n - 1) * Real.sqrt (n : ℝ) < 2 := by
    have hnonneg :
        0 ≤ (nthRootN n - 1) * Real.sqrt (n : ℝ) := by positivity
    nlinarith
  exact (lt_div_iff₀ hsqrt).2 hprod

/-- Exercise 64, gap 6. -/
theorem gap6 :
    ∀ n : ℕ, 0 < n → 0 < 2 / Real.sqrt n := by
  intro n hn
  exact div_pos (by norm_num) (Real.sqrt_pos.2 (by positivity))

/-- Exercise 64, gap 7. -/
theorem gap7
    (h4 : ∀ n : ℕ, 1 < n → 0 < nthRootN n - 1)
    (h5 : ∀ n : ℕ, 2 < n →
      nthRootN n - 1 < 2 / Real.sqrt n) :
    Tendsto nthRootN atTop (𝓝 1) := by
  have hsqrt :
      Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hinv :
      Tendsto (fun n : ℕ => (Real.sqrt (n : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hsqrt
  have hupper :
      Tendsto (fun n : ℕ => 2 / Real.sqrt (n : ℝ)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using hinv.const_mul 2
  have hdiff :
      Tendsto (fun n : ℕ => nthRootN n - 1) atTop (𝓝 0) := by
    apply squeeze_zero'
    · filter_upwards [Filter.eventually_gt_atTop 1] with n hn
      exact (h4 n hn).le
    · filter_upwards [Filter.eventually_gt_atTop 2] with n hn
      exact (h5 n hn).le
    · exact hupper
  have hadd := hdiff.add_const 1
  simpa using hadd

/-- Exercise 64, gap 8. -/
theorem gap8
    (a : ℝ)
    (ha : 1 < a) :
    ∀ ε : ℝ, 0 < ε → 1 < Real.rpow a ε := by
  intro ε hε
  exact Real.one_lt_rpow ha hε

/-- Exercise 64, gap 9; the rebound cutoff is repaired. -/
theorem gap9
    (a : ℝ)
    (ha : 1 < a)
    (h7 : Tendsto nthRootN atTop (𝓝 1))
    (h8 : ∀ ε : ℝ, 0 < ε → 1 < Real.rpow a ε) :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N < n → nthRootN n < Real.rpow a ε := by
  intro ε hε
  have hev : ∀ᶠ n in atTop, nthRootN n < Real.rpow a ε :=
    h7.eventually (Iio_mem_nhds (h8 ε hε))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hev
  exact ⟨N, fun n hn => hN n (Nat.le_of_lt hn)⟩

/-- Exercise 64, gap 10; the cutoff depends on `ε`. -/
theorem gap10
    (a : ℝ)
    (ha : 1 < a) :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N < n → 0 < u a n := by
  intro ε hε
  refine ⟨1, ?_⟩
  intro n hn
  unfold u logBase
  exact div_pos
    (div_pos (Real.log_pos (by exact_mod_cast hn)) (Real.log_pos ha))
    (by positivity)

/-- Exercise 64, gap 11; the cutoff depends on `ε`. -/
theorem gap11
    (a : ℝ)
    (ha : 1 < a)
    (h9 : ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N < n → nthRootN n < Real.rpow a ε) :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N < n → u a n < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := h9 ε hε
  refine ⟨max N 1, ?_⟩
  intro n hn
  have hNn : N < n := (le_max_left N 1).trans_lt hn
  have hone : 1 < n := (le_max_right N 1).trans_lt hn
  have hnpos : 0 < (n : ℝ) := by positivity
  have hapos : 0 < a := lt_trans zero_lt_one ha
  have hrootpos : 0 < nthRootN n := by
    unfold nthRootN
    exact Real.rpow_pos_of_pos hnpos _
  have harpowpos : 0 < Real.rpow a ε :=
    Real.rpow_pos_of_pos hapos _
  have hlog :=
    Real.log_lt_log hrootpos (hN n hNn)
  unfold nthRootN at hlog
  rw [show Real.log (Real.rpow (n : ℝ) (1 / (n : ℝ))) =
      (1 / (n : ℝ)) * Real.log (n : ℝ) from
        Real.log_rpow hnpos (1 / (n : ℝ)),
    show Real.log (Real.rpow a ε) = ε * Real.log a from
      Real.log_rpow hapos ε] at hlog
  have hlog' :
      Real.log (n : ℝ) / (n : ℝ) < ε * Real.log a := by
    simpa [div_eq_mul_inv, mul_comm] using hlog
  have hprod :
      Real.log (n : ℝ) < (ε * Real.log a) * (n : ℝ) :=
    (div_lt_iff₀ hnpos).mp hlog'
  unfold u logBase
  apply (div_lt_iff₀ hnpos).2
  apply (div_lt_iff₀ (Real.log_pos ha)).2
  nlinarith

/-- Exercise 64, gap 12; the cutoff depends on `ε`. -/
theorem gap12
    (a : ℝ) :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N < n → 0 < ε := by
  intro ε hε
  exact ⟨0, fun n hn => hε⟩

/-- Exercise 64, gap 13. -/
theorem gap13
    (a : ℝ)
    (ha : 1 < a)
    (h10 : ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N < n → 0 < u a n)
    (h11 : ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N < n → u a n < ε) :
    Tendsto (u a) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := h10 ε hε
  obtain ⟨N₁, hN₁⟩ := h11 ε hε
  refine ⟨max N₀ N₁ + 1, ?_⟩
  intro n hn
  have hmax : max N₀ N₁ < n :=
    lt_of_lt_of_le (Nat.lt_succ_self _) hn
  have h0 : N₀ < n :=
    lt_of_le_of_lt (le_max_left N₀ N₁) hmax
  have h1 : N₁ < n :=
    lt_of_le_of_lt (le_max_right N₀ N₁) hmax
  simp only [Real.dist_eq, sub_zero, abs_of_pos (hN₀ n h0)]
  exact hN₁ n h1

/-- Exercise 64, gap 14. -/
theorem gap14
    (a : ℝ)
    (ha : 1 < a)
    (h13 : Tendsto (u a) atTop (𝓝 0)) :
    Tendsto (u a) atTop (𝓝 0) := by
  exact h13

end

end ProofGap.Exercise64
