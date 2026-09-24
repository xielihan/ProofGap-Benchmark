import ProofGapLean.Prelude.Full
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

open scoped Topology

/-!
# Exercise 63

Semantic formalization of Exercise 63, gaps 1,...,14.
-/

namespace ProofGap.Exercise63

noncomputable section

def root (a : ℝ) (n : ℕ) : ℝ :=
  Real.rpow a (1 / (n : ℝ))

def cutoff (a ε : ℝ) : ℕ :=
  Nat.floor ((a - 1) / ε)

def Converges (a : ℝ) : Prop :=
  Tendsto (root a) atTop (𝓝 1)

private theorem converges_of_pos {a : ℝ} (ha : 0 < a) :
    Converges a := by
  have hexp :
      Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  unfold Converges root
  simpa using
    (tendsto_const_nhds (x := a)).rpow hexp (Or.inl ha.ne')

/-- Exercise 63, gap 1. -/
theorem gap1
    (a : ℝ)
    (ha : a = 1) :
    Converges a := by
  subst a
  exact converges_of_pos (by norm_num)

/-- Exercise 63, gap 2; positivity conditions are restored. -/
theorem gap2
    (a : ℝ) :
    ∀ (ε : ℝ) (n : ℕ), 1 < a → 0 < ε → 1 < n →
      (1 + ε) ^ n > 1 + (n : ℝ) * ε := by
  intro ε n ha hε hn
  have hbern :
      1 + ((n - 1 : ℕ) : ℝ) * ε ≤ (1 + ε) ^ (n - 1) := by
    simpa using one_add_mul_le_pow (by linarith : (-2 : ℝ) ≤ ε) (n - 1)
  have hmul :
      (1 + ((n - 1 : ℕ) : ℝ) * ε) * (1 + ε) ≤
        (1 + ε) ^ (n - 1) * (1 + ε) :=
    mul_le_mul_of_nonneg_right hbern (by linarith)
  rw [← pow_succ] at hmul
  have hnsub : (n - 1 : ℕ) + 1 = n := by omega
  rw [hnsub] at hmul
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  rw [hcast] at hmul
  have hnsubpos : 0 < (n : ℝ) - 1 := by
    have : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    linarith
  have hpositive : 0 < ((n : ℝ) - 1) * ε ^ 2 :=
    mul_pos hnsubpos (sq_pos_of_pos hε)
  have hstrict :
      1 + (n : ℝ) * ε <
        (1 + ((n : ℝ) - 1) * ε) * (1 + ε) := by
    nlinarith
  exact hstrict.trans_le hmul

/-- Exercise 63, gap 3; the cutoff depends on `ε`. -/
theorem gap3
    (a : ℝ) :
    ∀ ε : ℝ, 0 < ε → ∀ n : ℕ, cutoff a ε < n →
      1 + (n : ℝ) * ε > a := by
  intro ε hε n hn
  unfold cutoff at hn
  have hsuc :
      Nat.floor ((a - 1) / ε) + 1 ≤ n :=
    Nat.succ_le_iff.mpr hn
  have hcast :
      ((Nat.floor ((a - 1) / ε) : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by
    exact_mod_cast hsuc
  have hfloor :
      (a - 1) / ε <
        ((Nat.floor ((a - 1) / ε) : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hratio : (a - 1) / ε < (n : ℝ) :=
    hfloor.trans_le hcast
  have := (div_lt_iff₀ hε).mp hratio
  nlinarith

/-- Exercise 63, gap 4. -/
theorem gap4
    (a : ℝ)
    (h2 : ∀ (ε : ℝ) (n : ℕ), 1 < a → 0 < ε → 1 < n →
      (1 + ε) ^ n > 1 + (n : ℝ) * ε)
    (h3 : ∀ ε : ℝ, 0 < ε → ∀ n : ℕ, cutoff a ε < n →
      1 + (n : ℝ) * ε > a) :
    ∀ ε : ℝ, 0 < ε → ∀ n : ℕ, cutoff a ε < n →
      (1 + ε) ^ n > a := by
  intro ε hε n hn
  exact (h3 ε hε n hn).trans_le
    (one_add_mul_le_pow (by linarith : (-2 : ℝ) ≤ ε) n)

/-- Exercise 63, gap 5. -/
theorem gap5
    (a : ℝ)
    (ha : 1 < a) :
    ∀ ε : ℝ, 0 < ε → ∀ n : ℕ, cutoff a ε < n →
      1 < root a n := by
  intro ε hε n hn
  unfold root
  have hnpos : 0 < n := by
    have hcut : 0 ≤ cutoff a ε := Nat.zero_le _
    omega
  exact Real.one_lt_rpow ha (one_div_pos.mpr (Nat.cast_pos.mpr hnpos))

/-- Exercise 63, gap 6. -/
theorem gap6
    (a : ℝ)
    (ha : 1 < a)
    (h4 : ∀ ε : ℝ, 0 < ε → ∀ n : ℕ, cutoff a ε < n →
      (1 + ε) ^ n > a) :
    ∀ ε : ℝ, 0 < ε → ∀ n : ℕ, cutoff a ε < n →
      root a n < 1 + ε := by
  intro ε hε n hn
  have hnpos : 0 < n := by
    have hcut : 0 ≤ cutoff a ε := Nat.zero_le _
    omega
  have hpow := h4 ε hε n hn
  have hr :=
    Real.rpow_lt_rpow (by linarith : 0 ≤ a) hpow
      (one_div_pos.mpr (Nat.cast_pos.mpr hnpos))
  unfold root
  simpa [Real.pow_rpow_inv_natCast (by linarith : 0 ≤ 1 + ε)
    (Nat.ne_of_gt hnpos)] using hr

/-- Exercise 63, gap 7. -/
theorem gap7
    (a : ℝ) :
    ∀ ε : ℝ, 0 < ε → ∀ n : ℕ, cutoff a ε < n → 1 < 1 + ε := by
  intro ε hε n hn
  linarith

/-- Exercise 63, gap 8. -/
theorem gap8
    (a : ℝ)
    (ha : 1 < a)
    (h5 : ∀ ε : ℝ, 0 < ε → ∀ n : ℕ, cutoff a ε < n →
      1 < root a n)
    (h6 : ∀ ε : ℝ, 0 < ε → ∀ n : ℕ, cutoff a ε < n →
      root a n < 1 + ε) :
    ∀ ε : ℝ, 0 < ε → ∀ n : ℕ, cutoff a ε < n →
      |root a n - 1| < ε := by
  intro ε hε n hn
  rw [abs_of_pos (sub_pos.mpr (h5 ε hε n hn))]
  linarith [h6 ε hε n hn]

/-- Exercise 63, gap 9. -/
theorem gap9
    (a : ℝ)
    (ha : 1 < a)
    (h8 : ∀ ε : ℝ, 0 < ε → ∀ n : ℕ, cutoff a ε < n →
      |root a n - 1| < ε) :
    Converges a := by
  unfold Converges
  rw [Metric.tendsto_atTop]
  intro ε hε
  refine ⟨cutoff a ε + 1, ?_⟩
  intro n hn
  simpa [Real.dist_eq] using
    h8 ε hε n (lt_of_lt_of_le (Nat.lt_succ_self _) hn)

/-- Exercise 63, gap 10. -/
theorem gap10
    (a : ℝ)
    (ha0 : 0 < a)
    (ha1 : a < 1) :
    1 < 1 / a := by
  apply (lt_div_iff₀ ha0).2
  simpa using ha1

/-- Exercise 63, gap 11. -/
theorem gap11
    (a : ℝ)
    (ha0 : 0 < a)
    (ha1 : a < 1) :
    ∀ n : ℕ, root a n = 1 / root (1 / a) n := by
  intro n
  unfold root
  rw [show 1 / a = a⁻¹ by simp]
  rw [show Real.rpow a⁻¹ (1 / (n : ℝ)) =
    (Real.rpow a (1 / (n : ℝ)))⁻¹ from
      Real.inv_rpow ha0.le (1 / (n : ℝ))]
  simp

/-- Exercise 63, gap 12. -/
theorem gap12
    (a : ℝ)
    (ha0 : 0 < a)
    (ha1 : a < 1)
    (h10 : 1 < 1 / a)
    (h11 : ∀ n : ℕ, root a n = 1 / root (1 / a) n) :
    Converges a := by
  exact converges_of_pos ha0

/-- Exercise 63, gap 13. -/
theorem gap13
    (a : ℝ)
    (ha : 0 < a)
    (h1 : a = 1 → Converges a)
    (h9 : 1 < a → Converges a)
    (h12 : 0 < a → a < 1 → Converges a) :
    Converges a := by
  rcases lt_trichotomy a 1 with ha1 | haeq | h1a
  · exact h12 ha ha1
  · exact h1 haeq
  · exact h9 h1a

/-- Exercise 63, gap 14. -/
theorem gap14
    (a : ℝ)
    (ha : 0 < a)
    (h13 : 0 < a → Converges a) :
    Converges a := by
  exact h13 ha

end

end ProofGap.Exercise63
