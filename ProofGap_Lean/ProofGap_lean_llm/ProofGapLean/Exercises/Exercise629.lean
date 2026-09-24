import ProofGapLean.Prelude.Sequences
import ProofGapLean.Prelude.Finite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise629

noncomputable section

def productSeq (x : ℝ) (n : ℕ) : ℝ :=
  (Finset.range (n + 1)).prod (fun k => 1 + x ^ (2 ^ k))
def powerSeq (x : ℝ) (n : ℕ) : ℝ := x ^ (2 ^ (n + 1))

/-- Exercise 629, gap 1. -/
private lemma doubleExponentStep (x : ℝ) (n : ℕ) :
    x ^ (2 ^ (n + 1)) = (x ^ (2 ^ n)) ^ 2 := by
  calc
    x ^ (2 ^ (n + 1)) = x ^ (2 ^ n * 2) := by rw [pow_succ]
    _ = (x ^ (2 ^ n)) ^ 2 := by rw [pow_mul]

theorem gap1 (x : ℝ) (hx : |x| < 1) :
    1 + x = (1 - x ^ 2) / (1 - x) := by
  have hxne : 1 - x ≠ 0 := by
    have hlt : x < 1 := (abs_lt.mp hx).2
    linarith
  apply (eq_div_iff hxne).2
  ring

/-- Exercise 629, gap 2. -/
theorem gap2 (x : ℝ) (hx : |x| < 1) :
    1 + x ^ 2 = (1 - x ^ 4) / (1 - x ^ 2) := by
  rcases abs_lt.mp hx with ⟨hlo, hhi⟩
  have hprod : 0 < (1 - x) * (1 + x) := by
    exact mul_pos (by linarith) (by linarith)
  have hx2 : x ^ 2 < 1 := by
    nlinarith
  have hxne : 1 - x ^ 2 ≠ 0 := by
    linarith
  apply (eq_div_iff hxne).2
  ring

/-- Exercise 629, gap 3. -/
theorem gap3 (x : ℝ) (hx : |x| < 1) (n : ℕ) :
    1 + x ^ (2 ^ n) =
      (1 - x ^ (2 ^ (n + 1))) / (1 - x ^ (2 ^ n)) := by
  have hexp_ne : (2 : ℕ) ^ n ≠ 0 := by
    exact pow_ne_zero n (by omega)
  have habspow : |x| ^ (2 ^ n) < 1 :=
    pow_lt_one₀ (abs_nonneg x) hx hexp_ne
  have hpow : x ^ (2 ^ n) < 1 := by
    calc
      x ^ (2 ^ n) ≤ |x ^ (2 ^ n)| := le_abs_self _
      _ = |x| ^ (2 ^ n) := by rw [abs_pow]
      _ < 1 := habspow
  have hxne : 1 - x ^ (2 ^ n) ≠ 0 := by
    linarith
  apply (eq_div_iff hxne).2
  rw [doubleExponentStep]
  ring

/-- Exercise 629, gap 4; replace the product ellipsis by `Finset.range`. -/
theorem gap4 (x : ℝ) (hx : |x| < 1) (n : ℕ) :
    productSeq x n = (1 - x ^ (2 ^ (n + 1))) / (1 - x) := by
  have hxne : 1 - x ≠ 0 := by
    have hlt : x < 1 := (abs_lt.mp hx).2
    linarith
  induction n with
  | zero =>
      simpa [productSeq] using gap1 x hx
  | succ n ih =>
      rw [show productSeq x (Nat.succ n) =
          productSeq x n * (1 + x ^ (2 ^ (n + 1))) by
            simp [productSeq, Finset.prod_range_succ]]
      rw [ih]
      rw [doubleExponentStep x (n + 1)]
      field_simp [hxne]
      ring

/-- Exercise 629, gap 5. -/
theorem gap5 (x : ℝ) (hx : |x| < 1) :
    Filter.Tendsto (powerSeq x) Filter.atTop (nhds 0) := by
  have hle : ∀ n : ℕ, n ≤ 2 ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ]
        have hp : 0 < (2 : ℕ) ^ n := pow_pos (by omega) n
        omega
  refine Metric.tendsto_atTop.2 ?_
  intro ε hε
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε hx
  refine ⟨N, ?_⟩
  intro n hn
  have hindex : N ≤ 2 ^ (n + 1) :=
    hn.trans ((Nat.le_succ n).trans (hle (n + 1)))
  have hbound : |x| ^ (2 ^ (n + 1)) ≤ |x| ^ N :=
    pow_le_pow_of_le_one (abs_nonneg x) (le_of_lt hx) hindex
  rw [Real.dist_eq, sub_zero, powerSeq, abs_pow]
  exact lt_of_le_of_lt hbound hN

/-- Exercise 629, gap 6. -/
theorem gap6 (x : ℝ) (hx : |x| < 1) :
    Filter.Tendsto (productSeq x) Filter.atTop (nhds (1 / (1 - x))) := by
  have hconst : Filter.Tendsto (fun _ : ℕ => (1 : ℝ))
      Filter.atTop (nhds 1) := tendsto_const_nhds
  have hinv : Filter.Tendsto (fun _ : ℕ => (1 - x)⁻¹)
      Filter.atTop (nhds ((1 - x)⁻¹)) := tendsto_const_nhds
  have ht := (hconst.sub (gap5 x hx)).mul hinv
  have hfun : productSeq x =
      (fun n => (1 - powerSeq x n) * (1 - x)⁻¹) := by
    funext n
    rw [gap4 x hx n]
    rfl
  rw [hfun]
  simpa only [div_eq_mul_inv, sub_zero, one_mul] using ht

end

end ProofGap.Exercise629
