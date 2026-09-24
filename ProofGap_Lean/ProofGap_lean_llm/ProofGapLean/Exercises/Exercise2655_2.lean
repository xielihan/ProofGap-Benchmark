import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace ProofGap.Exercise2655_2

noncomputable section

open scoped BigOperators

def term (n : ℕ) : ℝ :=
  (2 : ℝ) ^ n / Nat.factorial (n + 1)

def remainder (N : ℕ) : ℝ :=
  ∑' l : ℕ, term (N + 1 + l)

def ratio (N : ℕ) : ℝ :=
  2 * Real.exp 1 / (N + 2)

def exactTailBound : ℝ :=
  term 12 * (7 / 6)

theorem gap1 :
    ∀ k : ℕ, 1 ≤ k →
      (Nat.factorial k : ℝ) > ((k : ℝ) / Real.exp 1) ^ k := by
  intro k hk
  have hkpos : 0 < (k : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hsqrt : 1 < Real.sqrt (2 * Real.pi * (k : ℝ)) := by
    have harg : (2 : ℝ) ≤ 2 * Real.pi * (k : ℝ) := by
      have hpi : 0 ≤ (Real.pi - 3) * (k : ℝ) :=
        mul_nonneg (sub_nonneg.mpr Real.pi_gt_three.le) hkpos.le
      have hkreal : (1 : ℝ) ≤ k := by exact_mod_cast hk
      nlinarith
    calc
      1 < Real.sqrt 2 := Real.one_lt_sqrt_two
      _ ≤ Real.sqrt (2 * Real.pi * (k : ℝ)) := by
        exact Real.sqrt_le_sqrt harg
  have hbase :
      0 < ((k : ℝ) / Real.exp 1) ^ k :=
    pow_pos (div_pos hkpos (Real.exp_pos 1)) _
  have hstrict :
      ((k : ℝ) / Real.exp 1) ^ k <
        Real.sqrt (2 * Real.pi * (k : ℝ)) *
          ((k : ℝ) / Real.exp 1) ^ k := by
    nlinarith [mul_pos (sub_pos.mpr hsqrt) hbase]
  exact hstrict.trans_le (Stirling.le_factorial_stirling k)

theorem gap2 (N : ℕ) :
    ∀ n : ℕ, N + 1 ≤ n →
      term n <
        (2 : ℝ) ^ n * (Real.exp 1 / (n + 1 : ℝ)) ^ (n + 1) := by
  intro n hn
  have hf := gap1 (n + 1) (by omega)
  have hbase :
      0 < (((n + 1 : ℕ) : ℝ) / Real.exp 1) ^ (n + 1) :=
    pow_pos (div_pos (by positivity) (Real.exp_pos 1)) _
  have hfac : 0 < (Nat.factorial (n + 1) : ℝ) := by positivity
  unfold term
  calc
    (2 : ℝ) ^ n / Nat.factorial (n + 1) <
        (2 : ℝ) ^ n /
          (((n + 1 : ℕ) : ℝ) / Real.exp 1) ^ (n + 1) :=
      div_lt_div_of_pos_left (pow_pos (by norm_num) _) hbase hf
    _ = (2 : ℝ) ^ n *
        (Real.exp 1 / (n + 1 : ℝ)) ^ (n + 1) := by
      push_cast
      rw [div_pow, div_pow, div_div_eq_mul_div]
      ring

theorem gap3 (N : ℕ) :
    ∀ n : ℕ, N + 1 ≤ n →
      (2 : ℝ) ^ n * (Real.exp 1 / (n + 1 : ℝ)) ^ (n + 1) =
        Real.exp 1 / (n + 1 : ℝ) *
          (2 * Real.exp 1 / (n + 1 : ℝ)) ^ n := by
  intro n hn
  simp only [pow_succ, div_pow, mul_pow]
  ring

theorem gap4 (N : ℕ) :
    ∀ n : ℕ, N + 1 ≤ n →
      Real.exp 1 / (n + 1 : ℝ) *
          (2 * Real.exp 1 / (n + 1 : ℝ)) ^ n ≤
        Real.exp 1 / (N + 2 : ℝ) * ratio N ^ n := by
  intro n hn
  unfold ratio
  have hden : (N + 2 : ℝ) ≤ (n + 1 : ℝ) := by
    exact_mod_cast (by omega : N + 2 ≤ n + 1)
  have hleft :
      Real.exp 1 / (n + 1 : ℝ) ≤ Real.exp 1 / (N + 2 : ℝ) := by
    exact div_le_div₀ (Real.exp_pos 1).le le_rfl (by positivity) hden
  have hratio :
      2 * Real.exp 1 / (n + 1 : ℝ) ≤
        2 * Real.exp 1 / (N + 2 : ℝ) := by
    exact div_le_div₀ (by positivity) le_rfl (by positivity) hden
  exact mul_le_mul hleft (pow_le_pow_left₀ (by positivity) hratio n)
    (by positivity) (by positivity)

theorem gap5 (N : ℕ) :
    ∀ n : ℕ, N + 1 ≤ n →
      term n < Real.exp 1 / (N + 2 : ℝ) * ratio N ^ n := by
  intro n hn
  exact (gap2 N n hn).trans_le ((gap3 N n hn).le.trans (gap4 N n hn))

theorem gap6 :
    ∀ n : ℕ, term (n + 1) / term n = 2 / (n + 2 : ℝ) := by
  intro n
  unfold term
  rw [Nat.factorial_succ, pow_succ]
  push_cast
  field_simp
  ring

theorem gap7 :
    ∀ n : ℕ, 12 ≤ n → term (n + 1) ≤ (1 / 7 : ℝ) * term n := by
  intro n hn
  have htpos : 0 < term n := by
    unfold term
    positivity
  have hratio : 2 / (n + 2 : ℝ) ≤ (1 / 7 : ℝ) := by
    have hden : (14 : ℝ) ≤ (n + 2 : ℝ) := by
      exact_mod_cast (by omega : 14 ≤ n + 2)
    rw [div_le_iff₀ (by positivity : 0 < (n + 2 : ℝ))]
    nlinarith
  have heq :
      term (n + 1) = (2 / (n + 2 : ℝ)) * term n := by
    apply (div_eq_iff htpos.ne').mp
    exact gap6 n
  rw [heq]
  exact mul_le_mul_of_nonneg_right hratio htpos.le

theorem gap8 (N : ℕ) (hN : N = 11) :
    remainder N ≤ term 12 * ∑' l : ℕ, (1 / 7 : ℝ) ^ l := by
  subst N
  have hpoint :
      ∀ l : ℕ, term (12 + l) ≤ term 12 * (1 / 7 : ℝ) ^ l := by
    intro l
    induction l with
    | zero => simp
    | succ l ih =>
        calc
          term (12 + (l + 1)) = term ((12 + l) + 1) := by
            congr 1
          _ ≤ (1 / 7 : ℝ) * term (12 + l) :=
            gap7 (12 + l) (by omega)
          _ ≤ (1 / 7 : ℝ) * (term 12 * (1 / 7 : ℝ) ^ l) :=
            mul_le_mul_of_nonneg_left ih (by norm_num)
          _ = term 12 * (1 / 7 : ℝ) ^ (l + 1) := by
            rw [pow_succ]
            ring
  have hgeom :
      Summable (fun l : ℕ => (1 / 7 : ℝ) ^ l) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  have hmajor :
      Summable (fun l : ℕ => term 12 * (1 / 7 : ℝ) ^ l) :=
    hgeom.mul_left (term 12)
  have htail :
      Summable (fun l : ℕ => term (12 + l)) :=
    hmajor.of_nonneg_of_le
      (fun l => by unfold term; positivity) hpoint
  calc
    remainder 11 = ∑' l : ℕ, term (12 + l) := by
      unfold remainder
      congr 1
    _ ≤ ∑' l : ℕ, term 12 * (1 / 7 : ℝ) ^ l :=
      htail.tsum_le_tsum hpoint hmajor
    _ = term 12 * ∑' l : ℕ, (1 / 7 : ℝ) ^ l := by
      exact hgeom.tsum_mul_left (term 12)

theorem gap9 :
    (∑' l : ℕ, (1 / 7 : ℝ) ^ l) = 7 / 6 := by
  rw [tsum_geometric_of_norm_lt_one (by norm_num :
    ‖(1 / 7 : ℝ)‖ < 1)]
  norm_num

theorem gap10 :
    exactTailBound =
      7 * (2 : ℝ) ^ 12 / (6 * Nat.factorial 13) := by
  norm_num [exactTailBound, term]

theorem gap11 :
    exactTailBound < (10 : ℝ) ^ (-5 : ℤ) := by
  norm_num [exactTailBound, term, zpow_neg]

theorem gap12 (N : ℕ) (hN : N = 11) :
    remainder N < (10 : ℝ) ^ (-5 : ℤ) := by
  calc
    remainder N ≤ term 12 * ∑' l : ℕ, (1 / 7 : ℝ) ^ l :=
      gap8 N hN
    _ = exactTailBound := by
      rw [gap9]
      rfl
    _ < (10 : ℝ) ^ (-5 : ℤ) := gap11

theorem gap13 (N : ℕ) (hN : N = 11) :
    11 ≤ N := by omega

end

end ProofGap.Exercise2655_2
