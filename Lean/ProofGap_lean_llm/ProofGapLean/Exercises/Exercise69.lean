import ProofGapLean.Prelude.Sequences
import ProofGapLean.Prelude.Discrete
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Topology.Instances.Real.Lemmas

open Filter Topology

/-!
# Exercise 69

Semantic formalization of `proof_gap/exercise_69/{1,...,32}.txt`.
-/

namespace ProofGap.Exercise69

noncomputable section

def x (n : ℕ) : ℝ :=
  (1 + 1 / (n : ℝ)) ^ n

def y (n : ℕ) : ℝ :=
  (1 + 1 / (n : ℝ)) ^ (n + 1)

def binomialExpansion (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1),
    (Nat.choose n j : ℝ) * (1 / (n : ℝ)) ^ j

def factorialExpansion (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1),
    (1 / (Nat.factorial j : ℝ)) *
      ∏ i ∈ Finset.Ico 1 j, (1 - (i : ℝ) / (n : ℝ))

def geometricUpper (n : ℕ) : ℝ :=
  2 + ∑ j ∈ Finset.range (n - 1), 1 / (2 : ℝ) ^ (j + 1)

def MonoIncOnPos (u : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, 0 < n → u n ≤ u (n + 1)

def MonoDecOnPos (u : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, 0 < n → u (n + 1) ≤ u n

def BoundedAboveOnPos (u : ℕ → ℝ) : Prop :=
  ∃ M : ℝ, ∀ n : ℕ, 0 < n → u n ≤ M

def BoundedBelowOnPos (u : ℕ → ℝ) : Prop :=
  ∃ M : ℝ, ∀ n : ℕ, 0 < n → M ≤ u n

def onePlusReciprocal (n : ℕ) : ℝ :=
  1 + 1 / (n : ℝ)

/-- Source: `proof_gap/exercise_69/1.txt`; the positive-index domain is restored. -/
theorem gap1 :
    ∀ n : ℕ, 0 < n → x n = (1 + 1 / (n : ℝ)) ^ n := by
  intro n _
  rfl

/-- Source: `proof_gap/exercise_69/2.txt`; the ellipsis is an explicit binomial sum. -/
theorem gap2 :
    ∀ n : ℕ, 0 < n →
      (1 + 1 / (n : ℝ)) ^ n = binomialExpansion n := by
  intro n _
  rw [add_comm]
  simp [binomialExpansion, add_pow, mul_comm]

/-- Source: `proof_gap/exercise_69/3.txt`. -/
theorem gap3
    (h2 : ∀ n : ℕ, 0 < n →
      (1 + 1 / (n : ℝ)) ^ n = binomialExpansion n) :
    ∀ n : ℕ, 0 < n → x n = binomialExpansion n := by
  intro n hn
  exact (gap1 n hn).trans (h2 n hn)

private theorem binomial_term_eq_factorial_term
    {n j : ℕ} (hn : 0 < n) (hj : j ≤ n) :
    (Nat.choose n j : ℝ) * (1 / (n : ℝ)) ^ j =
      (1 / (Nat.factorial j : ℝ)) *
        ∏ i ∈ Finset.Ico 1 j, (1 - (i : ℝ) / (n : ℝ)) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hfac0 : (Nat.factorial j : ℝ) ≠ 0 := by positivity
  have hdescCast :
      (Nat.descFactorial n j : ℝ) =
        (Nat.factorial j : ℝ) * (Nat.choose n j : ℝ) := by
    exact_mod_cast Nat.descFactorial_eq_factorial_mul_choose n j
  have hchoose :
      (Nat.choose n j : ℝ) =
        (Nat.descFactorial n j : ℝ) / (Nat.factorial j : ℝ) := by
    apply (eq_div_iff hfac0).2
    simpa [mul_comm] using hdescCast.symm
  have hdescProd :
      (Nat.descFactorial n j : ℝ) =
        ∏ i ∈ Finset.range j, ((n - i : ℕ) : ℝ) := by
    exact_mod_cast Nat.descFactorial_eq_prod_range n j
  have hprodRange :
      (∏ i ∈ Finset.range j, (1 - (i : ℝ) / (n : ℝ))) =
        (Nat.descFactorial n j : ℝ) * (1 / (n : ℝ)) ^ j := by
    calc
      (∏ i ∈ Finset.range j, (1 - (i : ℝ) / (n : ℝ))) =
          ∏ i ∈ Finset.range j,
            ((n - i : ℕ) : ℝ) * (1 / (n : ℝ)) := by
              apply Finset.prod_congr rfl
              intro i hi
              have hin : i ≤ n := (Finset.mem_range.mp hi).le.trans hj
              rw [Nat.cast_sub hin]
              field_simp
      _ = (∏ i ∈ Finset.range j, ((n - i : ℕ) : ℝ)) *
          ∏ _i ∈ Finset.range j, (1 / (n : ℝ)) := by
            rw [Finset.prod_mul_distrib]
      _ = (Nat.descFactorial n j : ℝ) * (1 / (n : ℝ)) ^ j := by
        rw [← hdescProd]
        simp
  have hrangeIco :
      (∏ i ∈ Finset.range j, (1 - (i : ℝ) / (n : ℝ))) =
        ∏ i ∈ Finset.Ico 1 j, (1 - (i : ℝ) / (n : ℝ)) := by
    by_cases hj0 : j = 0
    · subst j
      simp
    · rw [Finset.prod_range_eq_mul_Ico
        (fun i => (1 - (i : ℝ) / (n : ℝ))) (Nat.pos_of_ne_zero hj0)]
      norm_num
  rw [← hrangeIco, hprodRange, hchoose]
  field_simp

/-- Source: `proof_gap/exercise_69/4.txt`; all omitted products are finite. -/
theorem gap4 :
    ∀ n : ℕ, 0 < n → x n = factorialExpansion n := by
  intro n hn
  rw [gap1 n hn, gap2 n hn]
  unfold binomialExpansion factorialExpansion
  apply Finset.sum_congr rfl
  intro j hj
  exact binomial_term_eq_factorial_term hn (by
    have := Finset.mem_range.mp hj
    omega)

/-- Source: `proof_gap/exercise_69/5.txt`. -/
theorem gap5 :
    MonoIncOnPos x := by
  intro n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  let A : ℝ := 1 + 1 / (n : ℝ)
  let B : ℝ := 1 + 1 / ((n : ℝ) + 1)
  let T : ℝ := 1 / ((n : ℝ) + 1) ^ 2
  have hA : 0 < A := by
    dsimp [A]
    positivity
  have hB : 0 < B := by
    dsimp [B]
    positivity
  have hT : 0 < T := by
    dsimp [T]
    positivity
  have hTlt : T < 1 := by
    dsimp [T]
    rw [div_lt_iff₀ (sq_pos_of_pos (by linarith : (0 : ℝ) < n + 1))]
    nlinarith
  have hratio : 1 - T = B / A := by
    dsimp [A, B, T]
    field_simp
    ring
  have hbern :
      1 + (n : ℝ) * (-T) ≤ (1 - T) ^ n := by
    simpa [sub_eq_add_neg] using
      (one_add_mul_le_pow (a := -T) (by linarith : (-2 : ℝ) ≤ -T) n)
  have hmul := mul_le_mul_of_nonneg_left hbern hB.le
  have hone : 1 ≤ B * (1 + (n : ℝ) * (-T)) := by
    dsimp [B, T]
    have hnp1 : (0 : ℝ) < n + 1 := by linarith
    field_simp
    nlinarith [sq_nonneg (n : ℝ)]
  have hchain : 1 ≤ B * (1 - T) ^ n := hone.trans hmul
  have hscaled :=
    mul_le_mul_of_nonneg_right hchain (pow_nonneg hA.le n)
  have hfinal :
      (B * (1 - T) ^ n) * A ^ n = B ^ (n + 1) := by
    rw [hratio, div_pow]
    field_simp
    rw [pow_succ]
    ring
  rw [hfinal] at hscaled
  simpa [x, A, B, Nat.cast_add, Nat.cast_one] using hscaled

private theorem factorial_term_lt_geometric
    {n k : ℕ} (hn : 1 < n) (hk : 2 ≤ k) (hkn : k ≤ n) :
    (1 / (Nat.factorial k : ℝ)) *
        ∏ i ∈ Finset.Ico 1 k, (1 - (i : ℝ) / (n : ℝ)) <
      1 / (2 : ℝ) ^ (k - 1) := by
  have hnR : (0 : ℝ) < n := by positivity
  have hfactorPos :
      ∀ i ∈ Finset.Ico 1 k, 0 < 1 - (i : ℝ) / (n : ℝ) := by
    intro i hi
    have hilk : i < k := (Finset.mem_Ico.mp hi).2
    have hin : i < n := hilk.trans_le hkn
    rw [sub_pos, div_lt_one hnR]
    exact_mod_cast hin
  have hfactorLe :
      ∀ i ∈ Finset.Ico 1 k, 1 - (i : ℝ) / (n : ℝ) ≤ 1 := by
    intro i _
    have : (0 : ℝ) ≤ i := by positivity
    exact sub_le_self _ (div_nonneg this hnR.le)
  have hprod :
      (∏ i ∈ Finset.Ico 1 k, (1 - (i : ℝ) / (n : ℝ))) < 1 := by
    have hstrict :
        ∃ i ∈ Finset.Ico 1 k, 1 - (i : ℝ) / (n : ℝ) < 1 := by
      refine ⟨1, Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩, ?_⟩
      have : (0 : ℝ) < 1 / (n : ℝ) := one_div_pos.mpr hnR
      linarith
    have hp := Finset.prod_lt_prod hfactorPos hfactorLe hstrict
    simpa using hp
  have hterm :
      (1 / (Nat.factorial k : ℝ)) *
          (∏ i ∈ Finset.Ico 1 k, (1 - (i : ℝ) / (n : ℝ))) <
        1 / (Nat.factorial k : ℝ) := by
    have hcoeff : 0 < 1 / (Nat.factorial k : ℝ) := by positivity
    nlinarith
  have hfactNat : 2 ^ (k - 1) ≤ Nat.factorial k := by
    calc
      2 ^ (k - 1) =
          Nat.factorial 1 * (1 + 1) ^ (k - 1) := by norm_num
      _ ≤ Nat.factorial (1 + (k - 1)) :=
        Nat.factorial_mul_pow_le_factorial
      _ = Nat.factorial k := by congr 1; omega
  have hfact : (2 : ℝ) ^ (k - 1) ≤ (Nat.factorial k : ℝ) := by
    exact_mod_cast hfactNat
  exact hterm.trans_le
    (one_div_le_one_div_of_le (pow_pos (by norm_num) _) hfact)

/-- Source: `proof_gap/exercise_69/6.txt`; the geometric sum and valid range are explicit. -/
theorem gap6 :
    ∀ n : ℕ, 1 < n → x n < geometricUpper n := by
  intro n hn
  let f : ℕ → ℝ := fun k =>
    (1 / (Nat.factorial k : ℝ)) *
      ∏ i ∈ Finset.Ico 1 k, (1 - (i : ℝ) / (n : ℝ))
  let g : ℕ → ℝ := fun k => 1 / (2 : ℝ) ^ (k - 1)
  have htail :
      (∑ k ∈ Finset.Ico 2 (n + 1), f k) <
        ∑ k ∈ Finset.Ico 2 (n + 1), g k := by
    apply Finset.sum_lt_sum_of_nonempty
    · exact ⟨2, Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩⟩
    · intro k hk
      exact factorial_term_lt_geometric hn
        (Finset.mem_Ico.mp hk).1
        (by have := (Finset.mem_Ico.mp hk).2; omega)
  have hfactorial :
      factorialExpansion n = 2 + ∑ k ∈ Finset.Ico 2 (n + 1), f k := by
    unfold factorialExpansion
    rw [← Finset.sum_range_add_sum_Ico f (by omega : 2 ≤ n + 1)]
    norm_num [f, Finset.sum_range_succ, Finset.prod_Ico_eq_prod_range]
  have hgeometric :
      (∑ k ∈ Finset.Ico 2 (n + 1), g k) =
        ∑ j ∈ Finset.range (n - 1), 1 / (2 : ℝ) ^ (j + 1) := by
    rw [Finset.sum_Ico_eq_sum_range]
    apply Finset.sum_congr
    · congr 1
    · intro j hj
      dsimp [g]
      congr 2
      omega
  rw [gap4 n (by omega), hfactorial]
  unfold geometricUpper
  rw [← hgeometric]
  linarith

/-- Source: `proof_gap/exercise_69/7.txt`. -/
theorem gap7 :
    ∀ n : ℕ, 0 < n →
      geometricUpper n = 3 - 1 / (2 : ℝ) ^ (n - 1) := by
  intro n _
  unfold geometricUpper
  have hsum :
      (∑ j ∈ Finset.range (n - 1), 1 / (2 : ℝ) ^ (j + 1)) =
        1 - 1 / (2 : ℝ) ^ (n - 1) := by
    calc
      (∑ j ∈ Finset.range (n - 1), 1 / (2 : ℝ) ^ (j + 1)) =
          (1 / 2 : ℝ) *
            ∑ j ∈ Finset.range (n - 1), (1 / 2 : ℝ) ^ j := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _
              rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num]
              simp [one_div, inv_pow, pow_succ]
      _ = (1 / 2 : ℝ) *
          (((1 / 2 : ℝ) ^ (n - 1) - 1) / ((1 / 2 : ℝ) - 1)) := by
            rw [geom_sum_eq (by norm_num : (1 / 2 : ℝ) ≠ 1)]
      _ = 1 - 1 / (2 : ℝ) ^ (n - 1) := by
        rw [one_div_pow]
        ring
  rw [hsum]
  ring

/-- Source: `proof_gap/exercise_69/8.txt`; the positive-index domain is restored. -/
theorem gap8 :
    ∀ n : ℕ, 0 < n →
      3 - 1 / (2 : ℝ) ^ (n - 1) < 3 := by
  intro n _
  have hp : 0 < (2 : ℝ) ^ (n - 1) := pow_pos (by norm_num) _
  have : 0 < 1 / (2 : ℝ) ^ (n - 1) := one_div_pos.mpr hp
  linarith

/-- Source: `proof_gap/exercise_69/9.txt`. -/
theorem gap9 :
    ∀ n : ℕ, 0 < n → x n < 3 := by
  intro n hn
  by_cases h : n = 1
  · subst n
    norm_num [x]
  · have hn2 : 1 < n := by omega
    exact (gap6 n hn2).trans ((gap7 n hn).trans_lt (gap8 n hn))

/-- Source: `proof_gap/exercise_69/10.txt`. -/
theorem gap10
    (h9 : ∀ n : ℕ, 0 < n → x n < 3) :
    BoundedAboveOnPos x := by
  exact ⟨3, fun n hn => (h9 n hn).le⟩

/-- Source: `proof_gap/exercise_69/11.txt`. -/
theorem gap11
    (hmono : MonoIncOnPos x)
    (hbounded : BoundedAboveOnPos x) :
    ∃ e : ℝ, Tendsto x atTop (𝓝 e) := by
  rcases hbounded with ⟨M, hM⟩
  let v : ℕ → ℝ := fun n => x (n + 1)
  have hvmono : Monotone v := monotone_nat_of_le_succ fun n => by
    dsimp [v]
    simpa [Nat.add_assoc] using hmono (n + 1) (by omega)
  have hvbdd : BddAbove (Set.range v) := by
    refine ⟨M, ?_⟩
    rintro z ⟨n, rfl⟩
    exact hM (n + 1) (by omega)
  refine ⟨⨆ n, v n, ?_⟩
  rw [← tendsto_add_atTop_iff_nat 1]
  simpa [v, Nat.add_comm] using tendsto_atTop_ciSup hvmono hvbdd

/-- Source: `proof_gap/exercise_69/12.txt`; exclude the zero denominator at `n = 1`. -/
theorem gap12 :
    ∀ n : ℕ, 1 < n →
      ((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) ^ n =
        (1 + 1 / ((n : ℝ) ^ 2 - 1)) ^ n := by
  intro n hn
  congr 1
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have hden : (n : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  field_simp
  ring

/-- Source: `proof_gap/exercise_69/13.txt`; Bernoulli's strict form needs `1 < n`. -/
theorem gap13 :
    ∀ n : ℕ, 1 < n →
      (1 + 1 / ((n : ℝ) ^ 2 - 1)) ^ n >
        1 + (n : ℝ) / ((n : ℝ) ^ 2 - 1) := by
  intro n hn
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have hden : (0 : ℝ) < (n : ℝ) ^ 2 - 1 := by nlinarith
  let a : ℝ := 1 / ((n : ℝ) ^ 2 - 1)
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hbern :
      1 + ((n - 1 : ℕ) : ℝ) * a ≤ (1 + a) ^ (n - 1) :=
    one_add_mul_le_pow (by linarith : (-2 : ℝ) ≤ a) (n - 1)
  have hmul := mul_le_mul_of_nonneg_right hbern (by linarith : 0 ≤ 1 + a)
  have hmul' :
      (1 + ((n - 1 : ℕ) : ℝ) * a) * (1 + a) ≤ (1 + a) ^ n := by
    have hpow : (1 + a) ^ (n - 1) * (1 + a) = (1 + a) ^ n := by
      rw [← pow_succ]
      congr 1
      omega
    rw [hpow] at hmul
    exact hmul
  have hnsub : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_pos_of_lt hn
  have hstrict :
      1 + (n : ℝ) * a <
        (1 + ((n - 1 : ℕ) : ℝ) * a) * (1 + a) := by
    have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]
      norm_num
    have hnRsub : 0 < (n : ℝ) - 1 := by linarith
    rw [hcast]
    nlinarith [mul_pos hnRsub (sq_pos_of_pos ha)]
  have hfinal := hstrict.trans_le hmul'
  simpa [a, div_eq_mul_inv] using hfinal

/-- Source: `proof_gap/exercise_69/14.txt`. -/
theorem gap14 :
    ∀ n : ℕ, 1 < n →
      1 + (n : ℝ) / ((n : ℝ) ^ 2 - 1) >
        1 + 1 / (n : ℝ) := by
  intro n hn
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by positivity
  have hden : (0 : ℝ) < (n : ℝ) ^ 2 - 1 := by nlinarith
  have hfrac : 1 / (n : ℝ) < (n : ℝ) / ((n : ℝ) ^ 2 - 1) := by
    rw [div_lt_div_iff₀ hnpos hden]
    nlinarith
  linarith

/-- Source: `proof_gap/exercise_69/15.txt`. -/
theorem gap15 :
    ∀ n : ℕ, 1 < n →
      ((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)) ^ n >
        1 + 1 / (n : ℝ) := by
  intro n hn
  rw [gap12 n hn]
  exact (gap14 n hn).trans (gap13 n hn)

/-- Source: `proof_gap/exercise_69/16.txt`; the denominator requires `1 < n`. -/
theorem gap16 :
    ∀ n : ℕ, 1 < n →
      ((n : ℝ) / ((n : ℝ) - 1)) ^ n >
        (((n : ℝ) + 1) / (n : ℝ)) ^ (n + 1) := by
  intro n hn
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  let A : ℝ := (n : ℝ) / ((n : ℝ) - 1)
  let B : ℝ := ((n : ℝ) + 1) / (n : ℝ)
  let C : ℝ := (n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1)
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hnm1 : (n : ℝ) - 1 ≠ 0 := by linarith
  have hnp1 : (n : ℝ) + 1 ≠ 0 := by linarith
  have hden : (n : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  have hA : 0 < A := by
    dsimp [A]
    exact div_pos (by linarith) (by linarith)
  have hB : 0 < B := by
    dsimp [B]
    positivity
  have hCeq : C = A / B := by
    dsimp [A, B, C]
    field_simp [hn0, hnm1, hnp1, hden]
    ring
  have hBeq : 1 + 1 / (n : ℝ) = B := by
    dsimp [B]
    field_simp
  have hmain0 := gap15 n hn
  rw [hBeq] at hmain0
  have hmain : B < C ^ n := by
    simpa [C] using hmain0
  rw [hCeq] at hmain
  have hmul := mul_lt_mul_of_pos_right hmain (pow_pos hB n)
  have hleft : (A / B) ^ n * B ^ n = A ^ n := by
    rw [div_pow]
    field_simp
  have hright : B * B ^ n = B ^ (n + 1) := by
    rw [pow_succ]
    ring
  rw [hleft, hright] at hmul
  exact hmul

/-- Source: `proof_gap/exercise_69/17.txt`. -/
theorem gap17 :
    ∀ n : ℕ, 1 < n →
      (1 + 1 / ((n : ℝ) - 1)) ^ n >
        (1 + 1 / (n : ℝ)) ^ (n + 1) := by
  intro n hn
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hnm1 : (n : ℝ) - 1 ≠ 0 := by linarith
  have hleft :
      1 + 1 / ((n : ℝ) - 1) = (n : ℝ) / ((n : ℝ) - 1) := by
    field_simp
    ring
  have hright :
      1 + 1 / (n : ℝ) = ((n : ℝ) + 1) / (n : ℝ) := by
    field_simp
  rw [hleft, hright]
  exact gap16 n hn

/-- Source: `proof_gap/exercise_69/18.txt`; subtraction is used only when `1 < n`. -/
theorem gap18 :
    ∀ n : ℕ, 1 < n → y (n - 1) > y n := by
  intro n hn
  have hle : 1 ≤ n := by omega
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hle]
    norm_num
  unfold y
  rw [Nat.sub_add_cancel hle, hcast]
  exact gap17 n hn

/-- Source: `proof_gap/exercise_69/19.txt`. -/
theorem gap19 :
    MonoDecOnPos y := by
  intro n hn
  exact (gap18 (n + 1) (by omega)).le

/-- Source: `proof_gap/exercise_69/20.txt`; the positive-index domain is restored. -/
theorem gap20 :
    ∀ n : ℕ, 0 < n →
      y n = x n * (1 + 1 / (n : ℝ)) := by
  intro n _
  simp [x, y, pow_succ]

/-- Source: `proof_gap/exercise_69/21.txt`. -/
theorem gap21 :
    ∀ n : ℕ, 0 < n →
      x n * (1 + 1 / (n : ℝ)) >
        1 + (n : ℝ) * (1 / (n : ℝ)) := by
  intro n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpos : 0 < 1 / (n : ℝ) := one_div_pos.mpr hnR
  have hbern := one_add_mul_le_pow
    (a := (1 / (n : ℝ))) (by linarith : (-2 : ℝ) ≤ 1 / (n : ℝ)) (n + 1)
  have hrewrite :
      (1 + 1 / (n : ℝ)) ^ (n + 1) =
        x n * (1 + 1 / (n : ℝ)) := by
    simp [x, pow_succ]
  rw [hrewrite] at hbern
  push_cast at hbern
  exact (by
    nlinarith : 1 + (n : ℝ) * (1 / (n : ℝ)) <
      1 + ((n : ℝ) + 1) * (1 / (n : ℝ))).trans_le hbern

/-- Source: `proof_gap/exercise_69/22.txt`; the equality fails at `n = 0`. -/
theorem gap22 :
    ∀ n : ℕ, 0 < n →
      1 + (n : ℝ) * (1 / (n : ℝ)) = 2 := by
  intro n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp
  norm_num

/-- Source: `proof_gap/exercise_69/23.txt`. -/
theorem gap23 :
    ∀ n : ℕ, 0 < n → y n > 2 := by
  intro n hn
  rw [gap20 n hn]
  calc
    2 = 1 + (n : ℝ) * (1 / (n : ℝ)) := (gap22 n hn).symm
    _ < x n * (1 + 1 / (n : ℝ)) := gap21 n hn

/-- Source: `proof_gap/exercise_69/24.txt`. -/
theorem gap24
    (h23 : ∀ n : ℕ, 0 < n → y n > 2) :
    BoundedBelowOnPos y := by
  exact ⟨2, fun n hn => (h23 n hn).le⟩

/-- Source: `proof_gap/exercise_69/25.txt`. -/
theorem gap25
    (hmono : MonoDecOnPos y)
    (hbounded : BoundedBelowOnPos y) :
    ∃ L : ℝ, Tendsto y atTop (𝓝 L) := by
  rcases hbounded with ⟨M, hM⟩
  let v : ℕ → ℝ := fun n => y (n + 1)
  have hvanti : Antitone v := antitone_nat_of_succ_le fun n => by
    dsimp [v]
    simpa [Nat.add_assoc] using hmono (n + 1) (by omega)
  have hvbdd : BddBelow (Set.range v) := by
    refine ⟨M, ?_⟩
    rintro z ⟨n, rfl⟩
    exact hM (n + 1) (by omega)
  refine ⟨⨅ n, v n, ?_⟩
  rw [← tendsto_add_atTop_iff_nat 1]
  simpa [v, Nat.add_comm] using tendsto_atTop_ciInf hvanti hvbdd

/-- Source: `proof_gap/exercise_69/26.txt`; stated as the product limit law. -/
theorem gap26
    (e : ℝ)
    (hx : Tendsto x atTop (𝓝 e))
    (hrecip : Tendsto onePlusReciprocal atTop (𝓝 1)) :
    Tendsto y atTop (𝓝 (e * 1)) := by
  have hprod := hx.mul hrecip
  convert hprod using 1

/-- Source: `proof_gap/exercise_69/27.txt`. -/
theorem gap27 (e : ℝ) :
    e * 1 = e := by
  simp

/-- Source: `proof_gap/exercise_69/28.txt`. -/
theorem gap28
    (e : ℝ)
    (hx : Tendsto x atTop (𝓝 e))
    (hrecip : Tendsto onePlusReciprocal atTop (𝓝 1)) :
    Tendsto y atTop (𝓝 e) := by
  simpa using gap26 e hx hrecip

/-- Source: `proof_gap/exercise_69/29.txt`; equality of limits is expressed by a common limit. -/
theorem gap29
    (e : ℝ)
    (hx : Tendsto x atTop (𝓝 e))
    (hy : Tendsto y atTop (𝓝 e)) :
    ∃ L : ℝ, Tendsto x atTop (𝓝 L) ∧ Tendsto y atTop (𝓝 L) := by
  exact ⟨e, hx, hy⟩

/-- Source: `proof_gap/exercise_69/30.txt`. -/
theorem gap30
    (e : ℝ)
    (hx : Tendsto x atTop (𝓝 e)) :
    Tendsto x atTop (𝓝 e) := by
  exact hx

/-- Source: `proof_gap/exercise_69/31.txt`. -/
theorem gap31
    (e : ℝ)
    (hy : Tendsto y atTop (𝓝 e)) :
    Tendsto y atTop (𝓝 e) := by
  exact hy

/-- Source: `proof_gap/exercise_69/32.txt`. -/
theorem gap32
    (e : ℝ)
    (hxi : MonoIncOnPos x)
    (hxb : BoundedAboveOnPos x)
    (hyd : MonoDecOnPos y)
    (hyb : BoundedBelowOnPos y)
    (hxlim : Tendsto x atTop (𝓝 e))
    (hylim : Tendsto y atTop (𝓝 e)) :
    MonoIncOnPos x ∧ BoundedAboveOnPos x ∧
      MonoDecOnPos y ∧ BoundedBelowOnPos y ∧
      (∃ L : ℝ, Tendsto x atTop (𝓝 L) ∧ Tendsto y atTop (𝓝 L)) ∧
      Tendsto y atTop (𝓝 e) := by
  exact ⟨hxi, hxb, hyd, hyb, ⟨e, hxlim, hylim⟩, hylim⟩

end

end ProofGap.Exercise69
