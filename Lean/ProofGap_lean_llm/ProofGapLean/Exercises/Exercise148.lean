import ProofGapLean.Prelude.Sequences
import ProofGapLean.Prelude.Finite
import Mathlib.Analysis.SpecificLimits.Normed

open Filter Topology

namespace ProofGap.Exercise148

noncomputable section

def recurrence (x : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, 3 ≤ n → x n = (x (n - 1) + x (n - 2)) / 2

def diff (x : ℕ → ℝ) (n : ℕ) : ℝ := x (n + 1) - x n

/-- Source: `proof_gap/exercise_148/1.txt`; n≥2 is required to invoke the recurrence at n+1. -/
theorem gap1 (x : ℕ → ℝ) (hrec : recurrence x) :
    ∀ n : ℕ, 2 ≤ n →
      diff x n = (x n + x (n - 1)) / 2 - x n := by
  intro n hn
  unfold diff
  rw [hrec (n + 1) (by omega)]
  congr 2 <;> omega

/-- Source: `proof_gap/exercise_148/2.txt`; n is positive before using n-1. -/
theorem gap2 (x : ℕ → ℝ) :
    ∀ n : ℕ, 0 < n →
      (x n + x (n - 1)) / 2 - x n = (x (n - 1) - x n) / 2 := by
  intro n _
  ring

/-- Source: `proof_gap/exercise_148/3.txt`; replace the ellipsis by the difference recurrence. -/
theorem gap3 (x : ℕ → ℝ) (hrec : recurrence x) :
    ∀ n : ℕ, 2 ≤ n → diff x n = -(diff x (n - 1)) / 2 := by
  intro n hn
  rw [gap1 x hrec n hn, gap2 x n (by omega)]
  unfold diff
  rw [Nat.sub_add_cancel (by omega : 1 ≤ n)]
  ring

/-- Source: `proof_gap/exercise_148/4.txt`; closed form of the difference recurrence. -/
theorem gap4 (x : ℕ → ℝ) (hrec : recurrence x) :
    ∀ n : ℕ, 0 < n →
      diff x n = (x 2 - x 1) / ((-2 : ℝ) ^ (n - 1)) := by
  intro n hn
  induction n using Nat.case_strong_induction_on with
  | hz => omega
  | hi n ih =>
      by_cases hn0 : n = 0
      · subst n
        simp [diff]
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
        rw [gap3 x hrec (n + 1) (by omega)]
        rw [show n + 1 - 1 = n by omega, ih n (by omega) hnpos]
        norm_num [Nat.add_sub_cancel, pow_succ]
        field_simp
        have hp : (-2 : ℝ) ^ n = (-2 : ℝ) ^ (n - 1) * (-2) := by
          rw [← pow_succ, Nat.sub_add_cancel hnpos]
        rw [hp]
        ring

/-- Source: `proof_gap/exercise_148/5.txt`. -/
theorem gap5 (x : ℕ → ℝ) (a b : ℝ) (h1 : x 1 = a) (h2 : x 2 = b) :
    ∀ n : ℕ, 0 < n →
      (x 2 - x 1) / ((-2 : ℝ) ^ (n - 1)) =
        (b - a) / ((-2 : ℝ) ^ (n - 1)) := by
  intro n _
  rw [h1, h2]

/-- Source: `proof_gap/exercise_148/6.txt`. -/
theorem gap6 (x : ℕ → ℝ) (a b : ℝ)
    (h1 : x 1 = a) (h2 : x 2 = b) (hrec : recurrence x) :
    ∀ n : ℕ, 0 < n →
      diff x n = (b - a) / ((-2 : ℝ) ^ (n - 1)) := by
  intro n hn
  rw [gap4 x hrec n hn, gap5 x a b h1 h2 n hn]

/-- Source: `proof_gap/exercise_148/7.txt`; the telescoping range is explicit. -/
theorem gap7 (x : ℕ → ℝ) :
    ∀ n : ℕ, x (n + 1) =
      (∑ m ∈ Finset.Icc 1 n, (x (m + 1) - x m)) + x 1 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [show Finset.Icc 1 (n + 1) =
        insert (n + 1) (Finset.Icc 1 n) by
          ext i
          simp
          omega]
      simp [ih]
      ring

/-- Source: `proof_gap/exercise_148/8.txt`. -/
theorem gap8 (x : ℕ → ℝ) (a b : ℝ)
    (h1 : x 1 = a)
    (hdiff : ∀ n : ℕ, 0 < n →
      diff x n = (b - a) / ((-2 : ℝ) ^ (n - 1))) :
    ∀ n : ℕ,
      (∑ m ∈ Finset.Icc 1 n, (x (m + 1) - x m)) + x 1 =
        (b - a) * (∑ m ∈ Finset.Icc 1 n,
          (1 : ℝ) / ((-2 : ℝ) ^ (m - 1))) + a := by
  intro n
  rw [h1, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro m hm
  have hmpos : 0 < m := by
    simp only [Finset.mem_Icc] at hm
    omega
  rw [← diff, hdiff m hmpos]
  ring

/-- Source: `proof_gap/exercise_148/9.txt`. -/
theorem gap9 (x : ℕ → ℝ) (a b : ℝ)
    (h1 : x 1 = a)
    (hdiff : ∀ n : ℕ, 0 < n →
      diff x n = (b - a) / ((-2 : ℝ) ^ (n - 1))) :
    ∀ n : ℕ, x (n + 1) =
      (b - a) * (∑ m ∈ Finset.Icc 1 n,
        (1 : ℝ) / ((-2 : ℝ) ^ (m - 1))) + a := by
  intro n
  rw [gap7 x n, gap8 x a b h1 hdiff n]

private theorem geometricIcc (n : ℕ) :
    (∑ m ∈ Finset.Icc 1 n, (1 : ℝ) / ((-2 : ℝ) ^ (m - 1))) =
      ∑ k ∈ Finset.range n, (-(1 : ℝ) / 2) ^ k := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [show Finset.Icc 1 (n + 1) =
        insert (n + 1) (Finset.Icc 1 n) by
          ext i
          simp
          omega]
      rw [Finset.sum_insert (by simp), ih, Finset.sum_range_succ]
      rw [add_comm]
      congr 1
      rw [show n + 1 - 1 = n by omega]
      simp only [one_div]
      calc
        ((-2 : ℝ) ^ n)⁻¹ = ((-2 : ℝ)⁻¹) ^ n := by
          rw [inv_pow]
        _ = (-(1 : ℝ) / 2) ^ n := by norm_num

/-- Source: `proof_gap/exercise_148/10.txt`. -/
theorem gap10 (x : ℕ → ℝ) (a b : ℝ)
    (hformula : ∀ n : ℕ, x (n + 1) =
      (b - a) * (∑ m ∈ Finset.Icc 1 n,
        (1 : ℝ) / ((-2 : ℝ) ^ (m - 1))) + a) :
    Tendsto x atTop (𝓝 ((b - a) / (1 - (-(1 : ℝ) / 2)) + a)) := by
  have hgeom :
      HasSum (fun k : ℕ => (-(1 : ℝ) / 2) ^ k)
        ((1 - (-(1 : ℝ) / 2))⁻¹) :=
    hasSum_geometric_of_norm_lt_one (by norm_num)
  have hsum := hgeom.tendsto_sum_nat
  have hshift :
      Tendsto (fun n => x (n + 1)) atTop
        (𝓝 ((b - a) / (1 - (-(1 : ℝ) / 2)) + a)) := by
    have hc : Tendsto (fun _ : ℕ => b - a) atTop (𝓝 (b - a)) :=
      tendsto_const_nhds
    have ha : Tendsto (fun _ : ℕ => a) atTop (𝓝 a) :=
      tendsto_const_nhds
    have hlim := (hc.mul hsum).add ha
    norm_num at hlim
    have hconst :
        (b - a) * (2 / 3 : ℝ) + a =
          (b - a) / (1 - (-(1 : ℝ) / 2)) + a := by
      ring
    rw [hconst] at hlim
    apply hlim.congr'
    filter_upwards with n
    rw [hformula, geometricIcc]
    field_simp
  exact (tendsto_add_atTop_iff_nat 1).mp hshift

/-- Source: `proof_gap/exercise_148/11.txt`. -/
theorem gap11 (a b : ℝ) :
    (b - a) / (1 - (-(1 : ℝ) / 2)) + a = (a + 2 * b) / 3 := by
  ring

/-- Source: `proof_gap/exercise_148/12.txt`. -/
theorem gap12 (x : ℕ → ℝ) (a b : ℝ)
    (h1 : x 1 = a) (h2 : x 2 = b) (hrec : recurrence x) :
    Tendsto x atTop (𝓝 ((a + 2 * b) / 3)) := by
  have hdiff := gap6 x a b h1 h2 hrec
  have hformula := gap9 x a b h1 hdiff
  rw [← gap11 a b]
  exact gap10 x a b hformula

end

end ProofGap.Exercise148
