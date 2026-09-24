import ProofGapLean.Prelude.Sequences
import ProofGapLean.Prelude.Finite
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise431

noncomputable section

def oddSquareSum (n : ℕ) : ℝ :=
  (Finset.range n).sum (fun i => (((2 * i + 1 : ℕ) : ℝ) ^ 2))
def evenSquareSum (n : ℕ) : ℝ :=
  (Finset.range n).sum (fun i => (((2 * (i + 1) : ℕ) : ℝ) ^ 2))
def ratio (n : ℕ) : ℝ := oddSquareSum n / evenSquareSum n
def closedRatio (n : ℕ) : ℝ := ((2 * n - 1 : ℕ) : ℝ) / (2 * (n + 1))

/-- Source: `proof_gap/exercise_431/1.txt`; replace the odd-square ellipsis by a finite sum. -/
theorem gap1 : ∀ n : ℕ,
    oddSquareSum n = (n : ℝ) / 3 * (4 * (n : ℝ) ^ 2 - 1) := by
  intro n
  induction n with
  | zero =>
      simp [oddSquareSum]
  | succ n ih =>
      rw [oddSquareSum, Finset.sum_range_succ, ← oddSquareSum, ih]
      norm_num [Nat.cast_add, Nat.cast_mul]
      ring

/-- Source: `proof_gap/exercise_431/2.txt`; replace the even-square ellipsis by a finite sum. -/
theorem gap2 : ∀ n : ℕ,
    evenSquareSum n = 2 * (n : ℝ) * (n + 1) * (2 * n + 1) / 3 := by
  intro n
  induction n with
  | zero =>
      simp [evenSquareSum]
  | succ n ih =>
      rw [evenSquareSum, Finset.sum_range_succ, ← evenSquareSum, ih]
      norm_num [Nat.cast_add, Nat.cast_mul]
      ring

/-- Source: `proof_gap/exercise_431/3.txt`. -/
theorem gap3 :
    Filter.Tendsto ratio Filter.atTop (nhds 1) ↔
      Filter.Tendsto closedRatio Filter.atTop (nhds 1) := by
  have heq : ratio =ᶠ[Filter.atTop] closedRatio := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
    have hnpos : 0 < n := by omega
    have hsub : ((2 * n - 1 : ℕ) : ℝ) = 2 * (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ 2 * n)]
      norm_num [Nat.cast_mul]
    have hnR : (n : ℝ) ≠ 0 := by positivity
    have hn1R : (n : ℝ) + 1 ≠ 0 := by positivity
    have hoddR : 2 * (n : ℝ) + 1 ≠ 0 := by positivity
    have hevenR :
        2 * (n : ℝ) * ((n : ℝ) + 1) * (2 * (n : ℝ) + 1) / 3 ≠ 0 := by
      positivity
    rw [ratio, gap1 n, gap2 n, closedRatio, hsub]
    norm_num [Nat.cast_add, Nat.cast_mul]
    field_simp [hnR, hn1R, hoddR, hevenR]
    <;> ring
  exact Filter.tendsto_congr' heq

/-- Source: `proof_gap/exercise_431/4.txt`. -/
theorem gap4 : Filter.Tendsto closedRatio Filter.atTop (nhds 1) := by
  have hcast :
      Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  have hinv :
      Filter.Tendsto (fun n : ℕ => ((n : ℝ)⁻¹)) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hcast
  have hnum :
      Filter.Tendsto (fun n : ℕ => (2 : ℝ) - (n : ℝ)⁻¹) Filter.atTop
        (nhds ((2 : ℝ) - 0)) :=
    tendsto_const_nhds.sub hinv
  have hscaled :
      Filter.Tendsto (fun n : ℕ => (2 : ℝ) * (n : ℝ)⁻¹) Filter.atTop
        (nhds ((2 : ℝ) * 0)) :=
    tendsto_const_nhds.mul hinv
  have hden :
      Filter.Tendsto (fun n : ℕ => (2 : ℝ) + 2 * (n : ℝ)⁻¹) Filter.atTop
        (nhds ((2 : ℝ) + 2 * 0)) :=
    tendsto_const_nhds.add hscaled
  have halt :
      Filter.Tendsto
        (fun n : ℕ => ((2 : ℝ) - (n : ℝ)⁻¹) / (2 + 2 * (n : ℝ)⁻¹))
        Filter.atTop (nhds 1) := by
    simpa using hnum.div hden (by norm_num : (2 : ℝ) + 2 * 0 ≠ 0)
  have heq : closedRatio =ᶠ[Filter.atTop]
      (fun n : ℕ => ((2 : ℝ) - (n : ℝ)⁻¹) / (2 + 2 * (n : ℝ)⁻¹)) := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
    have hnpos : 0 < n := by omega
    have hsub : ((2 * n - 1 : ℕ) : ℝ) = 2 * (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ 2 * n)]
      norm_num [Nat.cast_mul]
    have hnR : (n : ℝ) ≠ 0 := by positivity
    have hn1R : (n : ℝ) + 1 ≠ 0 := by positivity
    have haltDen : (2 : ℝ) + 2 * (n : ℝ)⁻¹ ≠ 0 := by positivity
    rw [closedRatio, hsub]
    norm_num [Nat.cast_add, Nat.cast_mul]
    field_simp [hnR, hn1R, haltDen]
    <;> ring
  exact (Filter.tendsto_congr' heq).2 halt

/-- Source: `proof_gap/exercise_431/5.txt`. -/
theorem gap5 : Filter.Tendsto ratio Filter.atTop (nhds 1) := by
  exact gap3.mpr gap4

end

end ProofGap.Exercise431
