import Mathlib

noncomputable section

open Filter
open scoped BigOperators Topology

namespace ProofGapBatch5

abbrev SeqR := ℕ → ℝ

def nroot (n : ℕ) (x : ℝ) : ℝ :=
  Real.rpow (max x 0) ((n : ℝ)⁻¹)

def seqLim (u : ℕ → ℝ) (L : ℝ) : Prop :=
  Tendsto u atTop (𝓝 L)

def seqLimValue (u : ℕ → ℝ) : ℝ :=
  limUnder atTop u

def radiusOfConvergence (a : SeqR) : ℝ :=
  sSup {r : ℝ | 0 < r ∧ Summable (fun n : ℕ => ‖a n‖ * r ^ n)}

namespace exercise_2897

theorem proof_gap_exercise_2897_1
    (a b A B : SeqR) (R1 R2 : ℝ)
    (hRa : radiusOfConvergence a = R1) (hR1pos : 0 < R1)
    (hRb : radiusOfConvergence b = R2) (hR2pos : 0 < R2)
    (hA : ∀ n : ℕ, A n = a n + b n)
    (hB : ∀ n : ℕ, B n = a n * b n) :
    ∀ n : ℕ, 0 < n →
      nroot n |A n| = nroot n |a n + b n| ∧
      nroot n |a n + b n| ≤ nroot n (|a n| + |b n|) ∧
      nroot n (|a n| + |b n|) ≤ nroot n (2 * max (|a n|) (|b n|)) := by
  sorry

theorem proof_gap_exercise_2897_2
    (a b A B : SeqR) (R1 R2 : ℝ)
    (hRa : radiusOfConvergence a = R1) (hR1pos : 0 < R1)
    (hRb : radiusOfConvergence b = R2) (hR2pos : 0 < R2)
    (hA : ∀ n : ℕ, A n = a n + b n)
    (hB : ∀ n : ℕ, B n = a n * b n)
    (hroot_add : ∀ n : ℕ, 0 < n →
      nroot n |A n| = nroot n |a n + b n| ∧
      nroot n |a n + b n| ≤ nroot n (|a n| + |b n|) ∧
      nroot n (|a n| + |b n|) ≤ nroot n (2 * max (|a n|) (|b n|))) :
    ∀ n : ℕ, 0 < n →
      nroot n |A n| ≤ nroot n 2 * max (nroot n |a n|) (nroot n |b n|) := by
  sorry

theorem proof_gap_exercise_2897_3
    (a b A B : SeqR) (R1 R2 : ℝ)
    (hRa : radiusOfConvergence a = R1) (hR1pos : 0 < R1)
    (hRb : radiusOfConvergence b = R2) (hR2pos : 0 < R2)
    (hA : ∀ n : ℕ, A n = a n + b n)
    (hB : ∀ n : ℕ, B n = a n * b n) :
    seqLim (fun n : ℕ => nroot n 2) 1 := by
  sorry

theorem proof_gap_exercise_2897_4
    (a b A B : SeqR) (R1 R2 : ℝ)
    (hRa : radiusOfConvergence a = R1) (hR1pos : 0 < R1)
    (hRb : radiusOfConvergence b = R2) (hR2pos : 0 < R2)
    (hA : ∀ n : ℕ, A n = a n + b n)
    (hB : ∀ n : ℕ, B n = a n * b n)
    (hroot_two : seqLim (fun n : ℕ => nroot n 2) 1) :
    1 / radiusOfConvergence A = seqLimValue (fun n : ℕ => nroot n |A n|) := by
  sorry

theorem proof_gap_exercise_2897_5
    (a b A B : SeqR) (R1 R2 : ℝ)
    (hRa : radiusOfConvergence a = R1) (hR1pos : 0 < R1)
    (hRb : radiusOfConvergence b = R2) (hR2pos : 0 < R2)
    (hA : ∀ n : ℕ, A n = a n + b n)
    (hB : ∀ n : ℕ, B n = a n * b n)
    (hroot_A : 1 / radiusOfConvergence A = seqLimValue (fun n : ℕ => nroot n |A n|)) :
    seqLimValue (fun n : ℕ => nroot n |A n|) ≤ max (1 / R1) (1 / R2) := by
  sorry

theorem proof_gap_exercise_2897_6
    (a b A B : SeqR) (R1 R2 : ℝ)
    (hRa : radiusOfConvergence a = R1) (hR1pos : 0 < R1)
    (hRb : radiusOfConvergence b = R2) (hR2pos : 0 < R2)
    (hA : ∀ n : ℕ, A n = a n + b n)
    (hB : ∀ n : ℕ, B n = a n * b n)
    (hroot_A : 1 / radiusOfConvergence A = seqLimValue (fun n : ℕ => nroot n |A n|))
    (hlim_A_le : seqLimValue (fun n : ℕ => nroot n |A n|) ≤ max (1 / R1) (1 / R2)) :
    1 / radiusOfConvergence A ≤ max (1 / R1) (1 / R2) := by
  sorry

theorem proof_gap_exercise_2897_7
    (a b A B : SeqR) (R1 R2 : ℝ)
    (hRa : radiusOfConvergence a = R1) (hR1pos : 0 < R1)
    (hRb : radiusOfConvergence b = R2) (hR2pos : 0 < R2)
    (hA : ∀ n : ℕ, A n = a n + b n)
    (hB : ∀ n : ℕ, B n = a n * b n)
    (hrecip_A : 1 / radiusOfConvergence A ≤ max (1 / R1) (1 / R2)) :
    radiusOfConvergence A ≥ 1 / max (1 / R1) (1 / R2) := by
  sorry

theorem proof_gap_exercise_2897_8
    (a b A B : SeqR) (R1 R2 : ℝ)
    (hRa : radiusOfConvergence a = R1) (hR1pos : 0 < R1)
    (hRb : radiusOfConvergence b = R2) (hR2pos : 0 < R2)
    (hA : ∀ n : ℕ, A n = a n + b n)
    (hB : ∀ n : ℕ, B n = a n * b n)
    (hA_lower : radiusOfConvergence A ≥ 1 / max (1 / R1) (1 / R2)) :
    1 / max (1 / R1) (1 / R2) = min R1 R2 := by
  sorry

theorem proof_gap_exercise_2897_9
    (a b A B : SeqR) (R1 R2 : ℝ)
    (hRa : radiusOfConvergence a = R1) (hR1pos : 0 < R1)
    (hRb : radiusOfConvergence b = R2) (hR2pos : 0 < R2)
    (hA : ∀ n : ℕ, A n = a n + b n)
    (hB : ∀ n : ℕ, B n = a n * b n)
    (hA_lower : radiusOfConvergence A ≥ 1 / max (1 / R1) (1 / R2))
    (hrecip_max : 1 / max (1 / R1) (1 / R2) = min R1 R2) :
    radiusOfConvergence A ≥ min R1 R2 := by
  sorry

theorem proof_gap_exercise_2897_10
    (a b A B : SeqR) (R1 R2 : ℝ)
    (hRa : radiusOfConvergence a = R1) (hR1pos : 0 < R1)
    (hRb : radiusOfConvergence b = R2) (hR2pos : 0 < R2)
    (hA : ∀ n : ℕ, A n = a n + b n)
    (hB : ∀ n : ℕ, B n = a n * b n)
    (hA_lower_min : radiusOfConvergence A ≥ min R1 R2) :
    ∀ n : ℕ, 0 < n →
      nroot n |B n| = nroot n |a n * b n| ∧
      nroot n |a n * b n| = nroot n |a n| * nroot n |b n| := by
  sorry

theorem proof_gap_exercise_2897_11
    (a b A B : SeqR) (R1 R2 : ℝ)
    (hRa : radiusOfConvergence a = R1) (hR1pos : 0 < R1)
    (hRb : radiusOfConvergence b = R2) (hR2pos : 0 < R2)
    (hA : ∀ n : ℕ, A n = a n + b n)
    (hB : ∀ n : ℕ, B n = a n * b n)
    (hroot_mul : ∀ n : ℕ, 0 < n →
      nroot n |B n| = nroot n |a n * b n| ∧
      nroot n |a n * b n| = nroot n |a n| * nroot n |b n|) :
    1 / radiusOfConvergence B = seqLimValue (fun n : ℕ => nroot n |B n|) := by
  sorry

theorem proof_gap_exercise_2897_12
    (a b A B : SeqR) (R1 R2 : ℝ)
    (hRa : radiusOfConvergence a = R1) (hR1pos : 0 < R1)
    (hRb : radiusOfConvergence b = R2) (hR2pos : 0 < R2)
    (hA : ∀ n : ℕ, A n = a n + b n)
    (hB : ∀ n : ℕ, B n = a n * b n)
    (hroot_B : 1 / radiusOfConvergence B = seqLimValue (fun n : ℕ => nroot n |B n|)) :
    seqLimValue (fun n : ℕ => nroot n |B n|) ≤ (1 / R1) * (1 / R2) := by
  sorry

theorem proof_gap_exercise_2897_13
    (a b A B : SeqR) (R1 R2 : ℝ)
    (hRa : radiusOfConvergence a = R1) (hR1pos : 0 < R1)
    (hRb : radiusOfConvergence b = R2) (hR2pos : 0 < R2)
    (hA : ∀ n : ℕ, A n = a n + b n)
    (hB : ∀ n : ℕ, B n = a n * b n)
    (hlim_B_le : seqLimValue (fun n : ℕ => nroot n |B n|) ≤ (1 / R1) * (1 / R2)) :
    (1 / R1) * (1 / R2) = 1 / (R1 * R2) := by
  sorry

theorem proof_gap_exercise_2897_14
    (a b A B : SeqR) (R1 R2 : ℝ)
    (hRa : radiusOfConvergence a = R1) (hR1pos : 0 < R1)
    (hRb : radiusOfConvergence b = R2) (hR2pos : 0 < R2)
    (hA : ∀ n : ℕ, A n = a n + b n)
    (hB : ∀ n : ℕ, B n = a n * b n)
    (hroot_B : 1 / radiusOfConvergence B = seqLimValue (fun n : ℕ => nroot n |B n|))
    (hlim_B_le : seqLimValue (fun n : ℕ => nroot n |B n|) ≤ (1 / R1) * (1 / R2))
    (hmul_recip : (1 / R1) * (1 / R2) = 1 / (R1 * R2)) :
    1 / radiusOfConvergence B ≤ 1 / (R1 * R2) := by
  sorry

theorem proof_gap_exercise_2897_15
    (a b A B : SeqR) (R1 R2 : ℝ)
    (hRa : radiusOfConvergence a = R1) (hR1pos : 0 < R1)
    (hRb : radiusOfConvergence b = R2) (hR2pos : 0 < R2)
    (hA : ∀ n : ℕ, A n = a n + b n)
    (hB : ∀ n : ℕ, B n = a n * b n)
    (hrecip_B : 1 / radiusOfConvergence B ≤ 1 / (R1 * R2)) :
    radiusOfConvergence B ≥ R1 * R2 := by
  sorry

theorem proof_gap_exercise_2897_16
    (a b A B : SeqR) (R1 R2 : ℝ)
    (hRa : radiusOfConvergence a = R1) (hR1pos : 0 < R1)
    (hRb : radiusOfConvergence b = R2) (hR2pos : 0 < R2)
    (hA : ∀ n : ℕ, A n = a n + b n)
    (hB : ∀ n : ℕ, B n = a n * b n) :
    radiusOfConvergence A ≥ min R1 R2 ∧ radiusOfConvergence B ≥ R1 * R2 →
      0 < radiusOfConvergence A ∧ 0 < radiusOfConvergence B := by
  sorry

end exercise_2897

end ProofGapBatch5
