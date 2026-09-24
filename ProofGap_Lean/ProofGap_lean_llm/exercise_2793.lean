import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology Nat
open Filter

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

-- exercise: exercise_2793

def lpIntegerPoints : Set ℝ := Set.range (fun z : ℤ => (z : ℝ))
def lpDomain2793 : Set ℝ := (Set.univ : Set ℝ) \ lpIntegerPoints

noncomputable def lpTerm2793 (x : ℝ) (n : ℤ) : ℝ := 1 /. (((n : ℝ) - x) ^ (2 : ℕ))
noncomputable def lpPosTerm2793 (x : ℝ) (n : ℕ) : ℝ := 1 /. (((n : ℝ) - x) ^ (2 : ℕ))
noncomputable def lpNegTerm2793 (x : ℝ) (n : ℕ) : ℝ := 1 /. (((-(n : ℝ)) - x) ^ (2 : ℕ))
noncomputable def lpTwoSidedSum2793 (x : ℝ) : ℝ := tsum (lpTerm2793 x)

def lpDefinedOn2793 (f : ℝ -> ℝ) (s : Set ℝ) : Prop := ∀ x ∈ s, ∃ y : ℝ, f x = y
def lpContinuousOn2793 (f : ℝ -> ℝ) (s : Set ℝ) : Prop := ContinuousOn f s
def lpPeriodic2793 (f : ℝ -> ℝ) : Prop := (1 : ℝ) ≠ 0 ∧ ∀ x ∈ lpDomain2793, f (x + 1) = f x
def lpUniformPlus2793 (a b : ℝ) : Prop :=
  TendstoUniformlyOn (fun N : ℕ => fun x : ℝ => ∑ n ∈ Finset.Icc 0 N, lpPosTerm2793 x n)
    (fun x => tsum (lpPosTerm2793 x)) atTop (Set.Icc a b)
def lpUniformMinus2793 (a b : ℝ) : Prop :=
  TendstoUniformlyOn (fun N : ℕ => fun x : ℝ => ∑ n ∈ Finset.Icc 1 N, lpNegTerm2793 x n)
    (fun x => tsum (fun n : ℕ => if 1 ≤ n then lpNegTerm2793 x n else 0)) atTop (Set.Icc a b)
def lpUniformTwoSided2793 (f : ℝ -> ℝ) (a b : ℝ) : Prop :=
  TendstoUniformlyOn (fun N : ℕ => fun x : ℝ => ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), lpTerm2793 x n)
    f atTop (Set.Icc a b)
def lpIntervalHyp2793 (a b p x0 : ℝ) : Prop :=
  x0 ∈ lpDomain2793 ∧ Int.floor x0 < a ∧ a < x0 ∧ x0 < b ∧ b < Int.floor x0 + 1 ∧ p = max |a| |b|

theorem proof_gap_exercise_2793_1
  (f : ℝ -> ℝ) (n m : ℤ) (a b p : ℝ)
  (h : ∀ x ∈ lpDomain2793, f x = lpTwoSidedSum2793 x)
  : ∀ x ∈ lpDomain2793, Summable (lpPosTerm2793 x) := by
  sorry

theorem proof_gap_exercise_2793_2
  (f : ℝ -> ℝ) (n m : ℤ) (a b p : ℝ)
  (h : ∀ x ∈ lpDomain2793, f x = lpTwoSidedSum2793 x)
  (h1 : ∀ x ∈ lpDomain2793, Summable (lpPosTerm2793 x))
  : ∀ x ∈ lpDomain2793, Summable (fun n : ℕ => if 1 ≤ n then lpNegTerm2793 x n else 0) := by
  sorry

theorem proof_gap_exercise_2793_3
  (f : ℝ -> ℝ) (n m : ℤ) (a b p : ℝ)
  (h : ∀ x ∈ lpDomain2793, f x = lpTwoSidedSum2793 x)
  (h1 : ∀ x ∈ lpDomain2793, Summable (lpPosTerm2793 x))
  (h2 : ∀ x ∈ lpDomain2793, Summable (fun n : ℕ => if 1 ≤ n then lpNegTerm2793 x n else 0))
  : ∀ x ∈ lpDomain2793, Summable (lpTerm2793 x) := by
  sorry

theorem proof_gap_exercise_2793_4
  (f : ℝ -> ℝ) (n m : ℤ) (a b p : ℝ)
  (h : ∀ x ∈ lpDomain2793, Summable (lpTerm2793 x))
  : lpDefinedOn2793 f lpDomain2793 := by
  sorry

theorem proof_gap_exercise_2793_5
  (f : ℝ -> ℝ) (n m : ℤ) (a b p : ℝ)
  (ha : ∀ x0 ∈ lpDomain2793, a = a)
  (hb : ∀ x0 ∈ lpDomain2793, b = b)
  (hp : ∀ x0, lpIntervalHyp2793 a b p x0 -> p = max |a| |b|)
  : ∀ x0, lpIntervalHyp2793 a b p x0 ->
      ∀ n : ℕ, ∀ x : ℝ, ∀ a b : ℝ, 0 < n ∧ x ∈ Set.Icc a b ∧ (n : ℝ) > p ->
        |(lpPosTerm2793 x n)| ≤ 1 /. (((n : ℝ) - p) ^ (2 : ℕ)) := by
  sorry

theorem proof_gap_exercise_2793_6
  (f : ℝ -> ℝ) (n m : ℤ) (a b p : ℝ)
  : ∀ x0, lpIntervalHyp2793 a b p x0 ->
      ∀ n : ℕ, ∀ x : ℝ, ∀ a b : ℝ, 0 < n ∧ x ∈ Set.Icc a b ∧ (n : ℝ) > p ->
        |(lpNegTerm2793 x n)| ≤ 1 /. (((n : ℝ) - p) ^ (2 : ℕ)) := by
  sorry

theorem proof_gap_exercise_2793_7
  (f : ℝ -> ℝ) (n m : ℤ) (a b p : ℝ)
  : ∀ x0, lpIntervalHyp2793 a b p x0 -> Summable (fun n : ℕ => 1 /. (((n : ℝ) - p) ^ (2 : ℕ))) := by
  sorry

theorem proof_gap_exercise_2793_8
  (f : ℝ -> ℝ) (n m : ℤ) (a b p : ℝ)
  (h : ∀ x0, lpIntervalHyp2793 a b p x0 -> Summable (fun n : ℕ => 1 /. (((n : ℝ) - p) ^ (2 : ℕ))))
  : ∀ x0, lpIntervalHyp2793 a b p x0 -> lpUniformPlus2793 a b := by
  sorry

theorem proof_gap_exercise_2793_9
  (f : ℝ -> ℝ) (n m : ℤ) (a b p : ℝ)
  (h : ∀ x0, lpIntervalHyp2793 a b p x0 -> Summable (fun n : ℕ => 1 /. (((n : ℝ) - p) ^ (2 : ℕ))))
  : ∀ x0, lpIntervalHyp2793 a b p x0 -> lpUniformMinus2793 a b := by
  sorry

theorem proof_gap_exercise_2793_10
  (f : ℝ -> ℝ) (n m : ℤ) (a b p : ℝ)
  (hplus : ∀ x0, lpIntervalHyp2793 a b p x0 -> lpUniformPlus2793 a b)
  (hminus : ∀ x0, lpIntervalHyp2793 a b p x0 -> lpUniformMinus2793 a b)
  : ∀ x0, lpIntervalHyp2793 a b p x0 -> lpUniformTwoSided2793 f a b := by
  sorry

theorem proof_gap_exercise_2793_11
  (f : ℝ -> ℝ) (n m : ℤ) (a b p : ℝ)
  (h : ∀ x0, lpIntervalHyp2793 a b p x0 -> lpUniformTwoSided2793 f a b)
  : ∀ x0, lpIntervalHyp2793 a b p x0 -> lpContinuousOn2793 f (Set.Icc a b) := by
  sorry

theorem proof_gap_exercise_2793_12
  (f : ℝ -> ℝ) (n m : ℤ) (a b p : ℝ)
  (h : ∀ x0, lpIntervalHyp2793 a b p x0 -> lpContinuousOn2793 f (Set.Icc a b))
  : ∀ x0, lpIntervalHyp2793 a b p x0 -> ContinuousWithinAt f lpDomain2793 x0 := by
  sorry

theorem proof_gap_exercise_2793_13
  (f : ℝ -> ℝ) (n m : ℤ) (a b p : ℝ)
  (h : ∀ x0, lpIntervalHyp2793 a b p x0 -> ContinuousWithinAt f lpDomain2793 x0)
  : lpContinuousOn2793 f lpDomain2793 := by
  sorry

theorem proof_gap_exercise_2793_14
  (f : ℝ -> ℝ) (n m : ℤ) (a b p : ℝ)
  (h : ∀ x ∈ lpDomain2793, f x = lpTwoSidedSum2793 x)
  : ∀ x ∈ lpDomain2793, f (x + 1) = tsum (fun n : ℤ => 1 /. (((n : ℝ) - (x + 1)) ^ (2 : ℕ))) := by
  sorry

theorem proof_gap_exercise_2793_15
  (f : ℝ -> ℝ) (n m : ℤ) (a b p : ℝ)
  : ∀ x ∈ lpDomain2793,
      tsum (fun n : ℤ => 1 /. (((n : ℝ) - (x + 1)) ^ (2 : ℕ))) =
      tsum (fun n : ℤ => 1 /. ((((n : ℝ) - 1) - x) ^ (2 : ℕ))) := by
  sorry

theorem proof_gap_exercise_2793_16
  (f : ℝ -> ℝ) (n m : ℤ) (a b p : ℝ)
  : ∀ x ∈ lpDomain2793, m = n - 1 := by
  sorry

theorem proof_gap_exercise_2793_17
  (f : ℝ -> ℝ) (n m : ℤ) (a b p : ℝ)
  : ∀ x ∈ lpDomain2793,
      tsum (fun n : ℤ => 1 /. ((((n : ℝ) - 1) - x) ^ (2 : ℕ))) =
      tsum (fun m : ℤ => 1 /. (((m : ℝ) - x) ^ (2 : ℕ))) := by
  sorry

theorem proof_gap_exercise_2793_18
  (f : ℝ -> ℝ) (n m : ℤ) (a b p : ℝ)
  (h14 : ∀ x ∈ lpDomain2793, f (x + 1) = tsum (fun n : ℤ => 1 /. (((n : ℝ) - (x + 1)) ^ (2 : ℕ))))
  (h15 : ∀ x ∈ lpDomain2793, tsum (fun n : ℤ => 1 /. (((n : ℝ) - (x + 1)) ^ (2 : ℕ))) = tsum (fun n : ℤ => 1 /. ((((n : ℝ) - 1) - x) ^ (2 : ℕ))))
  (h17 : ∀ x ∈ lpDomain2793, tsum (fun n : ℤ => 1 /. ((((n : ℝ) - 1) - x) ^ (2 : ℕ))) = tsum (fun m : ℤ => 1 /. (((m : ℝ) - x) ^ (2 : ℕ))))
  (hdef : ∀ x ∈ lpDomain2793, f x = lpTwoSidedSum2793 x)
  : ∀ x ∈ lpDomain2793, f (x + 1) = f x := by
  sorry

theorem proof_gap_exercise_2793_19
  (f : ℝ -> ℝ) (n m : ℤ) (a b p : ℝ)
  (h : ∀ x ∈ lpDomain2793, f (x + 1) = f x)
  : lpPeriodic2793 f := by
  sorry

theorem proof_gap_exercise_2793_20
  (f : ℝ -> ℝ) (n m : ℤ) (a b p : ℝ)
  (hper : lpPeriodic2793 f)
  : lpDefinedOn2793 f lpDomain2793 := by
  sorry

theorem proof_gap_exercise_2793_21
  (f : ℝ -> ℝ) (n m : ℤ) (a b p : ℝ)
  (hdef : lpDefinedOn2793 f lpDomain2793)
  (hcont : lpContinuousOn2793 f lpDomain2793)
  (hper : lpPeriodic2793 f)
  : lpPeriodic2793 f := by
  sorry

theorem proof_gap_exercise_2793_22
  (f : ℝ -> ℝ) (n m : ℤ) (a b p : ℝ)
  (hdef : lpDefinedOn2793 f lpDomain2793)
  (hcont : lpContinuousOn2793 f lpDomain2793)
  (hper : lpPeriodic2793 f)
  : lpDefinedOn2793 f lpDomain2793 ∧ lpContinuousOn2793 f lpDomain2793 ∧ lpPeriodic2793 f := by
  sorry
