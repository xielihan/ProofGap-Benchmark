import ProofGapLean.Prelude.Sequences
import ProofGapLean.Prelude.Finite
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise425

open scoped BigOperators

noncomputable section

def geometricSum (n : ℕ) (x : ℝ) : ℝ :=
  (Finset.range n).sum (fun i => x ^ i)
def original (m n : ℕ) (x : ℝ) : ℝ := (x ^ m - 1) / (x ^ n - 1)
def cancelled (m n : ℕ) (x : ℝ) : ℝ := geometricSum m x / geometricSum n x
def HasLimitAt (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds L)

/-- Exercise 425, gap 1; replace ellipses by geometric sums. -/
private theorem geometricSum_factor (n : ℕ) (x : ℝ) :
    (x - 1) * geometricSum n x = x ^ n - 1 := by
  induction n with
  | zero =>
      simp [geometricSum]
  | succ n ih =>
      unfold geometricSum at ih ⊢
      rw [Finset.sum_range_succ, pow_succ]
      calc
        (x - 1) * ((Finset.range n).sum (fun i => x ^ i) + x ^ n) =
            (x - 1) * (Finset.range n).sum (fun i => x ^ i) +
              (x - 1) * x ^ n := by ring
        _ = (x ^ n - 1) + (x - 1) * x ^ n := by rw [ih]
        _ = x ^ n * x - 1 := by ring

private theorem continuous_geometricSum (n : ℕ) :
    Continuous (geometricSum n) := by
  unfold geometricSum
  fun_prop

private theorem geometricSum_one (n : ℕ) :
    geometricSum n 1 = (n : ℝ) := by
  simp [geometricSum]

private theorem cancelled_hasLimit (m n : ℕ) (hn : 0 < n) :
    HasLimitAt (cancelled m n) 1 ((m : ℝ) / n) := by
  unfold HasLimitAt cancelled
  have hm_lim :
      Filter.Tendsto (geometricSum m)
        (nhdsWithin (1 : ℝ) ({1} : Set ℝ)ᶜ) (nhds (m : ℝ)) := by
    rw [← geometricSum_one m]
    exact (continuous_geometricSum m).continuousAt.mono_left inf_le_left
  have hn_lim :
      Filter.Tendsto (geometricSum n)
        (nhdsWithin (1 : ℝ) ({1} : Set ℝ)ᶜ) (nhds (n : ℝ)) := by
    rw [← geometricSum_one n]
    exact (continuous_geometricSum n).continuousAt.mono_left inf_le_left
  have hn0 : (n : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr hn)
  exact hm_lim.div hn_lim hn0

private theorem original_eventuallyEq_cancelled (m n : ℕ) :
    original m n =ᶠ[nhdsWithin (1 : ℝ) ({1} : Set ℝ)ᶜ] cancelled m n := by
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx1 : x ≠ 1 := by
    simpa using hx
  change (x ^ m - 1) / (x ^ n - 1) =
    geometricSum m x / geometricSum n x
  rw [← geometricSum_factor m x, ← geometricSum_factor n x]
  exact mul_div_mul_left _ _ (sub_ne_zero.mpr hx1)

theorem gap1 (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    HasLimitAt (original m n) 1 ((m : ℝ) / n) ↔
      HasLimitAt (cancelled m n) 1 ((m : ℝ) / n) := by
  unfold HasLimitAt
  constructor
  · intro h
    exact h.congr' (original_eventuallyEq_cancelled m n)
  · intro h
    apply h.congr'
    filter_upwards [original_eventuallyEq_cancelled m n] with x hx
    exact hx.symm

/-- Exercise 425, gap 2. -/
theorem gap2 (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    HasLimitAt (cancelled m n) 1 ((m : ℝ) / n) := by
  exact cancelled_hasLimit m n hn

/-- Exercise 425, gap 3. -/
theorem gap3 (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    HasLimitAt (original m n) 1 ((m : ℝ) / n) := by
  exact (gap1 m n hm hn).2 (gap2 m n hm hn)

end

end ProofGap.Exercise425
