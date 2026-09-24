import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise3004

noncomputable section

open scoped BigOperators

def factorialR (n : ℕ) : ℝ := (n.factorial : ℝ)

def targetSeries (x : ℝ) : ℝ :=
  ∑' n : ℕ,
    ((-1 : ℝ) ^ n * (2 * (n : ℝ) ^ 2 + 1) / factorialR (2 * n)) *
      x ^ (2 * n)

def cosineSeries (x : ℝ) : ℝ :=
  ∑' n : ℕ, (-1 : ℝ) ^ n * x ^ (2 * n) / factorialR (2 * n)

def shiftedCosineSeries (x : ℝ) : ℝ :=
  ∑' n : ℕ, (-1 : ℝ) ^ n * x ^ (2 * n) / factorialR (2 * n)

def shiftedSineSeries (x : ℝ) : ℝ :=
  ∑' n : ℕ, (-1 : ℝ) ^ n * x ^ (2 * n + 1) / factorialR (2 * n + 1)

private theorem factorialR_succ (k : ℕ) :
    factorialR (k + 1) = ((k + 1 : ℕ) : ℝ) * factorialR k := by
  simp only [factorialR, Nat.factorial_succ, Nat.cast_mul]

theorem gap1 (n : ℕ) (hn : 1 ≤ n) :
    (2 * (n : ℝ) ^ 2 + 1) / factorialR (2 * n) =
      (1 / 2 : ℝ) / factorialR (2 * n - 2) +
      (1 / 2 : ℝ) / factorialR (2 * n - 1) +
      1 / factorialR (2 * n) := by
  have hpred : 2 * n - 1 = (2 * n - 2) + 1 := by omega
  have hcurr : 2 * n = (2 * n - 1) + 1 := by omega
  have hf1 :
      factorialR (2 * n - 1) =
        ((2 * n - 1 : ℕ) : ℝ) * factorialR (2 * n - 2) := by
    calc
      factorialR (2 * n - 1) = factorialR ((2 * n - 2) + 1) :=
        congrArg factorialR hpred
      _ = ((((2 * n - 2) + 1 : ℕ) : ℝ) * factorialR (2 * n - 2)) :=
        factorialR_succ (2 * n - 2)
      _ = ((2 * n - 1 : ℕ) : ℝ) * factorialR (2 * n - 2) := by
        rw [← hpred]
  have hf2 :
      factorialR (2 * n) =
        ((2 * n : ℕ) : ℝ) * factorialR (2 * n - 1) := by
    calc
      factorialR (2 * n) = factorialR ((2 * n - 1) + 1) :=
        congrArg factorialR hcurr
      _ = ((((2 * n - 1) + 1 : ℕ) : ℝ) * factorialR (2 * n - 1)) :=
        factorialR_succ (2 * n - 1)
      _ = ((2 * n : ℕ) : ℝ) * factorialR (2 * n - 1) := by
        rw [← hcurr]
  have hle : 1 ≤ 2 * n := by omega
  have hc1 : ((2 * n - 1 : ℕ) : ℝ) = 2 * (n : ℝ) - 1 := by
    rw [Nat.cast_sub hle]
    norm_num
  have hc2 : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by
    norm_num
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have htwo : 2 * (n : ℝ) ≠ 0 := by nlinarith
  have hone : 2 * (n : ℝ) - 1 ≠ 0 := by nlinarith
  have hFNat : 0 < (2 * n - 2).factorial := Nat.factorial_pos _
  have hFpos : (0 : ℝ) < factorialR (2 * n - 2) := by
    unfold factorialR
    exact_mod_cast hFNat
  have hF : factorialR (2 * n - 2) ≠ 0 := ne_of_gt hFpos
  rw [hf2, hf1, hc2, hc1]
  field_simp [hF, htwo, hone] <;> ring

theorem gap2 (x : ℝ) :
    targetSeries x =
      1 +
      (1 / 2 : ℝ) *
        (∑' n : ℕ,
          (-1 : ℝ) ^ (n + 1) * x ^ (2 * (n + 1)) / factorialR (2 * n)) +
      (1 / 2 : ℝ) *
        (∑' n : ℕ,
          (-1 : ℝ) ^ (n + 1) * x ^ (2 * (n + 1)) / factorialR (2 * n + 1)) +
      (∑' n : ℕ,
        (-1 : ℝ) ^ (n + 1) * x ^ (2 * (n + 1)) / factorialR (2 * (n + 1))) := by
  let c : ℕ → ℝ := fun n =>
    (-1 : ℝ) ^ n * x ^ (2 * n) / factorialR (2 * n)
  let s : ℕ → ℝ := fun n =>
    (-1 : ℝ) ^ n * x ^ (2 * n + 1) / factorialR (2 * n + 1)
  let a : ℕ → ℝ := fun n =>
    (-1 : ℝ) ^ (n + 1) * x ^ (2 * (n + 1)) / factorialR (2 * n)
  let b : ℕ → ℝ := fun n =>
    (-1 : ℝ) ^ (n + 1) * x ^ (2 * (n + 1)) / factorialR (2 * n + 1)
  let d : ℕ → ℝ := fun n =>
    (-1 : ℝ) ^ (n + 1) * x ^ (2 * (n + 1)) /
      factorialR (2 * (n + 1))
  let t : ℕ → ℝ := fun n =>
    ((-1 : ℝ) ^ n * (2 * (n : ℝ) ^ 2 + 1) / factorialR (2 * n)) *
      x ^ (2 * n)
  have hc : Summable c := by
    dsimp [c]
    simpa [factorialR] using (Real.hasSum_cos x).summable
  have hs : Summable s := by
    dsimp [s]
    simpa [factorialR] using (Real.hasSum_sin x).summable
  have ha : Summable a := by
    refine (hc.mul_left (-x ^ 2)).congr ?_
    intro n
    dsimp [a, c]
    simp [pow_succ, Nat.mul_add] <;> ring
  have hb : Summable b := by
    refine (hs.mul_left (-x)).congr ?_
    intro n
    dsimp [b, s]
    simp [pow_succ, Nat.mul_add] <;> ring
  have hinj : Function.Injective (fun n : ℕ => n + 1) := by
    intro m n hmn
    exact Nat.add_right_cancel hmn
  have hd : Summable d := by
    simpa [d, c, Function.comp_def] using hc.comp_injective hinj
  have hsplit (n : ℕ) :
      t (n + 1) = (1 / 2 : ℝ) * a n + ((1 / 2 : ℝ) * b n + d n) := by
    dsimp [t, a, b, d]
    calc
      (-1 : ℝ) ^ (n + 1) *
            (2 * (((n + 1 : ℕ) : ℝ)) ^ 2 + 1) /
            factorialR (2 * (n + 1)) * x ^ (2 * (n + 1)) =
          (-1 : ℝ) ^ (n + 1) *
            ((2 * (((n + 1 : ℕ) : ℝ)) ^ 2 + 1) /
              factorialR (2 * (n + 1))) * x ^ (2 * (n + 1)) := by
        ring
      _ =
          (1 / 2 : ℝ) *
              ((-1 : ℝ) ^ (n + 1) * x ^ (2 * (n + 1)) /
                factorialR (2 * n)) +
            ((1 / 2 : ℝ) *
                ((-1 : ℝ) ^ (n + 1) * x ^ (2 * (n + 1)) /
                  factorialR (2 * n + 1)) +
              (-1 : ℝ) ^ (n + 1) * x ^ (2 * (n + 1)) /
                factorialR (2 * (n + 1))) := by
        rw [gap1 (n + 1) (by omega)]
        have h0 : 2 * (n + 1) - 2 = 2 * n := by omega
        have h1 : 2 * (n + 1) - 1 = 2 * n + 1 := by omega
        rw [h0, h1]
        ring
  have hshift :
      Summable (fun n => (1 / 2 : ℝ) * a n + ((1 / 2 : ℝ) * b n + d n)) :=
    (ha.mul_left (1 / 2 : ℝ)).add
      ((hb.mul_left (1 / 2 : ℝ)).add hd)
  have ht : Summable t := by
    rw [← summable_nat_add_iff 1]
    refine hshift.congr ?_
    intro n
    simpa [Nat.add_comm] using (hsplit n).symm
  change (∑' n : ℕ, t n) = _
  calc
    (∑' n : ℕ, t n) =
        (∑ n ∈ Finset.range 1, t n) + (∑' n : ℕ, t (n + 1)) :=
      (ht.sum_add_tsum_nat_add 1).symm
    _ = 1 +
        (∑' n : ℕ, ((1 / 2 : ℝ) * a n + ((1 / 2 : ℝ) * b n + d n))) := by
      congr 1
      · simp [t, factorialR]
      · apply tsum_congr
        intro n
        exact hsplit n
    _ = 1 +
        ((1 / 2 : ℝ) * (∑' n : ℕ, a n) +
          ((1 / 2 : ℝ) * (∑' n : ℕ, b n) + (∑' n : ℕ, d n))) := by
      congr 1
      exact
        ((ha.hasSum.mul_left (1 / 2 : ℝ)).add
          ((hb.hasSum.mul_left (1 / 2 : ℝ)).add hd.hasSum)).tsum_eq
    _ = 1 + (1 / 2 : ℝ) * (∑' n : ℕ, a n) +
          (1 / 2 : ℝ) * (∑' n : ℕ, b n) + (∑' n : ℕ, d n) := by
      ring
    _ = _ := by rfl

theorem gap3 (x : ℝ) :
    targetSeries x =
      1 - x ^ 2 / 2 * shiftedCosineSeries x -
        x / 2 * shiftedSineSeries x + cosineSeries x - 1 := by
  let c : ℕ → ℝ := fun n =>
    (-1 : ℝ) ^ n * x ^ (2 * n) / factorialR (2 * n)
  let s : ℕ → ℝ := fun n =>
    (-1 : ℝ) ^ n * x ^ (2 * n + 1) / factorialR (2 * n + 1)
  let a : ℕ → ℝ := fun n =>
    (-1 : ℝ) ^ (n + 1) * x ^ (2 * (n + 1)) / factorialR (2 * n)
  let b : ℕ → ℝ := fun n =>
    (-1 : ℝ) ^ (n + 1) * x ^ (2 * (n + 1)) / factorialR (2 * n + 1)
  let d : ℕ → ℝ := fun n =>
    (-1 : ℝ) ^ (n + 1) * x ^ (2 * (n + 1)) /
      factorialR (2 * (n + 1))
  have hc : Summable c := by
    dsimp [c]
    simpa [factorialR] using (Real.hasSum_cos x).summable
  have hs : Summable s := by
    dsimp [s]
    simpa [factorialR] using (Real.hasSum_sin x).summable
  have hA : (∑' n : ℕ, a n) = -x ^ 2 * shiftedCosineSeries x := by
    calc
      (∑' n : ℕ, a n) = (∑' n : ℕ, (-x ^ 2) * c n) := by
        apply tsum_congr
        intro n
        dsimp [a, c]
        simp [pow_succ, pow_add, Nat.mul_add] <;> ring
      _ = -x ^ 2 * shiftedCosineSeries x := by
        simpa [c, shiftedCosineSeries] using
          (hc.hasSum.mul_left (-x ^ 2)).tsum_eq
  have hB : (∑' n : ℕ, b n) = -x * shiftedSineSeries x := by
    calc
      (∑' n : ℕ, b n) = (∑' n : ℕ, (-x) * s n) := by
        apply tsum_congr
        intro n
        dsimp [b, s]
        simp [pow_succ, pow_add, Nat.mul_add] <;> ring
      _ = -x * shiftedSineSeries x := by
        simpa [s, shiftedSineSeries] using
          (hs.hasSum.mul_left (-x)).tsum_eq
  have htail : (∑' n : ℕ, d n) = cosineSeries x - 1 := by
    have hsum : 1 + (∑' n : ℕ, d n) = cosineSeries x := by
      simpa [c, d, cosineSeries, factorialR, Nat.add_comm] using
        hc.sum_add_tsum_nat_add 1
    linarith
  rw [gap2 x]
  change 1 + (1 / 2 : ℝ) * (∑' n : ℕ, a n) +
      (1 / 2 : ℝ) * (∑' n : ℕ, b n) + (∑' n : ℕ, d n) = _
  rw [hA, hB, htail]
  ring

theorem gap4 (x : ℝ) :
    targetSeries x =
      1 - x ^ 2 / 2 * Real.cos x -
        x / 2 * Real.sin x + Real.cos x - 1 := by
  have hcos : cosineSeries x = Real.cos x := by
    simpa [cosineSeries, factorialR] using (Real.cos_eq_tsum x).symm
  have hshiftCos : shiftedCosineSeries x = Real.cos x := by
    simpa [shiftedCosineSeries, factorialR] using (Real.cos_eq_tsum x).symm
  have hshiftSin : shiftedSineSeries x = Real.sin x := by
    simpa [shiftedSineSeries, factorialR] using (Real.sin_eq_tsum x).symm
  rw [gap3 x, hcos, hshiftCos, hshiftSin]

theorem gap5 (x : ℝ) :
    1 - x ^ 2 / 2 * Real.cos x - x / 2 * Real.sin x + Real.cos x - 1 =
      (1 - x ^ 2 / 2) * Real.cos x - x / 2 * Real.sin x := by
  ring

theorem gap6 (x : ℝ) :
    targetSeries x =
      (1 - x ^ 2 / 2) * Real.cos x - x / 2 * Real.sin x := by
  rw [gap4 x, gap5 x]

end

end ProofGap.Exercise3004
