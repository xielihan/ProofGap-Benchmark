import ProofGapLean.Prelude.Sequences
import ProofGapLean.Prelude.Finite
import ProofGapLean.Prelude.Discrete
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise414

open scoped BigOperators

noncomputable section

def h (m n : ℕ) (x : ℝ) : ℝ :=
  ((1 + (m : ℝ) * x) ^ n - (1 + (n : ℝ) * x) ^ m) / x ^ 2

def binomialExpansion (r s : ℕ) (x : ℝ) : ℝ :=
  (Finset.range (s + 1)).sum
    (fun k => (s.choose k : ℝ) * ((r : ℝ) * x) ^ k)

def HasLimitAt (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds L)

def quadraticCoefficient (m n : ℕ) : ℝ :=
  (n.choose 2 : ℝ) * (m : ℝ) ^ 2 -
    (m.choose 2 : ℝ) * (n : ℝ) ^ 2

def finalValue (m n : ℕ) : ℝ :=
  (1 / 2 : ℝ) * m * n * ((n : ℝ) - m)

/-- Exercise 414, gap 1; replace ellipses by finite binomial sums. -/
private theorem binomialExpansion_eq_pow (r s : ℕ) (x : ℝ) :
    binomialExpansion r s x = (1 + (r : ℝ) * x) ^ s := by
  unfold binomialExpansion
  simpa [add_comm, mul_comm, mul_left_comm, mul_assoc] using
    (add_pow ((r : ℝ) * x) 1 s).symm

private def quadraticRemainder : ℕ → ℝ → ℝ → ℝ
  | 0, _, _ => 0
  | Nat.succ s, a, x =>
      quadraticRemainder s a x * (1 + a * x) + (s : ℝ) * a ^ 2

private theorem pow_sub_linear_eq (s : ℕ) (a x : ℝ) :
    (1 + a * x) ^ s - 1 - (s : ℝ) * a * x =
      x ^ 2 * quadraticRemainder s a x := by
  induction s with
  | zero =>
      simp [quadraticRemainder]
  | succ s ih =>
      rw [quadraticRemainder, pow_succ, Nat.cast_succ]
      calc
        (1 + a * x) ^ s * (1 + a * x) - 1 -
              ((s : ℝ) + 1) * a * x =
            ((1 + a * x) ^ s - 1 - (s : ℝ) * a * x) *
                (1 + a * x) +
              (s : ℝ) * a ^ 2 * x ^ 2 := by
                ring
        _ = (x ^ 2 * quadraticRemainder s a x) * (1 + a * x) +
              (s : ℝ) * a ^ 2 * x ^ 2 := by
                rw [ih]
        _ = x ^ 2 *
              (quadraticRemainder s a x * (1 + a * x) +
                (s : ℝ) * a ^ 2) := by
                ring

private theorem quadraticRemainder_continuous (s : ℕ) (a : ℝ) :
    Continuous (fun x : ℝ => quadraticRemainder s a x) := by
  induction s with
  | zero =>
      simpa [quadraticRemainder] using
        (continuous_const : Continuous (fun _ : ℝ => (0 : ℝ)))
  | succ s ih =>
      have hlin : Continuous (fun x : ℝ => 1 + a * x) :=
        continuous_const.add (continuous_const.mul continuous_id)
      have hc : Continuous (fun _ : ℝ => (s : ℝ) * a ^ 2) :=
        continuous_const
      simpa only [quadraticRemainder] using (ih.mul hlin).add hc

private theorem choose_two_cast (s : ℕ) :
    (s.choose 2 : ℝ) = (s : ℝ) * ((s : ℝ) - 1) / 2 := by
  induction s with
  | zero =>
      norm_num
  | succ s ih =>
      rw [Nat.choose_succ_succ, Nat.choose_one_right, Nat.cast_add,
        Nat.cast_succ, ih]
      ring

private theorem quadraticRemainder_zero_formula (s : ℕ) (a : ℝ) :
    quadraticRemainder s a 0 =
      ((s : ℝ) * ((s : ℝ) - 1) / 2) * a ^ 2 := by
  induction s with
  | zero =>
      simp [quadraticRemainder]
  | succ s ih =>
      simp only [quadraticRemainder, mul_zero, add_zero, mul_one]
      rw [ih, Nat.cast_succ]
      ring

private theorem quadraticRemainder_zero (s : ℕ) (a : ℝ) :
    quadraticRemainder s a 0 = (s.choose 2 : ℝ) * a ^ 2 := by
  rw [quadraticRemainder_zero_formula, choose_two_cast]

theorem gap1 (m n : ℕ) : ∀ x, x ≠ 0 →
    h m n x =
      (binomialExpansion m n x - binomialExpansion n m x) / x ^ 2 := by
  intro x hx
  simpa [h, binomialExpansion_eq_pow]

/-- Exercise 414, gap 2; express the little-o statement by its resulting limit. -/
theorem gap2 (m n : ℕ) :
    HasLimitAt (h m n) 0 (quadraticCoefficient m n) := by
  unfold HasLimitAt
  have hfull :
      Filter.Tendsto
        (fun x : ℝ =>
          quadraticRemainder n (m : ℝ) x -
            quadraticRemainder m (n : ℝ) x)
        (nhds 0) (nhds (quadraticCoefficient m n)) := by
    have hcont :
        ContinuousAt
          (fun x : ℝ =>
            quadraticRemainder n (m : ℝ) x -
              quadraticRemainder m (n : ℝ) x) 0 :=
      (quadraticRemainder_continuous n (m : ℝ)).continuousAt.sub
        (quadraticRemainder_continuous m (n : ℝ)).continuousAt
    have hzero :
        quadraticRemainder n (m : ℝ) 0 -
            quadraticRemainder m (n : ℝ) 0 =
          quadraticCoefficient m n := by
      simp only [quadraticCoefficient, quadraticRemainder_zero]
    rw [← hzero]
    exact hcont
  have hlim :
      Filter.Tendsto
        (fun x : ℝ =>
          quadraticRemainder n (m : ℝ) x -
            quadraticRemainder m (n : ℝ) x)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
        (nhds (quadraticCoefficient m n)) :=
    hfull.mono_left inf_le_left
  have heq :
      h m n =ᶠ[nhdsWithin 0 ({0} : Set ℝ)ᶜ]
        (fun x : ℝ =>
          quadraticRemainder n (m : ℝ) x -
            quadraticRemainder m (n : ℝ) x) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := by
      simpa using hx
    have hnum :
        (1 + (m : ℝ) * x) ^ n - (1 + (n : ℝ) * x) ^ m =
          x ^ 2 *
            (quadraticRemainder n (m : ℝ) x -
              quadraticRemainder m (n : ℝ) x) := by
      calc
        (1 + (m : ℝ) * x) ^ n - (1 + (n : ℝ) * x) ^ m =
            ((1 + (m : ℝ) * x) ^ n - 1 - (n : ℝ) * (m : ℝ) * x) -
              ((1 + (n : ℝ) * x) ^ m - 1 - (m : ℝ) * (n : ℝ) * x) := by
                ring
        _ = x ^ 2 * quadraticRemainder n (m : ℝ) x -
              x ^ 2 * quadraticRemainder m (n : ℝ) x := by
                rw [pow_sub_linear_eq, pow_sub_linear_eq]
        _ = x ^ 2 *
              (quadraticRemainder n (m : ℝ) x -
                quadraticRemainder m (n : ℝ) x) := by
                ring
    simp only [h]
    rw [hnum]
    have hx2 : x ^ 2 ≠ 0 := pow_ne_zero 2 hx0
    apply (div_eq_iff hx2).2
    ring
  exact hlim.congr' heq.symm

/-- Exercise 414, gap 3. -/
theorem gap3 (m n : ℕ) :
    quadraticCoefficient m n = finalValue m n := by
  simp only [quadraticCoefficient, finalValue, choose_two_cast]
  ring

/-- Exercise 414, gap 4. -/
theorem gap4 (m n : ℕ) :
    HasLimitAt (h m n) 0 (finalValue m n) := by
  simpa only [gap3] using gap2 m n

/-- Exercise 414, gap 5. -/
theorem gap5 (m n : ℕ) :
    HasLimitAt (h m n) 0 (finalValue m n) := by
  exact gap4 m n

end

end ProofGap.Exercise414
