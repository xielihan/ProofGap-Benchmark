import ProofGapLean.Prelude.Sequences
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise2569

noncomputable section

def squareSeq (a : ℕ → ℝ) (n : ℕ) : ℝ := (a n) ^ 2
def productAbs (a b : ℕ → ℝ) (n : ℕ) : ℝ := |a n * b n|
def sumSquare (a b : ℕ → ℝ) (n : ℕ) : ℝ := (a n + b n) ^ 2
def harmonic (n : ℕ) : ℝ := 1 / (n : ℝ)

theorem gap1
    (a b : ℕ → ℝ)
    (ha : Summable (squareSeq a))
    (hb : Summable (squareSeq b)) :
    ∀ n, 0 ≤ 2 * |a n * b n| := by
  intro n
  exact mul_nonneg (by norm_num) (abs_nonneg _)

theorem gap2
    (a b : ℕ → ℝ)
    (ha : Summable (squareSeq a))
    (hb : Summable (squareSeq b))
    (hpos : ∀ n, 0 ≤ 2 * |a n * b n|) :
    ∀ n, 2 * |a n * b n| ≤ (a n) ^ 2 + (b n) ^ 2 := by
  intro n
  calc
    2 * |a n * b n| = 2 * (|a n| * |b n|) := by rw [abs_mul]
    _ ≤ |a n| ^ 2 + |b n| ^ 2 := by
      nlinarith [sq_nonneg (|a n| - |b n|)]
    _ = (a n) ^ 2 + (b n) ^ 2 := by rw [sq_abs, sq_abs]

theorem gap3
    (a b : ℕ → ℝ)
    (ha : Summable (squareSeq a))
    (hb : Summable (squareSeq b))
    (hbound : ∀ n, 2 * |a n * b n| ≤ (a n) ^ 2 + (b n) ^ 2) :
    ∀ n, 0 ≤ (a n) ^ 2 + (b n) ^ 2 := by
  intro n
  exact add_nonneg (sq_nonneg (a n)) (sq_nonneg (b n))

theorem gap4
    (a b : ℕ → ℝ)
    (ha : Summable (squareSeq a))
    (hb : Summable (squareSeq b)) :
    Summable (fun n => (a n) ^ 2 + (b n) ^ 2) := by
  simpa [squareSeq] using ha.add hb

theorem gap5
    (a b : ℕ → ℝ)
    (hpos : ∀ n, 0 ≤ 2 * |a n * b n|)
    (hbound : ∀ n, 2 * |a n * b n| ≤ (a n) ^ 2 + (b n) ^ 2)
    (hsquares : Summable (fun n => (a n) ^ 2 + (b n) ^ 2)) :
    Summable (productAbs a b) := by
  refine hsquares.of_norm_bounded ?_
  intro n
  simp only [productAbs, Real.norm_eq_abs, abs_abs]
  nlinarith [hpos n, hbound n, abs_nonneg (a n * b n)]

theorem gap6
    (a b : ℕ → ℝ)
    (hproduct : Summable (productAbs a b)) :
    ∀ n, sumSquare a b n =
      (a n) ^ 2 + (b n) ^ 2 + 2 * a n * b n := by
  intro n
  simp only [sumSquare]
  ring

theorem gap7
    (a b : ℕ → ℝ)
    (ha : Summable (squareSeq a))
    (hb : Summable (squareSeq b))
    (hproduct : Summable (productAbs a b))
    (hexpand : ∀ n, sumSquare a b n =
      (a n) ^ 2 + (b n) ^ 2 + 2 * a n * b n) :
    Summable (sumSquare a b) := by
  have hsquares : Summable (fun n => (a n) ^ 2 + (b n) ^ 2) :=
    gap4 a b ha hb
  have hmajor :
      Summable (fun n =>
        ((a n) ^ 2 + (b n) ^ 2) + ((a n) ^ 2 + (b n) ^ 2)) :=
    hsquares.add hsquares
  refine hmajor.of_norm_bounded ?_
  intro n
  simp only [sumSquare, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg (a n + b n))]
  nlinarith [sq_nonneg (a n - b n)]

theorem gap8
    (a b : ℕ → ℝ)
    (hproduct : Summable (productAbs a b))
    (hb : ∀ n, b n = harmonic n) :
    Summable (fun n => |a n| / (n : ℝ)) := by
  refine hproduct.congr ?_
  intro n
  rw [productAbs, hb n, harmonic, abs_mul,
    abs_of_nonneg
      (div_nonneg zero_le_one
        (show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n))]
  simp [div_eq_mul_inv]

theorem gap9
    (a b : ℕ → ℝ)
    (hproduct : Summable (productAbs a b))
    (hsumSquare : Summable (sumSquare a b))
    (hb : ∀ n, b n = harmonic n)
    (hweighted : Summable (fun n => |a n| / (n : ℝ))) :
    Summable (productAbs a b) ∧
      Summable (sumSquare a b) ∧
      Summable (fun n => |a n| / (n : ℝ)) := by
  exact ⟨hproduct, hsumSquare, hweighted⟩

end

end ProofGap.Exercise2569
