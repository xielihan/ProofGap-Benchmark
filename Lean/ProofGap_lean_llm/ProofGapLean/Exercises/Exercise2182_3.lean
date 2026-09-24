import ProofGapLean.Prelude.Finite
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise2182_3
noncomputable section

open scoped BigOperators

def h (n : ℕ) : ℝ := 10 / (n : ℝ)
def powTwo (x : ℝ) : ℝ := Real.rpow 2 x
def m (n i : ℕ) : ℝ := powTwo ((i : ℝ) * h n)
def M (n i : ℕ) : ℝ := powTwo (((i : ℝ) + 1) * h n)
def lowerSum (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, h n * m n i
def upperSum (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, h n * M n i

private theorem powTwo_add (x y : ℝ) :
    powTwo (x + y) = powTwo x * powTwo y := by
  unfold powTwo
  change (2 : ℝ) ^ (x + y) = (2 : ℝ) ^ x * (2 : ℝ) ^ y
  exact Real.rpow_add (by norm_num : (0 : ℝ) < 2) x y

private theorem powTwo_nat_mul (x : ℝ) (i : ℕ) :
    powTwo ((i : ℝ) * x) = (powTwo x) ^ i := by
  induction i with
  | zero =>
      simp [powTwo]
  | succ i ih =>
      rw [Nat.cast_succ, add_mul, one_mul, powTwo_add, ih, pow_succ]

private theorem powTwo_succ_mul (x : ℝ) (i : ℕ) :
    powTwo (((i : ℝ) + 1) * x) =
      powTwo x * powTwo ((i : ℝ) * x) := by
  rw [add_mul, one_mul, powTwo_add]
  ring

private theorem powTwo_sub_one_ne_zero_of_pos {x : ℝ} (hx : 0 < x) :
    powTwo x - 1 ≠ 0 := by
  apply sub_ne_zero.mpr
  apply ne_of_gt
  unfold powTwo
  exact Real.one_lt_rpow (by norm_num : (1 : ℝ) < 2) hx

private theorem powTwo_ten : powTwo 10 = 1024 := by
  calc
    powTwo 10 = powTwo ((10 : ℝ) * 1) := by norm_num
    _ = (powTwo 1) ^ (10 : ℕ) := powTwo_nat_mul 1 10
    _ = 1024 := by norm_num [powTwo]

theorem gap1 (n i : ℕ) (hn : 0 < n) (hi : i < n) :
    m n i = powTwo ((i : ℝ) * h n) ∧
      M n i = powTwo (((i : ℝ) + 1) * h n) := by
  constructor <;> rfl

theorem gap2 (n : ℕ) (hn : 0 < n) :
    lowerSum n = ∑ i ∈ Finset.range n, h n * powTwo ((i : ℝ) * h n) := by
  rfl

theorem gap3 (n : ℕ) (hn : 0 < n) :
    (∑ i ∈ Finset.range n, h n * powTwo ((i : ℝ) * h n)) =
      h n * (powTwo ((n : ℝ) * h n) - 1) / (powTwo (h n) - 1) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hh : 0 < h n := by
    unfold h
    exact div_pos (by norm_num) hnpos
  have hq : powTwo (h n) - 1 ≠ 0 :=
    powTwo_sub_one_ne_zero_of_pos hh
  rw [powTwo_nat_mul (h n) n]
  calc
    (∑ i ∈ Finset.range n, h n * powTwo ((i : ℝ) * h n)) =
        h n * ∑ i ∈ Finset.range n, (powTwo (h n)) ^ i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [powTwo_nat_mul]
    _ = h n * ((powTwo (h n)) ^ n - 1) / (powTwo (h n) - 1) := by
      apply (eq_div_iff hq).2
      rw [mul_assoc, geom_sum_mul]

theorem gap4 (n : ℕ) (hn : 0 < n) :
    h n * (powTwo ((n : ℝ) * h n) - 1) / (powTwo (h n) - 1) =
      10230 / ((n : ℝ) * (powTwo (10 / (n : ℝ)) - 1)) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have hexp : 0 < 10 / (n : ℝ) := div_pos (by norm_num) hnpos
  have hq : powTwo (10 / (n : ℝ)) - 1 ≠ 0 :=
    powTwo_sub_one_ne_zero_of_pos hexp
  have hnh : (n : ℝ) * h n = 10 := by
    unfold h
    field_simp [hn0] <;> ring
  rw [hnh, powTwo_ten]
  simp only [h]
  field_simp [hn0, hq] <;> ring

theorem gap5 (n : ℕ) (hn : 0 < n) :
    lowerSum n =
      10230 / ((n : ℝ) * (powTwo (10 / (n : ℝ)) - 1)) := by
  calc
    lowerSum n =
        ∑ i ∈ Finset.range n, h n * powTwo ((i : ℝ) * h n) := gap2 n hn
    _ = h n * (powTwo ((n : ℝ) * h n) - 1) /
        (powTwo (h n) - 1) := gap3 n hn
    _ = 10230 /
        ((n : ℝ) * (powTwo (10 / (n : ℝ)) - 1)) := gap4 n hn

theorem gap6 (n : ℕ) (hn : 0 < n) :
    upperSum n =
      ∑ i ∈ Finset.range n, h n * powTwo (((i : ℝ) + 1) * h n) := by
  rfl

theorem gap7 (n : ℕ) (hn : 0 < n) :
    (∑ i ∈ Finset.range n, h n * powTwo (((i : ℝ) + 1) * h n)) =
      h n * powTwo (h n) * (powTwo ((n : ℝ) * h n) - 1) /
        (powTwo (h n) - 1) := by
  calc
    (∑ i ∈ Finset.range n,
        h n * powTwo (((i : ℝ) + 1) * h n)) =
        powTwo (h n) *
          (∑ i ∈ Finset.range n,
            h n * powTwo ((i : ℝ) * h n)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [powTwo_succ_mul]
      ring
    _ = powTwo (h n) *
        (h n * (powTwo ((n : ℝ) * h n) - 1) /
          (powTwo (h n) - 1)) := by
      rw [gap3 n hn]
    _ = h n * powTwo (h n) *
        (powTwo ((n : ℝ) * h n) - 1) /
          (powTwo (h n) - 1) := by
      ring

theorem gap8 (n : ℕ) (hn : 0 < n) :
    h n * powTwo (h n) * (powTwo ((n : ℝ) * h n) - 1) /
        (powTwo (h n) - 1) =
      10230 * powTwo (10 / (n : ℝ)) /
        ((n : ℝ) * (powTwo (10 / (n : ℝ)) - 1)) := by
  calc
    h n * powTwo (h n) * (powTwo ((n : ℝ) * h n) - 1) /
        (powTwo (h n) - 1) =
        powTwo (h n) *
          (h n * (powTwo ((n : ℝ) * h n) - 1) /
            (powTwo (h n) - 1)) := by
      ring
    _ = powTwo (h n) *
        (10230 /
          ((n : ℝ) * (powTwo (10 / (n : ℝ)) - 1))) := by
      rw [gap4 n hn]
    _ = 10230 * powTwo (10 / (n : ℝ)) /
        ((n : ℝ) * (powTwo (10 / (n : ℝ)) - 1)) := by
      simp only [h]
      ring

theorem gap9 (n : ℕ) (hn : 0 < n) :
    upperSum n =
      10230 * powTwo (10 / (n : ℝ)) /
        ((n : ℝ) * (powTwo (10 / (n : ℝ)) - 1)) := by
  calc
    upperSum n =
        ∑ i ∈ Finset.range n,
          h n * powTwo (((i : ℝ) + 1) * h n) := gap6 n hn
    _ = h n * powTwo (h n) *
        (powTwo ((n : ℝ) * h n) - 1) /
          (powTwo (h n) - 1) := gap7 n hn
    _ = 10230 * powTwo (10 / (n : ℝ)) /
        ((n : ℝ) * (powTwo (10 / (n : ℝ)) - 1)) := gap8 n hn

end
end ProofGap.Exercise2182_3
