import ProofGapLean.Prelude.Elementary
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1396_2

noncomputable section

def root (n : ℕ) (x : ℝ) : ℝ := Real.rpow x (1 / (n : ℝ))

def exactValue : ℝ :=
  3 * Real.rpow (1 + (7 / 243 : ℝ)) (1 / 5 : ℝ)

def taylorValue : ℝ :=
  3 * (1 + (1 / 5 : ℝ) * (7 / 243 : ℝ) +
    (((1 / 5 : ℝ) * ((1 / 5 : ℝ) - 1)) / (Nat.factorial 2 : ℝ)) *
      (7 / 243 : ℝ) ^ 2)

def errorBound : ℝ :=
  3 * (1 / (Nat.factorial 3 : ℝ)) * (1 / 5 : ℝ) *
    (4 / 5 : ℝ) * (9 / 5 : ℝ) * (7 / 243 : ℝ) ^ 3

def ApproxWithin (a b ε : ℝ) : Prop := |a - b| < ε

private theorem exact_taylor_bounds :
    taylorValue < exactValue ∧ exactValue < taylorValue + errorBound := by
  let y : ℝ := Real.rpow (250 / 243 : ℝ) (1 / 5 : ℝ)
  let L : ℝ := 1484632 / 1476225
  let U : ℝ := 1803829938 / 1793613375
  have hypos : 0 < y := by
    dsimp [y]
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hy0 : 0 ≤ y := le_of_lt hypos
  have hL0 : 0 ≤ L := by norm_num [L]
  have hU0 : 0 ≤ U := by norm_num [U]
  have hy5 : y ^ 5 = (250 / 243 : ℝ) := by
    dsimp [y]
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul (by norm_num : 0 ≤ (250 / 243 : ℝ))]
    norm_num
  have hLpow : L ^ 5 < (250 / 243 : ℝ) := by
    norm_num [L]
  have hUpow : (250 / 243 : ℝ) < U ^ 5 := by
    norm_num [U]
  have hLy : L < y := by
    by_contra h
    have hyL : y ≤ L := le_of_not_gt h
    have hp : y ^ 5 ≤ L ^ 5 := by
      apply sub_nonneg.mp
      rw [show L ^ 5 - y ^ 5 =
          (L - y) * (L ^ 4 + L ^ 3 * y + L ^ 2 * y ^ 2 + L * y ^ 3 + y ^ 4) by ring]
      exact mul_nonneg (sub_nonneg.mpr hyL) (by positivity)
    rw [hy5] at hp
    linarith
  have hyU : y < U := by
    by_contra h
    have hUy : U ≤ y := le_of_not_gt h
    have hp : U ^ 5 ≤ y ^ 5 := by
      apply sub_nonneg.mp
      rw [show y ^ 5 - U ^ 5 =
          (y - U) * (y ^ 4 + y ^ 3 * U + y ^ 2 * U ^ 2 + y * U ^ 3 + U ^ 4) by ring]
      exact mul_nonneg (sub_nonneg.mpr hUy) (by positivity)
    rw [hy5] at hp
    linarith
  have hexact : exactValue = 3 * y := by
    norm_num [exactValue, y]
  have htaylor : taylorValue = 3 * L := by
    norm_num [taylorValue, L]
  have hupper : taylorValue + errorBound = 3 * U := by
    norm_num [taylorValue, errorBound, U]
  constructor
  · rw [htaylor, hexact]
    linarith
  · rw [hexact, hupper]
    linarith

theorem gap1 :
    root 5 250 = exactValue := by
  unfold root exactValue
  have hbase : (250 : ℝ) = 243 * (1 + (7 / 243 : ℝ)) := by
    norm_num
  have h243 : Real.rpow (243 : ℝ) (1 / 5 : ℝ) = 3 := by
    let z : ℝ := Real.rpow (243 : ℝ) (1 / 5 : ℝ)
    have hzpos : 0 < z := by
      dsimp [z]
      exact Real.rpow_pos_of_pos (by norm_num) _
    have hz5 : z ^ 5 = (243 : ℝ) := by
      dsimp [z]
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul (by norm_num : 0 ≤ (243 : ℝ))]
      norm_num
    have hfactor :
        z ^ 5 - (3 : ℝ) ^ 5 =
          (z - 3) *
            (z ^ 4 + z ^ 3 * 3 + z ^ 2 * 3 ^ 2 + z * 3 ^ 3 + 3 ^ 4) := by
      ring
    have hsumpos :
        0 < z ^ 4 + z ^ 3 * 3 + z ^ 2 * 3 ^ 2 + z * 3 ^ 3 + 3 ^ 4 := by
      positivity
    have hm :
        (z - 3) *
            (z ^ 4 + z ^ 3 * 3 + z ^ 2 * 3 ^ 2 + z * 3 ^ 3 + 3 ^ 4) = 0 := by
      rw [← hfactor, hz5]
      norm_num
    have hzsub : z - 3 = 0 :=
      (mul_eq_zero.mp hm).resolve_right (ne_of_gt hsumpos)
    change z = 3
    exact sub_eq_zero.mp hzsub
  have hmul :
      Real.rpow ((243 : ℝ) * (1 + (7 / 243 : ℝ))) (1 / 5 : ℝ) =
        Real.rpow (243 : ℝ) (1 / 5 : ℝ) *
          Real.rpow (1 + (7 / 243 : ℝ)) (1 / 5 : ℝ) := by
    exact Real.mul_rpow (by norm_num) (by norm_num)
  calc
    Real.rpow (250 : ℝ) (1 / 5 : ℝ) =
        Real.rpow ((243 : ℝ) * (1 + (7 / 243 : ℝ))) (1 / 5 : ℝ) := by
      rw [hbase]
    _ = Real.rpow (243 : ℝ) (1 / 5 : ℝ) *
          Real.rpow (1 + (7 / 243 : ℝ)) (1 / 5 : ℝ) := hmul
    _ = 3 * Real.rpow (1 + (7 / 243 : ℝ)) (1 / 5 : ℝ) := by
      rw [h243]

theorem gap2 :
    ApproxWithin exactValue taylorValue errorBound := by
  unfold ApproxWithin
  rw [abs_lt]
  constructor <;>
    linarith [exact_taylor_bounds.1, exact_taylor_bounds.2]

theorem gap3 :
    ApproxWithin taylorValue (3.0171 : ℝ) (1 / 50000 : ℝ) := by
  norm_num [ApproxWithin, taylorValue]

theorem gap4 :
    ApproxWithin (root 5 250) (3.0171 : ℝ)
      (errorBound + 1 / 50000) := by
  rw [gap1]
  have h2 := gap2
  have h3 := gap3
  unfold ApproxWithin at h2 h3 ⊢
  calc
    |exactValue - (3.0171 : ℝ)| =
        |(exactValue - taylorValue) + (taylorValue - (3.0171 : ℝ))| := by
      congr 1
      ring
    _ ≤ |exactValue - taylorValue| + |taylorValue - (3.0171 : ℝ)| :=
      abs_add_le _ _
    _ < errorBound + 1 / 50000 := add_lt_add h2 h3

theorem gap5 :
    let Δ := |exactValue - taylorValue|
    0 ≤ Δ ∧ Δ < errorBound := by
  dsimp
  constructor
  · positivity
  · simpa [ApproxWithin] using gap2

theorem gap6 :
    ApproxWithin errorBound (0.00000345 : ℝ) (1 / 10000000 : ℝ) := by
  norm_num [ApproxWithin, errorBound]

end

end ProofGap.Exercise1396_2
