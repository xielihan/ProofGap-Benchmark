import ProofGapLean.Prelude.Elementary
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace ProofGap.Exercise1396_1

noncomputable section

def root (n : ℕ) (x : ℝ) : ℝ := Real.rpow x (1 / (n : ℝ))

def exactValue : ℝ :=
  3 * Real.rpow (1 + (1 / 9 : ℝ)) (1 / 3 : ℝ)

def taylorValue : ℝ :=
  3 * (1 + (1 / 3 : ℝ) * (1 / 9 : ℝ) +
    (((1 / 3 : ℝ) * ((1 / 3 : ℝ) - 1)) / (Nat.factorial 2 : ℝ)) *
      (1 / 9 : ℝ) ^ 2)

def errorBound : ℝ :=
  3 * (((1 / 3 : ℝ) * (2 / 3 : ℝ) * (5 / 3 : ℝ)) /
    (Nat.factorial 3 : ℝ)) * (1 / 9 : ℝ) ^ 3

def ApproxWithin (a b ε : ℝ) : Prop := |a - b| < ε

private theorem cube_of_rpow_one_third (x : ℝ) (hx : 0 < x) :
    (Real.rpow x (1 / 3 : ℝ)) ^ 3 = x := by
  change ((x ^ (1 / 3 : ℝ) : ℝ) ^ (3 : ℕ)) = x
  have hdef :
      (x ^ (1 / 3 : ℝ) : ℝ) =
        Real.exp (Real.log x * (1 / 3 : ℝ)) := by
    exact Real.rpow_def_of_pos hx (1 / 3 : ℝ)
  rw [hdef]
  let z : ℝ := Real.log x * (1 / 3 : ℝ)
  change Real.exp z ^ 3 = x
  calc
    Real.exp z ^ 3 = (Real.exp z * Real.exp z) * Real.exp z := by ring
    _ = Real.exp (z + z) * Real.exp z := by
      exact congrArg (fun y : ℝ => y * Real.exp z) (Real.exp_add z z).symm
    _ = Real.exp ((z + z) + z) := (Real.exp_add (z + z) z).symm
    _ = Real.exp (Real.log x) := by
      congr 1
      dsimp [z]
      ring
    _ = x := Real.exp_log hx

theorem gap1 :
    root 3 30 = exactValue := by
  unfold root exactValue
  let q : ℝ := 1 / 3
  let b : ℝ := 10 / 9
  have hmul :
      Real.rpow ((27 : ℝ) * b) q =
        Real.rpow (27 : ℝ) q * Real.rpow b q := by
    change ((27 : ℝ) * b) ^ q = (27 : ℝ) ^ q * b ^ q
    have hp : (0 : ℝ) < 27 * b := by
      dsimp [b]
      norm_num
    have h27p : (0 : ℝ) < 27 := by norm_num
    have hbp : (0 : ℝ) < b := by
      dsimp [b]
      norm_num
    have hpdef :
        ((27 : ℝ) * b) ^ q =
          Real.exp (Real.log ((27 : ℝ) * b) * q) := by
      exact Real.rpow_def_of_pos hp q
    have h27def :
        (27 : ℝ) ^ q = Real.exp (Real.log (27 : ℝ) * q) := by
      exact Real.rpow_def_of_pos h27p q
    have hbdef : b ^ q = Real.exp (Real.log b * q) := by
      exact Real.rpow_def_of_pos hbp q
    calc
      ((27 : ℝ) * b) ^ q =
          Real.exp (Real.log ((27 : ℝ) * b) * q) := hpdef
      _ = Real.exp ((Real.log (27 : ℝ) + Real.log b) * q) := by
        rw [Real.log_mul (by norm_num : (27 : ℝ) ≠ 0) hbp.ne']
      _ = Real.exp (Real.log (27 : ℝ) * q + Real.log b * q) := by
        congr 1
        ring
      _ = Real.exp (Real.log (27 : ℝ) * q) *
          Real.exp (Real.log b * q) := Real.exp_add _ _
      _ = (27 : ℝ) ^ q * b ^ q := by
        rw [h27def, hbdef]
  have h27 : Real.rpow (27 : ℝ) q = 3 := by
    let v : ℝ := Real.rpow (27 : ℝ) q
    have hv3 : v ^ 3 = (27 : ℝ) := by
      dsimp [v, q]
      exact cube_of_rpow_one_third 27 (by norm_num)
    have hv0 : 0 ≤ v := by
      dsimp [v]
      exact (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 27) q).le
    have hfactor : (v - 3) * (v ^ 2 + 3 * v + 9) = 0 := by
      nlinarith
    rcases mul_eq_zero.mp hfactor with h | h
    · dsimp [v] at h ⊢
      linarith
    · have hpos : 0 < v ^ 2 + 3 * v + 9 := by
        nlinarith [sq_nonneg v]
      exact (hpos.ne' h).elim
  calc
    Real.rpow (30 : ℝ) (1 / ((3 : ℕ) : ℝ)) =
        Real.rpow ((27 : ℝ) * b) q := by
      dsimp [b, q]
      norm_num
    _ = Real.rpow (27 : ℝ) q * Real.rpow b q := hmul
    _ = 3 * Real.rpow b q := by rw [h27]
    _ = 3 * Real.rpow (1 + (1 / 9 : ℝ)) (1 / 3 : ℝ) := by
      dsimp [b, q]
      norm_num

theorem gap2 :
    ApproxWithin exactValue taylorValue errorBound := by
  unfold ApproxWithin exactValue taylorValue errorBound
  let u : ℝ := Real.rpow (1 + (1 / 9 : ℝ)) (1 / 3 : ℝ)
  have hbase : (0 : ℝ) < 1 + 1 / 9 := by norm_num
  have hu : 0 < u := by
    dsimp [u]
    exact Real.rpow_pos_of_pos hbase _
  have hu3 : u ^ 3 = (10 / 9 : ℝ) := by
    have hb : (1 + (1 / 9 : ℝ)) = 10 / 9 := by norm_num
    dsimp [u]
    rw [hb]
    exact cube_of_rpow_one_third (10 / 9 : ℝ) (by norm_num)
  have hlo : (755 / 729 : ℝ) < u := by
    by_contra h
    have hle : u ≤ (755 / 729 : ℝ) := le_of_not_gt h
    have hprod :
        0 ≤ ((755 / 729 : ℝ) - u) *
          ((755 / 729 : ℝ) ^ 2 + (755 / 729 : ℝ) * u + u ^ 2) := by
      apply mul_nonneg
      · exact sub_nonneg.mpr hle
      · have hqu : 0 ≤ (755 / 729 : ℝ) * u :=
          mul_nonneg (by norm_num) hu.le
        nlinarith [sq_nonneg u]
    have hcub : u ^ 3 ≤ (755 / 729 : ℝ) ^ 3 := by
      nlinarith [hprod]
    rw [hu3] at hcub
    norm_num at hcub
  have hhi : u < (755 / 729 + 5 / 59049 : ℝ) := by
    by_contra h
    have hle : (755 / 729 + 5 / 59049 : ℝ) ≤ u := le_of_not_gt h
    have hprod :
        0 ≤ (u - (755 / 729 + 5 / 59049 : ℝ)) *
          (u ^ 2 + u * (755 / 729 + 5 / 59049 : ℝ) +
            (755 / 729 + 5 / 59049 : ℝ) ^ 2) := by
      apply mul_nonneg
      · exact sub_nonneg.mpr hle
      · have hua :
            0 ≤ u * (755 / 729 + 5 / 59049 : ℝ) :=
          mul_nonneg hu.le (by norm_num)
        nlinarith [sq_nonneg u]
    have hcub :
        (755 / 729 + 5 / 59049 : ℝ) ^ 3 ≤ u ^ 3 := by
      nlinarith [hprod]
    rw [hu3] at hcub
    norm_num at hcub
  dsimp [u] at hlo hhi ⊢
  norm_num [abs_lt]
  constructor <;> nlinarith

theorem gap3 :
    ApproxWithin taylorValue (3.1070 : ℝ) (1 / 100000 : ℝ) := by
  unfold ApproxWithin taylorValue
  norm_num [abs_lt]

theorem gap4 :
    ApproxWithin (root 3 30) (3.1070 : ℝ)
      (errorBound + 1 / 100000) := by
  unfold ApproxWithin
  rw [gap1]
  have h2 : |exactValue - taylorValue| < errorBound := by
    simpa only [ApproxWithin] using gap2
  have h3 :
      |taylorValue - (3.1070 : ℝ)| < (1 / 100000 : ℝ) := by
    simpa only [ApproxWithin] using gap3
  calc
    |exactValue - (3.1070 : ℝ)| =
        |(exactValue - taylorValue) +
          (taylorValue - (3.1070 : ℝ))| := by ring_nf
    _ ≤ |exactValue - taylorValue| +
          |taylorValue - (3.1070 : ℝ)| := abs_add_le _ _
    _ < errorBound + 1 / 100000 := add_lt_add h2 h3

theorem gap5 :
    let Δ := |exactValue - taylorValue|
    0 ≤ Δ ∧ Δ < errorBound := by
  dsimp
  constructor
  · exact abs_nonneg _
  · exact gap2

theorem gap6 :
    ApproxWithin errorBound (0.000254 : ℝ) (1 / 1000000 : ℝ) := by
  unfold ApproxWithin errorBound
  norm_num [abs_lt]

end

end ProofGap.Exercise1396_1
