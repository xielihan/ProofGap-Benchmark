import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace ProofGap.Exercise1105_3

noncomputable section

def nthRoot (n : ℕ) (x : ℝ) : ℝ :=
  Real.rpow x (1 / (n : ℝ))

def Approx (x y ε : ℝ) : Prop := |x - y| < ε

private theorem nthRootPow (n : ℕ) (a : ℝ) (hn : 0 < n) (ha : 0 < a) :
    nthRoot n (a ^ n) = a := by
  have hn0 : (n : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hexp : (n : ℝ) * (1 / (n : ℝ)) = 1 := by
    field_simp
  have hnat : Real.rpow a (n : ℝ) = a ^ n := by
    exact Real.rpow_natCast a n
  unfold nthRoot
  calc
    Real.rpow (a ^ n) (1 / (n : ℝ)) =
        Real.rpow (Real.rpow a (n : ℝ)) (1 / (n : ℝ)) := by
      rw [hnat]
    _ = Real.rpow a ((n : ℝ) * (1 / (n : ℝ))) :=
      (Real.rpow_mul ha.le (n : ℝ) (1 / (n : ℝ))).symm
    _ = Real.rpow a 1 := by rw [hexp]
    _ = a := Real.rpow_one a

private theorem nthRootPredPower (n : ℕ) (a : ℝ) (hn : 0 < n) (ha : 0 < a) :
    nthRoot n ((a ^ n) ^ (n - 1)) = a ^ (n - 1) := by
  have hbase : (a ^ n) ^ (n - 1) = (a ^ (n - 1)) ^ n := by
    calc
      (a ^ n) ^ (n - 1) = a ^ (n * (n - 1)) := by rw [← pow_mul]
      _ = a ^ ((n - 1) * n) := by rw [Nat.mul_comm]
      _ = (a ^ (n - 1)) ^ n := by rw [pow_mul]
  rw [hbase]
  exact nthRootPow n (a ^ (n - 1)) hn (pow_pos ha _)

private theorem rootDerivativeCoefficient (n : ℕ) (a : ℝ) (hn : 0 < n) (ha : 0 < a) :
    (1 / (n : ℝ)) * Real.rpow (a ^ n) (1 / (n : ℝ) - 1) =
      1 / ((n : ℝ) * nthRoot n ((a ^ n) ^ (n - 1))) := by
  have hn0 : (n : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hbpos : 0 < a ^ n := pow_pos ha n
  have hrsub :
      Real.rpow (a ^ n) (1 / (n : ℝ) - 1) =
        Real.rpow (a ^ n) (1 / (n : ℝ)) / Real.rpow (a ^ n) 1 :=
    Real.rpow_sub hbpos (1 / (n : ℝ)) 1
  have hrone : Real.rpow (a ^ n) 1 = a ^ n := Real.rpow_one (a ^ n)
  rw [hrsub, hrone]
  change
    (1 / (n : ℝ)) * (nthRoot n (a ^ n) / a ^ n) =
      1 / ((n : ℝ) * nthRoot n ((a ^ n) ^ (n - 1)))
  rw [nthRootPow n a hn ha, nthRootPredPower n a hn ha]
  have hn_split : n - 1 + 1 = n := Nat.sub_add_cancel hn
  have hpow : a ^ n = a ^ (n - 1) * a := by
    calc
      a ^ n = a ^ (n - 1 + 1) := by rw [hn_split]
      _ = a ^ (n - 1) * a := by rw [pow_succ]
  rw [hpow]
  have hpredne : a ^ (n - 1) ≠ 0 := pow_ne_zero _ ha.ne'
  field_simp [hn0, ha.ne', hpredne] <;> ring

private theorem localPowMono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    ∀ n : ℕ, x ^ n ≤ y ^ n := by
  have hy : 0 ≤ y := hx.trans hxy
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, pow_succ]
      exact mul_le_mul ih hxy hx (pow_nonneg hy n)

private theorem nthRootHundredBounds :
    (1930 / 1000 : ℝ) < nthRoot 7 100 ∧
      nthRoot 7 100 < (1932 / 1000 : ℝ) := by
  let r : ℝ := nthRoot 7 100
  have hr : 0 ≤ r := by
    dsimp [r, nthRoot]
    positivity
  have hrpow : r ^ 7 = 100 := by
    dsimp [r, nthRoot]
    have hnat :
        Real.rpow (Real.rpow 100 (1 / (7 : ℝ))) (7 : ℝ) =
          (Real.rpow 100 (1 / (7 : ℝ))) ^ 7 := by
      exact Real.rpow_natCast (Real.rpow 100 (1 / (7 : ℝ))) 7
    calc
      (Real.rpow 100 (1 / (7 : ℝ))) ^ 7 =
          Real.rpow (Real.rpow 100 (1 / (7 : ℝ))) (7 : ℝ) := hnat.symm
      _ = Real.rpow 100 ((1 / (7 : ℝ)) * (7 : ℝ)) :=
        (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 100)
          (1 / (7 : ℝ)) (7 : ℝ)).symm
      _ = Real.rpow 100 1 := by norm_num
      _ = 100 := Real.rpow_one 100
  change (1930 / 1000 : ℝ) < r ∧ r < (1932 / 1000 : ℝ)
  constructor
  · by_contra h
    have hrle : r ≤ (1930 / 1000 : ℝ) := le_of_not_gt h
    have hp := localPowMono hr hrle 7
    rw [hrpow] at hp
    norm_num at hp
  · by_contra h
    have hle : (1932 / 1000 : ℝ) ≤ r := le_of_not_gt h
    have hq : (0 : ℝ) ≤ 1932 / 1000 := by norm_num
    have hp := localPowMono hq hle 7
    rw [hrpow] at hp
    norm_num at hp

theorem gap1 (n : ℕ) (a : ℝ) (hn : 0 < n) (ha : 0 < a) :
    HasDerivAt (fun x : ℝ => nthRoot n (a ^ n + x))
      (1 / ((n : ℝ) * nthRoot n ((a ^ n) ^ (n - 1)))) 0 := by
  have hbpos : 0 < a ^ n := pow_pos ha n
  have houter :
      HasDerivAt (fun y : ℝ => Real.rpow y (1 / (n : ℝ)))
        ((1 / (n : ℝ)) * Real.rpow (a ^ n) (1 / (n : ℝ) - 1)) (a ^ n) := by
    simpa using
      (Real.hasDerivAt_rpow_const (x := a ^ n) (p := 1 / (n : ℝ))
        (Or.inl hbpos.ne'))
  have hinner : HasDerivAt (fun x : ℝ => a ^ n + x) 1 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_add (a ^ n))
  have houter0 :
      HasDerivAt (fun y : ℝ => Real.rpow y (1 / (n : ℝ)))
        ((1 / (n : ℝ)) * Real.rpow (a ^ n) (1 / (n : ℝ) - 1))
        (a ^ n + 0) := by
    simpa only [add_zero] using houter
  have hcomp :
      HasDerivAt
        (fun x : ℝ => Real.rpow (a ^ n + x) (1 / (n : ℝ)))
        (((1 / (n : ℝ)) * Real.rpow (a ^ n) (1 / (n : ℝ) - 1)) * 1) 0 :=
    houter0.comp 0 hinner
  have hstandard :
      HasDerivAt (fun x : ℝ => nthRoot n (a ^ n + x))
        ((1 / (n : ℝ)) * Real.rpow (a ^ n) (1 / (n : ℝ) - 1)) 0 := by
    simpa only [nthRoot, mul_one] using hcomp
  rw [rootDerivativeCoefficient n a hn ha] at hstandard
  exact hstandard

theorem gap2 (n : ℕ) (a x : ℝ) (hn : 0 < n) (ha : 0 < a) :
    nthRoot n (a ^ n) +
        x / ((n : ℝ) * nthRoot n ((a ^ n) ^ (n - 1))) =
      a + x / ((n : ℝ) * a ^ (n - 1)) := by
  rw [nthRootPow n a hn ha, nthRootPredPower n a hn ha]

theorem gap3 (n : ℕ) (a : ℝ) (hn : 0 < n) (ha : 0 < a) :
    HasDerivAt (fun x : ℝ => nthRoot n (a ^ n + x))
      (1 / ((n : ℝ) * a ^ (n - 1))) 0 := by
  have h := gap1 n a hn ha
  rw [nthRootPredPower n a hn ha] at h
  exact h

theorem gap4 :
    nthRoot 7 100 = nthRoot 7 (2 ^ 7 - 28) := by
  norm_num

theorem gap5 :
    Approx (nthRoot 7 (2 ^ 7 - 28))
      (2 - (28 / (7 * 2 ^ 6) : ℝ)) (8 / 1000 : ℝ) := by
  rw [← gap4]
  have h := nthRootHundredBounds
  unfold Approx
  rw [abs_lt]
  constructor <;> linarith [h.1, h.2]

theorem gap6 :
    Approx (2 - (28 / (7 * 2 ^ 6) : ℝ))
      (1938 / 1000 : ℝ) (1 / 1000 : ℝ) := by
  norm_num [Approx, abs_of_nonpos]

theorem gap7 :
    Approx (nthRoot 7 100) (1938 / 1000 : ℝ)
      (8 / 1000 : ℝ) := by
  have h := nthRootHundredBounds
  unfold Approx
  rw [abs_lt]
  constructor <;> linarith [h.1, h.2]

theorem gap8 :
    Approx (nthRoot 7 100) (1931 / 1000 : ℝ)
      (1 / 1000 : ℝ) := by
  have h := nthRootHundredBounds
  unfold Approx
  rw [abs_lt]
  constructor <;> linarith [h.1, h.2]

end

end ProofGap.Exercise1105_3
