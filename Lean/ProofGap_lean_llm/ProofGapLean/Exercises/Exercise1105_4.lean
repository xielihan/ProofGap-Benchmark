import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1105_4

noncomputable section

def nthRoot (n : ℕ) (x : ℝ) : ℝ :=
  Real.rpow x (1 / (n : ℝ))

def Approx (x y ε : ℝ) : Prop := |x - y| < ε

private theorem nthRoot_pow_eq (n : ℕ) (a : ℝ) (hn : 0 < n) (ha : 0 < a) :
    nthRoot n (a ^ n) = a := by
  unfold nthRoot
  simpa [one_div] using
    (Real.pow_rpow_inv_natCast (x := a) (n := n)
      (le_of_lt ha) (ne_of_gt hn))

private theorem nthRoot_pow_pred_eq (n : ℕ) (a : ℝ)
    (hn : 0 < n) (ha : 0 < a) :
    nthRoot n ((a ^ n) ^ (n - 1)) = a ^ (n - 1) := by
  have hpow : (a ^ n) ^ (n - 1) = (a ^ (n - 1)) ^ n := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm n (n - 1)]
  rw [hpow]
  exact nthRoot_pow_eq n (a ^ (n - 1)) hn (pow_pos ha _)

theorem gap1 (n : ℕ) (a : ℝ) (hn : 0 < n) (ha : 0 < a) :
    HasDerivAt (fun x : ℝ => nthRoot n (a ^ n + x))
      (1 / ((n : ℝ) * nthRoot n ((a ^ n) ^ (n - 1)))) 0 := by
  have hxpos : 0 < a ^ n := pow_pos ha n
  have houter :
      HasDerivAt (fun y : ℝ => Real.rpow y (1 / (n : ℝ)))
        ((1 / (n : ℝ)) * Real.rpow (a ^ n) (1 / (n : ℝ) - 1)) (a ^ n) := by
    exact Real.hasDerivAt_rpow_const (p := 1 / (n : ℝ)) (Or.inl (by positivity))
  have hinner : HasDerivAt (fun x : ℝ => a ^ n + x) 1 0 := by
    simpa using (hasDerivAt_id (x := (0 : ℝ))).const_add (a ^ n)
  have houter0 :
      HasDerivAt (fun y : ℝ => Real.rpow y (1 / (n : ℝ)))
        ((1 / (n : ℝ)) * Real.rpow (a ^ n) (1 / (n : ℝ) - 1))
        (a ^ n + 0) := by
    simpa using houter
  have hderiv :
      HasDerivAt (fun x : ℝ => nthRoot n (a ^ n + x))
        ((1 / (n : ℝ)) * Real.rpow (a ^ n) (1 / (n : ℝ) - 1)) 0 := by
    simpa [nthRoot] using houter0.comp (0 : ℝ) hinner
  have hroot : Real.rpow (a ^ n) (1 / (n : ℝ)) = a := by
    simpa [nthRoot] using nthRoot_pow_eq n a hn ha
  have hsub :
      Real.rpow (a ^ n) (1 / (n : ℝ) - 1) = a / a ^ n := by
    calc
      Real.rpow (a ^ n) (1 / (n : ℝ) - 1) =
          Real.exp (Real.log (a ^ n) * (1 / (n : ℝ) - 1)) :=
        Real.rpow_def_of_pos hxpos _
      _ = Real.exp (Real.log (a ^ n) * (1 / (n : ℝ))) /
          Real.exp (Real.log (a ^ n)) := by
        rw [← Real.exp_sub]
        congr 1
        ring
      _ = Real.rpow (a ^ n) (1 / (n : ℝ)) / (a ^ n) := by
        have hnum :
            Real.exp (Real.log (a ^ n) * (1 / (n : ℝ))) =
              Real.rpow (a ^ n) (1 / (n : ℝ)) :=
          (Real.rpow_def_of_pos hxpos _).symm
        rw [hnum, Real.exp_log hxpos]
      _ = a / a ^ n := by rw [hroot]
  have hpow : a ^ n = a ^ (n - 1) * a := by
    conv_lhs => rw [← Nat.sub_add_cancel hn]
    rw [pow_succ]
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hcoeff :
      (1 / (n : ℝ)) * (a / a ^ n) =
        1 / ((n : ℝ) * a ^ (n - 1)) := by
    rw [hpow]
    field_simp [hn0, ha0]
  rw [hsub, hcoeff] at hderiv
  rw [nthRoot_pow_pred_eq n a hn ha]
  exact hderiv

theorem gap2 (n : ℕ) (a x : ℝ) (hn : 0 < n) (ha : 0 < a) :
    nthRoot n (a ^ n) +
        x / ((n : ℝ) * nthRoot n ((a ^ n) ^ (n - 1))) =
      a + x / ((n : ℝ) * a ^ (n - 1)) := by
  rw [nthRoot_pow_eq n a hn ha, nthRoot_pow_pred_eq n a hn ha]

theorem gap3 (n : ℕ) (a : ℝ) (hn : 0 < n) (ha : 0 < a) :
    HasDerivAt (fun x : ℝ => nthRoot n (a ^ n + x))
      (1 / ((n : ℝ) * a ^ (n - 1))) 0 := by
  have h := gap1 n a hn ha
  rw [nthRoot_pow_pred_eq n a hn ha] at h
  exact h

theorem gap4 :
    nthRoot 10 1000 = nthRoot 10 (2 ^ 10 - 24) := by
  norm_num

theorem gap5 :
    Approx (nthRoot 10 (2 ^ 10 - 24))
      (2 - (24 / (10 * 2 ^ 9) : ℝ)) (1 / 10000 : ℝ) := by
  unfold Approx
  rw [abs_lt]
  let l : ℝ := 2 - 24 / (10 * 2 ^ 9) - 1 / 10000
  let u : ℝ := 2 - 24 / (10 * 2 ^ 9) + 1 / 10000
  have hlpow : l ^ 10 < (2 ^ 10 - 24 : ℝ) := by
    dsimp [l]
    norm_num
  have hupow : (2 ^ 10 - 24 : ℝ) < u ^ 10 := by
    dsimp [u]
    norm_num
  have hl : l < nthRoot 10 (2 ^ 10 - 24) := by
    calc
      l = nthRoot 10 (l ^ 10) :=
        (nthRoot_pow_eq 10 l (by norm_num) (by dsimp [l]; norm_num)).symm
      _ < nthRoot 10 (2 ^ 10 - 24) := by
        unfold nthRoot
        exact Real.rpow_lt_rpow (by positivity) hlpow (by norm_num)
  have hu : nthRoot 10 (2 ^ 10 - 24) < u := by
    calc
      nthRoot 10 (2 ^ 10 - 24) < nthRoot 10 (u ^ 10) := by
        unfold nthRoot
        exact Real.rpow_lt_rpow (by positivity) hupow (by norm_num)
      _ = u := nthRoot_pow_eq 10 u (by norm_num) (by dsimp [u]; norm_num)
  dsimp [l] at hl
  dsimp [u] at hu
  constructor <;> linarith

theorem gap6 :
    Approx (2 - (24 / (10 * 2 ^ 9) : ℝ))
      (19953 / 10000 : ℝ) (1 / 10000 : ℝ) := by
  norm_num [Approx, abs_lt]

theorem gap7 :
    Approx (nthRoot 10 1000) (19953 / 10000 : ℝ)
      (1 / 10000 : ℝ) := by
  unfold Approx
  rw [abs_lt]
  let l : ℝ := 19953 / 10000 - 1 / 10000
  let u : ℝ := 19953 / 10000 + 1 / 10000
  have hlpow : l ^ 10 < (1000 : ℝ) := by
    dsimp [l]
    norm_num
  have hupow : (1000 : ℝ) < u ^ 10 := by
    dsimp [u]
    norm_num
  have hl : l < nthRoot 10 1000 := by
    calc
      l = nthRoot 10 (l ^ 10) :=
        (nthRoot_pow_eq 10 l (by norm_num) (by dsimp [l]; norm_num)).symm
      _ < nthRoot 10 1000 := by
        unfold nthRoot
        exact Real.rpow_lt_rpow (by positivity) hlpow (by norm_num)
  have hu : nthRoot 10 1000 < u := by
    calc
      nthRoot 10 1000 < nthRoot 10 (u ^ 10) := by
        unfold nthRoot
        exact Real.rpow_lt_rpow (by positivity) hupow (by norm_num)
      _ = u := nthRoot_pow_eq 10 u (by norm_num) (by dsimp [u]; norm_num)
  dsimp [l] at hl
  dsimp [u] at hu
  constructor <;> linarith

theorem gap8 :
    Approx (nthRoot 10 1000) (19953 / 10000 : ℝ)
      (1 / 10000 : ℝ) := by
  exact gap7

end

end ProofGap.Exercise1105_4
