import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace ProofGap.Exercise1105_1

noncomputable section

def nthRoot (n : ℕ) (x : ℝ) : ℝ :=
  Real.rpow x (1 / (n : ℝ))

def Approx (x y ε : ℝ) : Prop := |x - y| < ε

private theorem nthRoot_of_pow (n : ℕ) (a : ℝ) (hn : 0 < n) (ha : 0 < a) :
    nthRoot n (a ^ n) = a := by
  unfold nthRoot
  simpa [one_div] using
    (Real.pow_rpow_inv_natCast (le_of_lt ha) (Nat.ne_of_gt hn))

private theorem nthRoot_of_pow_pred (n : ℕ) (a : ℝ) (hn : 0 < n) (ha : 0 < a) :
    nthRoot n ((a ^ n) ^ (n - 1)) = a ^ (n - 1) := by
  have hp : (a ^ n) ^ (n - 1) = (a ^ (n - 1)) ^ n := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  rw [hp]
  exact nthRoot_of_pow n (a ^ (n - 1)) hn (pow_pos ha _)

private theorem root_derivative_coefficient
    (n : ℕ) (a : ℝ) (hn : 0 < n) (ha : 0 < a) :
    (1 / (n : ℝ)) * (a ^ n) ^ (1 / (n : ℝ) - 1) =
      1 / ((n : ℝ) * a ^ (n - 1)) := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hroot : (a ^ n) ^ (1 / (n : ℝ)) = a := by
    simpa only [nthRoot] using nthRoot_of_pow n a hn ha
  have hidx : n = n - 1 + 1 := by omega
  have hpow : a ^ n = a ^ (n - 1) * a := by
    calc
      a ^ n = a ^ (n - 1 + 1) :=
        congrArg (fun k : ℕ => a ^ k) hidx
      _ = a ^ (n - 1) * a := by rw [pow_succ]
  rw [Real.rpow_sub (by positivity), hroot, Real.rpow_one, hpow]
  field_simp [hn0, ha.ne'] <;> ring

private theorem cube_mono_of_nonneg {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    x ^ 3 ≤ y ^ 3 := by
  have hy : 0 ≤ y := le_trans hx hxy
  have hxyprod : 0 ≤ y * x := mul_nonneg hy hx
  have hs : 0 ≤ y ^ 2 + y * x + x ^ 2 := by
    nlinarith [sq_nonneg x, sq_nonneg y]
  have hp : 0 ≤ (y - x) * (y ^ 2 + y * x + x ^ 2) :=
    mul_nonneg (sub_nonneg.mpr hxy) hs
  nlinarith

private theorem nthRoot_three_nine_nonneg : 0 ≤ nthRoot 3 9 := by
  unfold nthRoot
  exact (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 9) _).le

private theorem nthRoot_three_nine_cube : (nthRoot 3 9) ^ 3 = 9 := by
  unfold nthRoot
  rw [← Real.rpow_natCast]
  change Real.rpow (Real.rpow 9 (1 / (3 : ℝ))) (3 : ℝ) = 9
  calc
    Real.rpow (Real.rpow 9 (1 / (3 : ℝ))) (3 : ℝ) =
        Real.rpow 9 ((1 / (3 : ℝ)) * (3 : ℝ)) := by
      exact (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 9)
        (1 / (3 : ℝ)) (3 : ℝ)).symm
    _ = 9 := by norm_num

private theorem nthRoot_three_nine_between
    (l u : ℝ) (hl : 0 ≤ l) (hu : 0 ≤ u)
    (hlcube : l ^ 3 < 9) (hucube : 9 < u ^ 3) :
    l < nthRoot 3 9 ∧ nthRoot 3 9 < u := by
  constructor
  · by_contra h
    have hyr : nthRoot 3 9 ≤ l := le_of_not_gt h
    have hc := cube_mono_of_nonneg nthRoot_three_nine_nonneg hyr
    nlinarith [nthRoot_three_nine_cube]
  · by_contra h
    have hry : u ≤ nthRoot 3 9 := le_of_not_gt h
    have hc := cube_mono_of_nonneg hu hry
    nlinarith [nthRoot_three_nine_cube]

private theorem nthRoot_three_nine_bounds :
    (2080 / 1000 : ℝ) < nthRoot 3 9 ∧
      nthRoot 3 9 < (2081 / 1000 : ℝ) := by
  apply nthRoot_three_nine_between
  all_goals norm_num

theorem gap1 (n : ℕ) (a : ℝ) (hn : 0 < n) (ha : 0 < a) :
    HasDerivAt (fun x : ℝ => nthRoot n (a ^ n + x))
      (1 / ((n : ℝ) * nthRoot n ((a ^ n) ^ (n - 1)))) 0 := by
  rw [nthRoot_of_pow_pred n a hn ha]
  have hinner : HasDerivAt (fun x : ℝ => a ^ n + x) 1 0 := by
    simpa using
      ((hasDerivAt_const (x := (0 : ℝ)) (c := a ^ n)).add
        (hasDerivAt_id (x := (0 : ℝ))))
  have houter :
      HasDerivAt (fun y : ℝ => y ^ (1 / (n : ℝ)))
        ((1 / (n : ℝ)) * (a ^ n) ^ (1 / (n : ℝ) - 1)) (a ^ n) := by
    exact Real.hasDerivAt_rpow_const (p := 1 / (n : ℝ))
      (Or.inl (pow_ne_zero n ha.ne'))
  have houter' :
      HasDerivAt (fun y : ℝ => y ^ (1 / (n : ℝ)))
        ((1 / (n : ℝ)) * (a ^ n) ^ (1 / (n : ℝ) - 1)) (a ^ n + 0) := by
    simpa only [add_zero] using houter
  simpa only [nthRoot, root_derivative_coefficient n a hn ha, mul_one] using
    houter'.comp 0 hinner

theorem gap2 (n : ℕ) (a x : ℝ) (hn : 0 < n) (ha : 0 < a) :
    nthRoot n (a ^ n) +
        x / ((n : ℝ) * nthRoot n ((a ^ n) ^ (n - 1))) =
      a + x / ((n : ℝ) * a ^ (n - 1)) := by
  rw [nthRoot_of_pow n a hn ha, nthRoot_of_pow_pred n a hn ha]

theorem gap3 (n : ℕ) (a : ℝ) (hn : 0 < n) (ha : 0 < a) :
    HasDerivAt (fun x : ℝ => nthRoot n (a ^ n + x))
      (1 / ((n : ℝ) * a ^ (n - 1))) 0 := by
  rw [← nthRoot_of_pow_pred n a hn ha]
  exact gap1 n a hn ha

theorem gap4 :
    nthRoot 3 9 = nthRoot 3 (2 ^ 3 + 1) := by
  norm_num

theorem gap5 :
    Approx (nthRoot 3 (2 ^ 3 + 1))
      (2 + (1 / (3 * 2 ^ 2) : ℝ)) (4 / 1000 : ℝ) := by
  rw [← gap4]
  unfold Approx
  rw [abs_lt]
  have h := nthRoot_three_nine_bounds
  constructor
  · norm_num at h ⊢
    linarith [h.1]
  · norm_num at h ⊢
    linarith [h.2]

theorem gap6 :
    Approx (2 + (1 / (3 * 2 ^ 2) : ℝ))
      (2083 / 1000 : ℝ) (1 / 1000 : ℝ) := by
  norm_num [Approx, abs_of_nonneg, abs_of_nonpos]

theorem gap7 :
    Approx (nthRoot 3 9) (2083 / 1000 : ℝ)
      (4 / 1000 : ℝ) := by
  unfold Approx
  rw [abs_lt]
  have h := nthRoot_three_nine_bounds
  constructor
  · norm_num at h ⊢
    linarith [h.1]
  · norm_num at h ⊢
    linarith [h.2]

theorem gap8 :
    Approx (nthRoot 3 9) (2080 / 1000 : ℝ)
      (1 / 1000 : ℝ) := by
  unfold Approx
  rw [abs_lt]
  have h := nthRoot_three_nine_bounds
  constructor
  · norm_num at h ⊢
    linarith [h.1]
  · norm_num at h ⊢
    linarith [h.2]

end

end ProofGap.Exercise1105_1
