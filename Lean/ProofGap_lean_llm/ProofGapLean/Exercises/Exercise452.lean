import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise452

noncomputable section

def root (m : ℤ) (x : ℝ) : ℝ := Real.rpow x (1 / (m : ℝ))
def quotient (m n : ℤ) (alpha beta x : ℝ) : ℝ :=
  (root m (1 + alpha * x) - root n (1 + beta * x)) / x
def value (m n : ℤ) (alpha beta : ℝ) : ℝ :=
  alpha / (m : ℝ) - beta / (n : ℝ)
def HasLimitAt (g : ℝ → ℝ) (a L : ℝ) : Prop :=
  Filter.Tendsto g (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds L)

/-- Source: `proof_gap/exercise_452/1.txt`; replace the rationalization ellipsis by the corresponding closed limit. -/
private theorem root_hasDerivAt_one (m : ℤ) :
    HasDerivAt (root m) (1 / (m : ℝ)) 1 := by
  have h :
      HasDerivAt (fun x : ℝ => Real.rpow x (1 / (m : ℝ)))
        (1 / (m : ℝ)) 1 := by
    convert Real.hasDerivAt_rpow_const (x := (1 : ℝ)) (by norm_num) using 1 <;>
      norm_num
  change HasDerivAt (fun x : ℝ => Real.rpow x (1 / (m : ℝ)))
    (1 / (m : ℝ)) 1
  exact h

private theorem root_affine_hasDerivAt (m : ℤ) (a : ℝ) :
    HasDerivAt (fun x : ℝ => root m (1 + a * x)) (a / (m : ℝ)) 0 := by
  have hi : HasDerivAt (fun x : ℝ => 1 + a * x) a 0 := by
    simpa [add_comm] using
      (((hasDerivAt_id (0 : ℝ)).const_mul a).add_const 1)
  have ho :
      HasDerivAt (root m) (1 / (m : ℝ))
        ((fun x : ℝ => 1 + a * x) 0) := by
    simpa using root_hasDerivAt_one m
  simpa [div_eq_mul_inv, mul_comm] using ho.comp 0 hi

private theorem quotient_limit_all (m n : ℤ) (alpha beta : ℝ) :
    HasLimitAt (quotient m n alpha beta) 0 (value m n alpha beta) := by
  have hd :=
    (root_affine_hasDerivAt m alpha).sub
      (root_affine_hasDerivAt n beta)
  have ht := hd.tendsto_slope_zero
  change Filter.Tendsto
    (fun t : ℝ =>
      (root m (1 + alpha * t) - root n (1 + beta * t)) / t)
    (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
    (nhds (alpha / (m : ℝ) - beta / (n : ℝ)))
  simpa [root, div_eq_mul_inv, mul_comm] using ht

theorem gap1 (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (alpha beta : ℝ) :
    HasLimitAt (quotient m n alpha beta) 0
      (value m n alpha beta) := by
  simpa using quotient_limit_all (m : ℤ) (n : ℤ) alpha beta

/-- Source: `proof_gap/exercise_452/2.txt`. -/
theorem gap2 (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (alpha beta : ℝ) :
    HasLimitAt (quotient m n alpha beta) 0
      (((n : ℝ) * alpha - (m : ℝ) * beta) / ((m : ℝ) * n)) := by
  have hm0 : (m : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hm)
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hn)
  convert gap1 m n hm hn alpha beta using 1
  simp [value]
  field_simp [hm0, hn0]

/-- Source: `proof_gap/exercise_452/3.txt`. -/
theorem gap3 (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (alpha beta : ℝ) :
    ((n : ℝ) * alpha - (m : ℝ) * beta) / ((m : ℝ) * n) =
      alpha / m - beta / n := by
  have hm0 : (m : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hm)
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hn)
  field_simp [hm0, hn0] <;> ring

/-- Source: `proof_gap/exercise_452/4.txt`. -/
theorem gap4 (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (alpha beta : ℝ) :
    HasLimitAt (quotient m n alpha beta) 0
      (alpha / m - beta / n) := by
  simpa [value] using gap1 m n hm hn alpha beta

/-- Source: `proof_gap/exercise_452/5.txt`; bind the positive representatives of negative degrees. -/
theorem gap5 (m' n' : ℕ) (hm : 0 < m') (hn : 0 < n')
    (alpha beta : ℝ) : ∀ x, 0 < 1 + alpha * x → 0 < 1 + beta * x →
    root (-(m' : ℤ)) (1 + alpha * x) - root (-(n' : ℤ)) (1 + beta * x) =
      (root n' (1 + beta * x) - root m' (1 + alpha * x)) /
        (root m' (1 + alpha * x) * root n' (1 + beta * x)) := by
  intro x hα hβ
  have hma :
      root (-(m' : ℤ)) (1 + alpha * x) =
        (root (m' : ℤ) (1 + alpha * x))⁻¹ := by
    simpa [root, Real.rpow_neg (le_of_lt hα)]
  have hnb :
      root (-(n' : ℤ)) (1 + beta * x) =
        (root (n' : ℤ) (1 + beta * x))⁻¹ := by
    simpa [root, Real.rpow_neg (le_of_lt hβ)]
  have hmp : 0 < root (m' : ℤ) (1 + alpha * x) := by
    unfold root
    exact Real.rpow_pos_of_pos hα _
  have hnp : 0 < root (n' : ℤ) (1 + beta * x) := by
    unfold root
    exact Real.rpow_pos_of_pos hβ _
  rw [hma, hnb]
  let A : ℝ := root (m' : ℤ) (1 + alpha * x)
  let B : ℝ := root (n' : ℤ) (1 + beta * x)
  change A⁻¹ - B⁻¹ = (B - A) / (A * B)
  have hA : A ≠ 0 := by
    exact ne_of_gt hmp
  have hB : B ≠ 0 := by
    exact ne_of_gt hnp
  field_simp [hA, hB]

/-- Source: `proof_gap/exercise_452/6.txt`. -/
theorem gap6 (m' n' : ℕ) (hm : 0 < m') (hn : 0 < n')
    (alpha beta : ℝ) :
    HasLimitAt (quotient (-(m' : ℤ)) (-(n' : ℤ)) alpha beta) 0
      (beta / n' - alpha / m') := by
  convert quotient_limit_all (-(m' : ℤ)) (-(n' : ℤ)) alpha beta using 1 <;>
    simp [value] <;> ring

/-- Source: `proof_gap/exercise_452/7.txt`. -/
theorem gap7 (m' n' : ℕ) (hm : 0 < m') (hn : 0 < n')
    (alpha beta : ℝ) :
    beta / (n' : ℝ) - alpha / (m' : ℝ) =
      value (-(m' : ℤ)) (-(n' : ℤ)) alpha beta := by
  simp [value] <;> ring

/-- Source: `proof_gap/exercise_452/8.txt`. -/
theorem gap8 (m' n' : ℕ) (hm : 0 < m') (hn : 0 < n')
    (alpha beta : ℝ) :
    HasLimitAt (quotient (-(m' : ℤ)) (-(n' : ℤ)) alpha beta) 0
      (value (-(m' : ℤ)) (-(n' : ℤ)) alpha beta) := by
  simpa using
    quotient_limit_all (-(m' : ℤ)) (-(n' : ℤ)) alpha beta

/-- Source: `proof_gap/exercise_452/9.txt`; use nonzero integer degrees directly. -/
theorem gap9 (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (alpha beta : ℝ) :
    HasLimitAt (quotient m n alpha beta) 0 (value m n alpha beta) := by
  exact quotient_limit_all m n alpha beta

/-- Source: `proof_gap/exercise_452/10.txt`. -/
theorem gap10 (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (alpha beta : ℝ) :
    HasLimitAt (quotient m n alpha beta) 0 (value m n alpha beta) := by
  exact gap9 m n hm hn alpha beta

end

end ProofGap.Exercise452
