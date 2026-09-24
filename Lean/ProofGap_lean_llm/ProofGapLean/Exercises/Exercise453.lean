import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise453

noncomputable section

def root (m : ℤ) (x : ℝ) : ℝ := Real.rpow x (1 / (m : ℝ))
def quotient (m n : ℤ) (alpha beta x : ℝ) : ℝ :=
  (root m (1 + alpha * x) * root n (1 + beta * x) - 1) / x
def value (m n : ℤ) (alpha beta : ℝ) : ℝ :=
  alpha / (m : ℝ) + beta / (n : ℝ)
def HasLimitAt (g : ℝ → ℝ) (a L : ℝ) : Prop :=
  Filter.Tendsto g (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds L)

/-- Exercise 453, gap 1; replace the radical-product ellipsis by the closed limit. -/
private theorem quotient_limit (m n : ℤ) (alpha beta : ℝ) :
    HasLimitAt (quotient m n alpha beta) 0 (value m n alpha beta) := by
  have hroot (k : ℤ) (a : ℝ) :
      HasDerivAt (fun x : ℝ => root k (1 + a * x)) (a / (k : ℝ)) 0 := by
    have ha : HasDerivAt (fun x : ℝ => 1 + a * x) a 0 := by
      convert ((hasDerivAt_id (x := (0 : ℝ))).const_mul a).const_add 1 using 1 <;>
        simp
    have hp :
        HasDerivAt
          (fun y : ℝ => Real.rpow y (1 / (k : ℝ)))
          (1 / (k : ℝ)) 1 := by
      convert Real.hasDerivAt_rpow_const
        (x := (1 : ℝ)) (p := (1 / (k : ℝ))) (by norm_num) using 1 <;>
        norm_num
    have hp0 :
        HasDerivAt
          (fun y : ℝ => Real.rpow y (1 / (k : ℝ)))
          (1 / (k : ℝ)) (1 + a * 0) := by
      simpa using hp
    simpa [root, div_eq_mul_inv, mul_comm] using (hp0.comp 0 ha)
  have hprod :
      HasDerivAt
        (fun x : ℝ =>
          root m (1 + alpha * x) * root n (1 + beta * x))
        (alpha / (m : ℝ) + beta / (n : ℝ)) 0 := by
    convert (hroot m alpha).mul (hroot n beta) using 1 <;>
      simp [root]
  have hs := (hasDerivAt_iff_tendsto_slope_zero).1 hprod
  have hquot :
      quotient m n alpha beta =
        fun t : ℝ =>
          t⁻¹ *
            (root m (1 + alpha * t) * root n (1 + beta * t) - 1) := by
    funext t
    simp [quotient, div_eq_mul_inv, mul_comm]
  unfold HasLimitAt
  rw [hquot]
  simpa [value, root, div_eq_mul_inv, mul_comm] using hs

theorem gap1 (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (alpha beta : ℝ) :
    HasLimitAt (quotient m n alpha beta) 0 (value m n alpha beta) := by
  simpa using (quotient_limit (m : ℤ) (n : ℤ) alpha beta)

/-- Exercise 453, gap 2. -/
theorem gap2 (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (alpha beta : ℝ) :
    HasLimitAt (quotient m n alpha beta) 0
      (((n : ℝ) * alpha + (m : ℝ) * beta) / ((m : ℝ) * n)) := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hclosed :
      (((n : ℝ) * alpha + (m : ℝ) * beta) / ((m : ℝ) * n)) =
        alpha / (m : ℝ) + beta / (n : ℝ) := by
    field_simp [hm0, hn0]
  rw [hclosed]
  simpa [value] using gap1 m n hm hn alpha beta

/-- Exercise 453, gap 3. -/
theorem gap3 (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (alpha beta : ℝ) :
    ((n : ℝ) * alpha + (m : ℝ) * beta) / ((m : ℝ) * n) =
      alpha / m + beta / n := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  field_simp [hm0, hn0]

/-- Exercise 453, gap 4. -/
theorem gap4 (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (alpha beta : ℝ) :
    HasLimitAt (quotient m n alpha beta) 0 (alpha / m + beta / n) := by
  simpa [value] using gap1 m n hm hn alpha beta

/-- Exercise 453, gap 5. -/
theorem gap5 (m' n' : ℕ) (hm : 0 < m') (hn : 0 < n')
    (alpha beta : ℝ) : ∀ x, 0 < 1 + alpha * x → 0 < 1 + beta * x →
    root (-(m' : ℤ)) (1 + alpha * x) * root (-(n' : ℤ)) (1 + beta * x) - 1 =
      (1 - root m' (1 + alpha * x) * root n' (1 + beta * x)) /
        (root m' (1 + alpha * x) * root n' (1 + beta * x)) := by
  intro x hx hy
  have hA : 0 < root (m' : ℤ) (1 + alpha * x) := by
    unfold root
    exact Real.rpow_pos_of_pos hx _
  have hB : 0 < root (n' : ℤ) (1 + beta * x) := by
    unfold root
    exact Real.rpow_pos_of_pos hy _
  have hmneg :
      root (-(m' : ℤ)) (1 + alpha * x) =
        (root (m' : ℤ) (1 + alpha * x))⁻¹ := by
    simp [root, Real.rpow_neg, hx.le]
  have hnneg :
      root (-(n' : ℤ)) (1 + beta * x) =
        (root (n' : ℤ) (1 + beta * x))⁻¹ := by
    simp [root, Real.rpow_neg, hy.le]
  rw [hmneg, hnneg]
  let A : ℝ := root (m' : ℤ) (1 + alpha * x)
  let B : ℝ := root (n' : ℤ) (1 + beta * x)
  have hA0 : A ≠ 0 := by
    dsimp [A]
    exact ne_of_gt hA
  have hB0 : B ≠ 0 := by
    dsimp [B]
    exact ne_of_gt hB
  change A⁻¹ * B⁻¹ - 1 = (1 - A * B) / (A * B)
  field_simp [hA0, hB0]

/-- Exercise 453, gap 6. -/
theorem gap6 (m' n' : ℕ) (hm : 0 < m') (hn : 0 < n')
    (alpha beta : ℝ) :
    HasLimitAt (quotient (-(m' : ℤ)) (-(n' : ℤ)) alpha beta) 0
      (-alpha / m' - beta / n') := by
  simpa [value, div_neg, neg_div, sub_eq_add_neg] using
    (quotient_limit (-(m' : ℤ)) (-(n' : ℤ)) alpha beta)

/-- Exercise 453, gap 7. -/
theorem gap7 (m' n' : ℕ) (hm : 0 < m') (hn : 0 < n')
    (alpha beta : ℝ) :
    -alpha / (m' : ℝ) - beta / (n' : ℝ) =
      value (-(m' : ℤ)) (-(n' : ℤ)) alpha beta := by
  simp [value, div_neg, neg_div, sub_eq_add_neg]

/-- Exercise 453, gap 8. -/
theorem gap8 (m' n' : ℕ) (hm : 0 < m') (hn : 0 < n')
    (alpha beta : ℝ) :
    HasLimitAt (quotient (-(m' : ℤ)) (-(n' : ℤ)) alpha beta) 0
      (value (-(m' : ℤ)) (-(n' : ℤ)) alpha beta) := by
  exact quotient_limit (-(m' : ℤ)) (-(n' : ℤ)) alpha beta

/-- Exercise 453, gap 9. -/
theorem gap9 (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (alpha beta : ℝ) :
    HasLimitAt (quotient m n alpha beta) 0 (value m n alpha beta) := by
  exact quotient_limit m n alpha beta

/-- Exercise 453, gap 10. -/
theorem gap10 (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0)
    (alpha beta : ℝ) :
    HasLimitAt (quotient m n alpha beta) 0 (value m n alpha beta) := by
  exact gap9 m n hm hn alpha beta

end

end ProofGap.Exercise453
