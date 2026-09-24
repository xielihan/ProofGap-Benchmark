import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise3682

noncomputable section

def objective (q : ℝ × ℝ) : ℝ :=
  (q.1 - q.2 ^ 2) * (2 * q.1 - q.2 ^ 2)

def IsLocalMinOnSlope (k : ℝ) : Prop :=
  ∃ epsilon > 0, ∀ x, |x| < epsilon →
    objective (0, 0) ≤ objective (x, k * x)

def IsLocalMinOnVertical : Prop :=
  ∃ epsilon > 0, ∀ y, |y| < epsilon →
    objective (0, 0) ≤ objective (0, y)

def IsLocalMinAtOrigin : Prop :=
  ∃ epsilon > 0, ∀ x y, |x| < epsilon → |y| < epsilon →
    objective (0, 0) ≤ objective (x, y)

def LinewiseLocalMinimum : Prop :=
  (∀ k : ℝ, IsLocalMinOnSlope k) ∧ IsLocalMinOnVertical

theorem gap1 :
    ∀ x y : ℝ,
      objective (x, y) = (x - y ^ 2) * (2 * x - y ^ 2) := by
  intro x y
  rfl

theorem gap2 :
    ∀ x k : ℝ,
      objective (x, k * x) =
        (x - k ^ 2 * x ^ 2) * (2 * x - k ^ 2 * x ^ 2) := by
  intro x k
  simpa [objective, mul_pow]

theorem gap3 :
    ∀ x k : ℝ,
      (x - k ^ 2 * x ^ 2) * (2 * x - k ^ 2 * x ^ 2) =
        x ^ 2 * (1 - k ^ 2 * x) * (2 - k ^ 2 * x) := by
  intro x k
  ring

theorem gap4 :
    ∀ x k : ℝ,
      objective (x, k * x) =
        x ^ 2 * (1 - k ^ 2 * x) * (2 - k ^ 2 * x) := by
  intro x k
  calc
    objective (x, k * x) =
        (x - k ^ 2 * x ^ 2) * (2 * x - k ^ 2 * x ^ 2) := gap2 x k
    _ = x ^ 2 * (1 - k ^ 2 * x) * (2 - k ^ 2 * x) := gap3 x k

theorem gap5 :
    ∀ x k : ℝ, 0 < |x| → |x| < 1 / k ^ 2 →
      objective (x, k * x) > 0 := by
  intro x k hx hbound
  by_cases hk : k = 0
  · subst k
    have hfalse : |x| < 0 := by
      simpa using hbound
    exact (not_lt_of_ge (abs_nonneg x) hfalse).elim
  · have hk2 : 0 < k ^ 2 := sq_pos_of_ne_zero hk
    have hprod : k ^ 2 * |x| < 1 := by
      calc
        k ^ 2 * |x| < k ^ 2 * (1 / k ^ 2) :=
          mul_lt_mul_of_pos_left hbound hk2
        _ = 1 := by field_simp [hk]
    have hxle : x ≤ |x| := le_abs_self x
    have hkx : k ^ 2 * x < 1 :=
      lt_of_le_of_lt
        (mul_le_mul_of_nonneg_left hxle (le_of_lt hk2)) hprod
    rw [gap4 x k]
    have hxsq : 0 < x ^ 2 := sq_pos_of_ne_zero (abs_pos.mp hx)
    have hfac1 : 0 < 1 - k ^ 2 * x := sub_pos.mpr hkx
    have hfac2 : 0 < 2 - k ^ 2 * x := by linarith
    exact mul_pos (mul_pos hxsq hfac1) hfac2

theorem gap6 :
    objective (0, 0) = 0 := by
  norm_num [objective]

theorem gap7 :
    ∀ k : ℝ, IsLocalMinOnSlope k := by
  intro k
  by_cases hk : k = 0
  · subst k
    refine ⟨1, by norm_num, ?_⟩
    intro x hx
    rw [gap6, gap4]
    nlinarith [sq_nonneg x]
  · have hk2 : 0 < k ^ 2 := sq_pos_of_ne_zero hk
    refine ⟨1 / k ^ 2, div_pos (by norm_num) hk2, ?_⟩
    intro x hx
    rw [gap6]
    by_cases hzero : x = 0
    · subst x
      norm_num [objective]
    · exact le_of_lt (gap5 x k (abs_pos.mpr hzero) hx)

theorem gap8 :
    ∀ y : ℝ, objective (0, y) = y ^ 4 := by
  intro y
  unfold objective
  ring

theorem gap9 :
    IsLocalMinOnVertical := by
  refine ⟨1, by norm_num, ?_⟩
  intro y hy
  rw [gap6, gap8]
  positivity

theorem gap10 :
    ∀ a : ℝ, 0 < a →
      objective (a, Real.sqrt (1.5 * a)) = -0.25 * a ^ 2 := by
  intro a ha
  have harg : 0 ≤ 1.5 * a := by positivity
  have hs : (Real.sqrt (1.5 * a)) ^ 2 = 1.5 * a :=
    Real.sq_sqrt harg
  rw [gap1, hs]
  ring

theorem gap11 :
    ∃ a : ℝ, 0 < a ∧ -0.25 * a ^ 2 < 0 := by
  refine ⟨1, by norm_num, ?_⟩
  norm_num

theorem gap12 :
    ∃ a : ℝ, 0 < a ∧
      objective (a, Real.sqrt (1.5 * a)) < 0 := by
  refine ⟨1, by norm_num, ?_⟩
  rw [gap10 1 (by norm_num)]
  norm_num

theorem gap13 :
    ¬ IsLocalMinAtOrigin := by
  intro h
  rcases h with ⟨epsilon, hepsilon, hmin⟩
  let a : ℝ := min (epsilon / 2) (epsilon ^ 2 / 2)
  have hhalf : 0 < epsilon / 2 := by linarith
  have hsquarehalf : 0 < epsilon ^ 2 / 2 := by positivity
  have ha : 0 < a := by
    dsimp [a]
    exact lt_min hhalf hsquarehalf
  have hale1 : a ≤ epsilon / 2 := by
    dsimp [a]
    exact min_le_left _ _
  have hale2 : a ≤ epsilon ^ 2 / 2 := by
    dsimp [a]
    exact min_le_right _ _
  have haepsilon : a < epsilon := by linarith
  have harg : 0 ≤ 1.5 * a := by positivity
  have hsquare : (Real.sqrt (1.5 * a)) ^ 2 = 1.5 * a :=
    Real.sq_sqrt harg
  have hepssq : 1.5 * a < epsilon ^ 2 := by
    have hepssqpos : 0 < epsilon ^ 2 := sq_pos_of_ne_zero (ne_of_gt hepsilon)
    nlinarith [hale2]
  have hsqrt : Real.sqrt (1.5 * a) < epsilon := by
    have hsnonneg : 0 ≤ Real.sqrt (1.5 * a) := Real.sqrt_nonneg _
    by_contra hnot
    have hge : epsilon ≤ Real.sqrt (1.5 * a) := le_of_not_gt hnot
    have hsum : 0 ≤ Real.sqrt (1.5 * a) + epsilon := by linarith
    have hmul :
        0 ≤ (Real.sqrt (1.5 * a) - epsilon) *
          (Real.sqrt (1.5 * a) + epsilon) :=
      mul_nonneg (sub_nonneg.mpr hge) hsum
    nlinarith [hmul, hsquare, hepssq]
  have hnonneg := hmin a (Real.sqrt (1.5 * a))
    (by simpa [abs_of_pos ha] using haepsilon)
    (by simpa [abs_of_nonneg (Real.sqrt_nonneg _)] using hsqrt)
  rw [gap6, gap10 a ha] at hnonneg
  have hasq : 0 < a ^ 2 := sq_pos_of_ne_zero (ne_of_gt ha)
  nlinarith

theorem gap14 :
    ¬ (LinewiseLocalMinimum → IsLocalMinAtOrigin) := by
  intro h
  apply gap13
  apply h
  exact ⟨gap7, gap9⟩

theorem gap15 :
    ¬ (LinewiseLocalMinimum → IsLocalMinAtOrigin) := by
  exact gap14

end

end ProofGap.Exercise3682
