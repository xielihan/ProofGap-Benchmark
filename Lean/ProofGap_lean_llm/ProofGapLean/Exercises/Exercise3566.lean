import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise3566

noncomputable section

structure Point2 where
  x : ℝ
  y : ℝ

def familyFunction (p x y alpha : ℝ) : ℝ :=
  x * Real.cos alpha + y * Real.sin alpha - p

def parameterDerivative (p x y alpha : ℝ) : ℝ :=
  deriv (fun t => familyFunction p x y t) alpha

def envelopeCondition (p : ℝ) (q : Point2) (alpha : ℝ) : Prop :=
  familyFunction p q.x q.y alpha = 0 ∧
    parameterDerivative p q.x q.y alpha = 0

def envelope (p : ℝ) : Set Point2 :=
  {q | ∃ alpha : ℝ, envelopeCondition p q alpha}

def circle (p : ℝ) : Set Point2 :=
  {q | q.x ^ 2 + q.y ^ 2 = p ^ 2}

private theorem parameterDerivative_formula
    (p x y alpha : ℝ) :
    parameterDerivative p x y alpha =
      -x * Real.sin alpha + y * Real.cos alpha := by
  unfold parameterDerivative
  change deriv
    (fun t => x * Real.cos t + y * Real.sin t - p) alpha = _
  convert (((Real.hasDerivAt_cos alpha).const_mul x).add
    ((Real.hasDerivAt_sin alpha).const_mul y)).sub_const p |>.deriv using 1 <;>
    ring

private theorem exists_cos_sin_of_sq_add_sq_eq_one
    (a b : ℝ) (h : a ^ 2 + b ^ 2 = 1) :
    ∃ alpha : ℝ, Real.cos alpha = a ∧ Real.sin alpha = b := by
  have ha_sq : a ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg b]
  have ha_lower : -1 ≤ a := by
    nlinarith [sq_nonneg (a + 1)]
  have ha_upper : a ≤ 1 := by
    nlinarith [sq_nonneg (a - 1)]
  have hrad : 0 ≤ 1 - a ^ 2 := by
    nlinarith
  have hsqrt_sq : (Real.sqrt (1 - a ^ 2)) ^ 2 = b ^ 2 := by
    rw [Real.sq_sqrt hrad]
    nlinarith
  by_cases hb : 0 ≤ b
  · have hsqrt : Real.sqrt (1 - a ^ 2) = b := by
      nlinarith [Real.sqrt_nonneg (1 - a ^ 2)]
    refine ⟨Real.arccos a, Real.cos_arccos ha_lower ha_upper, ?_⟩
    rw [Real.sin_arccos]
    exact hsqrt
  · have hb_neg : b < 0 := lt_of_not_ge hb
    have hsqrt : Real.sqrt (1 - a ^ 2) = -b := by
      nlinarith [Real.sqrt_nonneg (1 - a ^ 2)]
    refine ⟨-Real.arccos a, ?_, ?_⟩
    · rw [Real.cos_neg, Real.cos_arccos ha_lower ha_upper]
    · rw [Real.sin_neg, Real.sin_arccos, hsqrt]
      ring

theorem gap1 (p : ℝ) :
    ∀ q : Point2, ∀ alpha : ℝ, envelopeCondition p q alpha →
      familyFunction p q.x q.y alpha = 0 := by
  intro q alpha h
  exact h.1

theorem gap2 (p : ℝ) :
    ∀ q : Point2, ∀ alpha : ℝ, envelopeCondition p q alpha →
      parameterDerivative p q.x q.y alpha = 0 := by
  intro q alpha h
  exact h.2

theorem gap3 (p : ℝ) :
    ∀ q : Point2, ∀ alpha : ℝ,
      familyFunction p q.x q.y alpha = 0 →
      q.x * Real.cos alpha + q.y * Real.sin alpha - p = 0 := by
  intro q alpha h
  simpa [familyFunction] using h

theorem gap4 (p : ℝ) :
    ∀ q : Point2, ∀ alpha : ℝ,
      parameterDerivative p q.x q.y alpha = 0 →
      -q.x * Real.sin alpha + q.y * Real.cos alpha = 0 := by
  intro q alpha h
  rw [parameterDerivative_formula] at h
  exact h

theorem gap5 (p : ℝ) :
    ∀ q : Point2, ∀ alpha : ℝ,
      q.x * Real.cos alpha + q.y * Real.sin alpha - p = 0 →
      -q.x * Real.sin alpha + q.y * Real.cos alpha = 0 →
      q.x ^ 2 + q.y ^ 2 = p ^ 2 := by
  intro q alpha hfamily hderiv
  have ha :
      q.x * Real.cos alpha + q.y * Real.sin alpha = p := by
    linarith
  calc
    q.x ^ 2 + q.y ^ 2 =
        (q.x ^ 2 + q.y ^ 2) * 1 := by ring
    _ = (q.x ^ 2 + q.y ^ 2) *
        (Real.sin alpha ^ 2 + Real.cos alpha ^ 2) := by
      rw [Real.sin_sq_add_cos_sq]
    _ = (q.x * Real.cos alpha + q.y * Real.sin alpha) ^ 2 +
        (-q.x * Real.sin alpha + q.y * Real.cos alpha) ^ 2 := by
      ring
    _ = p ^ 2 := by rw [ha, hderiv]; ring

theorem gap6 (p : ℝ) :
    envelope p = circle p := by
  ext q
  change (∃ alpha : ℝ, envelopeCondition p q alpha) ↔
    q.x ^ 2 + q.y ^ 2 = p ^ 2
  constructor
  · rintro ⟨alpha, halpha⟩
    exact gap5 p q alpha
      (gap1 p q alpha halpha)
      (gap4 p q alpha (gap2 p q alpha halpha))
  · intro hcircle
    by_cases hp : p = 0
    · have hx : q.x = 0 := by
        nlinarith [sq_nonneg q.x, sq_nonneg q.y]
      have hy : q.y = 0 := by
        nlinarith [sq_nonneg q.x, sq_nonneg q.y]
      refine ⟨0, ?_, ?_⟩
      · simp [familyFunction, hp, hx, hy]
      · rw [parameterDerivative_formula]
        simp [hx, hy]
    · have hunit :
          (q.x / p) ^ 2 + (q.y / p) ^ 2 = 1 := by
        calc
          (q.x / p) ^ 2 + (q.y / p) ^ 2 =
              q.x ^ 2 / p ^ 2 + q.y ^ 2 / p ^ 2 := by
            rw [div_pow, div_pow]
          _ = (q.x ^ 2 + q.y ^ 2) / p ^ 2 := by
            rw [add_div]
          _ = p ^ 2 / p ^ 2 := by rw [hcircle]
          _ = 1 := div_self (pow_ne_zero 2 hp)
      rcases exists_cos_sin_of_sq_add_sq_eq_one
          (q.x / p) (q.y / p) hunit with ⟨alpha, hcos, hsin⟩
      refine ⟨alpha, ?_, ?_⟩
      · unfold familyFunction
        rw [hcos, hsin]
        field_simp [hp] <;> nlinarith [hcircle]
      · rw [parameterDerivative_formula, hcos, hsin]
        field_simp [hp] <;> ring

end

end ProofGap.Exercise3566
