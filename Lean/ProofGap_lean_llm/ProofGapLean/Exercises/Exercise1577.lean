import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

namespace ProofGap.Exercise1577

noncomputable section

def ellipse (a b x y : ℝ) : Prop :=
  0 < x ∧ 0 < y ∧ x ^ 2 / a ^ 2 + y ^ 2 / b ^ 2 = 1

def tangentSlope (a b x y : ℝ) : ℝ := -(b ^ 2 * x) / (a ^ 2 * y)
def tangentArea (a b x y : ℝ) : ℝ := a ^ 2 * b ^ 2 / (2 * x * y)
def auxiliary (a x : ℝ) : ℝ := x ^ 2 * (a ^ 2 - x ^ 2)
def optimalX (a : ℝ) : ℝ := a / Real.sqrt 2
def optimalY (b : ℝ) : ℝ := b / Real.sqrt 2

def IsOptimal (a b x y : ℝ) : Prop :=
  ellipse a b x y ∧ ∀ x₁ y₁, ellipse a b x₁ y₁ →
    tangentArea a b x y ≤ tangentArea a b x₁ y₁

private lemma sqrt_two_pos : 0 < Real.sqrt 2 := by positivity

private lemma sqrt_two_sq : (Real.sqrt 2) ^ 2 = 2 := by
  norm_num

private lemma optimalX_sq (a : ℝ) : (optimalX a) ^ 2 = a ^ 2 / 2 := by
  unfold optimalX
  field_simp [sqrt_two_pos.ne']
  nlinarith [sqrt_two_sq]

private lemma optimalY_sq (b : ℝ) : (optimalY b) ^ 2 = b ^ 2 / 2 := by
  unfold optimalY
  field_simp [sqrt_two_pos.ne']
  nlinarith [sqrt_two_sq]

private lemma optimal_ellipse (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ellipse a b (optimalX a) (optimalY b) := by
  refine ⟨by unfold optimalX; positivity, by unfold optimalY; positivity, ?_⟩
  rw [optimalX_sq, optimalY_sq]
  field_simp [ha.ne', hb.ne']
  norm_num

private lemma optimal_area (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    tangentArea a b (optimalX a) (optimalY b) = a * b := by
  unfold tangentArea optimalX optimalY
  field_simp [ha.ne', hb.ne', sqrt_two_pos.ne']
  nlinarith [sqrt_two_sq]

private lemma area_lower_bound (a b x y : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hxy : ellipse a b x y) :
    a * b ≤ tangentArea a b x y := by
  rcases hxy with ⟨hx, hy, heq⟩
  have hcross : b ^ 2 * x ^ 2 + a ^ 2 * y ^ 2 = a ^ 2 * b ^ 2 := by
    field_simp [ha.ne', hb.ne'] at heq
    nlinarith
  have hprod : 2 * a * b * x * y ≤ a ^ 2 * b ^ 2 := by
    nlinarith [sq_nonneg (b * x - a * y)]
  unfold tangentArea
  apply (le_div_iff₀ (by positivity : 0 < 2 * x * y)).2
  nlinarith

theorem gap1 (a b x y : ℝ) :
    tangentSlope a b x y = -(b ^ 2 * x) / (a ^ 2 * y) := by
  rfl

theorem gap2 (a b x y X Y : ℝ) :
    Y - y = tangentSlope a b x y * (X - x) ↔
      Y - y = -(b ^ 2 * x) / (a ^ 2 * y) * (X - x) := by
  rfl

theorem gap3 (a b x y : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hxy : ellipse a b x y) :
    (a ^ 2 / x, b ^ 2 / y) =
      (a ^ 2 / x, b ^ 2 / y) := by
  rfl

theorem gap4 (a b x y : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hxy : ellipse a b x y) :
    tangentArea a b x y =
      a ^ 3 * b / (2 * x * Real.sqrt (a ^ 2 - x ^ 2)) := by
  rcases hxy with ⟨hx, hy, heq⟩
  have hrad : 0 < a ^ 2 - x ^ 2 := by
    field_simp [ha.ne', hb.ne'] at heq
    by_contra hn
    have hle : a ^ 2 - x ^ 2 ≤ 0 := le_of_not_gt hn
    have hmul : b ^ 2 * (a ^ 2 - x ^ 2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sq_nonneg b) hle
    have hpos : 0 < a ^ 2 * y ^ 2 :=
      mul_pos (sq_pos_of_pos ha) (sq_pos_of_pos hy)
    nlinarith
  have hs : 0 < Real.sqrt (a ^ 2 - x ^ 2) := Real.sqrt_pos.2 hrad
  have hrel : a * y = b * Real.sqrt (a ^ 2 - x ^ 2) := by
    have hsquare := Real.sq_sqrt hrad.le
    have hcross : b ^ 2 * x ^ 2 + a ^ 2 * y ^ 2 = a ^ 2 * b ^ 2 := by
      field_simp [ha.ne', hb.ne'] at heq
      nlinarith
    have hsquares :
        (a * y) ^ 2 = (b * Real.sqrt (a ^ 2 - x ^ 2)) ^ 2 := by
      calc
        (a * y) ^ 2 = a ^ 2 * y ^ 2 := by ring
        _ = b ^ 2 * (a ^ 2 - x ^ 2) := by nlinarith
        _ = b ^ 2 * (Real.sqrt (a ^ 2 - x ^ 2)) ^ 2 := by rw [hsquare]
        _ = (b * Real.sqrt (a ^ 2 - x ^ 2)) ^ 2 := by ring
    nlinarith [sq_nonneg (a * y + b * Real.sqrt (a ^ 2 - x ^ 2)),
      mul_pos ha hy, mul_pos hb hs]
  unfold tangentArea
  field_simp [hx.ne', hy.ne', hs.ne', ha.ne', hb.ne']
  nlinarith

theorem gap5 (a x : ℝ) :
    deriv (auxiliary a) x = 2 * a ^ 2 * x - 4 * x ^ 3 := by
  unfold auxiliary
  have h := ((hasDerivAt_id x).pow 2).mul
    ((hasDerivAt_const x (a ^ 2 : ℝ)).sub ((hasDerivAt_id x).pow 2))
  convert h.deriv using 1 <;> simp [id] <;> ring

theorem gap6 (a x : ℝ) (ha : 0 < a) (hx : 0 < x)
    (hcrit : deriv (auxiliary a) x = 0) :
    x = optimalX a := by
  rw [gap5] at hcrit
  have hx2 : 2 * x ^ 2 = a ^ 2 := by nlinarith
  have hxq2 : (x * Real.sqrt 2) ^ 2 = a ^ 2 := by
    rw [mul_pow, sqrt_two_sq]
    nlinarith
  have hxq : x * Real.sqrt 2 = a := by
    nlinarith [sq_nonneg (x * Real.sqrt 2 + a),
      mul_pos hx sqrt_two_pos]
  unfold optimalX
  exact (eq_div_iff sqrt_two_pos.ne').2 hxq

theorem gap7 (a b x y : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hopt : IsOptimal a b x y) :
    x = optimalX a ∧ y = optimalY b := by
  rcases hopt.1 with ⟨hx, hy, hellipse⟩
  have hle := hopt.2 (optimalX a) (optimalY b) (optimal_ellipse a b ha hb)
  rw [optimal_area a b ha hb] at hle
  have hlower := area_lower_bound a b x y ha hb ⟨hx, hy, hellipse⟩
  have harea : tangentArea a b x y = a * b := le_antisymm hle hlower
  have hcross : b ^ 2 * x ^ 2 + a ^ 2 * y ^ 2 = a ^ 2 * b ^ 2 := by
    field_simp [ha.ne', hb.ne'] at hellipse
    nlinarith
  have hprod : a ^ 2 * b ^ 2 = 2 * a * b * x * y := by
    unfold tangentArea at harea
    field_simp [hx.ne', hy.ne'] at harea
    have hmul := congrArg (fun z : ℝ => z * a * b) harea
    ring_nf at hmul ⊢
    exact hmul
  have hlin : b * x = a * y := by
    have hsquare : (b * x - a * y) ^ 2 = 0 := by
      nlinarith
    nlinarith [sq_nonneg (b * x - a * y)]
  have hlinsq : b ^ 2 * x ^ 2 = a ^ 2 * y ^ 2 := by
    nlinarith [congrArg (fun z : ℝ => z ^ 2) hlin]
  have hx2 : 2 * x ^ 2 = a ^ 2 := by
    have hb2 : 0 < b ^ 2 := sq_pos_of_pos hb
    nlinarith
  have hxq2 : (x * Real.sqrt 2) ^ 2 = a ^ 2 := by
    rw [mul_pow, sqrt_two_sq]
    nlinarith
  have hxq : x * Real.sqrt 2 = a := by
    nlinarith [sq_nonneg (x * Real.sqrt 2 + a),
      mul_pos hx sqrt_two_pos]
  have hxval : x = optimalX a := by
    unfold optimalX
    exact (eq_div_iff sqrt_two_pos.ne').2 hxq
  refine ⟨hxval, ?_⟩
  apply (mul_left_cancel₀ ha.ne')
  calc
    a * y = b * x := hlin.symm
    _ = b * (a / Real.sqrt 2) := by rw [hxval]; rfl
    _ = a * (b / Real.sqrt 2) := by ring
    _ = a * optimalY b := by rfl

theorem gap8 (a : ℝ) (ha : 0 < a) :
    ∀ x ∈ Set.Ioo 0 a, auxiliary a x ≤ auxiliary a (optimalX a) := by
  intro x hx
  rw [auxiliary, auxiliary, optimalX_sq]
  nlinarith [sq_nonneg (x ^ 2 - a ^ 2 / 2)]

theorem gap9 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    tangentArea a b (optimalX a) (optimalY b) = a * b := by
  exact optimal_area a b ha hb

theorem gap10 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    IsOptimal a b (optimalX a) (optimalY b) := by
  refine ⟨optimal_ellipse a b ha hb, ?_⟩
  intro x₁ y₁ hxy
  rw [optimal_area a b ha hb]
  exact area_lower_bound a b x₁ y₁ ha hb hxy

end

end ProofGap.Exercise1577
