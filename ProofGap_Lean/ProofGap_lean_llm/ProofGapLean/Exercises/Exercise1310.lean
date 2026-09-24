import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1310

noncomputable section

def xCoord (a t : ℝ) : ℝ := a * (t - Real.sin t)
def yCoord (a t : ℝ) : ℝ := a * (1 - Real.cos t)
def cot (t : ℝ) : ℝ := Real.cos t / Real.sin t
def csc (t : ℝ) : ℝ := 1 / Real.sin t

def d1 (a t : ℝ) : ℝ :=
  deriv (yCoord a) t / deriv (xCoord a) t

def d2 (a t : ℝ) : ℝ :=
  deriv (d1 a) t / deriv (xCoord a) t

def StrictlyConcaveArc (a : ℝ) : Prop :=
  ∀ t ∈ Set.Ioo (0 : ℝ) (2 * Real.pi), d2 a t < 0

private theorem cycloid_hasDerivAt_xCoord (a t : ℝ) :
    HasDerivAt (xCoord a) (a * (1 - Real.cos t)) t := by
  simpa [xCoord] using
    (((hasDerivAt_id t).sub (Real.hasDerivAt_sin t)).const_mul a)

private theorem cycloid_hasDerivAt_yCoord (a t : ℝ) :
    HasDerivAt (yCoord a) (a * Real.sin t) t := by
  simpa [yCoord] using
    (((hasDerivAt_const t (1 : ℝ)).sub (Real.hasDerivAt_cos t)).const_mul a)

private theorem cycloid_deriv_xCoord (a t : ℝ) :
    deriv (xCoord a) t = a * (1 - Real.cos t) :=
  (cycloid_hasDerivAt_xCoord a t).deriv

private theorem cycloid_deriv_yCoord (a t : ℝ) :
    deriv (yCoord a) t = a * Real.sin t :=
  (cycloid_hasDerivAt_yCoord a t).deriv

private theorem cycloid_hasDerivAt_deriv_xCoord (a t : ℝ) :
    HasDerivAt (deriv (xCoord a)) (a * Real.sin t) t := by
  have hfun : deriv (xCoord a) = fun s => a * (1 - Real.cos s) := by
    funext s
    exact cycloid_deriv_xCoord a s
  rw [hfun]
  simpa using
    (((hasDerivAt_const t (1 : ℝ)).sub (Real.hasDerivAt_cos t)).const_mul a)

private theorem cycloid_hasDerivAt_deriv_yCoord (a t : ℝ) :
    HasDerivAt (deriv (yCoord a)) (a * Real.cos t) t := by
  have hfun : deriv (yCoord a) = fun s => a * Real.sin s := by
    funext s
    exact cycloid_deriv_yCoord a s
  rw [hfun]
  simpa using ((Real.hasDerivAt_sin t).const_mul a)

private theorem cycloid_second_deriv_xCoord (a t : ℝ) :
    deriv (deriv (xCoord a)) t = a * Real.sin t :=
  (cycloid_hasDerivAt_deriv_xCoord a t).deriv

private theorem cycloid_second_deriv_yCoord (a t : ℝ) :
    deriv (deriv (yCoord a)) t = a * Real.cos t :=
  (cycloid_hasDerivAt_deriv_yCoord a t).deriv

private theorem cycloid_one_sub_cos (t : ℝ) :
    1 - Real.cos t = 2 * Real.sin (t / 2) ^ 2 := by
  have hcos : Real.cos t = 2 * Real.cos (t / 2) ^ 2 - 1 := by
    calc
      Real.cos t = Real.cos (2 * (t / 2)) := by
        congr 1
        ring
      _ = 2 * Real.cos (t / 2) ^ 2 - 1 := Real.cos_two_mul (t / 2)
  rw [hcos]
  nlinarith [Real.sin_sq_add_cos_sq (t / 2)]

theorem gap1 (a t : ℝ) (ha : a ≠ 0)
    (ht : 1 - Real.cos t ≠ 0) :
    d1 a t =
      a * Real.sin t / (a * (1 - Real.cos t)) := by
  rw [d1, cycloid_deriv_yCoord, cycloid_deriv_xCoord]

theorem gap2 (a t : ℝ) (ha : a ≠ 0)
    (ht : Real.sin (t / 2) ≠ 0) :
    a * Real.sin t / (a * (1 - Real.cos t)) =
      cot (t / 2) := by
  have hsin : Real.sin t =
      2 * Real.sin (t / 2) * Real.cos (t / 2) := by
    calc
      Real.sin t = Real.sin (2 * (t / 2)) := by
        congr 1
        ring
      _ = 2 * Real.sin (t / 2) * Real.cos (t / 2) :=
        Real.sin_two_mul (t / 2)
  rw [hsin, cycloid_one_sub_cos]
  unfold cot
  field_simp [ha, ht] <;> ring

theorem gap3 (a t : ℝ) (ha : a ≠ 0)
    (ht : Real.sin (t / 2) ≠ 0) :
    d1 a t = cot (t / 2) := by
  have hden : 1 - Real.cos t ≠ 0 := by
    rw [cycloid_one_sub_cos]
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 ht)
  calc
    d1 a t = a * Real.sin t / (a * (1 - Real.cos t)) :=
      gap1 a t ha hden
    _ = cot (t / 2) := gap2 a t ha ht

theorem gap4 (a t : ℝ) (ha : a ≠ 0)
    (ht : 1 - Real.cos t ≠ 0) :
    d2 a t =
      (deriv (xCoord a) t * deriv (deriv (yCoord a)) t -
        deriv (deriv (xCoord a)) t * deriv (yCoord a) t) /
        deriv (xCoord a) t ^ 3 := by
  have hdx : deriv (xCoord a) t ≠ 0 := by
    rw [cycloid_deriv_xCoord]
    exact mul_ne_zero ha ht
  have hq :
      HasDerivAt (d1 a)
        ((a * Real.cos t * deriv (xCoord a) t -
            deriv (yCoord a) t * (a * Real.sin t)) /
          deriv (xCoord a) t ^ 2) t := by
    simpa only [d1] using
      (cycloid_hasDerivAt_deriv_yCoord a t).div
        (cycloid_hasDerivAt_deriv_xCoord a t) hdx
  unfold d2
  rw [hq.deriv, cycloid_second_deriv_xCoord,
    cycloid_second_deriv_yCoord]
  field_simp [hdx] <;> ring

theorem gap5 (a t : ℝ) (ha : a ≠ 0)
    (ht : Real.sin (t / 2) ≠ 0) :
    d2 a t =
      -(csc (t / 2) ^ 2) /
        (2 * a * (1 - Real.cos t)) := by
  have hden : 1 - Real.cos t ≠ 0 := by
    rw [cycloid_one_sub_cos]
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 ht)
  rw [gap4 a t ha hden]
  rw [cycloid_deriv_xCoord, cycloid_deriv_yCoord,
    cycloid_second_deriv_xCoord, cycloid_second_deriv_yCoord]
  have htrig :
      (1 - Real.cos t) * Real.cos t - Real.sin t ^ 2 =
        -(1 - Real.cos t) := by
    nlinarith [Real.sin_sq_add_cos_sq t]
  have hnum :
      a * (1 - Real.cos t) * (a * Real.cos t) -
          a * Real.sin t * (a * Real.sin t) =
        -(a ^ 2 * (1 - Real.cos t)) := by
    calc
      a * (1 - Real.cos t) * (a * Real.cos t) -
          a * Real.sin t * (a * Real.sin t) =
          a ^ 2 * ((1 - Real.cos t) * Real.cos t - Real.sin t ^ 2) := by
            ring
      _ = a ^ 2 * (-(1 - Real.cos t)) := by rw [htrig]
      _ = -(a ^ 2 * (1 - Real.cos t)) := by ring
  rw [hnum, cycloid_one_sub_cos]
  unfold csc
  field_simp [ha, ht] <;> ring

theorem gap6 (a t : ℝ) (ha : 0 < a)
    (ht0 : 0 < t) (ht2π : t < 2 * Real.pi) :
    -(csc (t / 2) ^ 2) /
        (2 * a * (1 - Real.cos t)) < 0 := by
  have hhalf0 : 0 < t / 2 := by linarith
  have hhalfpi : t / 2 < Real.pi := by linarith
  have hsin : 0 < Real.sin (t / 2) :=
    Real.sin_pos_of_pos_of_lt_pi hhalf0 hhalfpi
  have hone : 0 < 1 - Real.cos t := by
    rw [cycloid_one_sub_cos]
    positivity
  have hcsc : 0 < csc (t / 2) ^ 2 := by
    unfold csc
    positivity
  have hden : 0 < 2 * a * (1 - Real.cos t) := by positivity
  exact div_neg_of_neg_of_pos (neg_neg_of_pos hcsc) hden

theorem gap7 (a t : ℝ) (ha : 0 < a)
    (ht0 : 0 < t) (ht2π : t < 2 * Real.pi) :
    d2 a t < 0 := by
  have hhalf0 : 0 < t / 2 := by linarith
  have hhalfpi : t / 2 < Real.pi := by linarith
  have ht : Real.sin (t / 2) ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hhalf0 hhalfpi)
  calc
    d2 a t = -(csc (t / 2) ^ 2) /
        (2 * a * (1 - Real.cos t)) :=
      gap5 a t (ne_of_gt ha) ht
    _ < 0 := gap6 a t ha ht0 ht2π

theorem gap8 (a : ℝ) (ha : 0 < a) :
    StrictlyConcaveArc a := by
  intro t ht
  exact gap7 a t ha ht.1 ht.2

end

end ProofGap.Exercise1310
