import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ProofGap.Exercise3535

noncomputable section

abbrev Point3 := ℝ × (ℝ × ℝ)

def curve (a t : ℝ) : Point3 :=
  (a * Real.exp t * Real.cos t,
    (a * Real.exp t * Real.sin t, a * Real.exp t))

def position (a t : ℝ) : Point3 := curve a t

def tangent (a t : ℝ) : Point3 :=
  (deriv (fun s => (curve a s).1) t,
    (deriv (fun s => (curve a s).2.1) t,
      deriv (fun s => (curve a s).2.2) t))

def algebraicTangent (a t : ℝ) : Point3 :=
  ((curve a t).1 - (curve a t).2.1,
    ((curve a t).1 + (curve a t).2.1, (curve a t).2.2))

def dot (U V : Point3) : ℝ :=
  U.1 * V.1 + U.2.1 * V.2.1 + U.2.2 * V.2.2

def norm3 (V : Point3) : ℝ :=
  Real.sqrt (V.1 ^ 2 + V.2.1 ^ 2 + V.2.2 ^ 2)

def angleCos (a t : ℝ) : ℝ :=
  dot (position a t) (tangent a t) /
    (norm3 (position a t) * norm3 (tangent a t))

theorem gap1 (a : ℝ) :
    ∀ t, position a t = curve a t := by
  intro t
  rfl

theorem gap2 (a : ℝ) :
    ∀ t,
      tangent a t =
        (deriv (fun s => (curve a s).1) t,
          (deriv (fun s => (curve a s).2.1) t,
            deriv (fun s => (curve a s).2.2) t)) := by
  intro t
  rfl

theorem gap3 (a : ℝ) :
    ∀ t,
      tangent a t =
        (a * Real.exp t * (Real.cos t - Real.sin t),
          (a * Real.exp t * (Real.sin t + Real.cos t), a * Real.exp t)) := by
  intro t
  apply Prod.ext
  · change
      deriv (fun s : ℝ => a * Real.exp s * Real.cos s) t =
        a * Real.exp t * (Real.cos t - Real.sin t)
    have hfun :
        (fun s : ℝ => a * Real.exp s * Real.cos s) =
          (fun s : ℝ => a * Real.exp s) * Real.cos := by
      funext s
      rfl
    rw [hfun]
    rw [((((Real.hasDerivAt_exp t).const_mul a).mul
      (Real.hasDerivAt_cos t)).deriv)]
    ring
  · apply Prod.ext
    · change
        deriv (fun s : ℝ => a * Real.exp s * Real.sin s) t =
          a * Real.exp t * (Real.sin t + Real.cos t)
      have hfun :
          (fun s : ℝ => a * Real.exp s * Real.sin s) =
            (fun s : ℝ => a * Real.exp s) * Real.sin := by
        funext s
        rfl
      rw [hfun]
      rw [((((Real.hasDerivAt_exp t).const_mul a).mul
        (Real.hasDerivAt_sin t)).deriv)]
      ring
    · change
        deriv (fun s : ℝ => a * Real.exp s) t = a * Real.exp t
      rw [((Real.hasDerivAt_exp t).const_mul a).deriv]

theorem gap4 (a : ℝ) :
    ∀ t,
      (a * Real.exp t * (Real.cos t - Real.sin t),
          (a * Real.exp t * (Real.sin t + Real.cos t), a * Real.exp t)) =
        algebraicTangent a t := by
  intro t
  apply Prod.ext
  · change
      a * Real.exp t * (Real.cos t - Real.sin t) =
        a * Real.exp t * Real.cos t - a * Real.exp t * Real.sin t
    ring
  · apply Prod.ext
    · change
        a * Real.exp t * (Real.sin t + Real.cos t) =
          a * Real.exp t * Real.cos t + a * Real.exp t * Real.sin t
      ring
    · rfl

theorem gap5 (a : ℝ) :
    ∀ t, tangent a t = algebraicTangent a t := by
  intro t
  calc
    tangent a t =
        (a * Real.exp t * (Real.cos t - Real.sin t),
          (a * Real.exp t * (Real.sin t + Real.cos t), a * Real.exp t)) :=
      gap3 a t
    _ = algebraicTangent a t := gap4 a t

theorem gap6 (a t : ℝ) (ha : a ≠ 0) :
    angleCos a t =
      dot (position a t) (tangent a t) /
        (norm3 (position a t) * norm3 (tangent a t)) := by
  rfl

theorem gap7 (a t : ℝ) (ha : a ≠ 0) :
    dot (position a t) (tangent a t) /
        (norm3 (position a t) * norm3 (tangent a t)) =
      ((curve a t).1 * ((curve a t).1 - (curve a t).2.1) +
          (curve a t).2.1 * ((curve a t).1 + (curve a t).2.1) +
          (curve a t).2.2 ^ 2) /
        (Real.sqrt
            ((curve a t).1 ^ 2 + (curve a t).2.1 ^ 2 + (curve a t).2.2 ^ 2) *
          Real.sqrt
            (((curve a t).1 - (curve a t).2.1) ^ 2 +
              ((curve a t).1 + (curve a t).2.1) ^ 2 +
              (curve a t).2.2 ^ 2)) := by
  simp only [gap1 a t, gap5 a t, dot, norm3, algebraicTangent, pow_two]

theorem gap8 (a t : ℝ) (ha : a ≠ 0) :
    ((curve a t).1 * ((curve a t).1 - (curve a t).2.1) +
          (curve a t).2.1 * ((curve a t).1 + (curve a t).2.1) +
          (curve a t).2.2 ^ 2) /
        (Real.sqrt
            ((curve a t).1 ^ 2 + (curve a t).2.1 ^ 2 + (curve a t).2.2 ^ 2) *
          Real.sqrt
            (((curve a t).1 - (curve a t).2.1) ^ 2 +
              ((curve a t).1 + (curve a t).2.1) ^ 2 +
              (curve a t).2.2 ^ 2)) =
      2 * (curve a t).2.2 ^ 2 /
        (Real.sqrt (2 * (curve a t).2.2 ^ 2) *
          Real.sqrt (3 * (curve a t).2.2 ^ 2)) := by
  have hxy :
      (curve a t).1 ^ 2 + (curve a t).2.1 ^ 2 =
        (curve a t).2.2 ^ 2 := by
    change
      (a * Real.exp t * Real.cos t) ^ 2 +
          (a * Real.exp t * Real.sin t) ^ 2 =
        (a * Real.exp t) ^ 2
    calc
      (a * Real.exp t * Real.cos t) ^ 2 +
            (a * Real.exp t * Real.sin t) ^ 2 =
          (a * Real.exp t) ^ 2 *
            (Real.sin t ^ 2 + Real.cos t ^ 2) := by ring
      _ = (a * Real.exp t) ^ 2 := by
        rw [Real.sin_sq_add_cos_sq]
        ring
  have hnum :
      (curve a t).1 * ((curve a t).1 - (curve a t).2.1) +
            (curve a t).2.1 * ((curve a t).1 + (curve a t).2.1) +
            (curve a t).2.2 ^ 2 =
        2 * (curve a t).2.2 ^ 2 := by
    calc
      (curve a t).1 * ((curve a t).1 - (curve a t).2.1) +
            (curve a t).2.1 * ((curve a t).1 + (curve a t).2.1) +
            (curve a t).2.2 ^ 2 =
          (curve a t).1 ^ 2 + (curve a t).2.1 ^ 2 +
            (curve a t).2.2 ^ 2 := by ring
      _ = 2 * (curve a t).2.2 ^ 2 := by
        rw [hxy]
        ring
  have hnorm :
      (curve a t).1 ^ 2 + (curve a t).2.1 ^ 2 +
          (curve a t).2.2 ^ 2 =
        2 * (curve a t).2.2 ^ 2 := by
    rw [hxy]
    ring
  have htan :
      ((curve a t).1 - (curve a t).2.1) ^ 2 +
            ((curve a t).1 + (curve a t).2.1) ^ 2 +
            (curve a t).2.2 ^ 2 =
        3 * (curve a t).2.2 ^ 2 := by
    calc
      ((curve a t).1 - (curve a t).2.1) ^ 2 +
            ((curve a t).1 + (curve a t).2.1) ^ 2 +
            (curve a t).2.2 ^ 2 =
          2 * ((curve a t).1 ^ 2 + (curve a t).2.1 ^ 2) +
            (curve a t).2.2 ^ 2 := by ring
      _ = 3 * (curve a t).2.2 ^ 2 := by
        rw [hxy]
        ring
  rw [hnum, hnorm, htan]

theorem gap9 (a t : ℝ) (ha : a ≠ 0) :
    2 * (curve a t).2.2 ^ 2 /
        (Real.sqrt (2 * (curve a t).2.2 ^ 2) *
          Real.sqrt (3 * (curve a t).2.2 ^ 2)) =
      2 / Real.sqrt 6 := by
  let z : ℝ := (curve a t).2.2
  change
    2 * z ^ 2 /
        (Real.sqrt (2 * z ^ 2) * Real.sqrt (3 * z ^ 2)) =
      2 / Real.sqrt 6
  have hz : z ≠ 0 := by
    dsimp [z, curve]
    exact mul_ne_zero ha (Real.exp_ne_zero t)
  have hzsq : 0 < z ^ 2 := by
    simpa [pow_two] using (mul_self_pos.mpr hz)
  let q : ℝ := Real.sqrt (z ^ 2)
  have hq0 : q ≠ 0 := by
    dsimp [q]
    exact Real.sqrt_ne_zero'.2 hzsq
  have hq : q ^ 2 = z ^ 2 := by
    dsimp [q]
    exact Real.sq_sqrt (le_of_lt hzsq)
  have hs2 : Real.sqrt (2 : ℝ) ≠ 0 :=
    Real.sqrt_ne_zero'.2 (by norm_num)
  have hs3 : Real.sqrt (3 : ℝ) ≠ 0 :=
    Real.sqrt_ne_zero'.2 (by norm_num)
  have hsqrt2 :
      Real.sqrt (2 * z ^ 2) = Real.sqrt 2 * q := by
    dsimp [q]
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hsqrt3 :
      Real.sqrt (3 * z ^ 2) = Real.sqrt 3 * q := by
    dsimp [q]
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
  have hsqrt : Real.sqrt 2 * Real.sqrt 3 = Real.sqrt 6 := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [hsqrt2, hsqrt3]
  rw [← hq]
  calc
    2 * q ^ 2 /
          ((Real.sqrt 2 * q) * (Real.sqrt 3 * q)) =
        2 / (Real.sqrt 2 * Real.sqrt 3) := by
      field_simp [hq0, hs2, hs3] <;> ring
    _ = 2 / Real.sqrt 6 := by rw [hsqrt]

theorem gap10 (a t : ℝ) (ha : a ≠ 0) :
    angleCos a t = 2 / Real.sqrt 6 := by
  rw [gap6 a t ha, gap7 a t ha, gap8 a t ha, gap9 a t ha]

theorem gap11 (a t : ℝ) (ha : a ≠ 0) :
    angleCos a t = 2 / Real.sqrt 6 := by
  exact gap10 a t ha

end

end ProofGap.Exercise3535
