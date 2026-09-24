import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise4403

noncomputable section

abbrev Vec3 := ℝ × ℝ × ℝ

def radius (center p : Vec3) : ℝ :=
  Real.sqrt ((p.1 - center.1) ^ 2 +
    (p.2.1 - center.2.1) ^ 2 +
    (p.2.2 - center.2.2) ^ 2)

def u (center p : Vec3) : ℝ :=
  Real.log (1 / radius center p)

def gradient (center p : Vec3) : Vec3 :=
  (-(p.1 - center.1) / radius center p ^ 2,
    -(p.2.1 - center.2.1) / radius center p ^ 2,
    -(p.2.2 - center.2.2) / radius center p ^ 2)

def norm3 (v : Vec3) : ℝ :=
  Real.sqrt (v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2)

def unitSphere (center : Vec3) : Set Vec3 :=
  {p | radius center p = 1}

private theorem hasDerivAt_log_inv_sqrt_quad
    (a b c x : ℝ)
    (h : Real.sqrt ((x - a) ^ 2 + b ^ 2 + c ^ 2) ≠ 0) :
    HasDerivAt
      (fun t : ℝ => Real.log
        (1 / Real.sqrt ((t - a) ^ 2 + b ^ 2 + c ^ 2)))
      (-(x - a) / Real.sqrt ((x - a) ^ 2 + b ^ 2 + c ^ 2) ^ 2) x := by
  have hS : (x - a) ^ 2 + b ^ 2 + c ^ 2 ≠ 0 := by
    intro hS
    apply h
    simp [hS]
  have hquad :
      HasDerivAt (fun t : ℝ => (t - a) ^ 2 + b ^ 2 + c ^ 2)
        (2 * (x - a)) x := by
    convert
      ((((hasDerivAt_id x).sub_const a).pow 2).add_const (b ^ 2)).add_const
        (c ^ 2) using 1 <;> simp [id] <;> ring
  have hsqrt := (Real.hasDerivAt_sqrt hS).comp x hquad
  have hlog := (Real.hasDerivAt_log h).comp x hsqrt
  have heq :
      (fun t : ℝ => Real.log
        (1 / Real.sqrt ((t - a) ^ 2 + b ^ 2 + c ^ 2))) =
      (fun t : ℝ => -Real.log
        (Real.sqrt ((t - a) ^ 2 + b ^ 2 + c ^ 2))) := by
    funext t
    rw [one_div, Real.log_inv]
  rw [heq]
  convert hlog.neg using 1 <;> field_simp [h] <;> ring

theorem gap1 (center p : Vec3) (h : radius center p ≠ 0) :
    HasDerivAt
      (fun x => u center (x, p.2.1, p.2.2))
      (-(p.1 - center.1) / radius center p ^ 2) p.1 := by
  simpa [u, radius] using
    (hasDerivAt_log_inv_sqrt_quad center.1
      (p.2.1 - center.2.1) (p.2.2 - center.2.2) p.1 h)

theorem gap2 (center p : Vec3) (h : radius center p ≠ 0) :
    HasDerivAt
      (fun y => u center (p.1, y, p.2.2))
      (-(p.2.1 - center.2.1) / radius center p ^ 2) p.2.1 := by
  have h' :
      Real.sqrt
          ((p.2.1 - center.2.1) ^ 2 +
            (p.1 - center.1) ^ 2 +
            (p.2.2 - center.2.2) ^ 2) ≠ 0 := by
    simpa [radius, add_comm, add_left_comm, add_assoc] using h
  simpa [u, radius, add_comm, add_left_comm, add_assoc] using
    (hasDerivAt_log_inv_sqrt_quad center.2.1
      (p.1 - center.1) (p.2.2 - center.2.2) p.2.1 h')

theorem gap3 (center p : Vec3) (h : radius center p ≠ 0) :
    HasDerivAt
      (fun z => u center (p.1, p.2.1, z))
      (-(p.2.2 - center.2.2) / radius center p ^ 2) p.2.2 := by
  have h' :
      Real.sqrt
          ((p.2.2 - center.2.2) ^ 2 +
            (p.1 - center.1) ^ 2 +
            (p.2.1 - center.2.1) ^ 2) ≠ 0 := by
    simpa [radius, add_comm, add_left_comm, add_assoc] using h
  simpa [u, radius, add_comm, add_left_comm, add_assoc] using
    (hasDerivAt_log_inv_sqrt_quad center.2.2
      (p.1 - center.1) (p.2.1 - center.2.1) p.2.2 h')

theorem gap4 (center p : Vec3) (h : radius center p ≠ 0) :
    norm3 (gradient center p) =
      Real.sqrt
        (1 / radius center p ^ 4 *
          ((p.1 - center.1) ^ 2 +
            (p.2.1 - center.2.1) ^ 2 +
            (p.2.2 - center.2.2) ^ 2)) := by
  unfold norm3 gradient
  apply congrArg Real.sqrt
  field_simp [h] <;> ring

theorem gap5 (center p : Vec3) (h : radius center p ≠ 0) :
    Real.sqrt
        (1 / radius center p ^ 4 *
          ((p.1 - center.1) ^ 2 +
            (p.2.1 - center.2.1) ^ 2 +
            (p.2.2 - center.2.2) ^ 2)) =
      1 / radius center p := by
  have hs :
      0 ≤ (p.1 - center.1) ^ 2 +
        (p.2.1 - center.2.1) ^ 2 +
        (p.2.2 - center.2.2) ^ 2 := by
    positivity
  have hrnonneg : 0 ≤ radius center p := by
    unfold radius
    exact Real.sqrt_nonneg _
  have hr2 :
      radius center p ^ 2 =
        (p.1 - center.1) ^ 2 +
          (p.2.1 - center.2.1) ^ 2 +
          (p.2.2 - center.2.2) ^ 2 := by
    unfold radius
    exact Real.sq_sqrt hs
  rw [← hr2]
  have halg :
      1 / radius center p ^ 4 * radius center p ^ 2 =
        (1 / radius center p) ^ 2 := by
    field_simp [h] <;> ring
  rw [halg, Real.sqrt_sq_eq_abs,
    abs_of_nonneg (one_div_nonneg.mpr hrnonneg)]

theorem gap6 (center p : Vec3) (h : radius center p ≠ 0) :
    norm3 (gradient center p) = 1 / radius center p := by
  exact (gap4 center p h).trans (gap5 center p h)

theorem gap7 (center p : Vec3) (h : radius center p = 1) :
    norm3 (gradient center p) = 1 := by
  have hn : radius center p ≠ 0 := by
    rw [h]
    exact one_ne_zero
  simpa [h] using gap6 center p hn

theorem gap8 (center p : Vec3) (h : p ∈ unitSphere center) :
    norm3 (gradient center p) = 1 := by
  apply gap7 center p
  simpa [unitSphere] using h

theorem gap9 (center p : Vec3) :
    p ∈ unitSphere center ↔ norm3 (gradient center p) = 1 := by
  constructor
  · intro hp
    exact gap8 center p hp
  · intro hn
    change radius center p = 1
    by_cases hr : radius center p = 0
    · have hz : norm3 (gradient center p) = 0 := by
        simp [norm3, gradient, hr]
      linarith
    · have hone : 1 / radius center p = 1 :=
        (gap6 center p hr).symm.trans hn
      calc
        radius center p = 1 * radius center p := by ring
        _ = (1 / radius center p) * radius center p := by rw [hone]
        _ = 1 := by field_simp [hr]

end

end ProofGap.Exercise4403
