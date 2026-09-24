import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3553

noncomputable section

structure Point3 where
  x : ℝ
  y : ℝ
  z : ℝ

def surface (a : ℝ) : Set Point3 :=
  {p | Real.sqrt p.x + Real.sqrt p.y + Real.sqrt p.z = Real.sqrt a}

def positiveSurfacePoint (a : ℝ) (p : Point3) : Prop :=
  0 < p.x ∧ 0 < p.y ∧ 0 < p.z ∧ p ∈ surface a

def tangentPlaneAt (p : Point3) : Set Point3 :=
  {q | (1 / (2 * Real.sqrt p.x)) * (q.x - p.x) +
      (1 / (2 * Real.sqrt p.y)) * (q.y - p.y) +
      (1 / (2 * Real.sqrt p.z)) * (q.z - p.z) = 0}

def scaledTangentPlaneAt (p : Point3) : Set Point3 :=
  {q | Real.sqrt (p.y * p.z) * (q.x - p.x) +
      Real.sqrt (p.x * p.z) * (q.y - p.y) +
      Real.sqrt (p.x * p.y) * (q.z - p.z) = 0}

def xInterceptCoordinate (a : ℝ) (p : Point3) : ℝ :=
  Real.sqrt (a * p.x)

def yInterceptCoordinate (a : ℝ) (p : Point3) : ℝ :=
  Real.sqrt (a * p.y)

def zInterceptCoordinate (a : ℝ) (p : Point3) : ℝ :=
  Real.sqrt (a * p.z)

theorem gap1 (a : ℝ) (ha : 0 < a) :
    ∀ p : Point3, positiveSurfacePoint a p →
      tangentPlaneAt p =
        {q | (1 / (2 * Real.sqrt p.x)) * (q.x - p.x) +
            (1 / (2 * Real.sqrt p.y)) * (q.y - p.y) +
            (1 / (2 * Real.sqrt p.z)) * (q.z - p.z) = 0} := by
  intro p hp
  rfl

theorem gap2 (a : ℝ) (ha : 0 < a) :
    ∀ p : Point3, positiveSurfacePoint a p →
      tangentPlaneAt p = scaledTangentPlaneAt p := by
  intro p hp
  rcases hp with ⟨hpx, hpy, hpz, hsurface⟩
  have hsx : 0 < Real.sqrt p.x := Real.sqrt_pos.2 hpx
  have hsy : 0 < Real.sqrt p.y := Real.sqrt_pos.2 hpy
  have hsz : 0 < Real.sqrt p.z := Real.sqrt_pos.2 hpz
  apply Set.ext
  intro q
  change
    (1 / (2 * Real.sqrt p.x) * (q.x - p.x) +
          1 / (2 * Real.sqrt p.y) * (q.y - p.y) +
          1 / (2 * Real.sqrt p.z) * (q.z - p.z) = 0) ↔
      (Real.sqrt (p.y * p.z) * (q.x - p.x) +
          Real.sqrt (p.x * p.z) * (q.y - p.y) +
          Real.sqrt (p.x * p.y) * (q.z - p.z) = 0)
  simp only [Real.sqrt_mul (le_of_lt hpy),
    Real.sqrt_mul (le_of_lt hpx)]
  let K : ℝ :=
    2 * Real.sqrt p.x * Real.sqrt p.y * Real.sqrt p.z
  have hK : K ≠ 0 := by
    dsimp [K]
    exact mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero (by norm_num) (ne_of_gt hsx))
        (ne_of_gt hsy))
      (ne_of_gt hsz)
  have hxcoef :
      K * (1 / (2 * Real.sqrt p.x)) =
        Real.sqrt p.y * Real.sqrt p.z := by
    dsimp [K]
    field_simp [ne_of_gt hsx, ne_of_gt hsy, ne_of_gt hsz] <;> ring
  have hycoef :
      K * (1 / (2 * Real.sqrt p.y)) =
        Real.sqrt p.x * Real.sqrt p.z := by
    dsimp [K]
    field_simp [ne_of_gt hsx, ne_of_gt hsy, ne_of_gt hsz] <;> ring
  have hzcoef :
      K * (1 / (2 * Real.sqrt p.z)) =
        Real.sqrt p.x * Real.sqrt p.y := by
    dsimp [K]
    field_simp [ne_of_gt hsx, ne_of_gt hsy, ne_of_gt hsz] <;> ring
  have hscale :
      K *
          (1 / (2 * Real.sqrt p.x) * (q.x - p.x) +
            1 / (2 * Real.sqrt p.y) * (q.y - p.y) +
            1 / (2 * Real.sqrt p.z) * (q.z - p.z)) =
        Real.sqrt p.y * Real.sqrt p.z * (q.x - p.x) +
          Real.sqrt p.x * Real.sqrt p.z * (q.y - p.y) +
          Real.sqrt p.x * Real.sqrt p.y * (q.z - p.z) := by
    calc
      _ =
          (K * (1 / (2 * Real.sqrt p.x))) * (q.x - p.x) +
            (K * (1 / (2 * Real.sqrt p.y))) * (q.y - p.y) +
            (K * (1 / (2 * Real.sqrt p.z))) * (q.z - p.z) := by
              ring
      _ = _ := by rw [hxcoef, hycoef, hzcoef]
  constructor
  · intro ht
    have hs := hscale
    rw [ht] at hs
    simpa only [mul_zero] using hs.symm
  · intro hs
    have hz :
        K *
            (1 / (2 * Real.sqrt p.x) * (q.x - p.x) +
              1 / (2 * Real.sqrt p.y) * (q.y - p.y) +
              1 / (2 * Real.sqrt p.z) * (q.z - p.z)) = 0 :=
      hscale.trans hs
    exact (mul_eq_zero.mp hz).resolve_left hK

theorem gap3 (a : ℝ) (p : Point3)
    (ha : 0 < a) (hp : positiveSurfacePoint a p) :
    xInterceptCoordinate a p = Real.sqrt (a * p.x) := by
  rfl

theorem gap4 (a : ℝ) (p : Point3)
    (ha : 0 < a) (hp : positiveSurfacePoint a p) :
    yInterceptCoordinate a p = Real.sqrt (a * p.y) := by
  rfl

theorem gap5 (a : ℝ) (p : Point3)
    (ha : 0 < a) (hp : positiveSurfacePoint a p) :
    zInterceptCoordinate a p = Real.sqrt (a * p.z) := by
  rfl

theorem gap6 (a : ℝ) (p : Point3)
    (ha : 0 < a) (hp : positiveSurfacePoint a p) :
    xInterceptCoordinate a p + yInterceptCoordinate a p +
        zInterceptCoordinate a p =
      Real.sqrt a *
        (Real.sqrt p.x + Real.sqrt p.y + Real.sqrt p.z) := by
  change
    Real.sqrt (a * p.x) + Real.sqrt (a * p.y) + Real.sqrt (a * p.z) =
      Real.sqrt a *
        (Real.sqrt p.x + Real.sqrt p.y + Real.sqrt p.z)
  simp only [Real.sqrt_mul (le_of_lt ha)]
  ring

theorem gap7 (a : ℝ) (p : Point3)
    (ha : 0 < a) (hp : positiveSurfacePoint a p) :
    Real.sqrt a *
        (Real.sqrt p.x + Real.sqrt p.y + Real.sqrt p.z) =
      Real.sqrt a * Real.sqrt a := by
  have hs := hp.2.2.2
  change
    Real.sqrt p.x + Real.sqrt p.y + Real.sqrt p.z = Real.sqrt a at hs
  exact congrArg (fun t : ℝ => Real.sqrt a * t) hs

theorem gap8 (a : ℝ) (p : Point3)
    (ha : 0 < a) (hp : positiveSurfacePoint a p) :
    Real.sqrt a * Real.sqrt a = a := by
  simpa [pow_two] using Real.sq_sqrt (le_of_lt ha)

theorem gap9 (a : ℝ) (p : Point3)
    (ha : 0 < a) (hp : positiveSurfacePoint a p) :
    xInterceptCoordinate a p + yInterceptCoordinate a p +
      zInterceptCoordinate a p = a := by
  calc
    xInterceptCoordinate a p + yInterceptCoordinate a p +
          zInterceptCoordinate a p =
        Real.sqrt a *
          (Real.sqrt p.x + Real.sqrt p.y + Real.sqrt p.z) :=
      gap6 a p ha hp
    _ = Real.sqrt a * Real.sqrt a := gap7 a p ha hp
    _ = a := gap8 a p ha hp

theorem gap10 (a : ℝ) (ha : 0 < a) :
    ∀ p : Point3, positiveSurfacePoint a p →
      xInterceptCoordinate a p + yInterceptCoordinate a p +
        zInterceptCoordinate a p = a := by
  intro p hp
  exact gap9 a p ha hp

end

end ProofGap.Exercise3553
