import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Calculus.Deriv.Inv

namespace ProofGap.Exercise3544

noncomputable section

structure Point3 where
  x : ℝ
  y : ℝ
  z : ℝ

def levelFunction (p : Point3) : ℝ :=
  Real.rpow 2 (p.x / p.z) + Real.rpow 2 (p.y / p.z) - 8

def surface : Set Point3 :=
  {p | Real.rpow 2 (p.x / p.z) + Real.rpow 2 (p.y / p.z) = 8}

def basePoint : Point3 := ⟨2, 2, 1⟩

def normalVector (p : Point3) : Point3 :=
  ⟨deriv (fun t => levelFunction ⟨t, p.y, p.z⟩) p.x,
    deriv (fun t => levelFunction ⟨p.x, t, p.z⟩) p.y,
    deriv (fun t => levelFunction ⟨p.x, p.y, t⟩) p.z⟩

def gradientFormula (p : Point3) : Point3 :=
  ⟨(1 / p.z) * Real.rpow 2 (p.x / p.z) * Real.log 2,
    (1 / p.z) * Real.rpow 2 (p.y / p.z) * Real.log 2,
    (p.x * Real.rpow 2 (p.x / p.z) +
        p.y * Real.rpow 2 (p.y / p.z)) *
      (-(1 / p.z ^ 2)) * Real.log 2⟩

def scaledNormalAtBase : Point3 :=
  ⟨4 * Real.log 2, 4 * Real.log 2, -16 * Real.log 2⟩

def tangentPlaneAt (p n : Point3) : Set Point3 :=
  {q | n.x * (q.x - p.x) + n.y * (q.y - p.y) +
    n.z * (q.z - p.z) = 0}

def rawTangentPlane : Set Point3 :=
  {p | p.x - 2 + (p.y - 2) - 4 * (p.z - 1) = 0}

def simplifiedTangentPlane : Set Point3 :=
  {p | p.x + p.y - 4 * p.z = 0}

def normalLine : Set Point3 :=
  {p | ∃ t : ℝ, p = ⟨2 + t, 2 + t, 1 - 4 * t⟩}

private theorem Point3.ext {p q : Point3}
    (hx : p.x = q.x) (hy : p.y = q.y) (hz : p.z = q.z) : p = q := by
  cases p with
  | mk px py pz =>
    cases q with
    | mk qx qy qz =>
      cases hx
      cases hy
      cases hz
      rfl

theorem gap1 :
    ∀ x y z : ℝ, z ≠ 0 →
      normalVector ⟨x, y, z⟩ = gradientFormula ⟨x, y, z⟩ := by
  intro x y z hz
  have htwo : (0 : ℝ) < 2 := by norm_num
  have hrpow (u : ℝ) :
      Real.rpow 2 u = Real.exp (Real.log 2 * u) := by
    change (2 : ℝ) ^ u = Real.exp (Real.log 2 * u)
    exact (Real.rpow_def_of_pos htwo) u
  have rpow_deriv {f : ℝ → ℝ} {a f' : ℝ}
      (hf : HasDerivAt f f' a) :
      HasDerivAt (fun t => Real.rpow 2 (f t))
        (Real.rpow 2 (f a) * (Real.log 2 * f')) a := by
    have hinner :
        HasDerivAt (fun t => Real.log 2 * f t)
          (Real.log 2 * f') a :=
      hf.const_mul (Real.log 2)
    have hexp :
        HasDerivAt (fun t => Real.exp (Real.log 2 * f t))
          (Real.exp (Real.log 2 * f a) * (Real.log 2 * f')) a := by
      simpa only [Function.comp_apply] using
        ((Real.hasDerivAt_exp (Real.log 2 * f a)).comp a hinner)
    simpa only [hrpow] using hexp
  apply Point3.ext
  · change
      deriv
          (fun t : ℝ =>
            Real.rpow 2 (t / z) + Real.rpow 2 (y / z) - 8)
          x =
        (1 / z) * Real.rpow 2 (x / z) * Real.log 2
    have hlinear :
        HasDerivAt (fun t : ℝ => t / z) (1 / z) x := by
      simpa using (hasDerivAt_id x).div_const z
    have hconst :
        HasDerivAt (fun _ : ℝ => Real.rpow 2 (y / z)) 0 x :=
      hasDerivAt_const x (Real.rpow 2 (y / z))
    have hfull :
        HasDerivAt
          (fun t : ℝ =>
            Real.rpow 2 (t / z) + Real.rpow 2 (y / z) - 8)
          (Real.rpow 2 (x / z) * (Real.log 2 * (1 / z))) x := by
      simpa using ((rpow_deriv hlinear).add hconst).sub_const 8
    rw [hfull.deriv]
    ring
  · change
      deriv
          (fun t : ℝ =>
            Real.rpow 2 (x / z) + Real.rpow 2 (t / z) - 8)
          y =
        (1 / z) * Real.rpow 2 (y / z) * Real.log 2
    have hlinear :
        HasDerivAt (fun t : ℝ => t / z) (1 / z) y := by
      simpa using (hasDerivAt_id y).div_const z
    have hconst :
        HasDerivAt (fun _ : ℝ => Real.rpow 2 (x / z)) 0 y :=
      hasDerivAt_const y (Real.rpow 2 (x / z))
    have hfull :
        HasDerivAt
          (fun t : ℝ =>
            Real.rpow 2 (x / z) + Real.rpow 2 (t / z) - 8)
          (Real.rpow 2 (y / z) * (Real.log 2 * (1 / z))) y := by
      simpa using (hconst.add (rpow_deriv hlinear)).sub_const 8
    rw [hfull.deriv]
    ring
  · change
      deriv
          (fun t : ℝ =>
            Real.rpow 2 (x / t) + Real.rpow 2 (y / t) - 8)
          z =
        (x * Real.rpow 2 (x / z) + y * Real.rpow 2 (y / z)) *
          (-(1 / z ^ 2)) * Real.log 2
    have hxquot :
        HasDerivAt (fun t : ℝ => x / t) (-x / z ^ 2) z := by
      simpa using
        (hasDerivAt_const z x).div (hasDerivAt_id z) hz
    have hyquot :
        HasDerivAt (fun t : ℝ => y / t) (-y / z ^ 2) z := by
      simpa using
        (hasDerivAt_const z y).div (hasDerivAt_id z) hz
    have hfull :
        HasDerivAt
          (fun t : ℝ =>
            Real.rpow 2 (x / t) + Real.rpow 2 (y / t) - 8)
          (Real.rpow 2 (x / z) * (Real.log 2 * (-x / z ^ 2)) +
            Real.rpow 2 (y / z) * (Real.log 2 * (-y / z ^ 2))) z := by
      simpa using
        ((rpow_deriv hxquot).add (rpow_deriv hyquot)).sub_const 8
    rw [hfull.deriv]
    ring

theorem gap2 :
    gradientFormula basePoint = scaledNormalAtBase := by
  have hpow : Real.rpow (2 : ℝ) (2 : ℝ) = 4 := by
    norm_num [Real.rpow_natCast]
  apply Point3.ext <;>
    norm_num [gradientFormula, basePoint, scaledNormalAtBase, hpow] <;>
    ring

theorem gap3
    (hGradient : normalVector basePoint = gradientFormula basePoint)
    (hEvaluation : gradientFormula basePoint = scaledNormalAtBase) :
    normalVector basePoint = scaledNormalAtBase := by
  exact hGradient.trans hEvaluation

theorem gap4
    (hNormal : normalVector basePoint = scaledNormalAtBase) :
    tangentPlaneAt basePoint (normalVector basePoint) = rawTangentPlane := by
  apply Set.ext
  intro q
  rw [hNormal]
  change
    (4 * Real.log 2) * (q.x - 2) +
          (4 * Real.log 2) * (q.y - 2) +
          (-16 * Real.log 2) * (q.z - 1) = 0 ↔
      q.x - 2 + (q.y - 2) - 4 * (q.z - 1) = 0
  have hlog : Real.log (2 : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  constructor
  · intro h
    have hfactor :
        (4 * Real.log 2) *
            (q.x - 2 + (q.y - 2) - 4 * (q.z - 1)) = 0 := by
      calc
        (4 * Real.log 2) *
              (q.x - 2 + (q.y - 2) - 4 * (q.z - 1)) =
            (4 * Real.log 2) * (q.x - 2) +
              (4 * Real.log 2) * (q.y - 2) +
              (-16 * Real.log 2) * (q.z - 1) := by ring
        _ = 0 := h
    exact (mul_eq_zero.mp hfactor).resolve_left
      (mul_ne_zero (by norm_num : (4 : ℝ) ≠ 0) hlog)
  · intro h
    calc
      (4 * Real.log 2) * (q.x - 2) +
            (4 * Real.log 2) * (q.y - 2) +
            (-16 * Real.log 2) * (q.z - 1) =
          (4 * Real.log 2) *
            (q.x - 2 + (q.y - 2) - 4 * (q.z - 1)) := by ring
      _ = 0 := mul_eq_zero.mpr (Or.inr h)

theorem gap5 :
    rawTangentPlane = simplifiedTangentPlane := by
  apply Set.ext
  intro p
  change
    p.x - 2 + (p.y - 2) - 4 * (p.z - 1) = 0 ↔
      p.x + p.y - 4 * p.z = 0
  have hidentity :
      p.x - 2 + (p.y - 2) - 4 * (p.z - 1) =
        p.x + p.y - 4 * p.z := by
    ring
  rw [hidentity]

theorem gap6
    (hRaw :
      tangentPlaneAt basePoint (normalVector basePoint) = rawTangentPlane)
    (hSimplify : rawTangentPlane = simplifiedTangentPlane) :
    tangentPlaneAt basePoint (normalVector basePoint) =
      simplifiedTangentPlane := by
  exact hRaw.trans hSimplify

theorem gap7 :
    normalLine =
      {p | (p.x - 2) / 1 = (p.y - 2) / 1 ∧
        (p.y - 2) / 1 = (p.z - 1) / (-4)} := by
  apply Set.ext
  intro p
  change
    (∃ t : ℝ, p = ⟨2 + t, 2 + t, 1 - 4 * t⟩) ↔
      (p.x - 2) / 1 = (p.y - 2) / 1 ∧
        (p.y - 2) / 1 = (p.z - 1) / (-4)
  constructor
  · intro h
    rcases h with ⟨t, rfl⟩
    constructor <;> ring
  · intro h
    rcases h with ⟨hxy, hyz⟩
    norm_num at hxy hyz
    refine ⟨p.y - 2, ?_⟩
    refine Point3.ext ?_ ?_ ?_
    · change p.x = 2 + (p.y - 2)
      linarith
    · change p.y = 2 + (p.y - 2)
      ring
    · change p.z = 1 - 4 * (p.y - 2)
      linarith

end

end ProofGap.Exercise3544
