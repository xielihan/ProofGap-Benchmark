import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise3554

noncomputable section

structure Point3 where
  x : ℝ
  y : ℝ
  z : ℝ

def graphFunction (f : ℝ → ℝ) (x y : ℝ) : ℝ :=
  x * f (y / x)

def graphSurface (f : ℝ → ℝ) : Set Point3 :=
  {p | p.x ≠ 0 ∧ p.z = graphFunction f p.x p.y}

def partialX (f : ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => graphFunction f t y) x

def partialY (f : ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => graphFunction f x t) y

def tangentPlaneAt (f : ℝ → ℝ) (p : Point3) : Set Point3 :=
  {q | q.z - p.z =
    partialX f p.x p.y * (q.x - p.x) +
      partialY f p.x p.y * (q.y - p.y)}

def homogeneousTangentPlane (f : ℝ → ℝ) (p : Point3) : Set Point3 :=
  {q | q.z =
    (f (p.y / p.x) - (p.y / p.x) * deriv f (p.y / p.x)) * q.x +
      deriv f (p.y / p.x) * q.y}

def origin : Point3 := ⟨0, 0, 0⟩

theorem gap1 (f : ℝ → ℝ) (hf : Differentiable ℝ f) :
    ∀ x y : ℝ, x ≠ 0 →
      partialX f x y =
        f (y / x) - (y / x) * deriv f (y / x) := by
  intro x y hx
  unfold partialX graphFunction
  have hquot :=
    (hasDerivAt_const x y).div (hasDerivAt_id x) hx
  have hchain :=
    (hf (y / x)).hasDerivAt.comp x hquot
  have hprod := (hasDerivAt_id x).mul hchain
  have hprod' :
      HasDerivAt (fun t : ℝ => t * f (y / t))
        (1 * f (y / x) +
          x * (deriv f (y / x) * ((0 * x - y * 1) / x ^ 2))) x := by
    simpa using hprod
  calc
    deriv (fun t : ℝ => t * f (y / t)) x =
        1 * f (y / x) +
          x * (deriv f (y / x) * ((0 * x - y * 1) / x ^ 2)) :=
      hprod'.deriv
    _ = f (y / x) - (y / x) * deriv f (y / x) := by
      field_simp [hx]
      ring

theorem gap2 (f : ℝ → ℝ) (hf : Differentiable ℝ f) :
    ∀ x y : ℝ, x ≠ 0 →
      partialY f x y = deriv f (y / x) := by
  intro x y hx
  unfold partialY graphFunction
  have hquot :=
    (hasDerivAt_id y).div (hasDerivAt_const y x) hx
  have hchain :=
    (hf (y / x)).hasDerivAt.comp y hquot
  have hprod := (hasDerivAt_const y x).mul hchain
  have hprod' :
      HasDerivAt (fun t : ℝ => x * f (t / x))
        (0 * f (y / x) +
          x * (deriv f (y / x) * ((1 * x - y * 0) / x ^ 2))) y := by
    simpa using hprod
  calc
    deriv (fun t : ℝ => x * f (t / x)) y =
        0 * f (y / x) +
          x * (deriv f (y / x) * ((1 * x - y * 0) / x ^ 2)) :=
      hprod'.deriv
    _ = deriv f (y / x) := by
      field_simp [hx]
      ring

theorem gap3 (f : ℝ → ℝ) (hf : Differentiable ℝ f) :
    ∀ p : Point3, p ∈ graphSurface f →
      tangentPlaneAt f p =
        {q | q.z - p.z =
          (f (p.y / p.x) -
              (p.y / p.x) * deriv f (p.y / p.x)) *
              (q.x - p.x) +
            deriv f (p.y / p.x) * (q.y - p.y)} := by
  intro p hp
  have hpx : p.x ≠ 0 := hp.1
  apply Set.ext
  intro q
  change
    (q.z - p.z =
      partialX f p.x p.y * (q.x - p.x) +
        partialY f p.x p.y * (q.y - p.y)) ↔
    (q.z - p.z =
      (f (p.y / p.x) -
          (p.y / p.x) * deriv f (p.y / p.x)) *
          (q.x - p.x) +
        deriv f (p.y / p.x) * (q.y - p.y))
  rw [gap1 f hf p.x p.y hpx, gap2 f hf p.x p.y hpx]

theorem gap4 (f : ℝ → ℝ) (hf : Differentiable ℝ f) :
    ∀ p : Point3, p ∈ graphSurface f →
      tangentPlaneAt f p = homogeneousTangentPlane f p := by
  intro p hp
  have hpx : p.x ≠ 0 := hp.1
  have hpz : p.z = p.x * f (p.y / p.x) := by
    simpa [graphFunction] using hp.2
  have hbase :
      (f (p.y / p.x) -
          (p.y / p.x) * deriv f (p.y / p.x)) * p.x +
        deriv f (p.y / p.x) * p.y = p.z := by
    rw [hpz]
    field_simp [hpx] <;> ring
  rw [gap3 f hf p hp]
  apply Set.ext
  intro q
  change
    (q.z - p.z =
      (f (p.y / p.x) -
          (p.y / p.x) * deriv f (p.y / p.x)) *
          (q.x - p.x) +
        deriv f (p.y / p.x) * (q.y - p.y)) ↔
    (q.z =
      (f (p.y / p.x) -
          (p.y / p.x) * deriv f (p.y / p.x)) * q.x +
        deriv f (p.y / p.x) * q.y)
  constructor
  · intro h
    calc
      q.z = (q.z - p.z) + p.z := by ring
      _ =
          ((f (p.y / p.x) -
              (p.y / p.x) * deriv f (p.y / p.x)) *
              (q.x - p.x) +
            deriv f (p.y / p.x) * (q.y - p.y)) + p.z := by
              rw [h]
      _ =
          ((f (p.y / p.x) -
              (p.y / p.x) * deriv f (p.y / p.x)) *
              (q.x - p.x) +
            deriv f (p.y / p.x) * (q.y - p.y)) +
          ((f (p.y / p.x) -
              (p.y / p.x) * deriv f (p.y / p.x)) * p.x +
            deriv f (p.y / p.x) * p.y) := by
              rw [hbase]
      _ =
          (f (p.y / p.x) -
              (p.y / p.x) * deriv f (p.y / p.x)) * q.x +
            deriv f (p.y / p.x) * q.y := by ring
  · intro h
    calc
      q.z - p.z =
          ((f (p.y / p.x) -
              (p.y / p.x) * deriv f (p.y / p.x)) * q.x +
            deriv f (p.y / p.x) * q.y) -
          ((f (p.y / p.x) -
              (p.y / p.x) * deriv f (p.y / p.x)) * p.x +
            deriv f (p.y / p.x) * p.y) := by
              rw [h, hbase]
      _ =
          (f (p.y / p.x) -
              (p.y / p.x) * deriv f (p.y / p.x)) *
              (q.x - p.x) +
            deriv f (p.y / p.x) * (q.y - p.y) := by ring

theorem gap5 (f : ℝ → ℝ) (p : Point3)
    (hp : p ∈ graphSurface f) :
    origin ∈ homogeneousTangentPlane f p := by
  simp [origin, homogeneousTangentPlane]

theorem gap6 (f : ℝ → ℝ) (hf : Differentiable ℝ f) :
    ∀ p : Point3, p ∈ graphSurface f →
      origin ∈ tangentPlaneAt f p := by
  intro p hp
  rw [gap4 f hf p hp]
  exact gap5 f p hp

end

end ProofGap.Exercise3554
