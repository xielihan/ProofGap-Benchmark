import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3240

noncomputable section

def u (x y z : ℝ) : ℝ := x * y + y * z + z * x

def partialX (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => f t y z) x

def partialY (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => f x t z) y

def partialZ (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => f x y t) z

def partialXX (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => partialX f t y z) x

def partialXY (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => partialX f x t z) y

def partialXZ (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => partialX f x y t) z

def partialYY (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => partialY f x t z) y

def partialYZ (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => partialY f x y t) z

def partialZZ (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => partialZ f x y t) z

def differential (f : ℝ → ℝ → ℝ → ℝ)
    (x y z dx dy dz : ℝ) : ℝ :=
  partialX f x y z * dx + partialY f x y z * dy + partialZ f x y z * dz

def secondDifferential (f : ℝ → ℝ → ℝ → ℝ)
    (x y z dx dy dz : ℝ) : ℝ :=
  partialXX f x y z * dx ^ 2 +
    partialYY f x y z * dy ^ 2 +
    partialZZ f x y z * dz ^ 2 +
    2 * partialXY f x y z * dx * dy +
    2 * partialYZ f x y z * dy * dz +
    2 * partialXZ f x y z * dz * dx

private theorem deriv_affine (a b x : ℝ) :
    deriv (fun t : ℝ => a * t + b) x = a := by
  simpa using
    (((hasDerivAt_const x a).mul (hasDerivAt_id x)).add_const b).deriv

private theorem u_partialX (x y z : ℝ) :
    partialX u x y z = y + z := by
  unfold partialX
  have hfun : (fun t : ℝ => u t y z) =
      (fun t : ℝ => (y + z) * t + y * z) := by
    funext t
    unfold u
    ring
  rw [hfun]
  exact deriv_affine (y + z) (y * z) x

private theorem u_partialY (x y z : ℝ) :
    partialY u x y z = z + x := by
  unfold partialY
  have hfun : (fun t : ℝ => u x t z) =
      (fun t : ℝ => (z + x) * t + z * x) := by
    funext t
    unfold u
    ring
  rw [hfun]
  exact deriv_affine (z + x) (z * x) y

private theorem u_partialZ (x y z : ℝ) :
    partialZ u x y z = x + y := by
  unfold partialZ
  have hfun : (fun t : ℝ => u x y t) =
      (fun t : ℝ => (x + y) * t + x * y) := by
    funext t
    unfold u
    ring
  rw [hfun]
  exact deriv_affine (x + y) (x * y) z

theorem gap1 (x y z dx dy dz : ℝ) :
    differential u x y z dx dy dz =
      (y + z) * dx + (z + x) * dy + (x + y) * dz := by
  rw [differential, u_partialX, u_partialY, u_partialZ]

theorem gap2 (x y z dx dy dz : ℝ) :
    secondDifferential u x y z dx dy dz =
      2 * (dx * dy + dy * dz + dz * dx) := by
  have hxx : partialXX u x y z = 0 := by
    unfold partialXX
    have hfun : (fun t : ℝ => partialX u t y z) = (fun _ : ℝ => y + z) := by
      funext t
      rw [u_partialX]
    rw [hfun]
    simpa using (hasDerivAt_const x (y + z)).deriv
  have hyy : partialYY u x y z = 0 := by
    unfold partialYY
    have hfun : (fun t : ℝ => partialY u x t z) = (fun _ : ℝ => z + x) := by
      funext t
      rw [u_partialY]
    rw [hfun]
    simpa using (hasDerivAt_const y (z + x)).deriv
  have hzz : partialZZ u x y z = 0 := by
    unfold partialZZ
    have hfun : (fun t : ℝ => partialZ u x y t) = (fun _ : ℝ => x + y) := by
      funext t
      rw [u_partialZ]
    rw [hfun]
    simpa using (hasDerivAt_const z (x + y)).deriv
  have hxy : partialXY u x y z = 1 := by
    unfold partialXY
    have hfun : (fun t : ℝ => partialX u x t z) = (fun t : ℝ => 1 * t + z) := by
      funext t
      rw [u_partialX]
      ring
    rw [hfun]
    exact deriv_affine 1 z y
  have hyz : partialYZ u x y z = 1 := by
    unfold partialYZ
    have hfun : (fun t : ℝ => partialY u x y t) = (fun t : ℝ => 1 * t + x) := by
      funext t
      rw [u_partialY]
      ring
    rw [hfun]
    exact deriv_affine 1 x z
  have hxz : partialXZ u x y z = 1 := by
    unfold partialXZ
    have hfun : (fun t : ℝ => partialX u x y t) = (fun t : ℝ => 1 * t + y) := by
      funext t
      rw [u_partialX]
      ring
    rw [hfun]
    exact deriv_affine 1 y z
  rw [secondDifferential, hxx, hyy, hzz, hxy, hyz, hxz]
  ring

end

end ProofGap.Exercise3240
