import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3269

noncomputable section

def u (x y : ℝ) : ℝ :=
  x ^ 3 + y ^ 3 - 3 * x * y * (x - y)

def iterDeriv (n : ℕ) (g : ℝ → ℝ) : ℝ → ℝ :=
  (deriv^[n]) g

def thirdDirectional (x y dx dy : ℝ) : ℝ :=
  iterDeriv 3 (fun s => u (x + s * dx) (y + s * dy)) 0

def thirdForm (dx dy : ℝ) : ℝ :=
  6 * (dx ^ 3 + dy ^ 3 - 3 * dx ^ 2 * dy + 3 * dx * dy ^ 2)

theorem gap1 (x y dx dy : ℝ) :
    thirdDirectional x y dx dy = thirdForm dx dy := by
  let A : ℝ :=
    dx ^ 3 + dy ^ 3 - 3 * dx ^ 2 * dy + 3 * dx * dy ^ 2
  let B : ℝ :=
    3 * x * dx ^ 2 + 3 * y * dy ^ 2 - 3 * dx ^ 2 * y -
      6 * x * dx * dy + 3 * x * dy ^ 2 + 6 * dx * y * dy
  let C : ℝ :=
    3 * x ^ 2 * dx + 3 * y ^ 2 * dy - 3 * x ^ 2 * dy -
      6 * x * dx * y + 3 * dx * y ^ 2 + 6 * x * y * dy
  let D : ℝ := u x y
  have hpoly :
      (fun s : ℝ => u (x + s * dx) (y + s * dy)) =
        (fun s : ℝ => A * s ^ 3 + (B * s ^ 2 + (C * s + D))) := by
    funext s
    dsimp [A, B, C, D, u]
    ring
  have hp (s : ℝ) :
      HasDerivAt
        (fun t : ℝ => A * t ^ 3 + (B * t ^ 2 + (C * t + D)))
        (3 * A * s ^ 2 + (2 * B * s + C)) s := by
    convert
      ((((hasDerivAt_id s).mul (hasDerivAt_id s)).mul
          (hasDerivAt_id s)).const_mul A).add
        ((((hasDerivAt_id s).mul (hasDerivAt_id s)).const_mul B).add
          (((hasDerivAt_id s).const_mul C).add (hasDerivAt_const s D)))
      using 1
    · funext t
      simp [id] <;> ring
    · simp [id] <;> ring
  have hq (s : ℝ) :
      HasDerivAt
        (fun t : ℝ => 3 * A * t ^ 2 + (2 * B * t + C))
        (6 * A * s + 2 * B) s := by
    convert
      (((hasDerivAt_id s).mul (hasDerivAt_id s)).const_mul (3 * A)).add
        (((hasDerivAt_id s).const_mul (2 * B)).add
          (hasDerivAt_const s C))
      using 1
    · funext t
      simp [id] <;> ring_nf <;> simp
    · simp [id] <;> ring
  have hr (s : ℝ) :
      HasDerivAt (fun t : ℝ => 6 * A * t + 2 * B) (6 * A) s := by
    convert
      ((hasDerivAt_id s).const_mul (6 * A)).add
        (hasDerivAt_const s (2 * B))
      using 1 <;> ring
  have hd1 :
      deriv (fun t : ℝ => A * t ^ 3 + (B * t ^ 2 + (C * t + D))) =
        (fun t : ℝ => 3 * A * t ^ 2 + (2 * B * t + C)) := by
    funext s
    exact (hp s).deriv
  have hd2 :
      deriv (fun t : ℝ => 3 * A * t ^ 2 + (2 * B * t + C)) =
        (fun t : ℝ => 6 * A * t + 2 * B) := by
    funext s
    exact (hq s).deriv
  unfold thirdDirectional iterDeriv thirdForm
  rw [hpoly]
  change
    deriv
        (deriv
          (deriv
            (fun t : ℝ => A * t ^ 3 + (B * t ^ 2 + (C * t + D))))) 0 =
      6 * A
  rw [hd1, hd2]
  exact (hr 0).deriv

end

end ProofGap.Exercise3269
