import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

namespace ProofGap.Exercise3292

noncomputable section

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  (deriv^[n]) f

def nthDifferential (n : ℕ) (u : ℝ → ℝ → ℝ → ℝ)
    (x y z dx dy dz : ℝ) : ℝ :=
  iterDeriv n
    (fun s => u (x + s * dx) (y + s * dy) (z + s * dz)) 0

def radiusSq (x y z : ℝ) : ℝ :=
  x ^ 2 + y ^ 2 + z ^ 2

def radialPairing (x y z dx dy dz : ℝ) : ℝ :=
  x * dx + y * dy + z * dz

private lemma hasDerivAt_affine (a da s : ℝ) :
    HasDerivAt (fun r : ℝ => a + r * da) da s := by
  convert (hasDerivAt_const s a).add ((hasDerivAt_id s).mul_const da) using 1
  all_goals simp

private lemma hasDerivAt_radiusPath
    (x y z dx dy dz s : ℝ) :
    HasDerivAt
      (fun r =>
        radiusSq (x + r * dx) (y + r * dy) (z + r * dz))
      (2 * ((x + s * dx) * dx + (y + s * dy) * dy +
        (z + s * dz) * dz)) s := by
  have hx := (hasDerivAt_affine x dx s).pow 2
  have hy := (hasDerivAt_affine y dy s).pow 2
  have hz := (hasDerivAt_affine z dz s).pow 2
  unfold radiusSq
  convert (hx.add hy).add hz using 1
  all_goals ring

private lemma hasDerivAt_radialPathPairing
    (x y z dx dy dz s : ℝ) :
    HasDerivAt
      (fun r =>
        (x + r * dx) * dx + (y + r * dy) * dy +
          (z + r * dz) * dz)
      (dx ^ 2 + dy ^ 2 + dz ^ 2) s := by
  have hx := (hasDerivAt_affine x dx s).mul_const dx
  have hy := (hasDerivAt_affine y dy s).mul_const dy
  have hz := (hasDerivAt_affine z dz s).mul_const dz
  convert (hx.add hy).add hz using 1
  all_goals ring

theorem gap1 (u : ℝ → ℝ → ℝ → ℝ) (f : ℝ → ℝ)
    (hu : ∀ x y z, u x y z = f (radiusSq x y z))
    (hf : Differentiable ℝ f) (x y z dx dy dz : ℝ) :
    nthDifferential 1 u x y z dx dy dz =
      2 * deriv f (radiusSq x y z) *
        radialPairing x y z dx dy dz := by
  have hfun :
      (fun s => u (x + s * dx) (y + s * dy) (z + s * dz)) =
        fun s => f (radiusSq (x + s * dx) (y + s * dy) (z + s * dz)) := by
    funext s
    exact hu _ _ _
  have hc :=
    hf.differentiableAt.hasDerivAt.comp 0
      (hasDerivAt_radiusPath x y z dx dy dz 0)
  unfold nthDifferential
  rw [hfun]
  convert hc.deriv using 1
  all_goals
    simp [radialPairing]
    ring

theorem gap2 (u : ℝ → ℝ → ℝ → ℝ) (f : ℝ → ℝ)
    (hu : ∀ x y z, u x y z = f (radiusSq x y z))
    (hf : ContDiff ℝ 2 f) (x y z dx dy dz : ℝ) :
    nthDifferential 2 u x y z dx dy dz =
      4 * iterDeriv 2 f (radiusSq x y z) *
          (radialPairing x y z dx dy dz) ^ 2 +
        2 * deriv f (radiusSq x y z) *
          (dx ^ 2 + dy ^ 2 + dz ^ 2) := by
  have hf1 : Differentiable ℝ f :=
    hf.differentiable (by decide)
  have hdf : ContDiff ℝ 1 (deriv f) := by
    exact hf.deriv'
  have hfun :
      (fun s => u (x + s * dx) (y + s * dy) (z + s * dz)) =
        fun s => f (radiusSq (x + s * dx) (y + s * dy) (z + s * dz)) := by
    funext s
    exact hu _ _ _
  have hfirst :
      deriv
          (fun s =>
            f (radiusSq (x + s * dx) (y + s * dy) (z + s * dz))) =
        fun s =>
          deriv f
              (radiusSq (x + s * dx) (y + s * dy) (z + s * dz)) *
            (2 * ((x + s * dx) * dx + (y + s * dy) * dy +
              (z + s * dz) * dz)) := by
    funext s
    exact
      (hf1.differentiableAt.hasDerivAt.comp s
        (hasDerivAt_radiusPath x y z dx dy dz s)).deriv
  have hleft :=
    (hdf.differentiable (by decide)).differentiableAt.hasDerivAt.comp 0
      (hasDerivAt_radiusPath x y z dx dy dz 0)
  have hright :=
    HasDerivAt.const_mul 2
      (hasDerivAt_radialPathPairing x y z dx dy dz 0)
  have hprod := hleft.mul hright
  unfold nthDifferential
  rw [hfun]
  simp only [iterDeriv, Function.iterate_succ_apply]
  rw [hfirst]
  convert hprod.deriv using 1
  all_goals
    simp [radialPairing, Function.comp_apply]
    ring

end

end ProofGap.Exercise3292
