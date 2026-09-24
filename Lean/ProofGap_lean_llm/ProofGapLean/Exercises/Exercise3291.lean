import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul

namespace ProofGap.Exercise3291

noncomputable section

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  (deriv^[n]) f

def nthDifferential (n : ℕ) (u : ℝ → ℝ → ℝ → ℝ)
    (x y z dx dy dz : ℝ) : ℝ :=
  iterDeriv n
    (fun s => u (x + s * dx) (y + s * dy) (z + s * dz)) 0

def firstProductDifferential
    (x y z dx dy dz : ℝ) : ℝ :=
  y * z * dx + x * z * dy + x * y * dz

def secondProductDifferential
    (x y z dx dy dz : ℝ) : ℝ :=
  2 * (z * dx * dy + y * dx * dz + x * dy * dz)

private theorem line_hasDerivAt (a da s : ℝ) :
    HasDerivAt (fun q : ℝ => a + q * da) da s := by
  simpa [add_comm] using ((hasDerivAt_id s).mul_const da).const_add a

private theorem productLine_hasDerivAt
    (x y z dx dy dz s : ℝ) :
    HasDerivAt
      (fun q : ℝ => (x + q * dx) * (y + q * dy) * (z + q * dz))
      (dx * (y + s * dy) * (z + s * dz) +
        (x + s * dx) * dy * (z + s * dz) +
        (x + s * dx) * (y + s * dy) * dz) s := by
  convert ((line_hasDerivAt x dx s).mul
    (line_hasDerivAt y dy s)).mul
      (line_hasDerivAt z dz s) using 1 <;>
    simp only [Pi.mul_apply] <;> ring

private theorem productLineFirst_hasDerivAt
    (x y z dx dy dz s : ℝ) :
    HasDerivAt
      (fun q : ℝ =>
        dx * (y + q * dy) * (z + q * dz) +
          (x + q * dx) * dy * (z + q * dz) +
          (x + q * dx) * (y + q * dy) * dz)
      (2 * (dx * dy * (z + s * dz) +
        dx * dz * (y + s * dy) +
        dy * dz * (x + s * dx))) s := by
  have hx := line_hasDerivAt x dx s
  have hy := line_hasDerivAt y dy s
  have hz := line_hasDerivAt z dz s
  convert (((hy.mul hz).const_mul dx).add ((hx.mul_const dy).mul hz)).add
    ((hx.mul hy).mul_const dz) using 1
  · funext q
    simp only [Pi.add_apply, Pi.mul_apply]
    ring
  · ring

theorem gap1 (u t : ℝ → ℝ → ℝ → ℝ) (f : ℝ → ℝ)
    (hu : ∀ x y z, u x y z = f (t x y z))
    (ht : ∀ x y z, t x y z = x * y * z)
    (hf : Differentiable ℝ f) (x y z dx dy dz : ℝ) :
    nthDifferential 1 u x y z dx dy dz =
      deriv f (t x y z) *
        firstProductDifferential x y z dx dy dz := by
  change deriv
    (fun s => u (x + s * dx) (y + s * dy) (z + s * dz)) 0 = _
  have hfun :
      (fun s => u (x + s * dx) (y + s * dy) (z + s * dz)) =
        (fun s =>
          f ((x + s * dx) * (y + s * dy) * (z + s * dz))) := by
    funext s
    rw [hu, ht]
  rw [hfun, ht]
  have hc := hf.differentiableAt.hasDerivAt.comp 0
    (productLine_hasDerivAt x y z dx dy dz 0)
  convert hc.deriv using 1 <;>
    simp only [firstProductDifferential] <;> ring

theorem gap2 (u t : ℝ → ℝ → ℝ → ℝ) (f : ℝ → ℝ)
    (hu : ∀ x y z, u x y z = f (t x y z))
    (ht : ∀ x y z, t x y z = x * y * z)
    (hf : ContDiff ℝ 2 f) (x y z dx dy dz : ℝ) :
    nthDifferential 2 u x y z dx dy dz =
      iterDeriv 2 f (t x y z) *
          (firstProductDifferential x y z dx dy dz) ^ 2 +
        deriv f (t x y z) *
          secondProductDifferential x y z dx dy dz := by
  change deriv (deriv (fun s =>
    u (x + s * dx) (y + s * dy) (z + s * dz))) 0 = _
  have hfun :
      (fun s => u (x + s * dx) (y + s * dy) (z + s * dz)) =
        (fun s =>
          f ((x + s * dx) * (y + s * dy) * (z + s * dz))) := by
    funext s
    rw [hu, ht]
  rw [hfun, ht]
  have hfdiff : Differentiable ℝ f := hf.differentiable (by decide)
  have hfirst :
      deriv (fun q : ℝ =>
        f ((x + q * dx) * (y + q * dy) * (z + q * dz))) =
      (fun s : ℝ =>
        deriv f ((x + s * dx) * (y + s * dy) * (z + s * dz)) *
          (dx * (y + s * dy) * (z + s * dz) +
            (x + s * dx) * dy * (z + s * dz) +
            (x + s * dx) * (y + s * dy) * dz)) := by
    funext s
    have hc := hfdiff.differentiableAt.hasDerivAt.comp s
      (productLine_hasDerivAt x y z dx dy dz s)
    simpa only [Function.comp_apply] using hc.deriv
  rw [hfirst]
  rw [show iterDeriv 2 f (x * y * z) =
    deriv (deriv f) (x * y * z) by rfl]
  have hdfcomp :=
    hf.differentiable_deriv_two.differentiableAt.hasDerivAt.comp 0
      (productLine_hasDerivAt x y z dx dy dz 0)
  have hprod := hdfcomp.mul
    (productLineFirst_hasDerivAt x y z dx dy dz 0)
  convert hprod.deriv using 1 <;>
    simp only [Function.comp_apply, firstProductDifferential,
      secondProductDifferential] <;> ring

end

end ProofGap.Exercise3291
