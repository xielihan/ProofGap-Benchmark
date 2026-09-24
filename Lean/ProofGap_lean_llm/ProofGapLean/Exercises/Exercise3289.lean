import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3289

noncomputable section

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  (deriv^[n]) f

def nthDifferential (n : ℕ) (u : ℝ → ℝ → ℝ)
    (x y dx dy : ℝ) : ℝ :=
  iterDeriv n (fun s => u (x + s * dx) (y + s * dy)) 0

private theorem hasDerivAt_affine_ratio
    (x y dx dy s : ℝ) (h : x + s * dx ≠ 0) :
    HasDerivAt
      (fun r : ℝ => (y + r * dy) / (x + r * dx))
      ((x * dy - y * dx) / (x + s * dx) ^ 2) s := by
  have hy : HasDerivAt (fun r : ℝ => y + r * dy) dy s := by
    simpa using
      (((hasDerivAt_id s).mul_const dy).const_add y)
  have hx' : HasDerivAt (fun r : ℝ => x + r * dx) dx s := by
    simpa using
      (((hasDerivAt_id s).mul_const dx).const_add x)
  convert hy.div hx' h using 1 <;> ring

theorem gap1 (u t : ℝ → ℝ → ℝ) (f : ℝ → ℝ)
    (hu : ∀ x y, u x y = f (t x y))
    (ht : ∀ x y, t x y = y / x)
    (hf : Differentiable ℝ f)
    (x y dx dy : ℝ) (hx : x ≠ 0) :
    nthDifferential 1 u x y dx dy =
      deriv f (t x y) * ((x * dy - y * dx) / x ^ 2) := by
  change
    deriv (fun s : ℝ => u (x + s * dx) (y + s * dy)) 0 =
      deriv f (t x y) * ((x * dy - y * dx) / x ^ 2)
  have hpath :
      (fun s : ℝ => u (x + s * dx) (y + s * dy)) =
        (fun s : ℝ => f ((y + s * dy) / (x + s * dx))) := by
    funext s
    rw [hu, ht]
  rw [hpath, ht x y]
  have hq :
      HasDerivAt
        (fun s : ℝ => (y + s * dy) / (x + s * dx))
        ((x * dy - y * dx) / x ^ 2) 0 := by
    simpa using
      (hasDerivAt_affine_ratio x y dx dy 0 (by simpa using hx))
  have hcomp :=
    (hf ((y + 0 * dy) / (x + 0 * dx))).hasDerivAt.comp 0 hq
  simpa [Function.comp_def] using hcomp.deriv

theorem gap2 (u t : ℝ → ℝ → ℝ) (f : ℝ → ℝ)
    (hu : ∀ x y, u x y = f (t x y))
    (ht : ∀ x y, t x y = y / x)
    (hf : ContDiff ℝ 2 f)
    (x y dx dy : ℝ) (hx : x ≠ 0) :
    nthDifferential 2 u x y dx dy =
      iterDeriv 2 f (t x y) *
          (x * dy - y * dx) ^ 2 / x ^ 4 -
        2 * deriv f (t x y) * dx *
          (x * dy - y * dx) / x ^ 3 := by
  change
    deriv (deriv (fun s : ℝ => u (x + s * dx) (y + s * dy))) 0 =
      deriv (deriv f) (t x y) * (x * dy - y * dx) ^ 2 / x ^ 4 -
        2 * deriv f (t x y) * dx * (x * dy - y * dx) / x ^ 3
  have hpath :
      (fun s : ℝ => u (x + s * dx) (y + s * dy)) =
        (fun s : ℝ => f ((y + s * dy) / (x + s * dx))) := by
    funext s
    rw [hu, ht]
  rw [hpath, ht x y]
  have hsucc : ContDiff ℝ (1 + 1) f := by
    simpa using hf
  have hsmooth :
      Differentiable ℝ f ∧ ContDiff ℝ 1 (fderiv ℝ f) := by
    simpa using (contDiff_succ_iff_fderiv.mp hsucc)
  have hf1 : Differentiable ℝ f :=
    hsmooth.1
  have hfderiv_cd : ContDiff ℝ 1 (fderiv ℝ f) :=
    hsmooth.2
  have hone : ContDiff ℝ 1 (fun _ : ℝ => (1 : ℝ)) :=
    contDiff_const
  have hdf_cd : ContDiff ℝ 1 (deriv f) := by
    simpa only [deriv] using hfderiv_cd.clm_apply hone
  have hdf : Differentiable ℝ (deriv f) :=
    hdf_cd.differentiable (by simp)
  have hp0 :
      HasDerivAt (fun s : ℝ => x + s * dx) dx 0 := by
    simpa using
      (((hasDerivAt_id (0 : ℝ)).mul_const dx).const_add x)
  have hden : ∀ᶠ s in nhds (0 : ℝ), x + s * dx ≠ 0 := by
    have h0 : (fun s : ℝ => x + s * dx) 0 ≠ 0 := by
      simpa using hx
    exact hp0.continuousAt.eventually_ne h0
  have hderiv :
      (fun s : ℝ =>
          deriv
            (fun r : ℝ => f ((y + r * dy) / (x + r * dx))) s) =ᶠ[nhds (0 : ℝ)]
        (fun s : ℝ =>
          deriv f ((y + s * dy) / (x + s * dx)) *
            ((x * dy - y * dx) / (x + s * dx) ^ 2)) := by
    refine hden.mono ?_
    intro s hs
    have hq := hasDerivAt_affine_ratio x y dx dy s hs
    have hcomp :=
      (hf1 ((y + s * dy) / (x + s * dx))).hasDerivAt.comp s hq
    simpa [Function.comp_def] using hcomp.deriv
  have hq0 :
      HasDerivAt
        (fun s : ℝ => (y + s * dy) / (x + s * dx))
        ((x * dy - y * dx) / x ^ 2) 0 := by
    simpa using
      (hasDerivAt_affine_ratio x y dx dy 0 (by simpa using hx))
  have houter :
      HasDerivAt
        (fun s : ℝ => deriv f ((y + s * dy) / (x + s * dx)))
        (deriv (deriv f) (y / x) *
          ((x * dy - y * dx) / x ^ 2)) 0 := by
    have hcomp :=
      (hdf ((y + 0 * dy) / (x + 0 * dx))).hasDerivAt.comp 0 hq0
    simpa [Function.comp_def] using hcomp
  have hp2 :
      HasDerivAt (fun s : ℝ => (x + s * dx) ^ 2) (2 * x * dx) 0 := by
    have hcoef : 2 * x * dx = dx * x + x * dx := by
      ring
    rw [hcoef]
    simpa [pow_two] using (hp0.mul hp0)
  have hx2 : (x + 0 * dx) ^ 2 ≠ 0 := by
    simpa using (pow_ne_zero 2 hx)
  have hk :
      HasDerivAt
        (fun s : ℝ => (x * dy - y * dx) / (x + s * dx) ^ 2)
        (-2 * (x * dy - y * dx) * dx / x ^ 3) 0 := by
    convert
      (hasDerivAt_const (x := (0 : ℝ)) (x * dy - y * dx)).div hp2 hx2
      using 1 <;>
      simp [hx] <;>
      field_simp [hx] <;>
      ring
  have hproduct :
      HasDerivAt
        (fun s : ℝ =>
          deriv f ((y + s * dy) / (x + s * dx)) *
            ((x * dy - y * dx) / (x + s * dx) ^ 2))
        (deriv (deriv f) (y / x) * (x * dy - y * dx) ^ 2 / x ^ 4 -
          2 * deriv f (y / x) * dx * (x * dy - y * dx) / x ^ 3) 0 := by
    convert houter.mul hk using 1 <;>
      simp [hx] <;>
      field_simp [hx] <;>
      ring
  exact (hderiv.deriv_eq).trans hproduct.deriv

end

end ProofGap.Exercise3289
