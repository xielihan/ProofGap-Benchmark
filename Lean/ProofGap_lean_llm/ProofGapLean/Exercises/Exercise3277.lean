import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3277

noncomputable section

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  (deriv^[n]) f

def nthDifferential (n : ℕ) (f : ℝ → ℝ → ℝ → ℝ)
    (x y z dx dy dz : ℝ) : ℝ :=
  iterDeriv n
    (fun t => f (x + t * dx) (y + t * dy) (z + t * dz)) 0

def phase (x y z : ℝ) : ℝ :=
  x + y + z

private theorem iterDeriv_const_mul_affine
    (n : ℕ) (f : ℝ → ℝ) (hf : ContDiff ℝ n f)
    (a b c t : ℝ) :
    iterDeriv n (fun s : ℝ => c * f (a + s * b)) t =
      c * iterDeriv n f (a + t * b) * b ^ n := by
  induction n generalizing f a b c t with
  | zero =>
      simp [iterDeriv]
  | succ n ih =>
      have hdiff : Differentiable ℝ f := hf.differentiable (by simp)
      have hfsucc : ContDiff ℝ ((n : WithTop ℕ∞) + 1) f := by
        simpa using hf
      have hfd : ContDiff ℝ n (fderiv ℝ f) :=
        (contDiff_succ_iff_fderiv.mp hfsucc).2.2
      have hderiv : ContDiff ℝ n (deriv f) := by
        simpa only [deriv] using
          hfd.clm_apply
            (contDiff_const : ContDiff ℝ n (fun _ : ℝ => (1 : ℝ)))
      have hfirst :
          deriv (fun s : ℝ => c * f (a + s * b)) =
            fun s : ℝ => (c * b) * deriv f (a + s * b) := by
        funext s
        have hinner : HasDerivAt (fun r : ℝ => a + r * b) b s := by
          simpa using ((hasDerivAt_id s).mul_const b).const_add a
        have hcomp :
            HasDerivAt (fun r : ℝ => f (a + r * b))
              (deriv f (a + s * b) * b) s :=
          (hdiff (a + s * b)).hasDerivAt.comp s hinner
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          (hcomp.const_mul c).deriv
      simp only [iterDeriv, Function.iterate_succ_apply]
      rw [hfirst]
      change iterDeriv n (fun s : ℝ => (c * b) * deriv f (a + s * b)) t =
        c * iterDeriv n (deriv f) (a + t * b) * b ^ (n + 1)
      rw [ih (f := deriv f) (hf := hderiv) (a := a) (b := b)
        (c := c * b) (t := t)]
      ring

theorem gap1 (x y z dx dy dz : ℝ) :
    nthDifferential 2 phase x y z dx dy dz = 0 := by
  unfold nthDifferential
  have hpath :
      (fun t : ℝ => phase (x + t * dx) (y + t * dy) (z + t * dz)) =
        fun t : ℝ => 1 * ((x + y + z) + t * (dx + dy + dz)) := by
    funext t
    simp only [phase, one_mul]
    ring
  rw [hpath]
  simpa [iterDeriv, Function.iterate_succ_apply] using
    (iterDeriv_const_mul_affine (n := 2) (f := fun r : ℝ => r)
      (hf := contDiff_id) (a := x + y + z) (b := dx + dy + dz)
      (c := 1) (t := 0))

theorem gap2 (u : ℝ → ℝ → ℝ → ℝ) (f : ℝ → ℝ)
    (hu : ∀ x y z, u x y z = f (x + y + z))
    (n : ℕ) (hf : ContDiff ℝ n f)
    (x y z dx dy dz : ℝ) :
    nthDifferential n u x y z dx dy dz =
      iterDeriv n f (x + y + z) * (dx + dy + dz) ^ n := by
  unfold nthDifferential
  have hpath :
      (fun t : ℝ => u (x + t * dx) (y + t * dy) (z + t * dz)) =
        fun t : ℝ => 1 * f ((x + y + z) + t * (dx + dy + dz)) := by
    funext t
    rw [hu]
    simp only [one_mul]
    congr 1
    ring
  rw [hpath]
  simpa only [one_mul, zero_mul, add_zero] using
    (iterDeriv_const_mul_affine (n := n) (f := f) (hf := hf)
      (a := x + y + z) (b := dx + dy + dz) (c := 1) (t := 0))

end

end ProofGap.Exercise3277
