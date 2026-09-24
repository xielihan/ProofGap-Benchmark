import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3278

noncomputable section

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  (deriv^[n]) f

def nthDifferential (n : ℕ) (f : ℝ → ℝ → ℝ → ℝ)
    (x y z dx dy dz : ℝ) : ℝ :=
  iterDeriv n
    (fun t => f (x + t * dx) (y + t * dy) (z + t * dz)) 0

def phase (a b c : ℝ) (x y z : ℝ) : ℝ :=
  a * x + b * y + c * z

def exponential (a b c : ℝ) (x y z : ℝ) : ℝ :=
  Real.exp (phase a b c x y z)

private theorem iterDeriv_exp_affine (n : ℕ) (A B : ℝ) :
    (deriv^[n]) (fun t : ℝ => Real.exp (A + t * B)) =
      (fun t : ℝ => Real.exp (A + t * B) * B ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      funext t
      have hinner : HasDerivAt (fun s : ℝ => A + s * B) B t := by
        simpa only [id_eq, one_mul] using
          (((hasDerivAt_id t).mul_const B).const_add A)
      simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using
        (((Real.hasDerivAt_exp (A + t * B)).comp t hinner).mul_const
          (B ^ n)).deriv

theorem gap1 (a b c x y z dx dy dz : ℝ) :
    nthDifferential 2 (phase a b c) x y z dx dy dz = 0 := by
  let A := phase a b c x y z
  let B := a * dx + b * dy + c * dz
  have hpath :
      (fun t : ℝ => phase a b c (x + t * dx) (y + t * dy) (z + t * dz)) =
        (fun t : ℝ => A + t * B) := by
    funext t
    dsimp [A, B, phase]
    ring
  have hfirst :
      deriv (fun t : ℝ => A + t * B) = (fun _ : ℝ => B) := by
    funext t
    simpa only [id_eq, one_mul] using
      (((hasDerivAt_id t).mul_const B).const_add A).deriv
  unfold nthDifferential iterDeriv
  rw [hpath]
  change deriv (deriv (fun t : ℝ => A + t * B)) 0 = 0
  rw [hfirst]
  simpa using (hasDerivAt_const (0 : ℝ) B).deriv

theorem gap2 (u : ℝ → ℝ → ℝ → ℝ) (a b c : ℝ)
    (hu : ∀ x y z, u x y z = exponential a b c x y z)
    (n : ℕ) (x y z dx dy dz : ℝ) :
    nthDifferential n u x y z dx dy dz =
      exponential a b c x y z *
        (a * dx + b * dy + c * dz) ^ n := by
  let A := phase a b c x y z
  let B := a * dx + b * dy + c * dz
  have hpath :
      (fun t : ℝ => u (x + t * dx) (y + t * dy) (z + t * dz)) =
        (fun t : ℝ => Real.exp (A + t * B)) := by
    funext t
    rw [hu]
    unfold exponential
    apply congrArg Real.exp
    dsimp [A, B, phase]
    ring
  unfold nthDifferential iterDeriv
  rw [hpath]
  simpa [A, B, exponential] using
    congrFun (iterDeriv_exp_affine n A B) (0 : ℝ)

end

end ProofGap.Exercise3278
