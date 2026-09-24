import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3283

noncomputable section

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  (deriv^[n]) f

def partialX (u : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => u t y z) x

def partialY (u : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => u x t z) y

def partialZ (u : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => u x y t) z

def partialXX (u : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  iterDeriv 2 (fun t => u t y z) x

def partialYY (u : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  iterDeriv 2 (fun t => u x t z) y

def partialZZ (u : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  iterDeriv 2 (fun t => u x y t) z

def partialXY (u : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => partialX u x t z) y

def partialYZ (u : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => partialY u x y t) z

def partialZX (u : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => partialZ u t y z) x

def radiusSq (x y z : ℝ) : ℝ :=
  x ^ 2 + y ^ 2 + z ^ 2

private theorem deriv_differentiable_of_contDiff_two (f : ℝ → ℝ)
    (hf : ContDiff ℝ 2 f) : Differentiable ℝ (deriv f) := by
  have hfd : ContDiff ℝ 1 (fderiv ℝ f) :=
    ((contDiff_succ_iff_fderiv (n := 1)).mp (by simpa using hf)).2.2
  have happ : Differentiable ℝ
      (fun x : ℝ => (fderiv ℝ f x) (1 : ℝ)) :=
    (hfd.differentiable (by decide)).clm_apply
      (differentiable_const (c := (1 : ℝ)))
  simpa only [deriv] using happ

private theorem hasDerivAt_radiusSq_first (a b t : ℝ) :
    HasDerivAt (fun s : ℝ => radiusSq s a b) (2 * t) t := by
  have hs : HasDerivAt (fun s : ℝ => s * s) (t + t) t := by
    simpa only [Pi.mul_apply, id_eq, one_mul, mul_one] using
      (hasDerivAt_id t).mul (hasDerivAt_id t)
  have ha : HasDerivAt (fun s : ℝ => s * s + a * a) (t + t) t := by
    simpa only [Pi.add_apply, add_zero] using
      hs.add (hasDerivAt_const t (a * a))
  have hb : HasDerivAt (fun s : ℝ => s * s + a * a + b * b) (t + t) t := by
    simpa only [Pi.add_apply, add_zero] using
      ha.add (hasDerivAt_const t (b * b))
  simpa only [radiusSq, pow_two, two_mul] using hb

theorem gap1 (u : ℝ → ℝ → ℝ → ℝ) (f : ℝ → ℝ)
    (hu : ∀ x y z, u x y z = f (radiusSq x y z))
    (hf : Differentiable ℝ f) (x y z : ℝ) :
    partialX u x y z =
      2 * x * deriv f (radiusSq x y z) := by
  unfold partialX
  rw [show (fun t => u t y z) = fun t => f (radiusSq t y z) by
    funext t
    exact hu t y z]
  have hr : HasDerivAt (fun t : ℝ => radiusSq t y z) (2 * x) x :=
    hasDerivAt_radiusSq_first y z x
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    ((hf (radiusSq x y z)).hasDerivAt.comp x hr).deriv

theorem gap2 (u : ℝ → ℝ → ℝ → ℝ) (f : ℝ → ℝ)
    (hu : ∀ x y z, u x y z = f (radiusSq x y z))
    (hf : ContDiff ℝ 2 f) (x y z : ℝ) :
    partialXX u x y z =
      2 * deriv f (radiusSq x y z) +
        4 * x ^ 2 * iterDeriv 2 f (radiusSq x y z) := by
  have hf1 : Differentiable ℝ f := hf.differentiable (by decide)
  have hdf : Differentiable ℝ (deriv f) :=
    deriv_differentiable_of_contDiff_two f hf
  change deriv (deriv (fun t => u t y z)) x =
    2 * deriv f (radiusSq x y z) +
      4 * x ^ 2 * deriv (deriv f) (radiusSq x y z)
  rw [show deriv (fun t => u t y z) =
      fun t => 2 * t * deriv f (radiusSq t y z) by
    funext t
    exact gap1 u f hu hf1 t y z]
  have hr : HasDerivAt (fun t : ℝ => radiusSq t y z) (2 * x) x :=
    hasDerivAt_radiusSq_first y z x
  have hlin : HasDerivAt (fun t : ℝ => 2 * t) 2 x := by
    simpa using (hasDerivAt_const x (2 : ℝ)).mul (hasDerivAt_id x)
  have hc : HasDerivAt (fun t : ℝ => deriv f (radiusSq t y z))
      (deriv (deriv f) (radiusSq x y z) * (2 * x)) x := by
    simpa [Function.comp_def] using
      ((hdf (radiusSq x y z)).hasDerivAt.comp x hr)
  have hd :
      deriv (fun t : ℝ => 2 * t * deriv f (radiusSq t y z)) x =
        2 * deriv f (radiusSq x y z) +
          (2 * x) * (deriv (deriv f) (radiusSq x y z) * (2 * x)) := by
    simpa using (hlin.mul hc).deriv
  rw [hd]
  ring

theorem gap3 (u : ℝ → ℝ → ℝ → ℝ) (f : ℝ → ℝ)
    (hu : ∀ x y z, u x y z = f (radiusSq x y z))
    (hf : ContDiff ℝ 2 f) (x y z : ℝ) :
    partialXY u x y z =
      4 * x * y * iterDeriv 2 f (radiusSq x y z) := by
  have hdf : Differentiable ℝ (deriv f) :=
    deriv_differentiable_of_contDiff_two f hf
  have hf1 : Differentiable ℝ f := hf.differentiable (by decide)
  unfold partialXY
  change deriv (fun t => partialX u x t z) y =
    4 * x * y * deriv (deriv f) (radiusSq x y z)
  rw [show (fun t => partialX u x t z) =
      fun t => 2 * x * deriv f (radiusSq x t z) by
    funext t
    exact gap1 u f hu hf1 x t z]
  have hr : HasDerivAt (fun t : ℝ => radiusSq x t z) (2 * y) y := by
    simpa only [radiusSq, add_comm, add_left_comm, add_assoc] using
      hasDerivAt_radiusSq_first x z y
  have hc : HasDerivAt (fun t : ℝ => deriv f (radiusSq x t z))
      (deriv (deriv f) (radiusSq x y z) * (2 * y)) y := by
    simpa [Function.comp_def] using
      ((hdf (radiusSq x y z)).hasDerivAt.comp y hr)
  have hp : HasDerivAt
      (fun t : ℝ => 2 * x * deriv f (radiusSq x t z))
      ((2 * x) * (deriv (deriv f) (radiusSq x y z) * (2 * y))) y := by
    simpa only [Pi.mul_apply, zero_mul, zero_add] using
      (hasDerivAt_const y (2 * x)).mul hc
  rw [hp.deriv]
  ring

theorem gap4 (u : ℝ → ℝ → ℝ → ℝ) (f : ℝ → ℝ)
    (hu : ∀ x y z, u x y z = f (radiusSq x y z))
    (hf : Differentiable ℝ f) (x y z : ℝ) :
    partialY u x y z =
      2 * y * deriv f (radiusSq x y z) := by
  unfold partialY
  rw [show (fun t => u x t z) = fun t => f (radiusSq x t z) by
    funext t
    exact hu x t z]
  have hr : HasDerivAt (fun t : ℝ => radiusSq x t z) (2 * y) y := by
    simpa only [radiusSq, add_comm, add_left_comm, add_assoc] using
      hasDerivAt_radiusSq_first x z y
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    ((hf (radiusSq x y z)).hasDerivAt.comp y hr).deriv

theorem gap5 (u : ℝ → ℝ → ℝ → ℝ) (f : ℝ → ℝ)
    (hu : ∀ x y z, u x y z = f (radiusSq x y z))
    (hf : Differentiable ℝ f) (x y z : ℝ) :
    partialZ u x y z =
      2 * z * deriv f (radiusSq x y z) := by
  unfold partialZ
  rw [show (fun t => u x y t) = fun t => f (radiusSq x y t) by
    funext t
    exact hu x y t]
  have hr : HasDerivAt (fun t : ℝ => radiusSq x y t) (2 * z) z := by
    simpa only [radiusSq, add_comm, add_left_comm, add_assoc] using
      hasDerivAt_radiusSq_first x y z
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    ((hf (radiusSq x y z)).hasDerivAt.comp z hr).deriv

theorem gap6 (u : ℝ → ℝ → ℝ → ℝ) (f : ℝ → ℝ)
    (hu : ∀ x y z, u x y z = f (radiusSq x y z))
    (hf : ContDiff ℝ 2 f) (x y z : ℝ) :
    partialYY u x y z =
      2 * deriv f (radiusSq x y z) +
        4 * y ^ 2 * iterDeriv 2 f (radiusSq x y z) := by
  have hf1 : Differentiable ℝ f := hf.differentiable (by decide)
  have hdf : Differentiable ℝ (deriv f) :=
    deriv_differentiable_of_contDiff_two f hf
  change deriv (deriv (fun t => u x t z)) y =
    2 * deriv f (radiusSq x y z) +
      4 * y ^ 2 * deriv (deriv f) (radiusSq x y z)
  rw [show deriv (fun t => u x t z) =
      fun t => 2 * t * deriv f (radiusSq x t z) by
    funext t
    exact gap4 u f hu hf1 x t z]
  have hr : HasDerivAt (fun t : ℝ => radiusSq x t z) (2 * y) y := by
    simpa only [radiusSq, add_comm, add_left_comm, add_assoc] using
      hasDerivAt_radiusSq_first x z y
  have hlin : HasDerivAt (fun t : ℝ => 2 * t) 2 y := by
    simpa using (hasDerivAt_const y (2 : ℝ)).mul (hasDerivAt_id y)
  have hc : HasDerivAt (fun t : ℝ => deriv f (radiusSq x t z))
      (deriv (deriv f) (radiusSq x y z) * (2 * y)) y := by
    simpa [Function.comp_def] using
      ((hdf (radiusSq x y z)).hasDerivAt.comp y hr)
  have hd :
      deriv (fun t : ℝ => 2 * t * deriv f (radiusSq x t z)) y =
        2 * deriv f (radiusSq x y z) +
          (2 * y) * (deriv (deriv f) (radiusSq x y z) * (2 * y)) := by
    simpa using (hlin.mul hc).deriv
  rw [hd]
  ring

theorem gap7 (u : ℝ → ℝ → ℝ → ℝ) (f : ℝ → ℝ)
    (hu : ∀ x y z, u x y z = f (radiusSq x y z))
    (hf : ContDiff ℝ 2 f) (x y z : ℝ) :
    partialZZ u x y z =
      2 * deriv f (radiusSq x y z) +
        4 * z ^ 2 * iterDeriv 2 f (radiusSq x y z) := by
  have hf1 : Differentiable ℝ f := hf.differentiable (by decide)
  have hdf : Differentiable ℝ (deriv f) :=
    deriv_differentiable_of_contDiff_two f hf
  change deriv (deriv (fun t => u x y t)) z =
    2 * deriv f (radiusSq x y z) +
      4 * z ^ 2 * deriv (deriv f) (radiusSq x y z)
  rw [show deriv (fun t => u x y t) =
      fun t => 2 * t * deriv f (radiusSq x y t) by
    funext t
    exact gap5 u f hu hf1 x y t]
  have hr : HasDerivAt (fun t : ℝ => radiusSq x y t) (2 * z) z := by
    simpa only [radiusSq, add_comm, add_left_comm, add_assoc] using
      hasDerivAt_radiusSq_first x y z
  have hlin : HasDerivAt (fun t : ℝ => 2 * t) 2 z := by
    simpa using (hasDerivAt_const z (2 : ℝ)).mul (hasDerivAt_id z)
  have hc : HasDerivAt (fun t : ℝ => deriv f (radiusSq x y t))
      (deriv (deriv f) (radiusSq x y z) * (2 * z)) z := by
    simpa [Function.comp_def] using
      ((hdf (radiusSq x y z)).hasDerivAt.comp z hr)
  have hd :
      deriv (fun t : ℝ => 2 * t * deriv f (radiusSq x y t)) z =
        2 * deriv f (radiusSq x y z) +
          (2 * z) * (deriv (deriv f) (radiusSq x y z) * (2 * z)) := by
    simpa using (hlin.mul hc).deriv
  rw [hd]
  ring

theorem gap8 (u : ℝ → ℝ → ℝ → ℝ) (f : ℝ → ℝ)
    (hu : ∀ x y z, u x y z = f (radiusSq x y z))
    (hf : ContDiff ℝ 2 f) (x y z : ℝ) :
    partialYZ u x y z =
      4 * y * z * iterDeriv 2 f (radiusSq x y z) := by
  have hdf : Differentiable ℝ (deriv f) :=
    deriv_differentiable_of_contDiff_two f hf
  have hf1 : Differentiable ℝ f := hf.differentiable (by decide)
  unfold partialYZ
  change deriv (fun t => partialY u x y t) z =
    4 * y * z * deriv (deriv f) (radiusSq x y z)
  rw [show (fun t => partialY u x y t) =
      fun t => 2 * y * deriv f (radiusSq x y t) by
    funext t
    exact gap4 u f hu hf1 x y t]
  have hr : HasDerivAt (fun t : ℝ => radiusSq x y t) (2 * z) z := by
    simpa only [radiusSq, add_comm, add_left_comm, add_assoc] using
      hasDerivAt_radiusSq_first x y z
  have hc : HasDerivAt (fun t : ℝ => deriv f (radiusSq x y t))
      (deriv (deriv f) (radiusSq x y z) * (2 * z)) z := by
    simpa [Function.comp_def] using
      ((hdf (radiusSq x y z)).hasDerivAt.comp z hr)
  have hp : HasDerivAt
      (fun t : ℝ => 2 * y * deriv f (radiusSq x y t))
      ((2 * y) * (deriv (deriv f) (radiusSq x y z) * (2 * z))) z := by
    simpa only [Pi.mul_apply, zero_mul, zero_add] using
      (hasDerivAt_const z (2 * y)).mul hc
  rw [hp.deriv]
  ring

theorem gap9 (u : ℝ → ℝ → ℝ → ℝ) (f : ℝ → ℝ)
    (hu : ∀ x y z, u x y z = f (radiusSq x y z))
    (hf : ContDiff ℝ 2 f) (x y z : ℝ) :
    partialZX u x y z =
      4 * x * z * iterDeriv 2 f (radiusSq x y z) := by
  have hdf : Differentiable ℝ (deriv f) :=
    deriv_differentiable_of_contDiff_two f hf
  have hf1 : Differentiable ℝ f := hf.differentiable (by decide)
  unfold partialZX
  change deriv (fun t => partialZ u t y z) x =
    4 * x * z * deriv (deriv f) (radiusSq x y z)
  rw [show (fun t => partialZ u t y z) =
      fun t => 2 * z * deriv f (radiusSq t y z) by
    funext t
    exact gap5 u f hu hf1 t y z]
  have hr : HasDerivAt (fun t : ℝ => radiusSq t y z) (2 * x) x :=
    hasDerivAt_radiusSq_first y z x
  have hc : HasDerivAt (fun t : ℝ => deriv f (radiusSq t y z))
      (deriv (deriv f) (radiusSq x y z) * (2 * x)) x := by
    simpa [Function.comp_def] using
      ((hdf (radiusSq x y z)).hasDerivAt.comp x hr)
  have hp : HasDerivAt
      (fun t : ℝ => 2 * z * deriv f (radiusSq t y z))
      ((2 * z) * (deriv (deriv f) (radiusSq x y z) * (2 * x))) x := by
    simpa only [Pi.mul_apply, zero_mul, zero_add] using
      (hasDerivAt_const x (2 * z)).mul hc
  rw [hp.deriv]
  ring

end

end ProofGap.Exercise3283
