import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise3300

noncomputable section

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  (deriv^[n]) f

def nthDifferential (n : ℕ) (u : ℝ → ℝ → ℝ → ℝ)
    (x y z dx dy dz : ℝ) : ℝ :=
  iterDeriv n
    (fun s => u (x + s * dx) (y + s * dy) (z + s * dz)) 0

def partial1 (f : ℝ → ℝ → ℝ → ℝ) (a b c : ℝ) : ℝ :=
  deriv (fun t => f t b c) a

def partial2 (f : ℝ → ℝ → ℝ → ℝ) (a b c : ℝ) : ℝ :=
  deriv (fun t => f a t c) b

def partial3 (f : ℝ → ℝ → ℝ → ℝ) (a b c : ℝ) : ℝ :=
  deriv (fun t => f a b t) c

def partial11 (f : ℝ → ℝ → ℝ → ℝ) (a b c : ℝ) : ℝ :=
  (deriv^[2]) (fun t => f t b c) a

def partial12 (f : ℝ → ℝ → ℝ → ℝ) (a b c : ℝ) : ℝ :=
  deriv (fun t => partial1 f a t c) b

def partial13 (f : ℝ → ℝ → ℝ → ℝ) (a b c : ℝ) : ℝ :=
  deriv (fun t => partial1 f a b t) c

def partial22 (f : ℝ → ℝ → ℝ → ℝ) (a b c : ℝ) : ℝ :=
  (deriv^[2]) (fun t => f a t c) b

def partial23 (f : ℝ → ℝ → ℝ → ℝ) (a b c : ℝ) : ℝ :=
  deriv (fun t => partial2 f a b t) c

def partial33 (f : ℝ → ℝ → ℝ → ℝ) (a b c : ℝ) : ℝ :=
  (deriv^[2]) (fun t => f a b t) c

def uncurry₃ (f : ℝ → ℝ → ℝ → ℝ) : ℝ × ℝ × ℝ → ℝ :=
  fun p => f p.1 p.2.1 p.2.2

private theorem deriv_affine_at
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → ℝ} (hF : ContDiff ℝ 1 F) (p v : E) (x : ℝ) :
    deriv (fun t : ℝ => F (p + (t - x) • v)) x = fderiv ℝ F p v := by
  have hFd : Differentiable ℝ F := hF.differentiable (by decide)
  have hg : HasDerivAt (fun t : ℝ => p + (t - x) • v) v x := by
    simpa using
      (((hasDerivAt_id x).sub_const x).smul_const v).const_add p
  have hc := ((hFd _).hasFDerivAt.comp x hg).hasDerivAt.deriv
  simpa [Function.comp_apply] using hc

private theorem second_deriv_affine_at
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → ℝ} (hF : ContDiff ℝ 2 F) (p v : E) (x : ℝ) :
    deriv (deriv fun t : ℝ => F (p + (t - x) • v)) x =
      (fderiv ℝ (fun q => fderiv ℝ F q) p) v v := by
  let L := fun q => fderiv ℝ F q
  have hFd : Differentiable ℝ F := hF.differentiable (by decide)
  have hstep := (contDiff_succ_iff_fderiv (n := 1)).mp hF
  have hLd : Differentiable ℝ L := hstep.2.2.differentiable (by decide)
  have hg : ∀ t : ℝ, HasDerivAt (fun s : ℝ => p + (s - x) • v) v t := by
    intro t
    simpa using
      (((hasDerivAt_id t).sub_const x).smul_const v).const_add p
  have hfirst :
      (deriv fun t : ℝ => F (p + (t - x) • v)) =
        fun t => L (p + (t - x) • v) v := by
    funext t
    have hc := ((hFd _).hasFDerivAt.comp t (hg t)).hasDerivAt.deriv
    simpa [L, Function.comp_apply] using hc
  rw [hfirst]
  have hcomp := (hLd _).hasFDerivAt.comp x (hg x)
  have happ : HasDerivAt
      (fun t : ℝ => L (p + (t - x) • v) v)
      ((fderiv ℝ L p) v v) x := by
    simpa [Function.comp_apply] using
      (hcomp.clm_apply (hasFDerivAt_const v x)).hasDerivAt
  simpa [L] using happ.deriv

private theorem mixed_deriv_affine_at
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : E → ℝ} (hF : ContDiff ℝ 2 F) (p v w : E) (x y : ℝ) :
    deriv (fun t : ℝ =>
      deriv (fun s : ℝ => F (p + (t - y) • w + (s - x) • v)) x) y =
      (fderiv ℝ (fun q => fderiv ℝ F q) p) w v := by
  let L := fun q => fderiv ℝ F q
  have hFd : Differentiable ℝ F := hF.differentiable (by decide)
  have hstep := (contDiff_succ_iff_fderiv (n := 1)).mp hF
  have hLd : Differentiable ℝ L := hstep.2.2.differentiable (by decide)
  have hinner : ∀ t : ℝ,
      deriv (fun s : ℝ => F (p + (t - y) • w + (s - x) • v)) x =
        L (p + (t - y) • w) v := by
    intro t
    have hg : HasDerivAt
        (fun s : ℝ => p + (t - y) • w + (s - x) • v) v x := by
      simpa using
        (((hasDerivAt_id x).sub_const x).smul_const v).const_add
          (p + (t - y) • w)
    have hc := ((hFd _).hasFDerivAt.comp x hg).hasDerivAt.deriv
    simpa [L, Function.comp_apply] using hc
  simp_rw [hinner]
  have hg : HasDerivAt (fun t : ℝ => p + (t - y) • w) w y := by
    simpa using
      (((hasDerivAt_id y).sub_const y).smul_const w).const_add p
  have hcomp := (hLd _).hasFDerivAt.comp y hg
  have happ : HasDerivAt
      (fun t : ℝ => L (p + (t - y) • w) v)
      ((fderiv ℝ L p) w v) y := by
    simpa [Function.comp_apply] using
      (hcomp.clm_apply (hasFDerivAt_const v y)).hasDerivAt
  simpa [L] using happ.deriv

theorem gap1 (u ξ η ζ f : ℝ → ℝ → ℝ → ℝ) (a b c : ℝ)
    (hu : ∀ x y z, u x y z = f (ξ x y z) (η x y z) (ζ x y z))
    (hξ : ∀ x y z, ξ x y z = a * x)
    (hη : ∀ x y z, η x y z = b * y)
    (hζ : ∀ x y z, ζ x y z = c * z)
    (hf : ContDiff ℝ 1 (uncurry₃ f))
    (x y z dx dy dz : ℝ) :
    nthDifferential 1 u x y z dx dy dz =
      a * partial1 f (ξ x y z) (η x y z) (ζ x y z) * dx +
        b * partial2 f (ξ x y z) (η x y z) (ζ x y z) * dy +
        c * partial3 f (ξ x y z) (η x y z) (ζ x y z) * dz := by
  classical
  simp only [nthDifferential, iterDeriv, Function.iterate_one]
  simp_rw [hu, hξ, hη, hζ]
  unfold partial1 partial2 partial3
  let F : ℝ × ℝ × ℝ → ℝ := uncurry₃ f
  let p : ℝ × ℝ × ℝ := (a * x, b * y, c * z)
  let v : ℝ × ℝ × ℝ := (a * dx, b * dy, c * dz)
  let e₁ : ℝ × ℝ × ℝ := (1, 0, 0)
  let e₂ : ℝ × ℝ × ℝ := (0, 1, 0)
  let e₃ : ℝ × ℝ × ℝ := (0, 0, 1)
  let L := fderiv ℝ F p
  have hfun :
      (fun s : ℝ => F (a * (x + s * dx), b * (y + s * dy), c * (z + s * dz))) =
        fun s : ℝ => F (p + (s - 0) • v) := by
    funext s
    apply congrArg F
    ext <;> dsimp [p, v] <;> ring
  have hline :
      deriv (fun s : ℝ => F (a * (x + s * dx), b * (y + s * dy), c * (z + s * dz))) 0 =
        L v := by
    rw [hfun]
    exact deriv_affine_at (F := F) hf p v 0
  have h₁ : deriv (fun t => f t (b * y) (c * z)) (a * x) = L e₁ := by
    simpa [F, p, e₁, L, uncurry₃] using
      (deriv_affine_at (F := F) hf p e₁ (a * x))
  have h₂ : deriv (fun t => f (a * x) t (c * z)) (b * y) = L e₂ := by
    simpa [F, p, e₂, L, uncurry₃] using
      (deriv_affine_at (F := F) hf p e₂ (b * y))
  have h₃ : deriv (fun t => f (a * x) (b * y) t) (c * z) = L e₃ := by
    simpa [F, p, e₃, L, uncurry₃] using
      (deriv_affine_at (F := F) hf p e₃ (c * z))
  have hv : v = (a * dx) • e₁ + (b * dy) • e₂ + (c * dz) • e₃ := by
    ext <;> simp [v, e₁, e₂, e₃]
  change deriv (fun s : ℝ => F (a * (x + s * dx), b * (y + s * dy), c * (z + s * dz))) 0 = _
  rw [hline, hv]
  simp only [map_add, map_smul, smul_eq_mul]
  rw [← h₁, ← h₂, ← h₃]
  ring

theorem gap2 (u ξ η ζ f : ℝ → ℝ → ℝ → ℝ) (a b c : ℝ)
    (hu : ∀ x y z, u x y z = f (ξ x y z) (η x y z) (ζ x y z))
    (hξ : ∀ x y z, ξ x y z = a * x)
    (hη : ∀ x y z, η x y z = b * y)
    (hζ : ∀ x y z, ζ x y z = c * z)
    (hf : ContDiff ℝ 2 (uncurry₃ f))
    (x y z dx dy dz : ℝ) :
    nthDifferential 2 u x y z dx dy dz =
      a ^ 2 * partial11 f (ξ x y z) (η x y z) (ζ x y z) * dx ^ 2 +
        b ^ 2 * partial22 f (ξ x y z) (η x y z) (ζ x y z) * dy ^ 2 +
        c ^ 2 * partial33 f (ξ x y z) (η x y z) (ζ x y z) * dz ^ 2 +
        2 * a * b * partial12 f (ξ x y z) (η x y z) (ζ x y z) * dx * dy +
        2 * a * c * partial13 f (ξ x y z) (η x y z) (ζ x y z) * dx * dz +
        2 * b * c * partial23 f (ξ x y z) (η x y z) (ζ x y z) * dy * dz := by
  classical
  simp only [nthDifferential, iterDeriv, Function.iterate_succ_apply,
    Function.iterate_zero_apply]
  simp_rw [hu, hξ, hη, hζ]
  unfold partial11 partial12 partial13 partial22 partial23 partial33
  let F : ℝ × ℝ × ℝ → ℝ := uncurry₃ f
  let p : ℝ × ℝ × ℝ := (a * x, b * y, c * z)
  let v : ℝ × ℝ × ℝ := (a * dx, b * dy, c * dz)
  let e₁ : ℝ × ℝ × ℝ := (1, 0, 0)
  let e₂ : ℝ × ℝ × ℝ := (0, 1, 0)
  let e₃ : ℝ × ℝ × ℝ := (0, 0, 1)
  let D := fderiv ℝ (fun q => fderiv ℝ F q) p
  have hfun :
      (fun s : ℝ => F (a * (x + s * dx), b * (y + s * dy), c * (z + s * dz))) =
        fun s : ℝ => F (p + (s - 0) • v) := by
    funext s
    apply congrArg F
    ext <;> dsimp [p, v] <;> ring
  have hline :
      deriv (deriv fun s : ℝ =>
        F (a * (x + s * dx), b * (y + s * dy), c * (z + s * dz))) 0 = D v v := by
    rw [hfun]
    exact second_deriv_affine_at (F := F) hf p v 0
  have h₁₁ := second_deriv_affine_at (F := F) hf p e₁ (a * x)
  have h₂₂ := second_deriv_affine_at (F := F) hf p e₂ (b * y)
  have h₃₃ := second_deriv_affine_at (F := F) hf p e₃ (c * z)
  have h₁₂ := mixed_deriv_affine_at (F := F) hf p e₁ e₂ (a * x) (b * y)
  have h₁₃ := mixed_deriv_affine_at (F := F) hf p e₁ e₃ (a * x) (c * z)
  have h₂₃ := mixed_deriv_affine_at (F := F) hf p e₂ e₃ (b * y) (c * z)
  have hsymm : ∀ w₁ w₂, D w₁ w₂ = D w₂ w₁ := by
    intro w₁ w₂
    exact hf.contDiffAt.isSymmSndFDerivAt (by norm_num [minSmoothness]) w₁ w₂
  have hv : v = (a * dx) • e₁ + (b * dy) • e₂ + (c * dz) • e₃ := by
    ext <;> simp [v, e₁, e₂, e₃]
  have hbilinear :
      D v v =
        (a * dx) * (a * dx) * D e₁ e₁ +
        (b * dy) * (b * dy) * D e₂ e₂ +
        (c * dz) * (c * dz) * D e₃ e₃ +
        2 * (a * dx) * (b * dy) * D e₂ e₁ +
        2 * (a * dx) * (c * dz) * D e₃ e₁ +
        2 * (b * dy) * (c * dz) * D e₃ e₂ := by
    rw [hv]
    simp only [map_add, map_smul, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [hsymm e₁ e₂, hsymm e₁ e₃, hsymm e₂ e₃]
    ring
  have h₁₁' : D e₁ e₁ = deriv^[2] (fun t => f t (b * y) (c * z)) (a * x) := by
    simpa [F, p, e₁, D, uncurry₃, Function.iterate_succ_apply,
      Function.iterate_zero_apply] using h₁₁.symm
  have h₂₂' : D e₂ e₂ = deriv^[2] (fun t => f (a * x) t (c * z)) (b * y) := by
    simpa [F, p, e₂, D, uncurry₃, Function.iterate_succ_apply,
      Function.iterate_zero_apply] using h₂₂.symm
  have h₃₃' : D e₃ e₃ = deriv^[2] (fun t => f (a * x) (b * y) t) (c * z) := by
    simpa [F, p, e₃, D, uncurry₃, Function.iterate_succ_apply,
      Function.iterate_zero_apply] using h₃₃.symm
  have h₁₂' : D e₂ e₁ = deriv (fun t => partial1 f (a * x) t (c * z)) (b * y) := by
    simpa [F, p, e₁, e₂, D, partial1, uncurry₃] using h₁₂.symm
  have h₁₃' : D e₃ e₁ = deriv (fun t => partial1 f (a * x) (b * y) t) (c * z) := by
    simpa [F, p, e₁, e₃, D, partial1, uncurry₃] using h₁₃.symm
  have h₂₃' : D e₃ e₂ = deriv (fun t => partial2 f (a * x) (b * y) t) (c * z) := by
    simpa [F, p, e₂, e₃, D, partial2, uncurry₃] using h₂₃.symm
  change deriv (deriv fun s : ℝ =>
    F (a * (x + s * dx), b * (y + s * dy), c * (z + s * dz))) 0 = _
  rw [hline, hbilinear, h₁₁', h₂₂', h₃₃', h₁₂', h₁₃', h₂₃']
  ring

end

end ProofGap.Exercise3300
