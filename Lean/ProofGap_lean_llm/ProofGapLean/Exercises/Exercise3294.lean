import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3294

noncomputable section

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  (deriv^[n]) f

def nthDifferential (n : ℕ) (u : ℝ → ℝ → ℝ)
    (x y dx dy : ℝ) : ℝ :=
  iterDeriv n (fun s => u (x + s * dx) (y + s * dy)) 0

def partial1 (f : ℝ → ℝ → ℝ) (a b : ℝ) : ℝ :=
  deriv (fun t => f t b) a

def partial2 (f : ℝ → ℝ → ℝ) (a b : ℝ) : ℝ :=
  deriv (fun t => f a t) b

def partial11 (f : ℝ → ℝ → ℝ) (a b : ℝ) : ℝ :=
  (deriv^[2]) (fun t => f t b) a

def partial12 (f : ℝ → ℝ → ℝ) (a b : ℝ) : ℝ :=
  deriv (fun t => partial1 f a t) b

def partial22 (f : ℝ → ℝ → ℝ) (a b : ℝ) : ℝ :=
  (deriv^[2]) (fun t => f a t) b

def uncurry₂ (f : ℝ → ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun p => f p.1 p.2

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

theorem gap1 (u ξ η f : ℝ → ℝ → ℝ)
    (hu : ∀ x y, u x y = f (ξ x y) (η x y))
    (hξ : ∀ x y, ξ x y = x + y)
    (hη : ∀ x y, η x y = x - y)
    (hf : ContDiff ℝ 1 (uncurry₂ f)) (x y dx dy : ℝ) :
    nthDifferential 1 u x y dx dy =
      partial1 f (ξ x y) (η x y) * (dx + dy) +
        partial2 f (ξ x y) (η x y) * (dx - dy) := by
  classical
  simp only [nthDifferential, iterDeriv, Function.iterate_one]
  simp_rw [hu, hξ, hη]
  unfold partial1 partial2
  let F : ℝ × ℝ → ℝ := uncurry₂ f
  let p : ℝ × ℝ := (x + y, x - y)
  let v : ℝ × ℝ := (dx + dy, dx - dy)
  let e₁ : ℝ × ℝ := (1, 0)
  let e₂ : ℝ × ℝ := (0, 1)
  let L := fderiv ℝ F p
  have hfun :
      (fun s : ℝ => F ((x + s * dx) + (y + s * dy),
        (x + s * dx) - (y + s * dy))) =
        fun s : ℝ => F (p + (s - 0) • v) := by
    funext s
    apply congrArg F
    ext <;> dsimp [p, v] <;> ring
  have hline :
      deriv (fun s : ℝ => F ((x + s * dx) + (y + s * dy),
        (x + s * dx) - (y + s * dy))) 0 = L v := by
    rw [hfun]
    exact deriv_affine_at (F := F) hf p v 0
  have h₁ : deriv (fun t => f t (x - y)) (x + y) = L e₁ := by
    simpa [F, p, e₁, L, uncurry₂] using
      (deriv_affine_at (F := F) hf p e₁ (x + y))
  have h₂ : deriv (fun t => f (x + y) t) (x - y) = L e₂ := by
    simpa [F, p, e₂, L, uncurry₂] using
      (deriv_affine_at (F := F) hf p e₂ (x - y))
  have hv : v = (dx + dy) • e₁ + (dx - dy) • e₂ := by
    ext <;> simp [v, e₁, e₂]
  change deriv (fun s : ℝ => F ((x + s * dx) + (y + s * dy),
    (x + s * dx) - (y + s * dy))) 0 = _
  rw [hline, hv]
  simp only [map_add, map_smul, smul_eq_mul]
  rw [← h₁, ← h₂]
  ring

theorem gap2 (u ξ η f : ℝ → ℝ → ℝ)
    (hu : ∀ x y, u x y = f (ξ x y) (η x y))
    (hξ : ∀ x y, ξ x y = x + y)
    (hη : ∀ x y, η x y = x - y)
    (hf : ContDiff ℝ 2 (uncurry₂ f)) (x y dx dy : ℝ) :
    nthDifferential 2 u x y dx dy =
      partial11 f (ξ x y) (η x y) * (dx + dy) ^ 2 +
        2 * partial12 f (ξ x y) (η x y) *
          (dx ^ 2 - dy ^ 2) +
        partial22 f (ξ x y) (η x y) * (dx - dy) ^ 2 := by
  classical
  simp only [nthDifferential, iterDeriv, Function.iterate_succ_apply,
    Function.iterate_zero_apply]
  simp_rw [hu, hξ, hη]
  unfold partial11 partial12 partial22
  let F : ℝ × ℝ → ℝ := uncurry₂ f
  let p : ℝ × ℝ := (x + y, x - y)
  let v : ℝ × ℝ := (dx + dy, dx - dy)
  let e₁ : ℝ × ℝ := (1, 0)
  let e₂ : ℝ × ℝ := (0, 1)
  let D := fderiv ℝ (fun q => fderiv ℝ F q) p
  have hfun :
      (fun s : ℝ => F ((x + s * dx) + (y + s * dy),
        (x + s * dx) - (y + s * dy))) =
        fun s : ℝ => F (p + (s - 0) • v) := by
    funext s
    apply congrArg F
    ext <;> dsimp [p, v] <;> ring
  have hline :
      deriv (deriv fun s : ℝ =>
        F ((x + s * dx) + (y + s * dy),
          (x + s * dx) - (y + s * dy))) 0 = D v v := by
    rw [hfun]
    exact second_deriv_affine_at (F := F) hf p v 0
  have h₁₁ := second_deriv_affine_at (F := F) hf p e₁ (x + y)
  have h₂₂ := second_deriv_affine_at (F := F) hf p e₂ (x - y)
  have h₁₂ := mixed_deriv_affine_at (F := F) hf p e₁ e₂ (x + y) (x - y)
  have hsymm : ∀ w₁ w₂, D w₁ w₂ = D w₂ w₁ := by
    intro w₁ w₂
    exact hf.contDiffAt.isSymmSndFDerivAt
      (by norm_num [minSmoothness]) w₁ w₂
  have hv : v = (dx + dy) • e₁ + (dx - dy) • e₂ := by
    ext <;> simp [v, e₁, e₂]
  have hbilinear :
      D v v =
        (dx + dy) ^ 2 * D e₁ e₁ +
        2 * (dx + dy) * (dx - dy) * D e₂ e₁ +
        (dx - dy) ^ 2 * D e₂ e₂ := by
    rw [hv]
    simp only [map_add, map_smul, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [hsymm e₁ e₂]
    ring
  have h₁₁' : D e₁ e₁ =
      deriv^[2] (fun t => f t (x - y)) (x + y) := by
    simpa [F, p, e₁, D, uncurry₂, Function.iterate_succ_apply,
      Function.iterate_zero_apply] using h₁₁.symm
  have h₂₂' : D e₂ e₂ =
      deriv^[2] (fun t => f (x + y) t) (x - y) := by
    simpa [F, p, e₂, D, uncurry₂, Function.iterate_succ_apply,
      Function.iterate_zero_apply] using h₂₂.symm
  have h₁₂' : D e₂ e₁ =
      deriv (fun t => partial1 f (x + y) t) (x - y) := by
    simpa [F, p, e₁, e₂, D, partial1, uncurry₂] using h₁₂.symm
  change deriv (deriv fun s : ℝ =>
    F ((x + s * dx) + (y + s * dy),
      (x + s * dx) - (y + s * dy))) 0 = _
  rw [hline, hbilinear, h₁₁', h₁₂', h₂₂']
  ring

end

end ProofGap.Exercise3294
