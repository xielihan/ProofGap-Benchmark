import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3296

noncomputable section

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  (deriv^[n]) f

def nthDifferential (n : ℕ) (u : ℝ → ℝ → ℝ → ℝ)
    (x y z dx dy dz : ℝ) : ℝ :=
  iterDeriv n
    (fun s => u (x + s * dx) (y + s * dy) (z + s * dz)) 0

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

private theorem hasDerivAt_uncurry₂_affine_fderiv
    (f : ℝ → ℝ → ℝ)
    (hf : Differentiable ℝ (uncurry₂ f))
    (a b da db s : ℝ) :
    HasDerivAt
      (fun t : ℝ => f (a + t * da) (b + t * db))
      (fderiv ℝ (uncurry₂ f) (a + s * da, b + s * db) (da, db))
      s := by
  have hline :
      HasDerivAt
        (fun t : ℝ => (a + t * da, b + t * db))
        (da, db) s := by
    simpa [smul_eq_mul] using
      ((hasDerivAt_const (x := s) ((a, b) : ℝ × ℝ)).add
        ((hasDerivAt_id s).smul_const ((da, db) : ℝ × ℝ)))
  have hF := (hf (a + s * da, b + s * db)).hasFDerivAt
  simpa [uncurry₂] using hF.comp_hasDerivAt s hline

private theorem partials_eq_fderiv
    (f : ℝ → ℝ → ℝ)
    (hf : Differentiable ℝ (uncurry₂ f)) (a b : ℝ) :
    partial1 f a b =
        fderiv ℝ (uncurry₂ f) (a, b) ((1, 0) : ℝ × ℝ) ∧
      partial2 f a b =
        fderiv ℝ (uncurry₂ f) (a, b) ((0, 1) : ℝ × ℝ) := by
  constructor
  · simpa [partial1] using
      (hasDerivAt_uncurry₂_affine_fderiv f hf 0 b 1 0 a).deriv
  · simpa [partial2] using
      (hasDerivAt_uncurry₂_affine_fderiv f hf a 0 0 1 b).deriv

private theorem hasDerivAt_uncurry₂_affine
    (f : ℝ → ℝ → ℝ)
    (hf : Differentiable ℝ (uncurry₂ f))
    (a b da db s : ℝ) :
    HasDerivAt
      (fun t : ℝ => f (a + t * da) (b + t * db))
      (partial1 f (a + s * da) (b + s * db) * da +
        partial2 f (a + s * da) (b + s * db) * db)
      s := by
  have hcomp :=
    hasDerivAt_uncurry₂_affine_fderiv f hf a b da db s
  have hp :=
    partials_eq_fderiv f hf (a + s * da) (b + s * db)
  let F := fderiv ℝ (uncurry₂ f) (a + s * da, b + s * db)
  have hvec :
      ((da, db) : ℝ × ℝ) =
        da • ((1, 0) : ℝ × ℝ) + db • ((0, 1) : ℝ × ℝ) := by
    ext <;> simp
  have hv :
      fderiv ℝ (uncurry₂ f) (a + s * da, b + s * db) (da, db) =
        partial1 f (a + s * da) (b + s * db) * da +
          partial2 f (a + s * da) (b + s * db) * db := by
    change F (da, db) = _
    rw [hvec, map_add, map_smul, map_smul]
    change
      da * F ((1, 0) : ℝ × ℝ) + db * F ((0, 1) : ℝ × ℝ) = _
    rw [← hp.1, ← hp.2]
    ring
  rw [hv] at hcomp
  exact hcomp

private theorem fderiv_fderiv_apply
    (F : ℝ × ℝ → ℝ)
    (hDF : Differentiable ℝ (fderiv ℝ F))
    (p v w : ℝ × ℝ) :
    fderiv ℝ (fun q : ℝ × ℝ => fderiv ℝ F q v) p w =
      fderiv ℝ (fderiv ℝ F) p w v := by
  have hA :
      HasFDerivAt (fderiv ℝ F)
        (fderiv ℝ (fderiv ℝ F) p) p :=
    (hDF p).hasFDerivAt
  have hB :
      HasFDerivAt (fun _ : ℝ × ℝ => v)
        (0 : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) p :=
    hasFDerivAt_const (x := p) v
  have h := hA.clm_apply hB
  have heq :=
    congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L w) h.fderiv
  simpa using heq

theorem gap1 (u : ℝ → ℝ → ℝ → ℝ) (f : ℝ → ℝ → ℝ)
    (hu : ∀ x y z, u x y z = f (x + y) z)
    (hf : ContDiff ℝ 1 (uncurry₂ f))
    (x y z dx dy dz : ℝ) :
    nthDifferential 1 u x y z dx dy dz =
      partial1 f (x + y) z * (dx + dy) +
        partial2 f (x + y) z * dz := by
  have hfd : Differentiable ℝ (uncurry₂ f) :=
    hf.differentiable (by norm_num)
  have hcurve :
      (fun s : ℝ => u (x + s * dx) (y + s * dy) (z + s * dz)) =
        (fun s : ℝ => f (x + y + s * (dx + dy)) (z + s * dz)) := by
    funext s
    rw [hu]
    congr 1 <;> ring
  unfold nthDifferential iterDeriv
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]
  rw [hcurve]
  simpa using
    (hasDerivAt_uncurry₂_affine f hfd (x + y) z (dx + dy) dz 0).deriv

theorem gap2 (u : ℝ → ℝ → ℝ → ℝ) (f : ℝ → ℝ → ℝ)
    (hu : ∀ x y z, u x y z = f (x + y) z)
    (hf : ContDiff ℝ 2 (uncurry₂ f))
    (x y z dx dy dz : ℝ) :
    nthDifferential 2 u x y z dx dy dz =
      partial11 f (x + y) z * (dx + dy) ^ 2 +
        2 * partial12 f (x + y) z * (dx + dy) * dz +
        partial22 f (x + y) z * dz ^ 2 := by
  have hstep :=
    (contDiff_succ_iff_fderiv (𝕜 := ℝ) (n := 1)
      (f := uncurry₂ f)).mp (by simpa using hf)
  have hfd : Differentiable ℝ (uncurry₂ f) := hstep.1
  have hcurve :
      (fun s : ℝ => u (x + s * dx) (y + s * dy) (z + s * dz)) =
        (fun s : ℝ => f (x + y + s * (dx + dy)) (z + s * dz)) := by
    funext s
    rw [hu]
    congr 1 <;> ring
  have hDf : ContDiff ℝ 1 (fderiv ℝ (uncurry₂ f)) := hstep.2.2
  have hDfd : Differentiable ℝ (fderiv ℝ (uncurry₂ f)) :=
    hDf.differentiable (by norm_num)
  have hP1raw :
      ContDiff ℝ 1
        (fun p : ℝ × ℝ =>
          fderiv ℝ (uncurry₂ f) p ((1, 0) : ℝ × ℝ)) := by
    fun_prop
  have hP2raw :
      ContDiff ℝ 1
        (fun p : ℝ × ℝ =>
          fderiv ℝ (uncurry₂ f) p ((0, 1) : ℝ × ℝ)) := by
    fun_prop
  have heq1 :
      uncurry₂ (partial1 f) =
        (fun p : ℝ × ℝ =>
          fderiv ℝ (uncurry₂ f) p ((1, 0) : ℝ × ℝ)) := by
    funext p
    simpa [uncurry₂] using
      (partials_eq_fderiv f hfd p.1 p.2).1
  have heq2 :
      uncurry₂ (partial2 f) =
        (fun p : ℝ × ℝ =>
          fderiv ℝ (uncurry₂ f) p ((0, 1) : ℝ × ℝ)) := by
    funext p
    simpa [uncurry₂] using
      (partials_eq_fderiv f hfd p.1 p.2).2
  have hP1 : ContDiff ℝ 1 (uncurry₂ (partial1 f)) := by
    rw [heq1]
    exact hP1raw
  have hP2 : ContDiff ℝ 1 (uncurry₂ (partial2 f)) := by
    rw [heq2]
    exact hP2raw
  have hP1d : Differentiable ℝ (uncurry₂ (partial1 f)) :=
    hP1.differentiable (by norm_num)
  have hP2d : Differentiable ℝ (uncurry₂ (partial2 f)) :=
    hP2.differentiable (by norm_num)
  have hfirst :
      deriv
          (fun s : ℝ =>
            f (x + y + s * (dx + dy)) (z + s * dz)) =
        (fun s : ℝ =>
          partial1 f (x + y + s * (dx + dy)) (z + s * dz) *
              (dx + dy) +
            partial2 f (x + y + s * (dx + dy)) (z + s * dz) * dz) := by
    funext s
    exact
      (hasDerivAt_uncurry₂_affine f hfd (x + y) z
          (dx + dy) dz s).deriv
  have hd1 :=
    hasDerivAt_uncurry₂_affine (partial1 f) hP1d
      (x + y) z (dx + dy) dz 0
  have hd2 :=
    hasDerivAt_uncurry₂_affine (partial2 f) hP2d
      (x + y) z (dx + dy) dz 0
  have hsecond :
      deriv
          (fun s : ℝ =>
            partial1 f (x + y + s * (dx + dy)) (z + s * dz) *
                (dx + dy) +
              partial2 f (x + y + s * (dx + dy)) (z + s * dz) * dz)
          0 =
        (partial1 (partial1 f) (x + y) z * (dx + dy) +
              partial2 (partial1 f) (x + y) z * dz) *
            (dx + dy) +
          (partial1 (partial2 f) (x + y) z * (dx + dy) +
              partial2 (partial2 f) (x + y) z * dz) * dz := by
    simpa using
      ((hd1.mul_const (dx + dy)).add (hd2.mul_const dz)).deriv
  have h11 :
      partial1 (partial1 f) (x + y) z = partial11 f (x + y) z := by
    simp [partial1, partial11, Function.iterate_succ_apply]
  have h12 :
      partial2 (partial1 f) (x + y) z = partial12 f (x + y) z := by
    rfl
  have h22 :
      partial2 (partial2 f) (x + y) z = partial22 f (x + y) z := by
    simp [partial2, partial22, Function.iterate_succ_apply]
  have hmixed :
      partial1 (partial2 f) (x + y) z = partial12 f (x + y) z := by
    have hm2 := (partials_eq_fderiv (partial2 f) hP2d (x + y) z).1
    have hm1 := (partials_eq_fderiv (partial1 f) hP1d (x + y) z).2
    rw [heq2] at hm2
    rw [heq1] at hm1
    have hca : ContDiffAt ℝ 2 (uncurry₂ f) (x + y, z) := hf.contDiffAt
    have hmin : minSmoothness ℝ 2 ≤ 2 := by
      simp
    have hcl :
        fderiv ℝ
              (fun p : ℝ × ℝ =>
                fderiv ℝ (uncurry₂ f) p ((0, 1) : ℝ × ℝ))
              (x + y, z) ((1, 0) : ℝ × ℝ) =
          fderiv ℝ
              (fun p : ℝ × ℝ =>
                fderiv ℝ (uncurry₂ f) p ((1, 0) : ℝ × ℝ))
              (x + y, z) ((0, 1) : ℝ × ℝ) := by
      calc
        fderiv ℝ
              (fun p : ℝ × ℝ =>
                fderiv ℝ (uncurry₂ f) p ((0, 1) : ℝ × ℝ))
              (x + y, z) ((1, 0) : ℝ × ℝ) =
            fderiv ℝ (fderiv ℝ (uncurry₂ f)) (x + y, z)
              ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ) :=
          fderiv_fderiv_apply (uncurry₂ f) hDfd (x + y, z)
            ((0, 1) : ℝ × ℝ) ((1, 0) : ℝ × ℝ)
        _ = fderiv ℝ (fderiv ℝ (uncurry₂ f)) (x + y, z)
              ((0, 1) : ℝ × ℝ) ((1, 0) : ℝ × ℝ) :=
          hca.isSymmSndFDerivAt hmin
            ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ)
        _ = fderiv ℝ
              (fun p : ℝ × ℝ =>
                fderiv ℝ (uncurry₂ f) p ((1, 0) : ℝ × ℝ))
              (x + y, z) ((0, 1) : ℝ × ℝ) :=
          (fderiv_fderiv_apply (uncurry₂ f) hDfd (x + y, z)
            ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ)).symm
    calc
      partial1 (partial2 f) (x + y) z =
          fderiv ℝ
              (fun p : ℝ × ℝ =>
                fderiv ℝ (uncurry₂ f) p ((0, 1) : ℝ × ℝ))
              (x + y, z) ((1, 0) : ℝ × ℝ) := hm2
      _ = fderiv ℝ
              (fun p : ℝ × ℝ =>
                fderiv ℝ (uncurry₂ f) p ((1, 0) : ℝ × ℝ))
              (x + y, z) ((0, 1) : ℝ × ℝ) := hcl
      _ = partial2 (partial1 f) (x + y) z := hm1.symm
      _ = partial12 f (x + y) z := h12
  unfold nthDifferential iterDeriv
  simp only [Function.iterate_succ_apply, Function.iterate_zero_apply]
  rw [hcurve, hfirst, hsecond, h11, h12, hmixed, h22]
  ring

end

end ProofGap.Exercise3296
