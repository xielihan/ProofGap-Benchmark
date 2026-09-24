import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3284

noncomputable section

def partialX (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => g t y) x

def partialY (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => g x t) y

def partialXX (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  (deriv^[2]) (fun t => g t y) x

def partialYY (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  (deriv^[2]) (fun t => g x t) y

def partialXY (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialX g x t) y

def u (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  f x (x / y)

def uncurry₂ (f : ℝ → ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun p => f p.1 p.2

private abbrev partial1 := partialX
private abbrev partial2 := partialY
private abbrev partial11 := partialXX
private abbrev partial12 := partialXY
private abbrev partial22 := partialYY

private theorem hasDerivAt_uncurry₂_chain
    (f : ℝ → ℝ → ℝ) (hf : Differentiable ℝ (uncurry₂ f))
    {A B : ℝ → ℝ} {s dA dB : ℝ}
    (hA : HasDerivAt A dA s) (hB : HasDerivAt B dB s) :
    HasDerivAt (fun t => f (A t) (B t))
      (partial1 f (A s) (B s) * dA +
        partial2 f (A s) (B s) * dB) s := by
  have hcomp :=
    (hf (A s, B s)).hasFDerivAt.comp s (hA.prodMk hB)
  have h₁ :
      partial1 f (A s) (B s) =
        fderiv ℝ (uncurry₂ f) (A s, B s) (1, 0) := by
    have h :=
      (hf (A s, B s)).hasFDerivAt.comp (A s)
        ((hasDerivAt_id (A s)).prodMk
          (hasDerivAt_const (x := A s) (c := B s)))
    simpa [partial1, uncurry₂, Function.comp_def] using
      h.hasDerivAt.deriv
  have h₂ :
      partial2 f (A s) (B s) =
        fderiv ℝ (uncurry₂ f) (A s, B s) (0, 1) := by
    have h :=
      (hf (A s, B s)).hasFDerivAt.comp (B s)
        ((hasDerivAt_const (x := B s) (c := A s)).prodMk
          (hasDerivAt_id (B s)))
    simpa [partial2, uncurry₂, Function.comp_def] using
      h.hasDerivAt.deriv
  have hv : (dA, dB) =
      dA • ((1, 0) : ℝ × ℝ) + dB • ((0, 1) : ℝ × ℝ) := by
    ext <;> simp
  convert hcomp.hasDerivAt using 1
  simp only [ContinuousLinearMap.comp_apply]
  simp only [ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.toSpanSingleton_apply, one_smul]
  change partial1 f (A s) (B s) * dA +
      partial2 f (A s) (B s) * dB =
    fderiv ℝ (uncurry₂ f) (A s, B s) (dA, dB)
  rw [hv, map_add, map_smul, map_smul, ← h₁, ← h₂]
  simp [smul_eq_mul]
  ring

private theorem partials_eq_fderiv
    (f : ℝ → ℝ → ℝ)
    (hf : Differentiable ℝ (uncurry₂ f)) (a b : ℝ) :
    partial1 f a b =
        fderiv ℝ (uncurry₂ f) (a, b) ((1, 0) : ℝ × ℝ) ∧
      partial2 f a b =
        fderiv ℝ (uncurry₂ f) (a, b) ((0, 1) : ℝ × ℝ) := by
  constructor
  · have h :=
      (hf (a, b)).hasFDerivAt.comp a
        ((hasDerivAt_id a).prodMk (hasDerivAt_const (x := a) (c := b)))
    simpa [partial1, uncurry₂, Function.comp_def] using
      h.hasDerivAt.deriv
  · have h :=
      (hf (a, b)).hasFDerivAt.comp b
        ((hasDerivAt_const (x := b) (c := a)).prodMk (hasDerivAt_id b))
    simpa [partial2, uncurry₂, Function.comp_def] using
      h.hasDerivAt.deriv

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

private theorem mixed_partials
    (f : ℝ → ℝ → ℝ) (hf : ContDiff ℝ 2 (uncurry₂ f))
    (a b : ℝ) :
    partial1 (partial2 f) a b = partial12 f a b := by
  have hstep :=
    (contDiff_succ_iff_fderiv (𝕜 := ℝ) (n := 1)
      (f := uncurry₂ f)).mp (by simpa using hf)
  have hfd : Differentiable ℝ (uncurry₂ f) := hstep.1
  have hDfd : Differentiable ℝ (fderiv ℝ (uncurry₂ f)) :=
    hstep.2.2.differentiable (by norm_num)
  have heq1 :
      uncurry₂ (partial1 f) =
        fun p : ℝ × ℝ =>
          fderiv ℝ (uncurry₂ f) p ((1, 0) : ℝ × ℝ) := by
    funext p
    simpa [uncurry₂] using
      (partials_eq_fderiv f hfd p.1 p.2).1
  have heq2 :
      uncurry₂ (partial2 f) =
        fun p : ℝ × ℝ =>
          fderiv ℝ (uncurry₂ f) p ((0, 1) : ℝ × ℝ) := by
    funext p
    simpa [uncurry₂] using
      (partials_eq_fderiv f hfd p.1 p.2).2
  have hP1 : Differentiable ℝ (uncurry₂ (partial1 f)) := by
    rw [heq1]
    fun_prop
  have hP2 : Differentiable ℝ (uncurry₂ (partial2 f)) := by
    rw [heq2]
    fun_prop
  have hm2 := (partials_eq_fderiv (partial2 f) hP2 a b).1
  have hm1 := (partials_eq_fderiv (partial1 f) hP1 a b).2
  rw [heq2] at hm2
  rw [heq1] at hm1
  calc
    partial1 (partial2 f) a b =
        fderiv ℝ (fderiv ℝ (uncurry₂ f)) (a, b)
          ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ) := by
      rw [hm2]
      exact fderiv_fderiv_apply _ hDfd _ _ _
    _ = fderiv ℝ (fderiv ℝ (uncurry₂ f)) (a, b)
          ((0, 1) : ℝ × ℝ) ((1, 0) : ℝ × ℝ) :=
      hf.contDiffAt.isSymmSndFDerivAt
        (by norm_num [minSmoothness]) _ _
    _ = partial2 (partial1 f) a b := by
      rw [hm1]
      exact (fderiv_fderiv_apply _ hDfd _ _ _).symm
    _ = partial12 f a b := rfl

private theorem differentiated_partials
    (f : ℝ → ℝ → ℝ) (hf : ContDiff ℝ 2 (uncurry₂ f)) :
    Differentiable ℝ (uncurry₂ (partialX f)) ∧
      Differentiable ℝ (uncurry₂ (partialY f)) := by
  have hstep :=
    (contDiff_succ_iff_fderiv (𝕜 := ℝ) (n := 1)
      (f := uncurry₂ f)).mp (by simpa using hf)
  have hfd : Differentiable ℝ (uncurry₂ f) := hstep.1
  have heq1 :
      uncurry₂ (partialX f) =
        fun p : ℝ × ℝ =>
          fderiv ℝ (uncurry₂ f) p ((1, 0) : ℝ × ℝ) := by
    funext p
    simpa [uncurry₂] using
      (partials_eq_fderiv f hfd p.1 p.2).1
  have heq2 :
      uncurry₂ (partialY f) =
        fun p : ℝ × ℝ =>
          fderiv ℝ (uncurry₂ f) p ((0, 1) : ℝ × ℝ) := by
    funext p
    simpa [uncurry₂] using
      (partials_eq_fderiv f hfd p.1 p.2).2
  constructor
  · rw [heq1]
    fun_prop
  · rw [heq2]
    fun_prop

private theorem nested_xx (f : ℝ → ℝ → ℝ) (a b : ℝ) :
    partialX (partialX f) a b = partialXX f a b := by
  simp [partialX, partialXX, Function.iterate_succ_apply]

private theorem nested_xy (f : ℝ → ℝ → ℝ) (a b : ℝ) :
    partialY (partialX f) a b = partialXY f a b := rfl

private theorem nested_yy (f : ℝ → ℝ → ℝ) (a b : ℝ) :
    partialY (partialY f) a b = partialYY f a b := by
  simp [partialY, partialYY, Function.iterate_succ_apply]


theorem gap1 (f : ℝ → ℝ → ℝ)
    (hf : ContDiff ℝ 1 (uncurry₂ f))
    (x y : ℝ) (hy : y ≠ 0) :
    partialX (u f) x y =
      partialX f x (x / y) + (1 / y) * partialY f x (x / y) := by
  have hfd : Differentiable ℝ (uncurry₂ f) :=
    hf.differentiable (by norm_num)
  unfold partialX u
  have hA : HasDerivAt (fun t : ℝ => t) 1 x := hasDerivAt_id x
  have hB : HasDerivAt (fun t : ℝ => t / y) (1 / y) x := by
    simpa using (hasDerivAt_id x).div_const y
  convert (hasDerivAt_uncurry₂_chain f hfd hA hB).deriv using 1 <;>
    simp only [partial1, partial2, partialX, partialY] <;> ring

theorem gap2 (f : ℝ → ℝ → ℝ)
    (hf : ContDiff ℝ 1 (uncurry₂ f))
    (x y : ℝ) (hy : y ≠ 0) :
    partialY (u f) x y =
      -(x / y ^ 2) * partialY f x (x / y) := by
  have hfd : Differentiable ℝ (uncurry₂ f) :=
    hf.differentiable (by norm_num)
  unfold partialY u
  have hA : HasDerivAt (fun _ : ℝ => x) 0 y :=
    hasDerivAt_const y x
  have hB : HasDerivAt (fun t : ℝ => x / t) (-x / y ^ 2) y := by
    convert (hasDerivAt_const y x).div (hasDerivAt_id y) hy using 1 <;>
      simp only [id_eq] <;> field_simp [hy] <;> ring
  convert (hasDerivAt_uncurry₂_chain f hfd hA hB).deriv using 1 <;>
    simp only [partial1, partial2, partialX, partialY] <;> ring

theorem gap3 (f : ℝ → ℝ → ℝ)
    (hf : ContDiff ℝ 2 (uncurry₂ f))
    (x y : ℝ) (hy : y ≠ 0) :
    partialXX (u f) x y =
      partialXX f x (x / y) +
        (2 / y) * partialXY f x (x / y) +
        (1 / y ^ 2) * partialYY f x (x / y) := by
  have hf1 : ContDiff ℝ 1 (uncurry₂ f) :=
    hf.of_le (by norm_num)
  have hpd := differentiated_partials f hf
  have hA : HasDerivAt (fun t : ℝ => t) 1 x := hasDerivAt_id x
  have hB : HasDerivAt (fun t : ℝ => t / y) (1 / y) x := by
    simpa using (hasDerivAt_id x).div_const y
  have hd1 :=
    hasDerivAt_uncurry₂_chain (partialX f) hpd.1 hA hB
  have hd2 :=
    hasDerivAt_uncurry₂_chain (partialY f) hpd.2 hA hB
  have heq :
      (fun t => partialX (u f) t y) =
        fun t =>
          partialX f t (t / y) + (1 / y) * partialY f t (t / y) := by
    funext t
    exact gap1 f hf1 t y hy
  change deriv (fun t => partialX (u f) t y) x = _
  rw [heq]
  have hraw :=
    (hd1.add (hd2.const_mul (1 / y))).deriv
  rw [mixed_partials f hf] at hraw
  simp only [partial1, partial2, partial11, partial12, partial22] at hraw
  rw [nested_xx, nested_xy, nested_yy] at hraw
  convert hraw using 1 <;>
    field_simp [hy] <;> ring

theorem gap4 (f : ℝ → ℝ → ℝ)
    (hf : ContDiff ℝ 2 (uncurry₂ f))
    (x y : ℝ) (hy : y ≠ 0) :
    partialYY (u f) x y =
      (2 * x / y ^ 3) * partialY f x (x / y) +
        (x ^ 2 / y ^ 4) * partialYY f x (x / y) := by
  have hf1 : ContDiff ℝ 1 (uncurry₂ f) :=
    hf.of_le (by norm_num)
  have hpd := differentiated_partials f hf
  have hA : HasDerivAt (fun _ : ℝ => x) 0 y :=
    hasDerivAt_const y x
  have hB : HasDerivAt (fun t : ℝ => x / t) (-x / y ^ 2) y := by
    convert (hasDerivAt_const y x).div (hasDerivAt_id y) hy using 1 <;>
      simp only [id_eq] <;> field_simp [hy] <;> ring
  have hd2 :=
    hasDerivAt_uncurry₂_chain (partialY f) hpd.2 hA hB
  have hc :
      HasDerivAt (fun t : ℝ => -(x / t ^ 2)) (2 * x / y ^ 3) y := by
    have h :=
      (hasDerivAt_const (x := y) (-x)).div
        ((hasDerivAt_id y).pow 2) (pow_ne_zero 2 hy)
    convert h using 1
    · funext t
      simp only [Pi.div_apply, Pi.pow_apply, id_eq]
      ring
    · simp only [Pi.pow_apply, id_eq]
      field_simp [hy]
      ring
  have hne : ∀ᶠ t in nhds y, t ≠ 0 :=
    (hasDerivAt_id y).continuousAt.eventually_ne hy
  have heq :
      (fun t => partialY (u f) x t) =ᶠ[nhds y]
        fun t => -(x / t ^ 2) * partialY f x (x / t) := by
    filter_upwards [hne] with t ht
    exact gap2 f hf1 x t ht
  change deriv (fun t => partialY (u f) x t) y = _
  rw [heq.deriv_eq]
  have hraw := (hc.mul hd2).deriv
  simp only [partial1, partial2, partial11, partial12, partial22] at hraw
  rw [nested_yy] at hraw
  convert hraw using 1 <;>
    field_simp [hy] <;> ring

theorem gap5 (f : ℝ → ℝ → ℝ)
    (hf : ContDiff ℝ 2 (uncurry₂ f))
    (x y : ℝ) (hy : y ≠ 0) :
    partialXY (u f) x y =
      -(x / y ^ 2) * partialXY f x (x / y) -
        (1 / y ^ 2) * partialY f x (x / y) -
        (x / y ^ 3) * partialYY f x (x / y) := by
  have hf1 : ContDiff ℝ 1 (uncurry₂ f) :=
    hf.of_le (by norm_num)
  have hpd := differentiated_partials f hf
  have hA : HasDerivAt (fun _ : ℝ => x) 0 y :=
    hasDerivAt_const y x
  have hB : HasDerivAt (fun t : ℝ => x / t) (-x / y ^ 2) y := by
    convert (hasDerivAt_const y x).div (hasDerivAt_id y) hy using 1 <;>
      simp only [id_eq] <;> field_simp [hy] <;> ring
  have hd1 :=
    hasDerivAt_uncurry₂_chain (partialX f) hpd.1 hA hB
  have hd2 :=
    hasDerivAt_uncurry₂_chain (partialY f) hpd.2 hA hB
  have hc :
      HasDerivAt (fun t : ℝ => 1 / t) (-1 / y ^ 2) y := by
    convert (hasDerivAt_const y (1 : ℝ)).div (hasDerivAt_id y) hy
      using 1 <;> simp only [id_eq] <;> field_simp [hy] <;> ring
  have hne : ∀ᶠ t in nhds y, t ≠ 0 :=
    (hasDerivAt_id y).continuousAt.eventually_ne hy
  have heq :
      (fun t => partialX (u f) x t) =ᶠ[nhds y]
        fun t =>
          partialX f x (x / t) + (1 / t) * partialY f x (x / t) := by
    filter_upwards [hne] with t ht
    exact gap1 f hf1 x t ht
  change deriv (fun t => partialX (u f) x t) y = _
  rw [heq.deriv_eq]
  have hraw := (hd1.add (hc.mul hd2)).deriv
  rw [mixed_partials f hf] at hraw
  simp only [partial1, partial2, partial11, partial12, partial22] at hraw
  rw [nested_xy, nested_yy] at hraw
  convert hraw using 1 <;>
    field_simp [hy] <;> ring

end

end ProofGap.Exercise3284
