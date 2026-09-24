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

namespace ProofGap.Exercise3295

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

def productDirection (x y dx dy : ℝ) : ℝ :=
  y * dx + x * dy

def quotientNumerator (x y dx dy : ℝ) : ℝ :=
  y * dx - x * dy

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

theorem gap1 (u ξ η f : ℝ → ℝ → ℝ)
    (hu : ∀ x y, u x y = f (ξ x y) (η x y))
    (hξ : ∀ x y, ξ x y = x * y)
    (hη : ∀ x y, η x y = x / y)
    (hf : ContDiff ℝ 1 (uncurry₂ f))
    (x y dx dy : ℝ) (hy : y ≠ 0) :
    nthDifferential 1 u x y dx dy =
      partial1 f (ξ x y) (η x y) * productDirection x y dx dy +
        partial2 f (ξ x y) (η x y) / y ^ 2 *
          quotientNumerator x y dx dy := by
  have hfd : Differentiable ℝ (uncurry₂ f) :=
    hf.differentiable (by norm_num)
  change deriv (fun s => u (x + s * dx) (y + s * dy)) 0 = _
  simp_rw [hu, hξ, hη]
  have hX : HasDerivAt (fun s : ℝ => x + s * dx) dx 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const dx).const_add x
  have hY : HasDerivAt (fun s : ℝ => y + s * dy) dy 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const dy).const_add y
  have hA :
      HasDerivAt
        (fun s : ℝ => (x + s * dx) * (y + s * dy))
        (productDirection x y dx dy) 0 := by
    convert hX.mul hY using 1 <;> simp [productDirection] <;> ring
  have hB :
      HasDerivAt
        (fun s : ℝ => (x + s * dx) / (y + s * dy))
        (quotientNumerator x y dx dy / y ^ 2) 0 := by
    convert hX.div hY (by simpa using hy) using 1 <;>
      simp [quotientNumerator] <;> ring
  convert (hasDerivAt_uncurry₂_chain f hfd hA hB).deriv using 1 <;>
    field_simp [hy] <;> ring

theorem gap2 (u ξ η f : ℝ → ℝ → ℝ)
    (hu : ∀ x y, u x y = f (ξ x y) (η x y))
    (hξ : ∀ x y, ξ x y = x * y)
    (hη : ∀ x y, η x y = x / y)
    (hf : ContDiff ℝ 2 (uncurry₂ f))
    (x y dx dy : ℝ) (hy : y ≠ 0) :
    nthDifferential 2 u x y dx dy =
      partial11 f (ξ x y) (η x y) *
          (productDirection x y dx dy) ^ 2 +
        partial22 f (ξ x y) (η x y) / y ^ 4 *
          (quotientNumerator x y dx dy) ^ 2 +
        2 * partial12 f (ξ x y) (η x y) / y ^ 2 *
          (y ^ 2 * dx ^ 2 - x ^ 2 * dy ^ 2) +
        2 * partial1 f (ξ x y) (η x y) * dx * dy -
        2 * partial2 f (ξ x y) (η x y) / y ^ 3 *
          quotientNumerator x y dx dy * dy := by
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
  let X : ℝ → ℝ := fun s => x + s * dx
  let Y : ℝ → ℝ := fun s => y + s * dy
  let A : ℝ → ℝ := fun s => X s * Y s
  let B : ℝ → ℝ := fun s => X s / Y s
  let P : ℝ → ℝ := fun s => Y s * dx + X s * dy
  let Q : ℝ := quotientNumerator x y dx dy
  have hX (s : ℝ) : HasDerivAt X dx s := by
    dsimp [X]
    simpa using ((hasDerivAt_id s).mul_const dx).const_add x
  have hY (s : ℝ) : HasDerivAt Y dy s := by
    dsimp [Y]
    simpa using ((hasDerivAt_id s).mul_const dy).const_add y
  have hA (s : ℝ) : HasDerivAt A (P s) s := by
    dsimp [A, P]
    convert (hX s).mul (hY s) using 1 <;> ring
  have hB (s : ℝ) (hs : Y s ≠ 0) :
      HasDerivAt B (Q / Y s ^ 2) s := by
    dsimp [B]
    convert (hX s).div (hY s) hs using 1
    dsimp [Q, quotientNumerator, X, Y]
    field_simp [hs, hy]
    ring
  have hY0 : Y 0 ≠ 0 := by simpa [Y] using hy
  have hYn : ∀ᶠ s in nhds (0 : ℝ), Y s ≠ 0 :=
    (hY 0).continuousAt.eventually_ne hY0
  have hcurve :
      (fun s => u (x + s * dx) (y + s * dy)) =
        fun s => f (A s) (B s) := by
    funext s
    simp [hu, hξ, hη, A, B, X, Y]
  have hfirst :
      deriv (fun s => f (A s) (B s)) =ᶠ[nhds (0 : ℝ)]
        fun s =>
          partial1 f (A s) (B s) * P s +
            partial2 f (A s) (B s) * (Q / Y s ^ 2) := by
    filter_upwards [hYn] with s hs
    exact (hasDerivAt_uncurry₂_chain f hfd (hA s) (hB s hs)).deriv
  have hd1 :
      HasDerivAt (fun s => partial1 f (A s) (B s))
        (partial11 f (A 0) (B 0) * P 0 +
          partial12 f (A 0) (B 0) * (Q / Y 0 ^ 2)) 0 := by
    simpa [partial11, partial12, partial1,
      Function.iterate_succ_apply, Function.iterate_zero_apply] using
      hasDerivAt_uncurry₂_chain (partial1 f) hP1
        (hA 0) (hB 0 hY0)
  have hd2 :
      HasDerivAt (fun s => partial2 f (A s) (B s))
        (partial12 f (A 0) (B 0) * P 0 +
          partial22 f (A 0) (B 0) * (Q / Y 0 ^ 2)) 0 := by
    convert hasDerivAt_uncurry₂_chain (partial2 f) hP2
      (hA 0) (hB 0 hY0) using 1
    rw [mixed_partials f hf]
    simp [partial22, partial2, Function.iterate_succ_apply,
      Function.iterate_zero_apply]
  have hP :
      HasDerivAt P (2 * dx * dy) 0 := by
    dsimp [P]
    convert ((hY 0).mul_const dx).add ((hX 0).mul_const dy)
      using 1 <;> ring
  have hC :
      HasDerivAt (fun s => Q / Y s ^ 2)
        (-2 * Q * dy / y ^ 3) 0 := by
    have hsq := (hY 0).pow 2
    convert (hasDerivAt_const (0 : ℝ) Q).div hsq
      (by simpa [Y] using pow_ne_zero 2 hy) using 1 <;>
      simp [Y] <;> field_simp [hy] <;> ring
  have hsecond :
      deriv
        (fun s =>
          partial1 f (A s) (B s) * P s +
            partial2 f (A s) (B s) * (Q / Y s ^ 2)) 0 =
        (partial11 f (A 0) (B 0) * P 0 +
            partial12 f (A 0) (B 0) * (Q / Y 0 ^ 2)) * P 0 +
          partial1 f (A 0) (B 0) * (2 * dx * dy) +
          (partial12 f (A 0) (B 0) * P 0 +
            partial22 f (A 0) (B 0) * (Q / Y 0 ^ 2)) *
              (Q / Y 0 ^ 2) +
          partial2 f (A 0) (B 0) * (-2 * Q * dy / y ^ 3) := by
    convert ((hd1.mul hP).add (hd2.mul hC)).deriv using 1 <;> ring
  change deriv (deriv (fun s => u (x + s * dx) (y + s * dy))) 0 = _
  rw [hcurve, hfirst.deriv_eq, hsecond]
  simp [A, B, P, Q, X, Y, productDirection, quotientNumerator]
  simp only [hξ, hη]
  field_simp [hy]
  ring

end

end ProofGap.Exercise3295
