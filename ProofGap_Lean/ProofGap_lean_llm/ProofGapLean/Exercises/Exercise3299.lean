import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3299

noncomputable section

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  (deriv^[n]) f

def partial1 (f : ℝ → ℝ → ℝ → ℝ) (a b c : ℝ) : ℝ :=
  deriv (fun s => f s b c) a

def partial2 (f : ℝ → ℝ → ℝ → ℝ) (a b c : ℝ) : ℝ :=
  deriv (fun s => f a s c) b

def partial3 (f : ℝ → ℝ → ℝ → ℝ) (a b c : ℝ) : ℝ :=
  deriv (fun s => f a b s) c

def partial11 (f : ℝ → ℝ → ℝ → ℝ) (a b c : ℝ) : ℝ :=
  (deriv^[2]) (fun s => f s b c) a

def partial12 (f : ℝ → ℝ → ℝ → ℝ) (a b c : ℝ) : ℝ :=
  deriv (fun s => partial1 f a s c) b

def partial13 (f : ℝ → ℝ → ℝ → ℝ) (a b c : ℝ) : ℝ :=
  deriv (fun s => partial1 f a b s) c

def partial22 (f : ℝ → ℝ → ℝ → ℝ) (a b c : ℝ) : ℝ :=
  (deriv^[2]) (fun s => f a s c) b

def partial23 (f : ℝ → ℝ → ℝ → ℝ) (a b c : ℝ) : ℝ :=
  deriv (fun s => partial2 f a b s) c

def partial33 (f : ℝ → ℝ → ℝ → ℝ) (a b c : ℝ) : ℝ :=
  (deriv^[2]) (fun s => f a b s) c

def uncurry₃ (f : ℝ → ℝ → ℝ → ℝ) : ℝ × ℝ × ℝ → ℝ :=
  fun p => f p.1 p.2.1 p.2.2

private abbrev Vec3 := ℝ × ℝ × ℝ

private theorem partials_eq_fderiv
    (f : ℝ → ℝ → ℝ → ℝ)
    (hf : Differentiable ℝ (uncurry₃ f)) (a b c : ℝ) :
    partial1 f a b c =
        fderiv ℝ (uncurry₃ f) (a, b, c) ((1, 0, 0) : Vec3) ∧
      partial2 f a b c =
        fderiv ℝ (uncurry₃ f) (a, b, c) ((0, 1, 0) : Vec3) ∧
      partial3 f a b c =
        fderiv ℝ (uncurry₃ f) (a, b, c) ((0, 0, 1) : Vec3) := by
  have h₁ :=
    (hf (a, b, c)).hasFDerivAt.comp a
      ((hasDerivAt_id a).prodMk
        ((hasDerivAt_const (x := a) (c := b)).prodMk
          (hasDerivAt_const (x := a) (c := c))))
  have h₂ :=
    (hf (a, b, c)).hasFDerivAt.comp b
      ((hasDerivAt_const (x := b) (c := a)).prodMk
        ((hasDerivAt_id b).prodMk
          (hasDerivAt_const (x := b) (c := c))))
  have h₃ :=
    (hf (a, b, c)).hasFDerivAt.comp c
      ((hasDerivAt_const (x := c) (c := a)).prodMk
        ((hasDerivAt_const (x := c) (c := b)).prodMk
          (hasDerivAt_id c)))
  constructor
  · simpa [partial1, uncurry₃, Function.comp_def] using
      h₁.hasDerivAt.deriv
  constructor
  · simpa [partial2, uncurry₃, Function.comp_def] using
      h₂.hasDerivAt.deriv
  · simpa [partial3, uncurry₃, Function.comp_def] using
      h₃.hasDerivAt.deriv

private theorem hasDerivAt_uncurry₃_chain
    (f : ℝ → ℝ → ℝ → ℝ) (hf : Differentiable ℝ (uncurry₃ f))
    {A B C : ℝ → ℝ} {s dA dB dC : ℝ}
    (hA : HasDerivAt A dA s) (hB : HasDerivAt B dB s)
    (hC : HasDerivAt C dC s) :
    HasDerivAt (fun t => f (A t) (B t) (C t))
      (partial1 f (A s) (B s) (C s) * dA +
        partial2 f (A s) (B s) (C s) * dB +
        partial3 f (A s) (B s) (C s) * dC) s := by
  have hcurve :
      HasDerivAt (fun t => (A t, B t, C t)) ((dA, dB, dC) : Vec3) s :=
    hA.prodMk (hB.prodMk hC)
  have hcomp :=
    (hf (A s, B s, C s)).hasFDerivAt.comp_hasDerivAt s hcurve
  have hp := partials_eq_fderiv f hf (A s) (B s) (C s)
  let L := fderiv ℝ (uncurry₃ f) (A s, B s, C s)
  let e₁ : Vec3 := (1, 0, 0)
  let e₂ : Vec3 := (0, 1, 0)
  let e₃ : Vec3 := (0, 0, 1)
  have hv : ((dA, dB, dC) : Vec3) =
      dA • e₁ + dB • e₂ + dC • e₃ := by
    ext <;> simp [e₁, e₂, e₃]
  convert hcomp using 1
  symm
  change L (dA, dB, dC) = _
  rw [hv, map_add, map_add, map_smul, map_smul, map_smul]
  rw [← hp.1, ← hp.2.1, ← hp.2.2]
  simp [smul_eq_mul]
  ring

private theorem fderiv_fderiv_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → ℝ) (hDF : Differentiable ℝ (fderiv ℝ F))
    (p v w : E) :
    fderiv ℝ (fun q : E => fderiv ℝ F q v) p w =
      fderiv ℝ (fderiv ℝ F) p w v := by
  have hA :
      HasFDerivAt (fderiv ℝ F)
        (fderiv ℝ (fderiv ℝ F) p) p :=
    (hDF p).hasFDerivAt
  have hB :
      HasFDerivAt (fun _ : E => v) (0 : E →L[ℝ] E) p :=
    hasFDerivAt_const (x := p) v
  have h := hA.clm_apply hB
  have heq := congrArg (fun L : E →L[ℝ] ℝ => L w) h.fderiv
  simpa using heq

private theorem differentiated_partials
    (f : ℝ → ℝ → ℝ → ℝ)
    (hf : ContDiff ℝ 2 (uncurry₃ f)) :
    Differentiable ℝ (uncurry₃ (partial1 f)) ∧
      Differentiable ℝ (uncurry₃ (partial2 f)) ∧
      Differentiable ℝ (uncurry₃ (partial3 f)) := by
  have hstep :=
    (contDiff_succ_iff_fderiv (𝕜 := ℝ) (n := 1)
      (f := uncurry₃ f)).mp (by simpa using hf)
  have hfd : Differentiable ℝ (uncurry₃ f) := hstep.1
  have heq1 :
      uncurry₃ (partial1 f) =
        fun p : Vec3 =>
          fderiv ℝ (uncurry₃ f) p ((1, 0, 0) : Vec3) := by
    funext p
    simpa [uncurry₃] using
      (partials_eq_fderiv f hfd p.1 p.2.1 p.2.2).1
  have heq2 :
      uncurry₃ (partial2 f) =
        fun p : Vec3 =>
          fderiv ℝ (uncurry₃ f) p ((0, 1, 0) : Vec3) := by
    funext p
    simpa [uncurry₃] using
      (partials_eq_fderiv f hfd p.1 p.2.1 p.2.2).2.1
  have heq3 :
      uncurry₃ (partial3 f) =
        fun p : Vec3 =>
          fderiv ℝ (uncurry₃ f) p ((0, 0, 1) : Vec3) := by
    funext p
    simpa [uncurry₃] using
      (partials_eq_fderiv f hfd p.1 p.2.1 p.2.2).2.2
  constructor
  · rw [heq1]
    fun_prop
  constructor
  · rw [heq2]
    fun_prop
  · rw [heq3]
    fun_prop

private theorem reverse_mixed_partials
    (f : ℝ → ℝ → ℝ → ℝ)
    (hf : ContDiff ℝ 2 (uncurry₃ f)) (a b c : ℝ) :
    partial1 (partial2 f) a b c = partial12 f a b c ∧
      partial1 (partial3 f) a b c = partial13 f a b c ∧
      partial2 (partial3 f) a b c = partial23 f a b c := by
  have hstep :=
    (contDiff_succ_iff_fderiv (𝕜 := ℝ) (n := 1)
      (f := uncurry₃ f)).mp (by simpa using hf)
  have hfd : Differentiable ℝ (uncurry₃ f) := hstep.1
  have hDfd : Differentiable ℝ (fderiv ℝ (uncurry₃ f)) :=
    hstep.2.2.differentiable (by norm_num)
  have hpd := differentiated_partials f hf
  let p : Vec3 := (a, b, c)
  let e₁ : Vec3 := (1, 0, 0)
  let e₂ : Vec3 := (0, 1, 0)
  let e₃ : Vec3 := (0, 0, 1)
  let H := fderiv ℝ (fderiv ℝ (uncurry₃ f)) p
  have hsymm (v w : Vec3) : H v w = H w v :=
    hf.contDiffAt.isSymmSndFDerivAt
      (by norm_num [minSmoothness]) v w
  have hcoord (g : ℝ → ℝ → ℝ → ℝ)
      (hg : Differentiable ℝ (uncurry₃ g)) :
      partial1 g a b c =
          fderiv ℝ (uncurry₃ g) p e₁ ∧
        partial2 g a b c =
          fderiv ℝ (uncurry₃ g) p e₂ ∧
        partial3 g a b c =
          fderiv ℝ (uncurry₃ g) p e₃ := by
    simpa [p, e₁, e₂, e₃] using
      partials_eq_fderiv g hg a b c
  have heq1 :
      uncurry₃ (partial1 f) =
        fun q : Vec3 => fderiv ℝ (uncurry₃ f) q e₁ := by
    funext q
    simpa [uncurry₃, e₁] using
      (partials_eq_fderiv f hfd q.1 q.2.1 q.2.2).1
  have heq2 :
      uncurry₃ (partial2 f) =
        fun q : Vec3 => fderiv ℝ (uncurry₃ f) q e₂ := by
    funext q
    simpa [uncurry₃, e₂] using
      (partials_eq_fderiv f hfd q.1 q.2.1 q.2.2).2.1
  have heq3 :
      uncurry₃ (partial3 f) =
        fun q : Vec3 => fderiv ℝ (uncurry₃ f) q e₃ := by
    funext q
    simpa [uncurry₃, e₃] using
      (partials_eq_fderiv f hfd q.1 q.2.1 q.2.2).2.2
  have hm12 :
      partial1 (partial2 f) a b c = partial12 f a b c := by
    have hleft := (hcoord (partial2 f) hpd.2.1).1
    have hright := (hcoord (partial1 f) hpd.1).2.1
    rw [heq2] at hleft
    rw [heq1] at hright
    calc
      partial1 (partial2 f) a b c = H e₁ e₂ := by
        rw [hleft]
        exact fderiv_fderiv_apply _ hDfd p e₂ e₁
      _ = H e₂ e₁ := hsymm e₁ e₂
      _ = partial2 (partial1 f) a b c := by
        rw [hright]
        exact (fderiv_fderiv_apply _ hDfd p e₁ e₂).symm
      _ = partial12 f a b c := rfl
  have hm13 :
      partial1 (partial3 f) a b c = partial13 f a b c := by
    have hleft := (hcoord (partial3 f) hpd.2.2).1
    have hright := (hcoord (partial1 f) hpd.1).2.2
    rw [heq3] at hleft
    rw [heq1] at hright
    calc
      partial1 (partial3 f) a b c = H e₁ e₃ := by
        rw [hleft]
        exact fderiv_fderiv_apply _ hDfd p e₃ e₁
      _ = H e₃ e₁ := hsymm e₁ e₃
      _ = partial3 (partial1 f) a b c := by
        rw [hright]
        exact (fderiv_fderiv_apply _ hDfd p e₁ e₃).symm
      _ = partial13 f a b c := rfl
  have hm23 :
      partial2 (partial3 f) a b c = partial23 f a b c := by
    have hleft := (hcoord (partial3 f) hpd.2.2).2.1
    have hright := (hcoord (partial2 f) hpd.2.1).2.2
    rw [heq3] at hleft
    rw [heq2] at hright
    calc
      partial2 (partial3 f) a b c = H e₂ e₃ := by
        rw [hleft]
        exact fderiv_fderiv_apply _ hDfd p e₃ e₂
      _ = H e₃ e₂ := hsymm e₂ e₃
      _ = partial3 (partial2 f) a b c := by
        rw [hright]
        exact (fderiv_fderiv_apply _ hDfd p e₂ e₃).symm
      _ = partial23 f a b c := rfl
  exact ⟨hm12, hm13, hm23⟩

private theorem nested11 (f : ℝ → ℝ → ℝ → ℝ) (a b c : ℝ) :
    partial1 (partial1 f) a b c = partial11 f a b c := by
  simp [partial1, partial11, Function.iterate_succ_apply]

private theorem nested22 (f : ℝ → ℝ → ℝ → ℝ) (a b c : ℝ) :
    partial2 (partial2 f) a b c = partial22 f a b c := by
  simp [partial2, partial22, Function.iterate_succ_apply]

private theorem nested33 (f : ℝ → ℝ → ℝ → ℝ) (a b c : ℝ) :
    partial3 (partial3 f) a b c = partial33 f a b c := by
  simp [partial3, partial33, Function.iterate_succ_apply]

private theorem forward12 (f : ℝ → ℝ → ℝ → ℝ) (a b c : ℝ) :
    partial2 (partial1 f) a b c = partial12 f a b c := rfl

private theorem forward13 (f : ℝ → ℝ → ℝ → ℝ) (a b c : ℝ) :
    partial3 (partial1 f) a b c = partial13 f a b c := rfl

private theorem forward23 (f : ℝ → ℝ → ℝ → ℝ) (a b c : ℝ) :
    partial3 (partial2 f) a b c = partial23 f a b c := rfl

theorem gap1 (u x y z : ℝ → ℝ) (f : ℝ → ℝ → ℝ → ℝ)
    (hu : ∀ t, u t = f (x t) (y t) (z t))
    (hx : ∀ t, x t = t) (hy : ∀ t, y t = t ^ 2)
    (hz : ∀ t, z t = t ^ 3)
    (hf : ContDiff ℝ 1 (uncurry₃ f)) (t : ℝ) :
    deriv u t =
      partial1 f (x t) (y t) (z t) +
        2 * t * partial2 f (x t) (y t) (z t) +
        3 * t ^ 2 * partial3 f (x t) (y t) (z t) := by
  have hfd : Differentiable ℝ (uncurry₃ f) :=
    hf.differentiable (by norm_num)
  have hfun :
      u = fun s => f s (s ^ 2) (s ^ 3) := by
    funext s
    rw [hu, hx, hy, hz]
  have hA : HasDerivAt (fun s : ℝ => s) 1 t :=
    hasDerivAt_id t
  have hB : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
    convert (hasDerivAt_id t).pow 2 using 1 <;>
      simp only [id_eq] <;> ring
  have hC : HasDerivAt (fun s : ℝ => s ^ 3) (3 * t ^ 2) t := by
    convert (hasDerivAt_id t).pow 3 using 1 <;>
      simp only [id_eq] <;> ring
  rw [hfun]
  convert (hasDerivAt_uncurry₃_chain f hfd hA hB hC).deriv using 1 <;>
    simp only [hx, hy, hz] <;> ring

theorem gap2 (u x y z : ℝ → ℝ) (f : ℝ → ℝ → ℝ → ℝ)
    (hu : ∀ t, u t = f (x t) (y t) (z t))
    (hx : ∀ t, x t = t) (hy : ∀ t, y t = t ^ 2)
    (hz : ∀ t, z t = t ^ 3)
    (hf : ContDiff ℝ 2 (uncurry₃ f)) (t : ℝ) :
    iterDeriv 2 u t =
      partial11 f (x t) (y t) (z t) +
        4 * t ^ 2 * partial22 f (x t) (y t) (z t) +
        9 * t ^ 4 * partial33 f (x t) (y t) (z t) +
        4 * t * partial12 f (x t) (y t) (z t) +
        6 * t ^ 2 * partial13 f (x t) (y t) (z t) +
        12 * t ^ 3 * partial23 f (x t) (y t) (z t) +
        2 * partial2 f (x t) (y t) (z t) +
        6 * t * partial3 f (x t) (y t) (z t) := by
  have hfd : Differentiable ℝ (uncurry₃ f) :=
    hf.differentiable (by decide)
  have hpd := differentiated_partials f hf
  let A : ℝ → ℝ := fun s => s
  let B : ℝ → ℝ := fun s => s ^ 2
  let C : ℝ → ℝ := fun s => s ^ 3
  let V₁ : ℝ → ℝ := fun _ => 1
  let V₂ : ℝ → ℝ := fun s => 2 * s
  let V₃ : ℝ → ℝ := fun s => 3 * s ^ 2
  have hA (s : ℝ) : HasDerivAt A (V₁ s) s := by
    simpa [A, V₁] using hasDerivAt_id s
  have hB (s : ℝ) : HasDerivAt B (V₂ s) s := by
    dsimp [B, V₂]
    convert (hasDerivAt_id s).pow 2 using 1 <;>
      simp only [id_eq] <;> ring
  have hC (s : ℝ) : HasDerivAt C (V₃ s) s := by
    dsimp [C, V₃]
    convert (hasDerivAt_id s).pow 3 using 1 <;>
      simp only [id_eq] <;> ring
  have hcurve :
      u = fun s => f (A s) (B s) (C s) := by
    funext s
    simp [hu, hx, hy, hz, A, B, C]
  have hfirst :
      deriv (fun s => f (A s) (B s) (C s)) =
        fun s =>
          partial1 f (A s) (B s) (C s) * V₁ s +
            partial2 f (A s) (B s) (C s) * V₂ s +
            partial3 f (A s) (B s) (C s) * V₃ s := by
    funext s
    exact
      (hasDerivAt_uncurry₃_chain f hfd (hA s) (hB s) (hC s)).deriv
  have hd1 :=
    hasDerivAt_uncurry₃_chain (partial1 f) hpd.1
      (hA t) (hB t) (hC t)
  have hd2 :=
    hasDerivAt_uncurry₃_chain (partial2 f) hpd.2.1
      (hA t) (hB t) (hC t)
  have hd3 :=
    hasDerivAt_uncurry₃_chain (partial3 f) hpd.2.2
      (hA t) (hB t) (hC t)
  have hm := reverse_mixed_partials f hf (A t) (B t) (C t)
  have hV₁ : HasDerivAt V₁ 0 t := by
    simpa [V₁] using hasDerivAt_const t (1 : ℝ)
  have hV₂ : HasDerivAt V₂ 2 t := by
    simpa [V₂] using (hasDerivAt_id t).const_mul 2
  have hV₃ : HasDerivAt V₃ (6 * t) t := by
    dsimp [V₃]
    convert ((hasDerivAt_id t).pow 2).const_mul 3 using 1 <;>
      simp only [id_eq] <;> ring
  have hraw :=
    (((hd1.mul hV₁).add (hd2.mul hV₂)).add (hd3.mul hV₃)).deriv
  rw [nested11, nested22, nested33, forward12, forward13, forward23,
    hm.1, hm.2.1, hm.2.2] at hraw
  change deriv (deriv u) t = _
  rw [hcurve, hfirst]
  change deriv
    ((fun s => partial1 f (A s) (B s) (C s)) * V₁ +
      (fun s => partial2 f (A s) (B s) (C s)) * V₂ +
      (fun s => partial3 f (A s) (B s) (C s)) * V₃) t = _
  rw [hraw]
  simp [A, B, C, V₁, V₂, V₃, hx, hy, hz]
  ring

end

end ProofGap.Exercise3299
