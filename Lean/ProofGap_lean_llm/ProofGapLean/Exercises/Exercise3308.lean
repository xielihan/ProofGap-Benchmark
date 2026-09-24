import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3308

noncomputable section
open Filter

def partialX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => f s y) x

def partialY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => f x s) y

def partialXX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => partialX f s y) x

def partialYY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => partialY f x s) y

def partialXY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => partialX f x s) y

def radiusSq (x y : ℝ) : ℝ := x ^ 2 + y ^ 2
def xi (x y : ℝ) : ℝ := x / radiusSq x y
def eta (x y : ℝ) : ℝ := y / radiusSq x y

def inversionMap (p : ℝ × ℝ) : ℝ × ℝ :=
  (xi p.1 p.2, eta p.1 p.2)

def puncturedPlane : Set (ℝ × ℝ) :=
  {p | p ≠ (0, 0)}

def CoordinatesC2 : Prop :=
  ContDiffOn ℝ 2 inversionMap puncturedPlane

def v (u : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ := u (xi x y) (eta x y)

private def uncurry₂ (f : ℝ → ℝ → ℝ) : ℝ × ℝ → ℝ := fun p => f p.1 p.2

private theorem radiusSq_ne_zero {x y : ℝ} (hxy : (x, y) ≠ (0, 0)) :
    radiusSq x y ≠ 0 := by
  intro h
  have hsx : x ^ 2 = 0 := by
    dsimp [radiusSq] at h
    nlinarith [sq_nonneg x, sq_nonneg y]
  have hsy : y ^ 2 = 0 := by
    dsimp [radiusSq] at h
    nlinarith [sq_nonneg x, sq_nonneg y]
  have hx : x = 0 := sq_eq_zero_iff.mp hsx
  have hy : y = 0 := sq_eq_zero_iff.mp hsy
  exact hxy (by simp [hx, hy])

private theorem partialX_xi_formula (x y : ℝ) (hxy : (x, y) ≠ (0, 0)) :
    partialX xi x y = (y ^ 2 - x ^ 2) / (radiusSq x y) ^ 2 := by
  have hr := radiusSq_ne_zero hxy
  have hn : HasDerivAt (fun s : ℝ => s) 1 x := hasDerivAt_id x
  have hd : HasDerivAt (fun s : ℝ => radiusSq s y) (2 * x) x := by
    convert ((hasDerivAt_id x).pow 2).add_const (y ^ 2) using 1
    all_goals dsimp [radiusSq]; ring
  change deriv (fun s => s / radiusSq s y) x = _
  have hh := (hn.div hd hr).deriv
  change deriv (fun s => s / radiusSq s y) x =
    (1 * radiusSq x y - x * (2 * x)) / radiusSq x y ^ 2 at hh
  rw [hh]
  unfold radiusSq
  field_simp [hr, radiusSq]
  ring

private theorem partialY_xi_formula (x y : ℝ) (hxy : (x, y) ≠ (0, 0)) :
    partialY xi x y = -(2 * x * y) / (radiusSq x y) ^ 2 := by
  have hr := radiusSq_ne_zero hxy
  have hn : HasDerivAt (fun _ : ℝ => x) 0 y := hasDerivAt_const y x
  have hd : HasDerivAt (fun s : ℝ => radiusSq x s) (2 * y) y := by
    convert (hasDerivAt_const (x := y) (c := x ^ 2)).add
      ((hasDerivAt_id y).pow 2) using 1
    all_goals dsimp [radiusSq]; ring
  change deriv (fun s => x / radiusSq x s) y = _
  have hh := (hn.div hd hr).deriv
  change deriv (fun s => x / radiusSq x s) y =
    (0 * radiusSq x y - x * (2 * y)) / radiusSq x y ^ 2 at hh
  rw [hh]
  unfold radiusSq
  field_simp [hr, radiusSq]
  ring

private theorem partialX_eta_formula (x y : ℝ) (hxy : (x, y) ≠ (0, 0)) :
    partialX eta x y = -(2 * x * y) / (radiusSq x y) ^ 2 := by
  have hr := radiusSq_ne_zero hxy
  have hn : HasDerivAt (fun _ : ℝ => y) 0 x := hasDerivAt_const x y
  have hd : HasDerivAt (fun s : ℝ => radiusSq s y) (2 * x) x := by
    convert ((hasDerivAt_id x).pow 2).add_const (y ^ 2) using 1
    all_goals dsimp [radiusSq]; ring
  change deriv (fun s => y / radiusSq s y) x = _
  have hh := (hn.div hd hr).deriv
  change deriv (fun s => y / radiusSq s y) x =
    (0 * radiusSq x y - y * (2 * x)) / radiusSq x y ^ 2 at hh
  rw [hh]
  unfold radiusSq
  field_simp [hr, radiusSq]
  ring

private theorem partialY_eta_formula (x y : ℝ) (hxy : (x, y) ≠ (0, 0)) :
    partialY eta x y = (x ^ 2 - y ^ 2) / (radiusSq x y) ^ 2 := by
  have hr := radiusSq_ne_zero hxy
  have hn : HasDerivAt (fun s : ℝ => s) 1 y := hasDerivAt_id y
  have hd : HasDerivAt (fun s : ℝ => radiusSq x s) (2 * y) y := by
    convert (hasDerivAt_const (x := y) (c := x ^ 2)).add
      ((hasDerivAt_id y).pow 2) using 1
    all_goals dsimp [radiusSq]; ring
  change deriv (fun s => s / radiusSq x s) y = _
  have hh := (hn.div hd hr).deriv
  change deriv (fun s => s / radiusSq x s) y =
    (1 * radiusSq x y - y * (2 * y)) / radiusSq x y ^ 2 at hh
  rw [hh]
  unfold radiusSq
  field_simp [hr, radiusSq]
  ring

private theorem hasDerivAt_partialX_xi
    (x y : ℝ) (hxy : (x, y) ≠ (0, 0)) :
    HasDerivAt (fun s => partialX xi s y) (partialXX xi x y) x := by
  let R : ℝ → ℝ := fun s =>
    (y ^ 2 - s ^ 2) / (radiusSq s y) ^ 2
  have hr := radiusSq_ne_zero hxy
  have hn : HasDerivAt (fun s : ℝ => y ^ 2 - s ^ 2) (-2 * x) x := by
    convert (hasDerivAt_const (x := x) (c := y ^ 2)).sub
      ((hasDerivAt_id x).pow 2) using 1
    all_goals simp
  have hd0 : HasDerivAt (fun s : ℝ => radiusSq s y) (2 * x) x := by
    convert ((hasDerivAt_id x).pow 2).add_const (y ^ 2) using 1
    all_goals dsimp [radiusSq]; ring
  have hd : HasDerivAt (fun s : ℝ => (radiusSq s y) ^ 2)
      (2 * radiusSq x y * (2 * x)) x := by
    convert hd0.pow 2 using 1 <;> ring
  have hdR : HasDerivAt R
      (((-2 * x) * (radiusSq x y) ^ 2 -
          (y ^ 2 - x ^ 2) * (2 * radiusSq x y * (2 * x))) /
        ((radiusSq x y) ^ 2) ^ 2) x := by
    dsimp [R, radiusSq]
    exact hn.div hd (pow_ne_zero 2 hr)
  have hp : ∀ᶠ s in nhds x, (s, y) ≠ (0, 0) :=
    (continuousAt_id.prodMk continuousAt_const).eventually_ne hxy
  have hev : (fun s => partialX xi s y) =ᶠ[nhds x] R := by
    filter_upwards [hp] with s hs
    exact partialX_xi_formula s y hs
  have ht := hdR.congr_of_eventuallyEq hev
  have heq : partialXX xi x y =
      ((-2 * x) * (radiusSq x y) ^ 2 -
          (y ^ 2 - x ^ 2) * (2 * radiusSq x y * (2 * x))) /
        ((radiusSq x y) ^ 2) ^ 2 := by
    exact ht.deriv
  simpa [heq] using ht

private theorem hasDerivAt_eventual_model
    {g R : ℝ → ℝ} {x : ℝ}
    (hR : DifferentiableAt ℝ R x) (hev : g =ᶠ[nhds x] R) :
    HasDerivAt g (deriv g x) x := by
  have ht := hR.hasDerivAt.congr_of_eventuallyEq hev
  rw [ht.deriv]
  exact ht

private theorem hasDerivAt_xi_x
    (x y : ℝ) (hxy : (x, y) ≠ (0, 0)) :
    HasDerivAt (fun s => xi s y) (partialX xi x y) x := by
  have hr := radiusSq_ne_zero hxy
  have hd : DifferentiableAt ℝ (fun s => xi s y) x := by
    dsimp [xi, radiusSq]
    fun_prop (disch := assumption)
  exact hd.hasDerivAt

private theorem hasDerivAt_eta_x
    (x y : ℝ) (hxy : (x, y) ≠ (0, 0)) :
    HasDerivAt (fun s => eta s y) (partialX eta x y) x := by
  have hr := radiusSq_ne_zero hxy
  have hd : DifferentiableAt ℝ (fun s => eta s y) x := by
    dsimp [eta, radiusSq]
    fun_prop (disch := assumption)
  exact hd.hasDerivAt

private theorem hasDerivAt_xi_y
    (x y : ℝ) (hxy : (x, y) ≠ (0, 0)) :
    HasDerivAt (fun s => xi x s) (partialY xi x y) y := by
  have hr := radiusSq_ne_zero hxy
  have hd : DifferentiableAt ℝ (fun s => xi x s) y := by
    dsimp [xi, radiusSq]
    fun_prop (disch := assumption)
  exact hd.hasDerivAt

private theorem hasDerivAt_eta_y
    (x y : ℝ) (hxy : (x, y) ≠ (0, 0)) :
    HasDerivAt (fun s => eta x s) (partialY eta x y) y := by
  have hr := radiusSq_ne_zero hxy
  have hd : DifferentiableAt ℝ (fun s => eta x s) y := by
    dsimp [eta, radiusSq]
    fun_prop (disch := assumption)
  exact hd.hasDerivAt

private theorem hasDerivAt_partialX_eta
    (x y : ℝ) (hxy : (x, y) ≠ (0, 0)) :
    HasDerivAt (fun s => partialX eta s y) (partialXX eta x y) x := by
  let R : ℝ → ℝ := fun s => -(2 * s * y) / (radiusSq s y) ^ 2
  have hr := radiusSq_ne_zero hxy
  have hpw : (x ^ 2 + y ^ 2) ^ 2 ≠ 0 := by
    exact pow_ne_zero 2 (by simpa [radiusSq] using hr)
  have hR : DifferentiableAt ℝ R x := by
    dsimp [R, radiusSq]
    fun_prop (disch := assumption)
  have hp : ∀ᶠ s in nhds x, (s, y) ≠ (0, 0) :=
    (continuousAt_id.prodMk continuousAt_const).eventually_ne hxy
  have hev : (fun s => partialX eta s y) =ᶠ[nhds x] R := by
    filter_upwards [hp] with s hs
    exact partialX_eta_formula s y hs
  exact hasDerivAt_eventual_model hR hev

private theorem hasDerivAt_partialY_xi
    (x y : ℝ) (hxy : (x, y) ≠ (0, 0)) :
    HasDerivAt (fun s => partialY xi x s) (partialYY xi x y) y := by
  let R : ℝ → ℝ := fun s => -(2 * x * s) / (radiusSq x s) ^ 2
  have hr := radiusSq_ne_zero hxy
  have hpw : (x ^ 2 + y ^ 2) ^ 2 ≠ 0 := by
    exact pow_ne_zero 2 (by simpa [radiusSq] using hr)
  have hR : DifferentiableAt ℝ R y := by
    dsimp [R, radiusSq]
    fun_prop (disch := assumption)
  have hp : ∀ᶠ s in nhds y, (x, s) ≠ (0, 0) :=
    (continuousAt_const.prodMk continuousAt_id).eventually_ne hxy
  have hev : (fun s => partialY xi x s) =ᶠ[nhds y] R := by
    filter_upwards [hp] with s hs
    exact partialY_xi_formula x s hs
  exact hasDerivAt_eventual_model hR hev

private theorem hasDerivAt_partialY_eta
    (x y : ℝ) (hxy : (x, y) ≠ (0, 0)) :
    HasDerivAt (fun s => partialY eta x s) (partialYY eta x y) y := by
  let R : ℝ → ℝ := fun s =>
    (x ^ 2 - s ^ 2) / (radiusSq x s) ^ 2
  have hr := radiusSq_ne_zero hxy
  have hpw : (x ^ 2 + y ^ 2) ^ 2 ≠ 0 := by
    exact pow_ne_zero 2 (by simpa [radiusSq] using hr)
  have hR : DifferentiableAt ℝ R y := by
    dsimp [R, radiusSq]
    fun_prop (disch := assumption)
  have hp : ∀ᶠ s in nhds y, (x, s) ≠ (0, 0) :=
    (continuousAt_const.prodMk continuousAt_id).eventually_ne hxy
  have hev : (fun s => partialY eta x s) =ᶠ[nhds y] R := by
    filter_upwards [hp] with s hs
    exact partialY_eta_formula x s hs
  exact hasDerivAt_eventual_model hR hev

private theorem hasDerivAt_uncurry₂_chain
    (f : ℝ → ℝ → ℝ) (hf : Differentiable ℝ (uncurry₂ f))
    {A B : ℝ → ℝ} {s dA dB : ℝ}
    (hA : HasDerivAt A dA s) (hB : HasDerivAt B dB s) :
    HasDerivAt (fun t => f (A t) (B t))
      (partialX f (A s) (B s) * dA +
        partialY f (A s) (B s) * dB) s := by
  have hcomp := (hf (A s, B s)).hasFDerivAt.comp s (hA.prodMk hB)
  have h₁ :
      partialX f (A s) (B s) =
        fderiv ℝ (uncurry₂ f) (A s, B s) (1, 0) := by
    have h := (hf (A s, B s)).hasFDerivAt.comp (A s)
      ((hasDerivAt_id (A s)).prodMk
        (hasDerivAt_const (x := A s) (c := B s)))
    simpa [partialX, uncurry₂, Function.comp_def] using h.hasDerivAt.deriv
  have h₂ :
      partialY f (A s) (B s) =
        fderiv ℝ (uncurry₂ f) (A s, B s) (0, 1) := by
    have h := (hf (A s, B s)).hasFDerivAt.comp (B s)
      ((hasDerivAt_const (x := B s) (c := A s)).prodMk
        (hasDerivAt_id (B s)))
    simpa [partialY, uncurry₂, Function.comp_def] using h.hasDerivAt.deriv
  have hv : (dA, dB) =
      dA • ((1, 0) : ℝ × ℝ) + dB • ((0, 1) : ℝ × ℝ) := by
    ext <;> simp
  convert hcomp.hasDerivAt using 1
  simp only [ContinuousLinearMap.comp_apply]
  simp only [ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.toSpanSingleton_apply, one_smul]
  change partialX f (A s) (B s) * dA +
      partialY f (A s) (B s) * dB =
    fderiv ℝ (uncurry₂ f) (A s, B s) (dA, dB)
  rw [hv, map_add, map_smul, map_smul, ← h₁, ← h₂]
  simp [smul_eq_mul]
  ring

private theorem partials_eq_fderiv
    (f : ℝ → ℝ → ℝ) (hf : Differentiable ℝ (uncurry₂ f)) (a b : ℝ) :
    partialX f a b =
        fderiv ℝ (uncurry₂ f) (a, b) ((1, 0) : ℝ × ℝ) ∧
      partialY f a b =
        fderiv ℝ (uncurry₂ f) (a, b) ((0, 1) : ℝ × ℝ) := by
  constructor
  · have h := (hf (a, b)).hasFDerivAt.comp a
      ((hasDerivAt_id a).prodMk (hasDerivAt_const (x := a) (c := b)))
    simpa [partialX, uncurry₂, Function.comp_def] using h.hasDerivAt.deriv
  · have h := (hf (a, b)).hasFDerivAt.comp b
      ((hasDerivAt_const (x := b) (c := a)).prodMk (hasDerivAt_id b))
    simpa [partialY, uncurry₂, Function.comp_def] using h.hasDerivAt.deriv

private theorem fderiv_fderiv_apply
    (F : ℝ × ℝ → ℝ) (hDF : Differentiable ℝ (fderiv ℝ F))
    (p v w : ℝ × ℝ) :
    fderiv ℝ (fun q : ℝ × ℝ => fderiv ℝ F q v) p w =
      fderiv ℝ (fderiv ℝ F) p w v := by
  have hA : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) p) p :=
    (hDF p).hasFDerivAt
  have hB : HasFDerivAt (fun _ : ℝ × ℝ => v)
      (0 : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) p := hasFDerivAt_const (x := p) v
  have h := hA.clm_apply hB
  have heq := congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L w) h.fderiv
  simpa using heq

private theorem mixed_partials
    (f : ℝ → ℝ → ℝ) (hf : ContDiff ℝ 2 (uncurry₂ f)) (a b : ℝ) :
    partialX (partialY f) a b = partialXY f a b := by
  have hstep := (contDiff_succ_iff_fderiv (𝕜 := ℝ) (n := 1)
    (f := uncurry₂ f)).mp (by simpa using hf)
  have hfd : Differentiable ℝ (uncurry₂ f) := hstep.1
  have hDfd : Differentiable ℝ (fderiv ℝ (uncurry₂ f)) :=
    hstep.2.2.differentiable (by norm_num)
  have heq1 : uncurry₂ (partialX f) =
      fun p : ℝ × ℝ => fderiv ℝ (uncurry₂ f) p ((1, 0) : ℝ × ℝ) := by
    funext p
    simpa [uncurry₂] using (partials_eq_fderiv f hfd p.1 p.2).1
  have heq2 : uncurry₂ (partialY f) =
      fun p : ℝ × ℝ => fderiv ℝ (uncurry₂ f) p ((0, 1) : ℝ × ℝ) := by
    funext p
    simpa [uncurry₂] using (partials_eq_fderiv f hfd p.1 p.2).2
  have hP1 : Differentiable ℝ (uncurry₂ (partialX f)) := by
    rw [heq1]
    fun_prop
  have hP2 : Differentiable ℝ (uncurry₂ (partialY f)) := by
    rw [heq2]
    fun_prop
  have hm2 := (partials_eq_fderiv (partialY f) hP2 a b).1
  have hm1 := (partials_eq_fderiv (partialX f) hP1 a b).2
  rw [heq2] at hm2
  rw [heq1] at hm1
  calc
    partialX (partialY f) a b =
        fderiv ℝ (fderiv ℝ (uncurry₂ f)) (a, b)
          ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ) := by
      rw [hm2]
      exact fderiv_fderiv_apply _ hDfd _ _ _
    _ = fderiv ℝ (fderiv ℝ (uncurry₂ f)) (a, b)
          ((0, 1) : ℝ × ℝ) ((1, 0) : ℝ × ℝ) :=
      hf.contDiffAt.isSymmSndFDerivAt (by norm_num [minSmoothness]) _ _
    _ = partialY (partialX f) a b := by
      rw [hm1]
      exact (fderiv_fderiv_apply _ hDfd _ _ _).symm
    _ = partialXY f a b := rfl

private theorem second_chain_at
    (f : ℝ → ℝ → ℝ) (hf : ContDiff ℝ 2 (uncurry₂ f))
    (A B A1 B1 : ℝ → ℝ) (s A2 B2 : ℝ)
    (hA : HasDerivAt A (A1 s) s) (hB : HasDerivAt B (B1 s) s)
    (hAev : ∀ᶠ t in nhds s, HasDerivAt A (A1 t) t)
    (hBev : ∀ᶠ t in nhds s, HasDerivAt B (B1 t) t)
    (hA1 : HasDerivAt A1 A2 s) (hB1 : HasDerivAt B1 B2 s) :
    deriv (fun t => deriv (fun r => f (A r) (B r)) t) s =
      partialXX f (A s) (B s) * A1 s ^ 2 +
      partialYY f (A s) (B s) * B1 s ^ 2 +
      2 * partialXY f (A s) (B s) * A1 s * B1 s +
      partialX f (A s) (B s) * A2 +
      partialY f (A s) (B s) * B2 := by
  have hstep := (contDiff_succ_iff_fderiv (𝕜 := ℝ) (n := 1)
    (f := uncurry₂ f)).mp (by simpa using hf)
  have hfd : Differentiable ℝ (uncurry₂ f) := hstep.1
  have hDfd : Differentiable ℝ (fderiv ℝ (uncurry₂ f)) :=
    hstep.2.2.differentiable (by norm_num)
  have heq1 : uncurry₂ (partialX f) =
      fun p : ℝ × ℝ => fderiv ℝ (uncurry₂ f) p ((1, 0) : ℝ × ℝ) := by
    funext p
    simpa [uncurry₂] using (partials_eq_fderiv f hfd p.1 p.2).1
  have heq2 : uncurry₂ (partialY f) =
      fun p : ℝ × ℝ => fderiv ℝ (uncurry₂ f) p ((0, 1) : ℝ × ℝ) := by
    funext p
    simpa [uncurry₂] using (partials_eq_fderiv f hfd p.1 p.2).2
  have hP1 : Differentiable ℝ (uncurry₂ (partialX f)) := by
    rw [heq1]
    fun_prop
  have hP2 : Differentiable ℝ (uncurry₂ (partialY f)) := by
    rw [heq2]
    fun_prop
  have hfirst : (fun t => deriv (fun r => f (A r) (B r)) t) =ᶠ[nhds s]
      fun t => partialX f (A t) (B t) * A1 t +
        partialY f (A t) (B t) * B1 t := by
    filter_upwards [hAev, hBev] with t hAt hBt
    exact (hasDerivAt_uncurry₂_chain f hfd hAt hBt).deriv
  have hpx := hasDerivAt_uncurry₂_chain (partialX f) hP1 hA hB
  have hpy0 := hasDerivAt_uncurry₂_chain (partialY f) hP2 hA hB
  have hm := mixed_partials f hf (A s) (B s)
  have hpy : HasDerivAt (fun t => partialY f (A t) (B t))
      (partialXY f (A s) (B s) * A1 s +
        partialYY f (A s) (B s) * B1 s) s := by
    convert hpy0 using 1
    rw [hm]
    rfl
  have hsum := (hpx.mul hA1).add (hpy.mul hB1)
  have hsum' : HasDerivAt
      (fun t => partialX f (A t) (B t) * A1 t +
        partialY f (A t) (B t) * B1 t)
      ((partialX (partialX f) (A s) (B s) * A1 s +
          partialY (partialX f) (A s) (B s) * B1 s) * A1 s +
        partialX f (A s) (B s) * A2 +
        ((partialXY f (A s) (B s) * A1 s +
          partialYY f (A s) (B s) * B1 s) * B1 s +
        partialY f (A s) (B s) * B2)) s := by
    simpa only using hsum
  rw [hfirst.deriv_eq, hsum'.deriv]
  unfold partialXX partialXY partialYY partialX partialY
  ring

private theorem second_chain_x (u : ℝ → ℝ → ℝ) (x y : ℝ)
    (hu : ContDiff ℝ 2 (Function.uncurry u))
    (hxy : (x, y) ≠ (0, 0)) :
    partialXX (v u) x y =
      partialXX u (xi x y) (eta x y) * partialX xi x y ^ 2 +
      partialYY u (xi x y) (eta x y) * partialX eta x y ^ 2 +
      2 * partialXY u (xi x y) (eta x y) *
        partialX xi x y * partialX eta x y +
      partialX u (xi x y) (eta x y) * partialXX xi x y +
      partialY u (xi x y) (eta x y) * partialXX eta x y := by
  have hp : ∀ᶠ s in nhds x, (s, y) ≠ (0, 0) :=
    (continuousAt_id.prodMk continuousAt_const).eventually_ne hxy
  have hAev : ∀ᶠ s in nhds x,
      HasDerivAt (fun r => xi r y) (partialX xi s y) s := by
    filter_upwards [hp] with s hs
    exact hasDerivAt_xi_x s y hs
  have hBev : ∀ᶠ s in nhds x,
      HasDerivAt (fun r => eta r y) (partialX eta s y) s := by
    filter_upwards [hp] with s hs
    exact hasDerivAt_eta_x s y hs
  simpa [partialXX, v, uncurry₂] using
    second_chain_at u (by simpa [uncurry₂] using hu)
      (fun s => xi s y) (fun s => eta s y)
      (fun s => partialX xi s y) (fun s => partialX eta s y)
      x (partialXX xi x y) (partialXX eta x y)
      (hasDerivAt_xi_x x y hxy) (hasDerivAt_eta_x x y hxy)
      hAev hBev (hasDerivAt_partialX_xi x y hxy)
      (hasDerivAt_partialX_eta x y hxy)

private theorem second_chain_y (u : ℝ → ℝ → ℝ) (x y : ℝ)
    (hu : ContDiff ℝ 2 (Function.uncurry u))
    (hxy : (x, y) ≠ (0, 0)) :
    partialYY (v u) x y =
      partialXX u (xi x y) (eta x y) * partialY xi x y ^ 2 +
      partialYY u (xi x y) (eta x y) * partialY eta x y ^ 2 +
      2 * partialXY u (xi x y) (eta x y) *
        partialY xi x y * partialY eta x y +
      partialX u (xi x y) (eta x y) * partialYY xi x y +
      partialY u (xi x y) (eta x y) * partialYY eta x y := by
  have hp : ∀ᶠ s in nhds y, (x, s) ≠ (0, 0) :=
    (continuousAt_const.prodMk continuousAt_id).eventually_ne hxy
  have hAev : ∀ᶠ s in nhds y,
      HasDerivAt (fun r => xi x r) (partialY xi x s) s := by
    filter_upwards [hp] with s hs
    exact hasDerivAt_xi_y x s hs
  have hBev : ∀ᶠ s in nhds y,
      HasDerivAt (fun r => eta x r) (partialY eta x s) s := by
    filter_upwards [hp] with s hs
    exact hasDerivAt_eta_y x s hs
  simpa [partialYY, v, uncurry₂] using
    second_chain_at u (by simpa [uncurry₂] using hu)
      (fun s => xi x s) (fun s => eta x s)
      (fun s => partialY xi x s) (fun s => partialY eta x s)
      y (partialYY xi x y) (partialYY eta x y)
      (hasDerivAt_xi_y x y hxy) (hasDerivAt_eta_y x y hxy)
      hAev hBev (hasDerivAt_partialY_xi x y hxy)
      (hasDerivAt_partialY_eta x y hxy)

private theorem mixed_eta_direct (x y : ℝ) (hxy : (x, y) ≠ (0, 0)) :
    deriv (fun s => partialX eta x s) y =
      deriv (fun s => partialY eta s y) x := by
  have hr := radiusSq_ne_zero hxy
  let L : ℝ → ℝ := fun s => -(2 * x * s) / (radiusSq x s) ^ 2
  let R : ℝ → ℝ := fun s => (s ^ 2 - y ^ 2) / (radiusSq s y) ^ 2
  have hpY : ∀ᶠ s in nhds y, (x, s) ≠ (0, 0) :=
    (continuousAt_const.prodMk continuousAt_id).eventually_ne hxy
  have hpX : ∀ᶠ s in nhds x, (s, y) ≠ (0, 0) :=
    (continuousAt_id.prodMk continuousAt_const).eventually_ne hxy
  have hevL : (fun s => partialX eta x s) =ᶠ[nhds y] L := by
    filter_upwards [hpY] with s hs
    exact partialX_eta_formula x s hs
  have hevR : (fun s => partialY eta s y) =ᶠ[nhds x] R := by
    filter_upwards [hpX] with s hs
    exact partialY_eta_formula s y hs
  have hbaseY : HasDerivAt (fun s : ℝ => radiusSq x s) (2 * y) y := by
    convert (hasDerivAt_const (x := y) (c := x ^ 2)).add
      ((hasDerivAt_id y).pow 2) using 1
    all_goals dsimp [radiusSq]; ring
  have hdenY : HasDerivAt (fun s : ℝ => (radiusSq x s) ^ 2)
      (2 * radiusSq x y * (2 * y)) y := by
    convert hbaseY.pow 2 using 1 <;> ring
  have hnumL : HasDerivAt (fun s : ℝ => -(2 * x * s)) (-(2 * x)) y := by
    convert ((hasDerivAt_id y).const_mul (2 * x)).neg using 1 <;> ring
  have hL : HasDerivAt L
      (((-(2 * x)) * (radiusSq x y) ^ 2 -
        (-(2 * x * y)) * (2 * radiusSq x y * (2 * y))) /
        ((radiusSq x y) ^ 2) ^ 2) y := by
    dsimp [L]
    exact hnumL.div hdenY (pow_ne_zero 2 hr)
  have hbaseX : HasDerivAt (fun s : ℝ => radiusSq s y) (2 * x) x := by
    convert ((hasDerivAt_id x).pow 2).add_const (y ^ 2) using 1
    all_goals dsimp [radiusSq]; ring
  have hdenX : HasDerivAt (fun s : ℝ => (radiusSq s y) ^ 2)
      (2 * radiusSq x y * (2 * x)) x := by
    convert hbaseX.pow 2 using 1 <;> ring
  have hnumR : HasDerivAt (fun s : ℝ => s ^ 2 - y ^ 2) (2 * x) x := by
    convert ((hasDerivAt_id x).pow 2).sub_const (y ^ 2) using 1
    all_goals simp
  have hR : HasDerivAt R
      (((2 * x) * (radiusSq x y) ^ 2 -
        (x ^ 2 - y ^ 2) * (2 * radiusSq x y * (2 * x))) /
        ((radiusSq x y) ^ 2) ^ 2) x := by
    dsimp [R]
    exact hnumR.div hdenX (pow_ne_zero 2 hr)
  rw [hevL.deriv_eq, hevR.deriv_eq, hL.deriv, hR.deriv]
  field_simp [hr]
  unfold radiusSq
  ring

private theorem mixed_xi_direct (x y : ℝ) (hxy : (x, y) ≠ (0, 0)) :
    deriv (fun s => partialX xi x s) y =
      deriv (fun s => partialY xi s y) x := by
  have hyx : (y, x) ≠ ((0, 0) : ℝ × ℝ) := by
    intro h
    apply hxy
    have hy : y = 0 := congrArg Prod.fst h
    have hx : x = 0 := congrArg Prod.snd h
    simp_all
  have h := (mixed_eta_direct y x hyx).symm
  simpa only [partialX, partialY, xi, eta, radiusSq, add_comm] using h

theorem gap1 (u : ℝ → ℝ → ℝ) (x y : ℝ)
    (hxy : (x, y) ≠ (0, 0)) :
    v u x y = u (xi x y) (eta x y) := by
  rfl

theorem gap2 (u : ℝ → ℝ → ℝ) (x y : ℝ)
    (hu : ContDiff ℝ 2 (Function.uncurry u))
    (hcoord : CoordinatesC2) (hxy : (x, y) ≠ (0, 0)) :
    partialXX (v u) x y =
      partialXX u (xi x y) (eta x y) * partialX xi x y ^ 2 +
      partialYY u (xi x y) (eta x y) * partialX eta x y ^ 2 +
      2 * partialXY u (xi x y) (eta x y) *
        partialX xi x y * partialX eta x y +
      partialX u (xi x y) (eta x y) * partialXX xi x y +
      partialY u (xi x y) (eta x y) * partialXX eta x y := by
  exact second_chain_x u x y hu hxy

theorem gap3 (u : ℝ → ℝ → ℝ) (x y : ℝ)
    (hu : ContDiff ℝ 2 (Function.uncurry u))
    (hcoord : CoordinatesC2) (hxy : (x, y) ≠ (0, 0)) :
    partialYY (v u) x y =
      partialXX u (xi x y) (eta x y) * partialY xi x y ^ 2 +
      partialYY u (xi x y) (eta x y) * partialY eta x y ^ 2 +
      2 * partialXY u (xi x y) (eta x y) *
        partialY xi x y * partialY eta x y +
      partialX u (xi x y) (eta x y) * partialYY xi x y +
      partialY u (xi x y) (eta x y) * partialYY eta x y := by
  exact second_chain_y u x y hu hxy

theorem gap4 (x y : ℝ) (hxy : (x, y) ≠ (0, 0)) :
    partialX xi x y = (y ^ 2 - x ^ 2) / (radiusSq x y) ^ 2 := by
  exact partialX_xi_formula x y hxy

theorem gap5 (x y : ℝ) (hxy : (x, y) ≠ (0, 0)) :
    (y ^ 2 - x ^ 2) / (radiusSq x y) ^ 2 =
      -partialY eta x y := by
  rw [partialY_eta_formula x y hxy]
  ring

theorem gap6 (x y : ℝ) (hxy : (x, y) ≠ (0, 0)) :
    partialY xi x y = -(2 * x * y) / (radiusSq x y) ^ 2 := by
  exact partialY_xi_formula x y hxy

theorem gap7 (x y : ℝ) (hxy : (x, y) ≠ (0, 0)) :
    -(2 * x * y) / (radiusSq x y) ^ 2 =
      partialX eta x y := by
  exact (partialX_eta_formula x y hxy).symm

theorem gap8 (x y : ℝ) (hxy : (x, y) ≠ (0, 0)) :
    partialYY xi x y =
      deriv (fun s => partialY xi x s) y := by
  rfl

theorem gap9 (x y : ℝ) (hcoord : CoordinatesC2)
    (hxy : (x, y) ≠ (0, 0)) :
    deriv (fun s => partialY xi x s) y =
      deriv (fun s => partialX eta x s) y := by
  have hp : ∀ᶠ s in nhds y, (x, s) ≠ (0, 0) :=
    (continuousAt_const.prodMk continuousAt_id).eventually_ne hxy
  have hev : (fun s => partialY xi x s) =ᶠ[nhds y]
      (fun s => partialX eta x s) := by
    filter_upwards [hp] with s hs
    rw [partialY_xi_formula x s hs, partialX_eta_formula x s hs]
  exact hev.deriv_eq

theorem gap10 (x y : ℝ) (hcoord : CoordinatesC2)
    (hxy : (x, y) ≠ (0, 0)) :
    deriv (fun s => partialX eta x s) y =
      deriv (fun s => partialY eta s y) x := by
  exact mixed_eta_direct x y hxy

theorem gap11 (x y : ℝ) (hcoord : CoordinatesC2)
    (hxy : (x, y) ≠ (0, 0)) :
    deriv (fun s => partialY eta s y) x =
      -partialXX xi x y := by
  have hp : ∀ᶠ s in nhds x, (s, y) ≠ (0, 0) :=
    (continuousAt_id.prodMk continuousAt_const).eventually_ne hxy
  have hev : (fun s => partialY eta s y) =ᶠ[nhds x]
      (fun s => -partialX xi s y) := by
    filter_upwards [hp] with s hs
    rw [partialY_eta_formula s y hs, partialX_xi_formula s y hs]
    ring
  calc
    deriv (fun s => partialY eta s y) x =
        deriv (fun s => -partialX xi s y) x := hev.deriv_eq
    _ = -partialXX xi x y := by
      simpa using (hasDerivAt_partialX_xi x y hxy).neg.deriv

theorem gap12 (x y : ℝ) (hcoord : CoordinatesC2)
    (hxy : (x, y) ≠ (0, 0)) :
    partialYY xi x y = -partialXX xi x y := by
  calc
    partialYY xi x y =
        deriv (fun s => partialY xi x s) y := gap8 x y hxy
    _ = deriv (fun s => partialX eta x s) y := gap9 x y hcoord hxy
    _ = deriv (fun s => partialY eta s y) x := gap10 x y hcoord hxy
    _ = -partialXX xi x y := gap11 x y hcoord hxy

theorem gap13 (x y : ℝ) (hxy : (x, y) ≠ (0, 0)) :
    partialYY eta x y =
      deriv (fun s => partialY eta x s) y := by
  rfl

theorem gap14 (x y : ℝ) (hcoord : CoordinatesC2)
    (hxy : (x, y) ≠ (0, 0)) :
    deriv (fun s => partialY eta x s) y =
      deriv (fun s => -partialX xi x s) y := by
  have hp : ∀ᶠ s in nhds y, (x, s) ≠ (0, 0) :=
    (continuousAt_const.prodMk continuousAt_id).eventually_ne hxy
  have hev : (fun s => partialY eta x s) =ᶠ[nhds y]
      (fun s => -partialX xi x s) := by
    filter_upwards [hp] with s hs
    rw [partialY_eta_formula x s hs, partialX_xi_formula x s hs]
    ring
  exact hev.deriv_eq

theorem gap15 (x y : ℝ) (hcoord : CoordinatesC2)
    (hxy : (x, y) ≠ (0, 0)) :
    deriv (fun s => -partialX xi x s) y =
      -deriv (fun s => partialY xi s y) x := by
  let R : ℝ → ℝ := fun s =>
    (s ^ 2 - x ^ 2) / (radiusSq x s) ^ 2
  have hr := radiusSq_ne_zero hxy
  have hpw : (x ^ 2 + y ^ 2) ^ 2 ≠ 0 := by
    exact pow_ne_zero 2 (by simpa [radiusSq] using hr)
  have hR : DifferentiableAt ℝ R y := by
    dsimp [R, radiusSq]
    fun_prop (disch := assumption)
  have hp : ∀ᶠ s in nhds y, (x, s) ≠ (0, 0) :=
    (continuousAt_const.prodMk continuousAt_id).eventually_ne hxy
  have hev : (fun s => partialX xi x s) =ᶠ[nhds y] R := by
    filter_upwards [hp] with s hs
    exact partialX_xi_formula x s hs
  have hd := hasDerivAt_eventual_model hR hev
  calc
    deriv (fun s => -partialX xi x s) y =
        -deriv (fun s => partialX xi x s) y := by
      simpa using hd.neg.deriv
    _ = -deriv (fun s => partialY xi s y) x :=
      congrArg Neg.neg (mixed_xi_direct x y hxy)

theorem gap16 (x y : ℝ) (hcoord : CoordinatesC2)
    (hxy : (x, y) ≠ (0, 0)) :
    -deriv (fun s => partialY xi s y) x =
      -partialXX eta x y := by
  have hp : ∀ᶠ s in nhds x, (s, y) ≠ (0, 0) :=
    (continuousAt_id.prodMk continuousAt_const).eventually_ne hxy
  have hev : (fun s => partialY xi s y) =ᶠ[nhds x]
      (fun s => partialX eta s y) := by
    filter_upwards [hp] with s hs
    rw [partialY_xi_formula s y hs, partialX_eta_formula s y hs]
  calc
    -deriv (fun s => partialY xi s y) x =
        -deriv (fun s => partialX eta s y) x :=
      congrArg Neg.neg hev.deriv_eq
    _ = -partialXX eta x y :=
      congrArg Neg.neg (hasDerivAt_partialX_eta x y hxy).deriv

theorem gap17 (x y : ℝ) (hcoord : CoordinatesC2)
    (hxy : (x, y) ≠ (0, 0)) :
    partialYY eta x y = -partialXX eta x y := by
  calc
    partialYY eta x y =
        deriv (fun s => partialY eta x s) y := gap13 x y hxy
    _ = deriv (fun s => -partialX xi x s) y := gap14 x y hcoord hxy
    _ = -deriv (fun s => partialY xi s y) x := gap15 x y hcoord hxy
    _ = -partialXX eta x y := gap16 x y hcoord hxy

theorem gap18 (u : ℝ → ℝ → ℝ)
    (huHarmonic : ∀ p q, partialXX u p q + partialYY u p q = 0)
    (x y : ℝ) (hxy : (x, y) ≠ (0, 0)) :
    partialXX u (xi x y) (eta x y) +
      partialYY u (xi x y) (eta x y) = 0 := by
  exact huHarmonic (xi x y) (eta x y)

theorem gap19 (u : ℝ → ℝ → ℝ) (x y : ℝ)
    (hu : ContDiff ℝ 2 (Function.uncurry u))
    (hcoord : CoordinatesC2) (hxy : (x, y) ≠ (0, 0)) :
    partialXX (v u) x y + partialYY (v u) x y =
      (partialXX u (xi x y) (eta x y) +
        partialYY u (xi x y) (eta x y)) *
      (partialX xi x y ^ 2 + partialX eta x y ^ 2) := by
  have hcr1 : partialY eta x y = -partialX xi x y := by
    rw [partialY_eta_formula x y hxy, partialX_xi_formula x y hxy]
    ring
  have hcr2 : partialY xi x y = partialX eta x y := by
    rw [partialY_xi_formula x y hxy, partialX_eta_formula x y hxy]
  rw [gap2 u x y hu hcoord hxy, gap3 u x y hu hcoord hxy,
    hcr1, hcr2, gap12 x y hcoord hxy, gap17 x y hcoord hxy]
  ring

theorem gap20 (u : ℝ → ℝ → ℝ)
    (huHarmonic : ∀ p q, partialXX u p q + partialYY u p q = 0)
    (x y : ℝ) (hxy : (x, y) ≠ (0, 0)) :
    (partialXX u (xi x y) (eta x y) +
      partialYY u (xi x y) (eta x y)) *
      (partialX xi x y ^ 2 + partialX eta x y ^ 2) = 0 := by
  rw [gap18 u huHarmonic x y hxy]
  ring

theorem gap21 (u : ℝ → ℝ → ℝ)
    (hu : ContDiff ℝ 2 (Function.uncurry u))
    (hcoord : CoordinatesC2)
    (huHarmonic : ∀ p q, partialXX u p q + partialYY u p q = 0)
    (x y : ℝ) (hxy : (x, y) ≠ (0, 0)) :
    partialXX (v u) x y + partialYY (v u) x y = 0 := by
  rw [gap19 u x y hu hcoord hxy]
  exact gap20 u huHarmonic x y hxy

theorem gap22 (u : ℝ → ℝ → ℝ)
    (hu : ContDiff ℝ 2 (Function.uncurry u))
    (hcoord : CoordinatesC2)
    (huHarmonic : ∀ p q, partialXX u p q + partialYY u p q = 0) :
    ∀ x y, (x, y) ≠ (0, 0) →
      partialXX (v u) x y + partialYY (v u) x y = 0 := by
  intro x y hxy
  exact gap21 u hu hcoord huHarmonic x y hxy

end

end ProofGap.Exercise3308
