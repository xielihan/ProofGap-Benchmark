import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3502

noncomputable section

def partialX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ := deriv (fun t => f t y) x
def partialY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ := deriv (fun t => f x t) y
def partialXX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ := partialX (partialX f) x y
def partialYY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ := partialY (partialY f) x y

def differential (f : ℝ → ℝ → ℝ) (u v du dv : ℝ) : ℝ :=
  partialX f u v * du + partialY f u v * dv

def conformalScale (φ : ℝ → ℝ → ℝ) (u v : ℝ) : ℝ :=
  partialX φ u v ^ 2 + partialY φ u v ^ 2

private theorem hasDerivAt_partialX
    (f : ℝ → ℝ → ℝ) (x y : ℝ)
    (hf : DifferentiableAt ℝ (Function.uncurry f) (x, y)) :
    HasDerivAt (fun t : ℝ => f t y) (partialX f x y) x := by
  have hp : DifferentiableAt ℝ (fun t : ℝ => (t, y)) x := by fun_prop
  have hc : DifferentiableAt ℝ (fun t : ℝ => f t y) x := by
    simpa [Function.uncurry, Function.comp_def] using hf.comp x hp
  simpa [partialX] using hc.hasDerivAt

private theorem hasDerivAt_partialY
    (f : ℝ → ℝ → ℝ) (x y : ℝ)
    (hf : DifferentiableAt ℝ (Function.uncurry f) (x, y)) :
    HasDerivAt (fun t : ℝ => f x t) (partialY f x y) y := by
  have hp : DifferentiableAt ℝ (fun t : ℝ => (x, t)) y := by fun_prop
  have hc : DifferentiableAt ℝ (fun t : ℝ => f x t) y := by
    simpa [Function.uncurry, Function.comp_def] using hf.comp y hp
  simpa [partialY] using hc.hasDerivAt

private theorem hasDerivAt_comp₂
    (F : ℝ → ℝ → ℝ) (g h : ℝ → ℝ) {x dg dh : ℝ}
    (hF : DifferentiableAt ℝ (Function.uncurry F) (g x, h x))
    (hg : HasDerivAt g dg x) (hh : HasDerivAt h dh x) :
    HasDerivAt (fun t => F (g t) (h t))
      (dg * partialX F (g x) (h x) + dh * partialY F (g x) (h x)) x := by
  let D := fderiv ℝ (Function.uncurry F) (g x, h x)
  have hc := hF.hasFDerivAt.comp x
    (hg.hasFDerivAt.prodMk hh.hasFDerivAt)
  have hc' : HasDerivAt (fun t => F (g t) (h t)) (D (dg, dh)) x := by
    simpa [D, Function.comp_def, Function.uncurry] using hc.hasDerivAt
  have hdx0 : HasDerivAt (fun t : ℝ => F t (h x))
      (D (1, 0)) (g x) := by
    have hx := hF.hasFDerivAt.comp (g x)
      ((hasDerivAt_id (g x)).hasFDerivAt.prodMk
        (hasDerivAt_const (g x) (h x)).hasFDerivAt)
    simpa [D, Function.comp_def, Function.uncurry] using hx.hasDerivAt
  have hdx : partialX F (g x) (h x) = D (1, 0) := by
    change deriv (fun t : ℝ => F t (h x)) (g x) = D (1, 0)
    exact hdx0.deriv
  have hdy0 : HasDerivAt (fun t : ℝ => F (g x) t)
      (D (0, 1)) (h x) := by
    have hy := hF.hasFDerivAt.comp (h x)
      ((hasDerivAt_const (h x) (g x)).hasFDerivAt.prodMk
        (hasDerivAt_id (h x)).hasFDerivAt)
    simpa [D, Function.comp_def, Function.uncurry] using hy.hasDerivAt
  have hdy : partialY F (g x) (h x) = D (0, 1) := by
    change deriv (fun t : ℝ => F (g x) t) (h x) = D (0, 1)
    exact hdy0.deriv
  have hlin : D (dg, dh) = dg * D (1, 0) + dh * D (0, 1) := by
    calc
      D (dg, dh) = D (dg • (1, 0) + dh • (0, 1)) := by
        congr 1
        ext <;> simp
      _ = dg • D (1, 0) + dh • D (0, 1) := by
        rw [map_add, map_smul, map_smul]
      _ = dg * D (1, 0) + dh * D (0, 1) := by simp
  convert hc' using 1
  simpa [hdx, hdy] using hlin.symm

private theorem differentiableAt_uncurry_partialX
    {f : ℝ → ℝ → ℝ} {x y : ℝ}
    (h : ContDiffAt ℝ 2 (Function.uncurry f) (x, y)) :
    DifferentiableAt ℝ (Function.uncurry (partialX f)) (x, y) := by
  let F := Function.uncurry f
  let ex : ℝ × ℝ := (1, 0)
  let evX : ((ℝ × ℝ) →L[ℝ] ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.apply ℝ ℝ ex
  have hfd : ContDiffAt ℝ 1 (fderiv ℝ F) (x, y) := by
    simpa [F] using h.fderiv_right (by norm_num)
  have hD : DifferentiableAt ℝ
      (fun q : ℝ × ℝ => (fderiv ℝ F q) ex) (x, y) := by
    simpa [evX, Function.comp_def] using
      evX.differentiableAt.comp (x, y) (hfd.differentiableAt (by decide))
  have hnear : ∀ᶠ q : ℝ × ℝ in nhds (x, y),
      DifferentiableAt ℝ F q := by
    filter_upwards [h.eventually (by decide)] with q hq
    exact hq.differentiableAt (by decide)
  have heq : Function.uncurry (partialX f) =ᶠ[nhds (x, y)]
      (fun q : ℝ × ℝ => (fderiv ℝ F q) ex) := by
    filter_upwards [hnear] with q hq
    have hs := hq.hasFDerivAt.comp q.1
      ((hasDerivAt_id q.1).hasFDerivAt.prodMk
        (hasDerivAt_const q.1 q.2).hasFDerivAt)
    unfold partialX
    simpa [F, ex, Function.comp_def, Function.uncurry] using
      hs.hasDerivAt.deriv
  exact hD.congr_of_eventuallyEq heq

private theorem differentiableAt_uncurry_partialY
    {f : ℝ → ℝ → ℝ} {x y : ℝ}
    (h : ContDiffAt ℝ 2 (Function.uncurry f) (x, y)) :
    DifferentiableAt ℝ (Function.uncurry (partialY f)) (x, y) := by
  let F := Function.uncurry f
  let ey : ℝ × ℝ := (0, 1)
  let evY : ((ℝ × ℝ) →L[ℝ] ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.apply ℝ ℝ ey
  have hfd : ContDiffAt ℝ 1 (fderiv ℝ F) (x, y) := by
    simpa [F] using h.fderiv_right (by norm_num)
  have hD : DifferentiableAt ℝ
      (fun q : ℝ × ℝ => (fderiv ℝ F q) ey) (x, y) := by
    simpa [evY, Function.comp_def] using
      evY.differentiableAt.comp (x, y) (hfd.differentiableAt (by decide))
  have hnear : ∀ᶠ q : ℝ × ℝ in nhds (x, y),
      DifferentiableAt ℝ F q := by
    filter_upwards [h.eventually (by decide)] with q hq
    exact hq.differentiableAt (by decide)
  have heq : Function.uncurry (partialY f) =ᶠ[nhds (x, y)]
      (fun q : ℝ × ℝ => (fderiv ℝ F q) ey) := by
    filter_upwards [hnear] with q hq
    have hs := hq.hasFDerivAt.comp q.2
      ((hasDerivAt_const q.2 q.1).hasFDerivAt.prodMk
        (hasDerivAt_id q.2).hasFDerivAt)
    unfold partialY
    simpa [F, ey, Function.comp_def, Function.uncurry] using
      hs.hasDerivAt.deriv
  exact hD.congr_of_eventuallyEq heq

private theorem mixed_partial_comm
    {f : ℝ → ℝ → ℝ} {x y : ℝ}
    (h : ContDiffAt ℝ 2 (Function.uncurry f) (x, y)) :
    partialX (partialY f) x y = partialY (partialX f) x y := by
  let F := Function.uncurry f
  let D := fderiv ℝ (fderiv ℝ F) (x, y)
  let ex : ℝ × ℝ := (1, 0)
  let ey : ℝ × ℝ := (0, 1)
  have hnear : ∀ᶠ q : ℝ × ℝ in nhds (x, y),
      ContDiffAt ℝ 2 F q := by
    simpa [F] using h.eventually (by decide)
  have hnearX := (continuousAt_id.prodMk continuousAt_const).eventually hnear
  have hnearY := (continuousAt_const.prodMk continuousAt_id).eventually hnear
  have hpartialY : (fun t : ℝ => partialY f t y) =ᶠ[nhds x]
      (fun t : ℝ => (fderiv ℝ F (t, y)) ey) := by
    filter_upwards [hnearX] with t ht
    have hs := (ht.differentiableAt (by decide)).hasFDerivAt.comp y
      ((hasDerivAt_const y t).hasFDerivAt.prodMk
        (hasDerivAt_id y).hasFDerivAt)
    unfold partialY
    simpa [F, ey, Function.comp_def, Function.uncurry] using
      hs.hasDerivAt.deriv
  have hpartialX : (fun t : ℝ => partialX f x t) =ᶠ[nhds y]
      (fun t : ℝ => (fderiv ℝ F (x, t)) ex) := by
    filter_upwards [hnearY] with t ht
    have hs := (ht.differentiableAt (by decide)).hasFDerivAt.comp x
      ((hasDerivAt_id x).hasFDerivAt.prodMk
        (hasDerivAt_const x t).hasFDerivAt)
    unfold partialX
    simpa [F, ex, Function.comp_def, Function.uncurry] using
      hs.hasDerivAt.deriv
  have hc : ContDiffAt ℝ 1 (fderiv ℝ F) (x, y) := by
    simpa [F] using h.fderiv_right (by norm_num)
  have hd : DifferentiableAt ℝ (fderiv ℝ F) (x, y) :=
    hc.differentiableAt (by decide)
  have hFD : HasFDerivAt (fderiv ℝ F) D (x, y) := by
    simpa [D] using hd.hasFDerivAt
  let evY : ((ℝ × ℝ) →L[ℝ] ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.apply ℝ ℝ ey
  let evX : ((ℝ × ℝ) →L[ℝ] ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.apply ℝ ℝ ex
  have hEvalY := evY.hasFDerivAt.comp (x, y) hFD
  have hEvalX := evX.hasFDerivAt.comp (x, y) hFD
  have houtY : HasDerivAt
      (fun t : ℝ => (fderiv ℝ F (t, y)) ey) (D ex ey) x := by
    have hcomp := hEvalY.comp x
      ((hasDerivAt_id x).hasFDerivAt.prodMk
        (hasDerivAt_const x y).hasFDerivAt)
    simpa [evY, ex, ey, Function.comp_def] using hcomp.hasDerivAt
  have houtX : HasDerivAt
      (fun t : ℝ => (fderiv ℝ F (x, t)) ex) (D ey ex) y := by
    have hcomp := hEvalX.comp y
      ((hasDerivAt_const y x).hasFDerivAt.prodMk
        (hasDerivAt_id y).hasFDerivAt)
    simpa [evX, ex, ey, Function.comp_def] using hcomp.hasDerivAt
  have hlhs : partialX (partialY f) x y = D ex ey := by
    unfold partialX
    exact hpartialY.deriv_eq.trans houtY.deriv
  have hrhs : partialY (partialX f) x y = D ey ex := by
    unfold partialY
    exact hpartialX.deriv_eq.trans houtX.deriv
  have hsymm : D ex ey = D ey ex := by
    simpa [D, F, ex, ey] using
      h.isSymmSndFDerivAt (by norm_num)
        ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ)
  exact hlhs.trans (hsymm.trans hrhs.symm)

private theorem eventually_partialX_eq
    {f g : ℝ → ℝ → ℝ} {x y : ℝ}
    (hfg : ∀ᶠ p : ℝ × ℝ in nhds (x, y), f p.1 p.2 = g p.1 p.2) :
    ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      partialX f p.1 p.2 = partialX g p.1 p.2 := by
  rcases mem_nhds_iff.1 hfg with ⟨s, hs, hsopen, hxy⟩
  filter_upwards [hsopen.mem_nhds hxy] with p hp
  have hlocal : ∀ᶠ q : ℝ × ℝ in nhds p,
      f q.1 q.2 = g q.1 q.2 :=
    Filter.mem_of_superset (hsopen.mem_nhds hp) hs
  have hpull : (fun t : ℝ => f t p.2) =ᶠ[nhds p.1]
      (fun t : ℝ => g t p.2) := by
    simpa using (continuousAt_id.prodMk continuousAt_const).eventually hlocal
  unfold partialX
  exact hpull.deriv_eq

private theorem eventually_partialY_eq
    {f g : ℝ → ℝ → ℝ} {x y : ℝ}
    (hfg : ∀ᶠ p : ℝ × ℝ in nhds (x, y), f p.1 p.2 = g p.1 p.2) :
    ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      partialY f p.1 p.2 = partialY g p.1 p.2 := by
  rcases mem_nhds_iff.1 hfg with ⟨s, hs, hsopen, hxy⟩
  filter_upwards [hsopen.mem_nhds hxy] with p hp
  have hlocal : ∀ᶠ q : ℝ × ℝ in nhds p,
      f q.1 q.2 = g q.1 q.2 :=
    Filter.mem_of_superset (hsopen.mem_nhds hp) hs
  have hpull : (fun t : ℝ => f p.1 t) =ᶠ[nhds p.2]
      (fun t : ℝ => g p.1 t) := by
    simpa using (continuousAt_const.prodMk continuousAt_id).eventually hlocal
  unfold partialY
  exact hpull.deriv_eq

theorem gap1 (x φ : ℝ → ℝ → ℝ) (u v du dv : ℝ)
    (hx : ∀ᶠ p : ℝ × ℝ in nhds (u, v), x p.1 p.2 = φ p.1 p.2) :
    differential x u v du dv =
      partialX φ u v * du + partialY φ u v * dv := by
  have hx₁ : (fun t : ℝ => x t v) =ᶠ[nhds u] (fun t => φ t v) := by
    simpa using (continuousAt_id.prodMk continuousAt_const).eventually hx
  have hx₂ : (fun t : ℝ => x u t) =ᶠ[nhds v] (fun t => φ u t) := by
    simpa using (continuousAt_const.prodMk continuousAt_id).eventually hx
  simp only [differential, partialX, partialY]
  rw [hx₁.deriv_eq, hx₂.deriv_eq]

theorem gap2 (y ψ : ℝ → ℝ → ℝ) (u v du dv : ℝ)
    (hy : ∀ᶠ p : ℝ × ℝ in nhds (u, v), y p.1 p.2 = ψ p.1 p.2) :
    differential y u v du dv =
      partialX ψ u v * du + partialY ψ u v * dv := by
  have hy₁ : (fun t : ℝ => y t v) =ᶠ[nhds u] (fun t => ψ t v) := by
    simpa using (continuousAt_id.prodMk continuousAt_const).eventually hy
  have hy₂ : (fun t : ℝ => y u t) =ᶠ[nhds v] (fun t => ψ u t) := by
    simpa using (continuousAt_const.prodMk continuousAt_id).eventually hy
  simp only [differential, partialX, partialY]
  rw [hy₁.deriv_eq, hy₂.deriv_eq]

theorem gap3 (φ ψ : ℝ → ℝ → ℝ) (u v du dv : ℝ)
    (hCR1 : partialX φ u v = partialY ψ u v)
    (hCR2 : partialY φ u v = -partialX ψ u v) :
    partialX ψ u v * du + partialY ψ u v * dv =
      -partialY φ u v * du + partialX φ u v * dv := by
  rw [hCR1, hCR2]
  ring

theorem gap4 (y φ ψ : ℝ → ℝ → ℝ) (u v du dv : ℝ)
    (hy : differential y u v du dv =
      partialX ψ u v * du + partialY ψ u v * dv)
    (hCR : partialX ψ u v * du + partialY ψ u v * dv =
      -partialY φ u v * du + partialX φ u v * dv) :
    differential y u v du dv =
      -partialY φ u v * du + partialX φ u v * dv := by
  exact hy.trans hCR

theorem gap5 (φ : ℝ → ℝ → ℝ) (u v : ℝ)
    (hLocalDiffeomorphism : conformalScale φ u v ≠ 0) :
    conformalScale φ u v ≠ 0 := by
  exact hLocalDiffeomorphism

theorem gap6 (φ : ℝ → ℝ → ℝ) (u v du dv dx dy : ℝ)
    (hScale : conformalScale φ u v ≠ 0)
    (hDx : dx = partialX φ u v * du + partialY φ u v * dv)
    (hDy : dy = -partialY φ u v * du + partialX φ u v * dv) :
    du = 1 / conformalScale φ u v *
      (partialX φ u v * dx - partialY φ u v * dy) := by
  rw [hDx, hDy]
  unfold conformalScale at hScale ⊢
  field_simp
  nlinarith

theorem gap7 (φ : ℝ → ℝ → ℝ) (u v du dv dx dy : ℝ)
    (hScale : conformalScale φ u v ≠ 0)
    (hDx : dx = partialX φ u v * du + partialY φ u v * dv)
    (hDy : dy = -partialY φ u v * du + partialX φ u v * dv) :
    dv = 1 / conformalScale φ u v *
      (partialY φ u v * dx + partialX φ u v * dy) := by
  rw [hDx, hDy]
  unfold conformalScale at hScale ⊢
  field_simp
  nlinarith

theorem gap8 (φ U : ℝ → ℝ → ℝ) (u v x y : ℝ)
    (hInverseCoefficient :
      partialX U x y = 1 / conformalScale φ u v * partialX φ u v) :
    partialX U x y = 1 / conformalScale φ u v * partialX φ u v := by
  exact hInverseCoefficient

theorem gap9 (φ V : ℝ → ℝ → ℝ) (u v x y : ℝ)
    (hInverseCoefficient :
      1 / conformalScale φ u v * partialX φ u v = partialY V x y) :
    1 / conformalScale φ u v * partialX φ u v = partialY V x y := by
  exact hInverseCoefficient

theorem gap10 (U V : ℝ → ℝ → ℝ) (x y : ℝ)
    (a : ℝ)
    (hUx : partialX U x y = a)
    (hVy : a = partialY V x y) :
    partialX U x y = partialY V x y := by
  exact hUx.trans hVy

theorem gap11 (φ U : ℝ → ℝ → ℝ) (u v x y : ℝ)
    (hInverseCoefficient :
      partialY U x y = -(1 / conformalScale φ u v * partialY φ u v)) :
    partialY U x y = -(1 / conformalScale φ u v * partialY φ u v) := by
  exact hInverseCoefficient

theorem gap12 (φ V : ℝ → ℝ → ℝ) (u v x y : ℝ)
    (hInverseCoefficient :
      -(1 / conformalScale φ u v * partialY φ u v) = -partialX V x y) :
    -(1 / conformalScale φ u v * partialY φ u v) = -partialX V x y := by
  exact hInverseCoefficient

theorem gap13 (U V : ℝ → ℝ → ℝ) (x y : ℝ)
    (a : ℝ)
    (hUy : partialY U x y = a)
    (hVx : a = -partialX V x y) :
    partialY U x y = -partialX V x y := by
  exact hUy.trans hVx

theorem gap14 (φ U : ℝ → ℝ → ℝ) (u v x y : ℝ)
    (hScale : conformalScale φ u v ≠ 0)
    (hUx : partialX U x y = 1 / conformalScale φ u v * partialX φ u v)
    (hUy : partialY U x y = -(1 / conformalScale φ u v * partialY φ u v)) :
    partialX U x y ^ 2 + partialY U x y ^ 2 =
      1 / conformalScale φ u v := by
  rw [hUx, hUy]
  unfold conformalScale at hScale ⊢
  field_simp

theorem gap15 (U V z Z : ℝ → ℝ → ℝ) (x y u v : ℝ)
    (hPoint : u = U x y ∧ v = V x y)
    (hCompose : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      Z p.1 p.2 = z (U p.1 p.2) (V p.1 p.2))
    (hC2z : ContDiffAt ℝ 2 (Function.uncurry z) (u, v))
    (hC2U : ContDiffAt ℝ 2 (Function.uncurry U) (x, y))
    (hC2V : ContDiffAt ℝ 2 (Function.uncurry V) (x, y))
    (hCR1 : partialX U x y = partialY V x y)
    (hCR2 : partialY U x y = -partialX V x y)
    (hHarmonicU : partialXX U x y + partialYY U x y = 0)
    (hHarmonicV : partialXX V x y + partialYY V x y = 0) :
    partialXX Z x y + partialYY Z x y =
      (partialX U x y ^ 2 + partialY U x y ^ 2) *
        (partialXX z u v + partialYY z u v) := by
  rcases hPoint with ⟨rfl, rfl⟩
  have hUV : Filter.Tendsto
      (fun p : ℝ × ℝ => (U p.1 p.2, V p.1 p.2))
      (nhds (x, y)) (nhds (U x y, V x y)) := by
    simpa [Function.uncurry] using
      hC2U.continuousAt.prodMk hC2V.continuousAt
  have hC2zNear : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      ContDiffAt ℝ 2 (Function.uncurry z) (U p.1 p.2, V p.1 p.2) :=
    hUV.eventually (hC2z.eventually (by decide))
  have hC2UNear : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      ContDiffAt ℝ 2 (Function.uncurry U) p :=
    hC2U.eventually (by decide)
  have hC2VNear : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      ContDiffAt ℝ 2 (Function.uncurry V) p :=
    hC2V.eventually (by decide)
  have hComposeX := eventually_partialX_eq
    (f := Z) (g := fun a b => z (U a b) (V a b)) hCompose
  have hZx : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      partialX Z p.1 p.2 =
        partialX z (U p.1 p.2) (V p.1 p.2) * partialX U p.1 p.2 +
          partialY z (U p.1 p.2) (V p.1 p.2) * partialX V p.1 p.2 := by
    filter_upwards [hComposeX, hC2zNear, hC2UNear, hC2VNear] with p hp hz hU hV
    calc
      partialX Z p.1 p.2 =
          partialX (fun a b => z (U a b) (V a b)) p.1 p.2 := hp
      _ = _ := by
        have hu := hasDerivAt_partialX U p.1 p.2
          (hU.differentiableAt (by decide))
        have hv := hasDerivAt_partialX V p.1 p.2
          (hV.differentiableAt (by decide))
        change deriv (fun t => z (U t p.2) (V t p.2)) p.1 = _
        rw [(hasDerivAt_comp₂ z (fun t => U t p.2) (fun t => V t p.2)
          (hz.differentiableAt (by decide)) hu hv).deriv]
        ring
  have hComposeY := eventually_partialY_eq
    (f := Z) (g := fun a b => z (U a b) (V a b)) hCompose
  have hZy : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      partialY Z p.1 p.2 =
        partialX z (U p.1 p.2) (V p.1 p.2) * partialY U p.1 p.2 +
          partialY z (U p.1 p.2) (V p.1 p.2) * partialY V p.1 p.2 := by
    filter_upwards [hComposeY, hC2zNear, hC2UNear, hC2VNear] with p hp hz hU hV
    calc
      partialY Z p.1 p.2 =
          partialY (fun a b => z (U a b) (V a b)) p.1 p.2 := hp
      _ = _ := by
        have hu := hasDerivAt_partialY U p.1 p.2
          (hU.differentiableAt (by decide))
        have hv := hasDerivAt_partialY V p.1 p.2
          (hV.differentiableAt (by decide))
        change deriv (fun t => z (U p.1 t) (V p.1 t)) p.2 = _
        rw [(hasDerivAt_comp₂ z (fun t => U p.1 t) (fun t => V p.1 t)
          (hz.differentiableAt (by decide)) hu hv).deriv]
        ring
  have hDiffz := hC2z.differentiableAt (by decide)
  have hDiffU := hC2U.differentiableAt (by decide)
  have hDiffV := hC2V.differentiableAt (by decide)
  have hDiffZx := differentiableAt_uncurry_partialX hC2z
  have hDiffZy := differentiableAt_uncurry_partialY hC2z
  have hDiffUx := differentiableAt_uncurry_partialX hC2U
  have hDiffUy := differentiableAt_uncurry_partialY hC2U
  have hDiffVx := differentiableAt_uncurry_partialX hC2V
  have hDiffVy := differentiableAt_uncurry_partialY hC2V
  have hmix : partialX (partialY z) (U x y) (V x y) =
      partialY (partialX z) (U x y) (V x y) :=
    mixed_partial_comm hC2z
  have hXX :
      partialXX Z x y =
        partialXX z (U x y) (V x y) * partialX U x y ^ 2 +
          2 * partialY (partialX z) (U x y) (V x y) *
            partialX U x y * partialX V x y +
          partialYY z (U x y) (V x y) * partialX V x y ^ 2 +
          partialX z (U x y) (V x y) * partialXX U x y +
          partialY z (U x y) (V x y) * partialXX V x y := by
    have hu := hasDerivAt_partialX U x y hDiffU
    have hv := hasDerivAt_partialX V x y hDiffV
    have hux := hasDerivAt_partialX (partialX U) x y hDiffUx
    have hvx := hasDerivAt_partialX (partialX V) x y hDiffVx
    have hA := hasDerivAt_comp₂ (partialX z) (fun t => U t y)
      (fun t => V t y) hDiffZx hu hv
    have hB := hasDerivAt_comp₂ (partialY z) (fun t => U t y)
      (fun t => V t y) hDiffZy hu hv
    have hR := (hA.mul hux).add (hB.mul hvx)
    change HasDerivAt
      (fun t : ℝ =>
        partialX z (U t y) (V t y) * partialX U t y +
          partialY z (U t y) (V t y) * partialX V t y) _ x at hR
    have hdR := hR.deriv
    rw [hmix] at hdR
    have hz : (fun t : ℝ => partialX Z t y) =ᶠ[nhds x]
        (fun t : ℝ =>
          partialX z (U t y) (V t y) * partialX U t y +
            partialY z (U t y) (V t y) * partialX V t y) := by
      simpa using (continuousAt_id.prodMk continuousAt_const).eventually hZx
    change deriv (fun t : ℝ => partialX Z t y) x = _
    calc
      deriv (fun t : ℝ => partialX Z t y) x =
          deriv (fun t : ℝ =>
            partialX z (U t y) (V t y) * partialX U t y +
              partialY z (U t y) (V t y) * partialX V t y) x := hz.deriv_eq
      _ = _ := by
        rw [hdR]
        unfold partialXX partialYY
        ring
  have hYY :
      partialYY Z x y =
        partialXX z (U x y) (V x y) * partialY U x y ^ 2 +
          2 * partialY (partialX z) (U x y) (V x y) *
            partialY U x y * partialY V x y +
          partialYY z (U x y) (V x y) * partialY V x y ^ 2 +
          partialX z (U x y) (V x y) * partialYY U x y +
          partialY z (U x y) (V x y) * partialYY V x y := by
    have hu := hasDerivAt_partialY U x y hDiffU
    have hv := hasDerivAt_partialY V x y hDiffV
    have huy := hasDerivAt_partialY (partialY U) x y hDiffUy
    have hvy := hasDerivAt_partialY (partialY V) x y hDiffVy
    have hA := hasDerivAt_comp₂ (partialX z) (fun t => U x t)
      (fun t => V x t) hDiffZx hu hv
    have hB := hasDerivAt_comp₂ (partialY z) (fun t => U x t)
      (fun t => V x t) hDiffZy hu hv
    have hR := (hA.mul huy).add (hB.mul hvy)
    change HasDerivAt
      (fun t : ℝ =>
        partialX z (U x t) (V x t) * partialY U x t +
          partialY z (U x t) (V x t) * partialY V x t) _ y at hR
    have hdR := hR.deriv
    rw [hmix] at hdR
    have hz : (fun t : ℝ => partialY Z x t) =ᶠ[nhds y]
        (fun t : ℝ =>
          partialX z (U x t) (V x t) * partialY U x t +
            partialY z (U x t) (V x t) * partialY V x t) := by
      simpa using (continuousAt_const.prodMk continuousAt_id).eventually hZy
    change deriv (fun t : ℝ => partialY Z x t) y = _
    calc
      deriv (fun t : ℝ => partialY Z x t) y =
          deriv (fun t : ℝ =>
            partialX z (U x t) (V x t) * partialY U x t +
              partialY z (U x t) (V x t) * partialY V x t) y := hz.deriv_eq
      _ = _ := by
        rw [hdR]
        unfold partialXX partialYY
        ring
  have hVx : partialX V x y = -partialY U x y := by
    linarith
  have hUyy : partialYY U x y = -partialXX U x y := by
    linarith
  have hVyy : partialYY V x y = -partialXX V x y := by
    linarith
  rw [hXX, hYY, hVx, ← hCR1, hUyy, hVyy]
  ring

theorem gap16 (φ U z : ℝ → ℝ → ℝ) (u v x y : ℝ)
    (hScale :
      partialX U x y ^ 2 + partialY U x y ^ 2 =
        1 / conformalScale φ u v) :
    (partialX U x y ^ 2 + partialY U x y ^ 2) *
        (partialXX z u v + partialYY z u v) =
      1 / conformalScale φ u v * (partialXX z u v + partialYY z u v) := by
  rw [hScale]

theorem gap17 (φ z Z : ℝ → ℝ → ℝ) (u v x y : ℝ)
    (hPhysicalPDE : partialXX Z x y + partialYY Z x y = 0)
    (hTransform : partialXX Z x y + partialYY Z x y =
      1 / conformalScale φ u v * (partialXX z u v + partialYY z u v)) :
    1 / conformalScale φ u v * (partialXX z u v + partialYY z u v) = 0 := by
  exact hTransform.symm.trans hPhysicalPDE

theorem gap18 (Z : ℝ → ℝ → ℝ) (x y : ℝ)
    (q : ℝ)
    (hTransform : partialXX Z x y + partialYY Z x y = q)
    (hScaled : q = 0) :
    partialXX Z x y + partialYY Z x y = 0 := by
  exact hTransform.trans hScaled

theorem gap19 (φ z : ℝ → ℝ → ℝ) (u v : ℝ)
    (hScale : conformalScale φ u v ≠ 0)
    (hScaled : 1 / conformalScale φ u v *
      (partialXX z u v + partialYY z u v) = 0) :
    partialXX z u v + partialYY z u v = 0 := by
  apply (mul_eq_zero.mp hScaled).resolve_left
  exact one_div_ne_zero hScale

theorem gap20 (φ z Z : ℝ → ℝ → ℝ) (u v x y : ℝ)
    (hScale : conformalScale φ u v ≠ 0)
    (hTransform : partialXX Z x y + partialYY Z x y =
      1 / conformalScale φ u v * (partialXX z u v + partialYY z u v)) :
    partialXX Z x y + partialYY Z x y = 0 →
      partialXX z u v + partialYY z u v = 0 := by
  intro hPDE
  apply (mul_eq_zero.mp (hTransform.symm.trans hPDE)).resolve_left
  exact one_div_ne_zero hScale

end

end ProofGap.Exercise3502
