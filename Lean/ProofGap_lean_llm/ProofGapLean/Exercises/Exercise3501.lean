import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3501

noncomputable section

def partialX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f t y) x

def partialY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f x t) y

def partialXX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  partialX (partialX f) x y

def partialXY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  partialY (partialX f) x y

def partialYY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  partialY (partialY f) x y

def pde (A B C : ℝ) (U : ℝ → ℝ → ℝ) (x y : ℝ) : Prop :=
  A * partialXX U x y + 2 * B * partialXY U x y +
    C * partialYY U x y = 0

def transformedPDE (A B C lam1 lam2 : ℝ)
    (V : ℝ → ℝ → ℝ) (ξ η : ℝ) : Prop :=
  (A + 2 * B * lam1 + C * lam1 ^ 2) * partialXX V ξ η +
    2 * (A + B * (lam1 + lam2) + C * lam1 * lam2) *
      partialXY V ξ η +
    (A + 2 * B * lam2 + C * lam2 ^ 2) * partialYY V ξ η = 0

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
      (dg * partialX F (g x) (h x) +
        dh * partialY F (g x) (h x)) x := by
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
      evX.differentiableAt.comp (x, y)
        (hfd.differentiableAt (by decide))
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
      evY.differentiableAt.comp (x, y)
        (hfd.differentiableAt (by decide))
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
    partialX (partialY f) x y = partialXY f x y := by
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
  have hrhs : partialXY f x y = D ey ex := by
    unfold partialXY partialY
    exact hpartialX.deriv_eq.trans houtX.deriv
  have hsymm : D ex ey = D ey ex := by
    simpa [D, F, ex, ey] using
      h.isSymmSndFDerivAt (by norm_num)
        ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ)
  exact hlhs.trans (hsymm.trans hrhs.symm)

private theorem affineX
    {w : ℝ → ℝ → ℝ} {lam x y : ℝ}
    (hw : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      w p.1 p.2 = p.1 + lam * p.2) :
    HasDerivAt (fun t => w t y) 1 x := by
  have heq : (fun t : ℝ => w t y) =ᶠ[nhds x]
      (fun t : ℝ => t + lam * y) := by
    simpa using (continuousAt_id.prodMk continuousAt_const).eventually hw
  exact ((hasDerivAt_id x).add_const _).congr_of_eventuallyEq heq

private theorem affineY
    {w : ℝ → ℝ → ℝ} {lam x y : ℝ}
    (hw : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      w p.1 p.2 = p.1 + lam * p.2) :
    HasDerivAt (fun t => w x t) lam y := by
  have heq : (fun t : ℝ => w x t) =ᶠ[nhds y]
      (fun t : ℝ => x + lam * t) := by
    simpa using (continuousAt_const.prodMk continuousAt_id).eventually hw
  have hbase : HasDerivAt (fun t : ℝ => x + lam * t) lam y := by
    convert ((hasDerivAt_id y).const_mul lam).const_add x using 1 <;> ring
  exact hbase.congr_of_eventuallyEq heq

theorem gap1 (ξ η U V : ℝ → ℝ → ℝ) (lam1 lam2 x y : ℝ)
    (hξ : ∀ᶠ p : ℝ × ℝ in nhds (x, y), ξ p.1 p.2 = p.1 + lam1 * p.2)
    (hη : ∀ᶠ p : ℝ × ℝ in nhds (x, y), η p.1 p.2 = p.1 + lam2 * p.2)
    (hCompose : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      U p.1 p.2 = V (ξ p.1 p.2) (η p.1 p.2))
    (hDiffV : DifferentiableAt ℝ (Function.uncurry V) (ξ x y, η x y)) :
    partialX U x y = partialX V (ξ x y) (η x y) +
      partialY V (ξ x y) (η x y) := by
  have hU : (fun t : ℝ => U t y) =ᶠ[nhds x]
      (fun t : ℝ => V (ξ t y) (η t y)) := by
    simpa using (continuousAt_id.prodMk continuousAt_const).eventually hCompose
  change deriv (fun t : ℝ => U t y) x = _
  calc
    deriv (fun t : ℝ => U t y) x =
        deriv (fun t : ℝ => V (ξ t y) (η t y)) x := hU.deriv_eq
    _ = _ := by
      convert (hasDerivAt_comp₂ V (fun t => ξ t y) (fun t => η t y)
        hDiffV (affineX hξ) (affineX hη)).deriv using 1 <;> ring

theorem gap2 (ξ η U V : ℝ → ℝ → ℝ) (lam1 lam2 x y : ℝ)
    (hξ : ∀ᶠ p : ℝ × ℝ in nhds (x, y), ξ p.1 p.2 = p.1 + lam1 * p.2)
    (hη : ∀ᶠ p : ℝ × ℝ in nhds (x, y), η p.1 p.2 = p.1 + lam2 * p.2)
    (hCompose : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      U p.1 p.2 = V (ξ p.1 p.2) (η p.1 p.2))
    (hDiffV : DifferentiableAt ℝ (Function.uncurry V) (ξ x y, η x y)) :
    partialY U x y = lam1 * partialX V (ξ x y) (η x y) +
      lam2 * partialY V (ξ x y) (η x y) := by
  have hU : (fun t : ℝ => U x t) =ᶠ[nhds y]
      (fun t : ℝ => V (ξ x t) (η x t)) := by
    simpa using (continuousAt_const.prodMk continuousAt_id).eventually hCompose
  change deriv (fun t : ℝ => U x t) y = _
  calc
    deriv (fun t : ℝ => U x t) y =
        deriv (fun t : ℝ => V (ξ x t) (η x t)) y := hU.deriv_eq
    _ = _ := by
      convert (hasDerivAt_comp₂ V (fun t => ξ x t) (fun t => η x t)
        hDiffV (affineY hξ) (affineY hη)).deriv using 1 <;> ring

theorem gap3 (ξ η U V : ℝ → ℝ → ℝ) (lam1 lam2 x y : ℝ)
    (hUx : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      partialX U p.1 p.2 = partialX V (ξ p.1 p.2) (η p.1 p.2) +
        partialY V (ξ p.1 p.2) (η p.1 p.2))
    (hξ : ∀ᶠ p : ℝ × ℝ in nhds (x, y), ξ p.1 p.2 = p.1 + lam1 * p.2)
    (hη : ∀ᶠ p : ℝ × ℝ in nhds (x, y), η p.1 p.2 = p.1 + lam2 * p.2)
    (hC2V : ContDiffAt ℝ 2 (Function.uncurry V) (ξ x y, η x y)) :
    partialXX U x y = partialXX V (ξ x y) (η x y) +
      2 * partialXY V (ξ x y) (η x y) +
      partialYY V (ξ x y) (η x y) := by
  have hA := hasDerivAt_comp₂ (partialX V) (fun t => ξ t y)
    (fun t => η t y) (differentiableAt_uncurry_partialX hC2V)
      (affineX hξ) (affineX hη)
  have hB := hasDerivAt_comp₂ (partialY V) (fun t => ξ t y)
    (fun t => η t y) (differentiableAt_uncurry_partialY hC2V)
      (affineX hξ) (affineX hη)
  have hd := (hA.add hB).deriv
  rw [mixed_partial_comm hC2V] at hd
  have hd' :
      deriv (fun t : ℝ =>
        partialX V (ξ t y) (η t y) + partialY V (ξ t y) (η t y)) x =
        1 * partialX (partialX V) (ξ x y) (η x y) +
          1 * partialY (partialX V) (ξ x y) (η x y) +
          (1 * partialXY V (ξ x y) (η x y) +
            1 * partialY (partialY V) (ξ x y) (η x y)) := by
    simpa only using hd
  have hlocal : (fun t : ℝ => partialX U t y) =ᶠ[nhds x]
      (fun t : ℝ =>
        partialX V (ξ t y) (η t y) + partialY V (ξ t y) (η t y)) := by
    simpa using (continuousAt_id.prodMk continuousAt_const).eventually hUx
  change deriv (fun t : ℝ => partialX U t y) x = _
  rw [hlocal.deriv_eq, hd']
  unfold partialXX partialXY partialYY
  ring

theorem gap4 (ξ η U V : ℝ → ℝ → ℝ) (lam1 lam2 x y : ℝ)
    (hUx : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      partialX U p.1 p.2 = partialX V (ξ p.1 p.2) (η p.1 p.2) +
        partialY V (ξ p.1 p.2) (η p.1 p.2))
    (hξ : ∀ᶠ p : ℝ × ℝ in nhds (x, y), ξ p.1 p.2 = p.1 + lam1 * p.2)
    (hη : ∀ᶠ p : ℝ × ℝ in nhds (x, y), η p.1 p.2 = p.1 + lam2 * p.2)
    (hC2V : ContDiffAt ℝ 2 (Function.uncurry V) (ξ x y, η x y)) :
    partialXY U x y = lam1 * partialXX V (ξ x y) (η x y) +
      (lam1 + lam2) * partialXY V (ξ x y) (η x y) +
      lam2 * partialYY V (ξ x y) (η x y) := by
  have hA := hasDerivAt_comp₂ (partialX V) (fun t => ξ x t)
    (fun t => η x t) (differentiableAt_uncurry_partialX hC2V)
      (affineY hξ) (affineY hη)
  have hB := hasDerivAt_comp₂ (partialY V) (fun t => ξ x t)
    (fun t => η x t) (differentiableAt_uncurry_partialY hC2V)
      (affineY hξ) (affineY hη)
  have hd := (hA.add hB).deriv
  rw [mixed_partial_comm hC2V] at hd
  have hd' :
      deriv (fun t : ℝ =>
        partialX V (ξ x t) (η x t) + partialY V (ξ x t) (η x t)) y =
        lam1 * partialX (partialX V) (ξ x y) (η x y) +
          lam2 * partialY (partialX V) (ξ x y) (η x y) +
          (lam1 * partialXY V (ξ x y) (η x y) +
            lam2 * partialY (partialY V) (ξ x y) (η x y)) := by
    simpa only using hd
  have hlocal : (fun t : ℝ => partialX U x t) =ᶠ[nhds y]
      (fun t : ℝ =>
        partialX V (ξ x t) (η x t) + partialY V (ξ x t) (η x t)) := by
    simpa using (continuousAt_const.prodMk continuousAt_id).eventually hUx
  change deriv (fun t : ℝ => partialX U x t) y = _
  rw [hlocal.deriv_eq, hd']
  unfold partialXX partialXY partialYY
  ring

theorem gap5 (ξ η U V : ℝ → ℝ → ℝ) (lam1 lam2 x y : ℝ)
    (hUy : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      partialY U p.1 p.2 =
        lam1 * partialX V (ξ p.1 p.2) (η p.1 p.2) +
          lam2 * partialY V (ξ p.1 p.2) (η p.1 p.2))
    (hξ : ∀ᶠ p : ℝ × ℝ in nhds (x, y), ξ p.1 p.2 = p.1 + lam1 * p.2)
    (hη : ∀ᶠ p : ℝ × ℝ in nhds (x, y), η p.1 p.2 = p.1 + lam2 * p.2)
    (hC2V : ContDiffAt ℝ 2 (Function.uncurry V) (ξ x y, η x y)) :
    partialYY U x y = lam1 ^ 2 * partialXX V (ξ x y) (η x y) +
      2 * lam1 * lam2 * partialXY V (ξ x y) (η x y) +
      lam2 ^ 2 * partialYY V (ξ x y) (η x y) := by
  have hA := hasDerivAt_comp₂ (partialX V) (fun t => ξ x t)
    (fun t => η x t) (differentiableAt_uncurry_partialX hC2V)
      (affineY hξ) (affineY hη)
  have hB := hasDerivAt_comp₂ (partialY V) (fun t => ξ x t)
    (fun t => η x t) (differentiableAt_uncurry_partialY hC2V)
      (affineY hξ) (affineY hη)
  have hd := ((hA.const_mul lam1).add (hB.const_mul lam2)).deriv
  rw [mixed_partial_comm hC2V] at hd
  have hd' :
      deriv (fun t : ℝ =>
        lam1 * partialX V (ξ x t) (η x t) +
          lam2 * partialY V (ξ x t) (η x t)) y =
        lam1 * (lam1 * partialX (partialX V) (ξ x y) (η x y) +
          lam2 * partialY (partialX V) (ξ x y) (η x y)) +
          lam2 * (lam1 * partialXY V (ξ x y) (η x y) +
            lam2 * partialY (partialY V) (ξ x y) (η x y)) := by
    simpa only using hd
  have hlocal : (fun t : ℝ => partialY U x t) =ᶠ[nhds y]
      (fun t : ℝ =>
        lam1 * partialX V (ξ x t) (η x t) +
          lam2 * partialY V (ξ x t) (η x t)) := by
    simpa using (continuousAt_const.prodMk continuousAt_id).eventually hUy
  change deriv (fun t : ℝ => partialY U x t) y = _
  rw [hlocal.deriv_eq, hd']
  unfold partialXX partialXY partialYY
  ring

theorem gap6 (A B C lam1 lam2 : ℝ)
    (ξ η U V : ℝ → ℝ → ℝ) (x y : ℝ)
    (hUxx : partialXX U x y = partialXX V (ξ x y) (η x y) +
      2 * partialXY V (ξ x y) (η x y) + partialYY V (ξ x y) (η x y))
    (hUxy : partialXY U x y = lam1 * partialXX V (ξ x y) (η x y) +
      (lam1 + lam2) * partialXY V (ξ x y) (η x y) +
      lam2 * partialYY V (ξ x y) (η x y))
    (hUyy : partialYY U x y = lam1 ^ 2 * partialXX V (ξ x y) (η x y) +
      2 * lam1 * lam2 * partialXY V (ξ x y) (η x y) +
      lam2 ^ 2 * partialYY V (ξ x y) (η x y)) :
    pde A B C U x y ↔
      transformedPDE A B C lam1 lam2 V (ξ x y) (η x y) := by
  unfold pde transformedPDE
  rw [hUxx, hUxy, hUyy]
  constructor <;> intro h <;> linarith

theorem gap7 (A B C lam1 : ℝ)
    (hC : C ≠ 0) (hDisc : A * C - B ^ 2 < 0)
    (hlam1 : lam1 = (-B + Real.sqrt (B ^ 2 - A * C)) / C) :
    A + 2 * B * lam1 + C * lam1 ^ 2 = 0 := by
  have hnonneg : 0 ≤ B ^ 2 - A * C := by linarith
  have hsqrt := Real.sq_sqrt hnonneg
  rw [hlam1]
  field_simp [hC]
  nlinarith

theorem gap8 (A B C lam2 : ℝ)
    (hC : C ≠ 0) (hDisc : A * C - B ^ 2 < 0)
    (hlam2 : lam2 = (-B - Real.sqrt (B ^ 2 - A * C)) / C) :
    A + 2 * B * lam2 + C * lam2 ^ 2 = 0 := by
  have hnonneg : 0 ≤ B ^ 2 - A * C := by linarith
  have hsqrt := Real.sq_sqrt hnonneg
  rw [hlam2]
  field_simp [hC]
  nlinarith

theorem gap9 (A B C lam1 lam2 : ℝ)
    (hC : C ≠ 0)
    (hlam1 : lam1 = (-B + Real.sqrt (B ^ 2 - A * C)) / C)
    (hlam2 : lam2 = (-B - Real.sqrt (B ^ 2 - A * C)) / C) :
    lam1 + lam2 = -(2 * B / C) := by
  rw [hlam1, hlam2]
  field_simp [hC]
  ring

theorem gap10 (A B C lam1 lam2 : ℝ)
    (hC : C ≠ 0) (hDisc : A * C - B ^ 2 < 0)
    (hlam1 : lam1 = (-B + Real.sqrt (B ^ 2 - A * C)) / C)
    (hlam2 : lam2 = (-B - Real.sqrt (B ^ 2 - A * C)) / C) :
    lam1 * lam2 = A / C := by
  have hnonneg : 0 ≤ B ^ 2 - A * C := by linarith
  have hsqrt := Real.sq_sqrt hnonneg
  rw [hlam1, hlam2]
  field_simp [hC]
  nlinarith

theorem gap11 (A B C lam1 lam2 : ℝ)
    (hC : C ≠ 0)
    (hSum : lam1 + lam2 = -(2 * B / C))
    (hProduct : lam1 * lam2 = A / C) :
    A + B * (lam1 + lam2) + C * lam1 * lam2 =
      2 * (A * C - B ^ 2) / C := by
  rw [hSum, mul_assoc C lam1 lam2, hProduct]
  field_simp [hC]
  ring

theorem gap12 (A B C : ℝ)
    (hC : C ≠ 0) (hDisc : A * C - B ^ 2 < 0) :
    2 * (A * C - B ^ 2) / C ≠ 0 := by
  intro h
  have hnum : A * C - B ^ 2 = 0 := by
    field_simp [hC] at h
    linarith
  linarith

theorem gap13 (A B C lam1 lam2 : ℝ)
    (hCoefficient :
      A + B * (lam1 + lam2) + C * lam1 * lam2 =
        2 * (A * C - B ^ 2) / C)
    (hNonzero : 2 * (A * C - B ^ 2) / C ≠ 0) :
    A + B * (lam1 + lam2) + C * lam1 * lam2 ≠ 0 := by
  rw [hCoefficient]
  exact hNonzero

theorem gap14 (A B C lam1 lam2 : ℝ)
    (ξ η U V : ℝ → ℝ → ℝ) (x y : ℝ)
    (hTransform : pde A B C U x y ↔
      transformedPDE A B C lam1 lam2 V (ξ x y) (η x y))
    (hRoot₁ : A + 2 * B * lam1 + C * lam1 ^ 2 = 0)
    (hRoot₂ : A + 2 * B * lam2 + C * lam2 ^ 2 = 0)
    (hMixed : A + B * (lam1 + lam2) + C * lam1 * lam2 ≠ 0) :
    pde A B C U x y ↔ partialXY V (ξ x y) (η x y) = 0 := by
  rw [hTransform]
  unfold transformedPDE
  rw [hRoot₁, hRoot₂]
  simp only [zero_mul, zero_add, add_zero]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with htwo | hxy
    · exact False.elim (by
        apply hMixed
        have : (2 : ℝ) ≠ 0 := by norm_num
        exact (mul_eq_zero.mp htwo).resolve_left this)
    · exact hxy
  · intro h
    rw [h]
    ring

theorem gap15 (V : ℝ → ℝ → ℝ) (ξ η : ℝ) :
    partialXY V ξ η = partialXY V ξ η := by
  rfl

theorem gap16 (A B C : ℝ) (U : ℝ → ℝ → ℝ) (x y : ℝ) (q : ℝ)
    (hCanonical : pde A B C U x y ↔ q = 0) :
    pde A B C U x y ↔ q = 0 := by
  exact hCanonical

theorem gap17 (A B C : ℝ) (U : ℝ → ℝ → ℝ) (x y : ℝ) (q : ℝ)
    (hCanonical : pde A B C U x y ↔ q = 0) :
    pde A B C U x y ↔ q = 0 := by
  exact hCanonical

theorem gap18 (V : ℝ → ℝ → ℝ)
    (hCanonical : ∀ ξ η, partialXY V ξ η = 0)
    (hDiff : ∀ ξ, Differentiable ℝ (fun η => partialX V ξ η)) :
    ∃ f : ℝ → ℝ, ∀ ξ η, partialX V ξ η = f ξ := by
  refine ⟨fun ξ => partialX V ξ 0, ?_⟩
  intro ξ η
  exact is_const_of_deriv_eq_zero (hDiff ξ)
    (fun t => by simpa [partialXY, partialY] using hCanonical ξ t) η 0

theorem gap19 (V : ℝ → ℝ → ℝ)
    (hSeparated : ∃ f : ℝ → ℝ, ∀ ξ η, partialX V ξ η = f ξ)
    (hDiff : ∀ η, Differentiable ℝ (fun ξ => V ξ η)) :
    ∃ Φ Ψ : ℝ → ℝ, ∀ ξ η, V ξ η = Φ ξ + Ψ η := by
  rcases hSeparated with ⟨f, hf⟩
  refine ⟨fun ξ => V ξ 0, fun η => V 0 η - V 0 0, ?_⟩
  intro ξ η
  have hzero : ∀ t : ℝ,
      deriv (fun s : ℝ => V s η - V s 0) t = 0 := by
    intro t
    rw [deriv_fun_sub (hDiff η t) (hDiff 0 t)]
    change partialX V t η - partialX V t 0 = 0
    rw [hf t η, hf t 0]
    ring
  have hconst := is_const_of_deriv_eq_zero ((hDiff η).sub (hDiff 0))
    hzero ξ 0
  change V ξ η - V ξ 0 = V 0 η - V 0 0 at hconst
  linarith

theorem gap20 (f : ℝ → ℝ)
    (hf : Continuous f) :
    ∃ Φ : ℝ → ℝ, ∀ ξ, deriv Φ ξ = f ξ := by
  refine ⟨fun ξ => ∫ t in (0 : ℝ)..ξ, f t, ?_⟩
  intro ξ
  exact (intervalIntegral.integral_hasDerivAt_right
    (hf.intervalIntegrable 0 ξ)
    hf.aestronglyMeasurable.stronglyMeasurableAtFilter
    hf.continuousAt).deriv

theorem gap21 (ξ η : ℝ → ℝ → ℝ) (Φ Ψ : ℝ → ℝ)
    (lam1 lam2 x y : ℝ)
    (hξ : ξ x y = x + lam1 * y)
    (hη : η x y = x + lam2 * y) :
    Φ (ξ x y) + Ψ (η x y) =
      Φ (x + lam1 * y) + Ψ (x + lam2 * y) := by
  rw [hξ, hη]

theorem gap22 (ξ η U V : ℝ → ℝ → ℝ) (Φ Ψ : ℝ → ℝ)
    (lam1 lam2 x y : ℝ)
    (hCompose : U x y = V (ξ x y) (η x y))
    (hGeneral : V (ξ x y) (η x y) = Φ (ξ x y) + Ψ (η x y))
    (hξ : ξ x y = x + lam1 * y)
    (hη : η x y = x + lam2 * y) :
    U x y = Φ (x + lam1 * y) + Ψ (x + lam2 * y) := by
  rw [hCompose, hGeneral, hξ, hη]

-- Statement correction: the original statement allowed the degenerate
-- equation A = B = C = 0, for which every U solves the PDE but a separated
-- representation need not exist.
theorem gap23 (A B C lam1 lam2 : ℝ) (U : ℝ → ℝ → ℝ)
    (hRoot₁ : A + 2 * B * lam1 + C * lam1 ^ 2 = 0)
    (hRoot₂ : A + 2 * B * lam2 + C * lam2 ^ 2 = 0)
    (hDistinct : lam1 ≠ lam2)
    (hMixed : A + B * (lam1 + lam2) + C * lam1 * lam2 ≠ 0)
    (hC2U : ContDiff ℝ 2 (Function.uncurry U)) :
    (∃ Φ Ψ : ℝ → ℝ,
      ContDiff ℝ 2 Φ ∧ ContDiff ℝ 2 Ψ ∧
        ∀ x y, U x y =
          Φ (x + lam1 * y) + Ψ (x + lam2 * y)) ↔
      ∀ x y, pde A B C U x y := by
  let ξf : ℝ → ℝ → ℝ := fun x y => x + lam1 * y
  let ηf : ℝ → ℝ → ℝ := fun x y => x + lam2 * y
  have hξevent : ∀ x y,
      ∀ᶠ p : ℝ × ℝ in nhds (x, y),
        ξf p.1 p.2 = p.1 + lam1 * p.2 :=
    fun _ _ => Filter.Eventually.of_forall (fun _ => rfl)
  have hηevent : ∀ x y,
      ∀ᶠ p : ℝ × ℝ in nhds (x, y),
        ηf p.1 p.2 = p.1 + lam2 * p.2 :=
    fun _ _ => Filter.Eventually.of_forall (fun _ => rfl)
  constructor
  · rintro ⟨Φ, Ψ, hΦ, hΨ, hUsep⟩
    let V : ℝ → ℝ → ℝ := fun a b => Φ a + Ψ b
    have hC2V : ContDiff ℝ 2 (Function.uncurry V) := by
      unfold V Function.uncurry
      exact
        (hΦ.comp (contDiff_fst : ContDiff ℝ 2 (Prod.fst : ℝ × ℝ → ℝ))).add
          (hΨ.comp (contDiff_snd : ContDiff ℝ 2 (Prod.snd : ℝ × ℝ → ℝ)))
    have hCompose : ∀ a b, U a b = V (ξf a b) (ηf a b) := by
      intro a b
      simpa [V, ξf, ηf] using hUsep a b
    have hUx : ∀ a b,
        partialX U a b =
          partialX V (ξf a b) (ηf a b) +
            partialY V (ξf a b) (ηf a b) := by
      intro a b
      exact gap1 ξf ηf U V lam1 lam2 a b
        (hξevent a b) (hηevent a b)
        (Filter.Eventually.of_forall (fun p => hCompose p.1 p.2))
        ((hC2V.differentiable (by decide)) (ξf a b, ηf a b))
    have hUy : ∀ a b,
        partialY U a b =
          lam1 * partialX V (ξf a b) (ηf a b) +
            lam2 * partialY V (ξf a b) (ηf a b) := by
      intro a b
      exact gap2 ξf ηf U V lam1 lam2 a b
        (hξevent a b) (hηevent a b)
        (Filter.Eventually.of_forall (fun p => hCompose p.1 p.2))
        ((hC2V.differentiable (by decide)) (ξf a b, ηf a b))
    have hVxy : ∀ a b, partialXY V a b = 0 := by
      intro a b
      have hx : ∀ t : ℝ, partialX V a t = deriv Φ a := by
        intro t
        simpa [partialX, V] using
          (deriv_add_const (f := Φ) (x := a) (Ψ t))
      unfold partialXY partialY
      rw [show (fun t : ℝ => partialX V a t) =
          (fun _ : ℝ => deriv Φ a) by funext t; exact hx t]
      simp
    intro x y
    have hUxx := gap3 ξf ηf U V lam1 lam2 x y
      (Filter.Eventually.of_forall (fun p => hUx p.1 p.2))
      (hξevent x y) (hηevent x y) hC2V.contDiffAt
    have hUxy := gap4 ξf ηf U V lam1 lam2 x y
      (Filter.Eventually.of_forall (fun p => hUx p.1 p.2))
      (hξevent x y) (hηevent x y) hC2V.contDiffAt
    have hUyy := gap5 ξf ηf U V lam1 lam2 x y
      (Filter.Eventually.of_forall (fun p => hUy p.1 p.2))
      (hξevent x y) (hηevent x y) hC2V.contDiffAt
    have hTransform := gap6 A B C lam1 lam2 ξf ηf U V x y
      hUxx hUxy hUyy
    exact (gap14 A B C lam1 lam2 ξf ηf U V x y
      hTransform hRoot₁ hRoot₂ hMixed).2 (hVxy _ _)
  · intro hPDE
    have hden : lam2 - lam1 ≠ 0 := sub_ne_zero.mpr hDistinct.symm
    let X : ℝ → ℝ → ℝ :=
      fun a b => (lam2 * a - lam1 * b) / (lam2 - lam1)
    let Y : ℝ → ℝ → ℝ :=
      fun a b => (b - a) / (lam2 - lam1)
    let V : ℝ → ℝ → ℝ := fun a b => U (X a b) (Y a b)
    have hXY_left : ∀ x y, X (ξf x y) (ηf x y) = x ∧
        Y (ξf x y) (ηf x y) = y := by
      intro x y
      constructor <;> dsimp [X, Y, ξf, ηf] <;>
        field_simp [hden] <;> ring
    have hXY_right : ∀ a b, ξf (X a b) (Y a b) = a ∧
        ηf (X a b) (Y a b) = b := by
      intro a b
      constructor <;> dsimp [X, Y, ξf, ηf] <;>
        field_simp [hden] <;> ring
    have hC2XY : ContDiff ℝ 2
        (fun p : ℝ × ℝ => (X p.1 p.2, Y p.1 p.2)) := by
      dsimp [X, Y]
      fun_prop
    have hC2V : ContDiff ℝ 2 (Function.uncurry V) := by
      change ContDiff ℝ 2
        (fun p : ℝ × ℝ => U (X p.1 p.2) (Y p.1 p.2))
      exact hC2U.comp hC2XY
    have hCompose : ∀ a b, U a b = V (ξf a b) (ηf a b) := by
      intro a b
      simp only [V]
      rw [(hXY_left a b).1, (hXY_left a b).2]
    have hUx : ∀ a b,
        partialX U a b =
          partialX V (ξf a b) (ηf a b) +
            partialY V (ξf a b) (ηf a b) := by
      intro a b
      exact gap1 ξf ηf U V lam1 lam2 a b
        (hξevent a b) (hηevent a b)
        (Filter.Eventually.of_forall (fun p => hCompose p.1 p.2))
        ((hC2V.differentiable (by decide)) (ξf a b, ηf a b))
    have hUy : ∀ a b,
        partialY U a b =
          lam1 * partialX V (ξf a b) (ηf a b) +
            lam2 * partialY V (ξf a b) (ηf a b) := by
      intro a b
      exact gap2 ξf ηf U V lam1 lam2 a b
        (hξevent a b) (hηevent a b)
        (Filter.Eventually.of_forall (fun p => hCompose p.1 p.2))
        ((hC2V.differentiable (by decide)) (ξf a b, ηf a b))
    have hCanonicalImage : ∀ x y,
        partialXY V (ξf x y) (ηf x y) = 0 := by
      intro x y
      have hUxx := gap3 ξf ηf U V lam1 lam2 x y
        (Filter.Eventually.of_forall (fun p => hUx p.1 p.2))
        (hξevent x y) (hηevent x y) hC2V.contDiffAt
      have hUxy := gap4 ξf ηf U V lam1 lam2 x y
        (Filter.Eventually.of_forall (fun p => hUx p.1 p.2))
        (hξevent x y) (hηevent x y) hC2V.contDiffAt
      have hUyy := gap5 ξf ηf U V lam1 lam2 x y
        (Filter.Eventually.of_forall (fun p => hUy p.1 p.2))
        (hξevent x y) (hηevent x y) hC2V.contDiffAt
      have hTransform := gap6 A B C lam1 lam2 ξf ηf U V x y
        hUxx hUxy hUyy
      exact (gap14 A B C lam1 lam2 ξf ηf U V x y
        hTransform hRoot₁ hRoot₂ hMixed).1 (hPDE x y)
    have hCanonical : ∀ a b, partialXY V a b = 0 := by
      intro a b
      have h := hCanonicalImage (X a b) (Y a b)
      rw [(hXY_right a b).1, (hXY_right a b).2] at h
      exact h
    have hDiffPX : ∀ a,
        Differentiable ℝ (fun b => partialX V a b) := by
      intro a b
      have hpair : DifferentiableAt ℝ (fun t : ℝ => (a, t)) b := by
        fun_prop
      exact (differentiableAt_uncurry_partialX
        (hC2V.contDiffAt : ContDiffAt ℝ 2
          (Function.uncurry V) (a, b))).comp b hpair
    rcases gap18 V hCanonical hDiffPX with ⟨f, hf⟩
    let Φ : ℝ → ℝ := fun a => V a 0
    let Ψ : ℝ → ℝ := fun b => V 0 b - V 0 0
    have hΦ : ContDiff ℝ 2 Φ := by
      dsimp [Φ]
      exact hC2V.comp (contDiff_id.prodMk contDiff_const)
    have hΨ : ContDiff ℝ 2 Ψ := by
      dsimp [Ψ]
      exact
        (hC2V.comp (contDiff_const.prodMk contDiff_id)).sub contDiff_const
    have hDiffV : ∀ b, Differentiable ℝ (fun a => V a b) := by
      intro b a
      have hpair : DifferentiableAt ℝ (fun t : ℝ => (t, b)) a := by
        fun_prop
      exact (hC2V.differentiable (by decide) (a, b)).comp a hpair
    have hVsep : ∀ a b, V a b = Φ a + Ψ b := by
      intro a b
      have hzero : ∀ t : ℝ,
          deriv (fun s : ℝ => V s b - V s 0) t = 0 := by
        intro t
        rw [deriv_fun_sub (hDiffV b t) (hDiffV 0 t)]
        change partialX V t b - partialX V t 0 = 0
        rw [hf t b, hf t 0]
        ring
      have hconst := is_const_of_deriv_eq_zero
        ((hDiffV b).sub (hDiffV 0)) hzero a 0
      change V a b - V a 0 = V 0 b - V 0 0 at hconst
      dsimp [Φ, Ψ]
      linarith
    refine ⟨Φ, Ψ, hΦ, hΨ, ?_⟩
    intro x y
    rw [hCompose x y, hVsep]

end

end ProofGap.Exercise3501
