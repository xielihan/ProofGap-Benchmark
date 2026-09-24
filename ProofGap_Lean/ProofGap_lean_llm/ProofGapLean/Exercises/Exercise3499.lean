import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3499

noncomputable section

def partialX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ := deriv (fun t => f t y) x
def partialY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ := deriv (fun t => f x t) y
def partialXX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ := partialX (partialX f) x y
def partialXY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ := partialY (partialX f) x y
def partialYY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ := partialY (partialY f) x y

private theorem differentiableAt_xSlice
    {f : ℝ → ℝ → ℝ}
    (hf : DifferentiableAt ℝ (Function.uncurry f) (x, y)) :
    DifferentiableAt ℝ (fun t => f t y) x := by
  have hp : DifferentiableAt ℝ (fun t : ℝ => (t, y)) x :=
    differentiableAt_id.prodMk (hasDerivAt_const x y).differentiableAt
  simpa only [Function.comp_apply, Function.uncurry_apply_pair] using hf.comp x hp

private theorem differentiableAt_ySlice
    {f : ℝ → ℝ → ℝ}
    (hf : DifferentiableAt ℝ (Function.uncurry f) (x, y)) :
    DifferentiableAt ℝ (fun t => f x t) y := by
  have hp : DifferentiableAt ℝ (fun t : ℝ => (x, t)) y :=
    (hasDerivAt_const y x).differentiableAt.prodMk differentiableAt_id
  simpa only [Function.comp_apply, Function.uncurry_apply_pair] using hf.comp y hp

private theorem partialX_eq_fderiv (f : ℝ → ℝ → ℝ) (x y : ℝ)
    (hf : DifferentiableAt ℝ (Function.uncurry f) (x, y)) :
    partialX f x y =
      fderiv ℝ (Function.uncurry f) (x, y) (1, 0) := by
  unfold partialX
  have hp : HasDerivAt (fun t : ℝ => (t, y)) (1, 0) x :=
    (hasDerivAt_id x).prodMk (hasDerivAt_const x y)
  have h := (hf.hasFDerivAt.comp x hp.hasFDerivAt).hasDerivAt.deriv
  simpa [Function.uncurry] using h

private theorem partialY_eq_fderiv (f : ℝ → ℝ → ℝ) (x y : ℝ)
    (hf : DifferentiableAt ℝ (Function.uncurry f) (x, y)) :
    partialY f x y =
      fderiv ℝ (Function.uncurry f) (x, y) (0, 1) := by
  unfold partialY
  have hp : HasDerivAt (fun t : ℝ => (x, t)) (0, 1) y :=
    (hasDerivAt_const y x).prodMk (hasDerivAt_id y)
  have h := (hf.hasFDerivAt.comp y hp.hasFDerivAt).hasDerivAt.deriv
  simpa [Function.uncurry] using h

private theorem hasDerivAt_comp₂
    (F : ℝ → ℝ → ℝ) (g h : ℝ → ℝ) {t dg dh : ℝ}
    (hF : DifferentiableAt ℝ (Function.uncurry F) (g t, h t))
    (hg : HasDerivAt g dg t) (hh : HasDerivAt h dh t) :
    HasDerivAt (fun s => F (g s) (h s))
      (partialX F (g t) (h t) * dg +
        partialY F (g t) (h t) * dh) t := by
  let D := fderiv ℝ (Function.uncurry F) (g t, h t)
  have hc := hF.hasFDerivAt.comp t
    (hg.hasFDerivAt.prodMk hh.hasFDerivAt)
  have hc' : HasDerivAt (fun s => F (g s) (h s)) (D (dg, dh)) t := by
    simpa [D, Function.comp_def, Function.uncurry] using hc.hasDerivAt
  have hdx := partialX_eq_fderiv F (g t) (h t) hF
  have hdy := partialY_eq_fderiv F (g t) (h t) hF
  have hlin : D (dg, dh) = dg * D (1, 0) + dh * D (0, 1) := by
    calc
      D (dg, dh) = D (dg • (1, 0) + dh • (0, 1)) := by
        congr 1
        ext <;> simp
      _ = dg • D (1, 0) + dh • D (0, 1) := by
        rw [map_add, map_smul, map_smul]
      _ = dg * D (1, 0) + dh * D (0, 1) := by simp
  convert hc' using 1
  rw [hdx, hdy, hlin]
  ring

private theorem mixed_partial_comm_C2At
    {f : ℝ → ℝ → ℝ} {x y : ℝ}
    (hf : ContDiffAt ℝ 2 (Function.uncurry f) (x, y)) :
    partialX (partialY f) x y = partialXY f x y := by
  let F := Function.uncurry f
  let H := fderiv ℝ (fderiv ℝ F) (x, y)
  let ex : ℝ × ℝ := (1, 0)
  let ey : ℝ × ℝ := (0, 1)
  have hFnear :
      ∀ᶠ p : ℝ × ℝ in nhds (x, y), DifferentiableAt ℝ F p := by
    filter_upwards [hf.eventually (by norm_num)] with p hp
    exact hp.differentiableAt two_ne_zero
  have hpX : ContinuousAt (fun t : ℝ => (t, y)) x :=
    continuousAt_id.prodMk continuousAt_const
  have hpY : ContinuousAt (fun t : ℝ => (x, t)) y :=
    continuousAt_const.prodMk continuousAt_id
  have hpartialY :
      (fun t : ℝ => partialY f t y) =ᶠ[nhds x]
        (fun t => fderiv ℝ F (t, y) ey) := by
    filter_upwards [hpX.eventually hFnear] with t ht
    simpa [F, ey] using partialY_eq_fderiv f t y ht
  have hpartialX :
      (fun t : ℝ => partialX f x t) =ᶠ[nhds y]
        (fun t => fderiv ℝ F (x, t) ex) := by
    filter_upwards [hpY.eventually hFnear] with t ht
    simpa [F, ex] using partialX_eq_fderiv f x t ht
  have hDf : DifferentiableAt ℝ (fderiv ℝ F) (x, y) := by
    apply ContDiffAt.differentiableAt _ one_ne_zero
    exact hf.fderiv_right (by norm_num)
  have hFD : HasFDerivAt (fderiv ℝ F) H (x, y) := by
    simpa [H] using hDf.hasFDerivAt
  let evY : ((ℝ × ℝ) →L[ℝ] ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.apply ℝ ℝ ey
  let evX : ((ℝ × ℝ) →L[ℝ] ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.apply ℝ ℝ ex
  have hEvalY := evY.hasFDerivAt.comp (x, y) hFD
  have hEvalX := evX.hasFDerivAt.comp (x, y) hFD
  have houtY :
      HasDerivAt (fun t : ℝ => fderiv ℝ F (t, y) ey)
        (H ex ey) x := by
    have hcomp := hEvalY.comp x
      ((hasDerivAt_id x).hasFDerivAt.prodMk
        (hasDerivAt_const x y).hasFDerivAt)
    simpa [evY, ex, ey, Function.comp_def] using hcomp.hasDerivAt
  have houtX :
      HasDerivAt (fun t : ℝ => fderiv ℝ F (x, t) ex)
        (H ey ex) y := by
    have hcomp := hEvalX.comp y
      ((hasDerivAt_const y x).hasFDerivAt.prodMk
        (hasDerivAt_id y).hasFDerivAt)
    simpa [evX, ex, ey, Function.comp_def] using hcomp.hasDerivAt
  have hlhs : partialX (partialY f) x y = H ex ey := by
    unfold partialX
    exact hpartialY.deriv_eq.trans houtY.deriv
  have hrhs : partialXY f x y = H ey ex := by
    unfold partialXY
    exact hpartialX.deriv_eq.trans houtX.deriv
  have hsymm : H ex ey = H ey ex := by
    simpa [H, F] using
      (hf.isSymmSndFDerivAt (by norm_num) ex ey)
  exact hlhs.trans (hsymm.trans hrhs.symm)

theorem gap1 (u v : ℝ → ℝ → ℝ) (x y : ℝ)
    (hX : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      p.1 = (u p.1 p.2 + v p.1 p.2) ^ 2)
    (hDiffu : DifferentiableAt ℝ (Function.uncurry u) (x, y))
    (hDiffv : DifferentiableAt ℝ (Function.uncurry v) (x, y)) :
    1 = 2 * (u x y + v x y) * (partialX u x y + partialX v x y) := by
  have hp : ContinuousAt (fun t : ℝ => (t, y)) x :=
    continuousAt_id.prodMk continuousAt_const
  have heq :
      (fun t : ℝ => t) =ᶠ[nhds x]
        fun t => (u t y + v t y) ^ 2 := hp.eventually hX
  have hu := (differentiableAt_xSlice hDiffu).hasDerivAt
  have hv := (differentiableAt_xSlice hDiffv).hasDerivAt
  have hrhs := (hu.add hv).pow 2
  have h := heq.deriv_eq.trans hrhs.deriv
  simpa [partialX] using h

theorem gap2 (u v : ℝ → ℝ → ℝ) (x y : ℝ)
    (hY : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      p.2 = (u p.1 p.2 - v p.1 p.2) ^ 2)
    (hDiffu : DifferentiableAt ℝ (Function.uncurry u) (x, y))
    (hDiffv : DifferentiableAt ℝ (Function.uncurry v) (x, y)) :
    0 = 2 * (u x y - v x y) * (partialX u x y - partialX v x y) := by
  have hp : ContinuousAt (fun t : ℝ => (t, y)) x :=
    continuousAt_id.prodMk continuousAt_const
  have heq :
      (fun _ : ℝ => y) =ᶠ[nhds x]
        fun t => (u t y - v t y) ^ 2 := hp.eventually hY
  have hu := (differentiableAt_xSlice hDiffu).hasDerivAt
  have hv := (differentiableAt_xSlice hDiffv).hasDerivAt
  have hrhs := (hu.sub hv).pow 2
  have h := heq.deriv_eq.trans hrhs.deriv
  simpa [partialX] using h

theorem gap3 (u v : ℝ → ℝ → ℝ) (x y : ℝ)
    (hX : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      p.1 = (u p.1 p.2 + v p.1 p.2) ^ 2)
    (hDiffu : DifferentiableAt ℝ (Function.uncurry u) (x, y))
    (hDiffv : DifferentiableAt ℝ (Function.uncurry v) (x, y)) :
    0 = 2 * (u x y + v x y) * (partialY u x y + partialY v x y) := by
  have hp : ContinuousAt (fun t : ℝ => (x, t)) y :=
    continuousAt_const.prodMk continuousAt_id
  have heq :
      (fun _ : ℝ => x) =ᶠ[nhds y]
        fun t => (u x t + v x t) ^ 2 := hp.eventually hX
  have hu := (differentiableAt_ySlice hDiffu).hasDerivAt
  have hv := (differentiableAt_ySlice hDiffv).hasDerivAt
  have hrhs := (hu.add hv).pow 2
  have h := heq.deriv_eq.trans hrhs.deriv
  simpa [partialY] using h

theorem gap4 (u v : ℝ → ℝ → ℝ) (x y : ℝ)
    (hY : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      p.2 = (u p.1 p.2 - v p.1 p.2) ^ 2)
    (hDiffu : DifferentiableAt ℝ (Function.uncurry u) (x, y))
    (hDiffv : DifferentiableAt ℝ (Function.uncurry v) (x, y)) :
    1 = 2 * (u x y - v x y) * (partialY u x y - partialY v x y) := by
  have hp : ContinuousAt (fun t : ℝ => (x, t)) y :=
    continuousAt_const.prodMk continuousAt_id
  have heq :
      (fun t : ℝ => t) =ᶠ[nhds y]
        fun t => (u x t - v x t) ^ 2 := hp.eventually hY
  have hu := (differentiableAt_ySlice hDiffu).hasDerivAt
  have hv := (differentiableAt_ySlice hDiffv).hasDerivAt
  have hrhs := (hu.sub hv).pow 2
  have h := heq.deriv_eq.trans hrhs.deriv
  simpa [partialY] using h

theorem gap5 (u v : ℝ → ℝ → ℝ) (x y : ℝ)
    (hDiff : 0 = 2 * (u x y - v x y) * (partialX u x y - partialX v x y))
    (hBranch : u x y - v x y ≠ 0) :
    partialX u x y = partialX v x y := by
  have hfactor : 2 * (u x y - v x y) ≠ 0 :=
    mul_ne_zero (by norm_num) hBranch
  apply sub_eq_zero.mp
  exact (mul_eq_zero.mp (by linarith [hDiff])).resolve_left hfactor

theorem gap6 (u v : ℝ → ℝ → ℝ) (x y : ℝ)
    (hSum : u x y + v x y ≠ 0)
    (hDerivative : 1 = 2 * (u x y + v x y) *
      (partialX u x y + partialX v x y))
    (hEqual : partialX u x y = partialX v x y) :
    partialX v x y = 1 / (4 * (u x y + v x y)) := by
  field_simp [hSum]
  rw [hEqual] at hDerivative
  linarith

theorem gap7 (u v : ℝ → ℝ → ℝ) (x y : ℝ)
    (hEqual : partialX u x y = partialX v x y)
    (hVx : partialX v x y = 1 / (4 * (u x y + v x y))) :
    partialX u x y = 1 / (4 * (u x y + v x y)) := hEqual.trans hVx

theorem gap8 (u v : ℝ → ℝ → ℝ) (x y : ℝ)
    (hSum : u x y + v x y ≠ 0)
    (hDerivative : 0 = 2 * (u x y + v x y) *
      (partialY u x y + partialY v x y)) :
    partialY u x y = -partialY v x y := by
  have hfactor : 2 * (u x y + v x y) ≠ 0 :=
    mul_ne_zero (by norm_num) hSum
  have hzero : partialY u x y + partialY v x y = 0 :=
    (mul_eq_zero.mp (by linarith [hDerivative])).resolve_left hfactor
  linarith

theorem gap9 (u v : ℝ → ℝ → ℝ) (x y : ℝ)
    (hDiff : 1 = 2 * (u x y - v x y) *
      (partialY u x y - partialY v x y))
    (hOpposite : partialY u x y = -partialY v x y)
    (hDifference : u x y - v x y ≠ 0) :
    -partialY v x y = 1 / (4 * (u x y - v x y)) := by
  field_simp [hDifference]
  rw [hOpposite] at hDiff
  linarith

theorem gap10 (u v : ℝ → ℝ → ℝ) (x y : ℝ)
    (hOpposite : partialY u x y = -partialY v x y)
    (hValue : -partialY v x y = 1 / (4 * (u x y - v x y))) :
    partialY u x y = 1 / (4 * (u x y - v x y)) := hOpposite.trans hValue

theorem gap11 (u v z Z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hCompose : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      Z p.1 p.2 = z (u p.1 p.2) (v p.1 p.2))
    (hDiffz : DifferentiableAt ℝ (Function.uncurry z) (u x y, v x y))
    (hDiffu : DifferentiableAt ℝ (Function.uncurry u) (x, y))
    (hDiffv : DifferentiableAt ℝ (Function.uncurry v) (x, y)) :
    partialX Z x y = partialX z (u x y) (v x y) * partialX u x y +
      partialY z (u x y) (v x y) * partialX v x y := by
  have hp : ContinuousAt (fun t : ℝ => (t, y)) x :=
    continuousAt_id.prodMk continuousAt_const
  have heq :
      (fun t => Z t y) =ᶠ[nhds x]
        fun t => z (u t y) (v t y) := hp.eventually hCompose
  have hu := (differentiableAt_xSlice hDiffu).hasDerivAt
  have hv := (differentiableAt_xSlice hDiffv).hasDerivAt
  have hchain := hasDerivAt_comp₂ z (fun t => u t y) (fun t => v t y)
    hDiffz hu hv
  exact heq.deriv_eq.trans hchain.deriv

theorem gap12 (u v z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hUx : partialX u x y = 1 / (4 * (u x y + v x y)))
    (hVx : partialX v x y = 1 / (4 * (u x y + v x y))) :
    partialX z (u x y) (v x y) * partialX u x y +
        partialY z (u x y) (v x y) * partialX v x y =
      1 / (4 * (u x y + v x y)) *
        (partialX z (u x y) (v x y) + partialY z (u x y) (v x y)) := by
  rw [hUx, hVx]
  ring

theorem gap13 (u v z Z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hChain : partialX Z x y =
      partialX z (u x y) (v x y) * partialX u x y +
        partialY z (u x y) (v x y) * partialX v x y)
    (hSimplify :
      partialX z (u x y) (v x y) * partialX u x y +
          partialY z (u x y) (v x y) * partialX v x y =
        1 / (4 * (u x y + v x y)) *
          (partialX z (u x y) (v x y) + partialY z (u x y) (v x y))) :
    partialX Z x y = 1 / (4 * (u x y + v x y)) *
      (partialX z (u x y) (v x y) + partialY z (u x y) (v x y)) :=
  hChain.trans hSimplify

theorem gap14 (u v z Z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hChain : partialY Z x y =
      partialX z (u x y) (v x y) * partialY u x y +
        partialY z (u x y) (v x y) * partialY v x y)
    (hUy : partialY u x y = 1 / (4 * (u x y - v x y)))
    (hVy : partialY v x y = -(1 / (4 * (u x y - v x y)))) :
    partialY Z x y = 1 / (4 * (u x y - v x y)) *
      (partialX z (u x y) (v x y) - partialY z (u x y) (v x y)) := by
  rw [hChain, hUy, hVy]
  ring

theorem gap15 (u v z Z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hSum : u x y + v x y ≠ 0)
    (hZx : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      partialX Z p.1 p.2 = 1 / (4 * (u p.1 p.2 + v p.1 p.2)) *
        (partialX z (u p.1 p.2) (v p.1 p.2) +
          partialY z (u p.1 p.2) (v p.1 p.2)))
    (hUx : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      partialX u p.1 p.2 = 1 / (4 * (u p.1 p.2 + v p.1 p.2)))
    (hVx : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      partialX v p.1 p.2 = 1 / (4 * (u p.1 p.2 + v p.1 p.2)))
    (hDiffu : DifferentiableAt ℝ (Function.uncurry u) (x, y))
    (hDiffv : DifferentiableAt ℝ (Function.uncurry v) (x, y))
    (hDiffZu : DifferentiableAt ℝ (Function.uncurry (partialX z)) (u x y, v x y))
    (hDiffZv : DifferentiableAt ℝ (Function.uncurry (partialY z)) (u x y, v x y))
    (hC2z : ContDiffAt ℝ 2 (Function.uncurry z) (u x y, v x y)) :
    partialXX Z x y =
      -(1 / (8 * (u x y + v x y) ^ 3)) *
          (partialX z (u x y) (v x y) + partialY z (u x y) (v x y)) +
        1 / (16 * (u x y + v x y) ^ 2) *
          (partialXX z (u x y) (v x y) +
            2 * partialXY z (u x y) (v x y) +
            partialYY z (u x y) (v x y)) := by
  have hp : ContinuousAt (fun t : ℝ => (t, y)) x :=
    continuousAt_id.prodMk continuousAt_const
  have hZslice :
      (fun t => partialX Z t y) =ᶠ[nhds x]
        (fun t => 1 / (4 * (u t y + v t y)) *
          (partialX z (u t y) (v t y) +
            partialY z (u t y) (v t y))) :=
    hp.eventually hZx
  have hu : HasDerivAt (fun t => u t y) (partialX u x y) x :=
    (differentiableAt_xSlice hDiffu).hasDerivAt
  have hv : HasDerivAt (fun t => v t y) (partialX v x y) x :=
    (differentiableAt_xSlice hDiffv).hasDerivAt
  have hux :
      partialX u x y = 1 / (4 * (u x y + v x y)) :=
    hUx.self_of_nhds
  have hvx :
      partialX v x y = 1 / (4 * (u x y + v x y)) :=
    hVx.self_of_nhds
  have hden :
      HasDerivAt (fun t => 4 * (u t y + v t y))
        (4 * (partialX u x y + partialX v x y)) x := by
    simpa using (hu.add hv).const_mul 4
  have hden_ne : 4 * (u x y + v x y) ≠ 0 :=
    mul_ne_zero (by norm_num) hSum
  have hcoef :
      HasDerivAt (fun t => 1 / (4 * (u t y + v t y)))
        (-(1 / (8 * (u x y + v x y) ^ 3))) x := by
    have hraw :
        HasDerivAt (fun t => 1 / (4 * (u t y + v t y)))
          (-(4 * (partialX u x y + partialX v x y)) /
            (4 * (u x y + v x y)) ^ 2) x := by
      simpa only [one_div] using hden.inv hden_ne
    convert hraw using 1
    rw [hux, hvx]
    field_simp [hSum, hux, hvx]
    ring
  have hzx := hasDerivAt_comp₂ (partialX z)
    (fun t => u t y) (fun t => v t y) hDiffZu hu hv
  have hzy := hasDerivAt_comp₂ (partialY z)
    (fun t => u t y) (fun t => v t y) hDiffZv hu hv
  have hmixed :
      partialX (partialY z) (u x y) (v x y) =
        partialXY z (u x y) (v x y) :=
    mixed_partial_comm_C2At hC2z
  have hinner :
      HasDerivAt
        (fun t => partialX z (u t y) (v t y) +
          partialY z (u t y) (v t y))
        (1 / (4 * (u x y + v x y)) *
          (partialXX z (u x y) (v x y) +
            2 * partialXY z (u x y) (v x y) +
            partialYY z (u x y) (v x y))) x := by
    convert hzx.add hzy using 1
    rw [hux, hvx, hmixed]
    unfold partialXX partialXY partialYY
    ring
  have htotal :
      HasDerivAt
        (fun t => 1 / (4 * (u t y + v t y)) *
          (partialX z (u t y) (v t y) +
            partialY z (u t y) (v t y)))
        (-(1 / (8 * (u x y + v x y) ^ 3)) *
            (partialX z (u x y) (v x y) +
              partialY z (u x y) (v x y)) +
          1 / (4 * (u x y + v x y)) *
            (1 / (4 * (u x y + v x y)) *
              (partialXX z (u x y) (v x y) +
                2 * partialXY z (u x y) (v x y) +
                partialYY z (u x y) (v x y)))) x := by
    simpa only [Pi.mul_apply] using hcoef.mul hinner
  change deriv (fun t => partialX Z t y) x = _
  rw [hZslice.deriv_eq, htotal.deriv]
  field_simp [hSum]
  ring

theorem gap16 (u v z Z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hDifference : u x y - v x y ≠ 0)
    (hZy : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      partialY Z p.1 p.2 = 1 / (4 * (u p.1 p.2 - v p.1 p.2)) *
        (partialX z (u p.1 p.2) (v p.1 p.2) -
          partialY z (u p.1 p.2) (v p.1 p.2)))
    (hUy : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      partialY u p.1 p.2 = 1 / (4 * (u p.1 p.2 - v p.1 p.2)))
    (hVy : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      partialY v p.1 p.2 = -(1 / (4 * (u p.1 p.2 - v p.1 p.2))))
    (hDiffu : DifferentiableAt ℝ (Function.uncurry u) (x, y))
    (hDiffv : DifferentiableAt ℝ (Function.uncurry v) (x, y))
    (hDiffZu : DifferentiableAt ℝ (Function.uncurry (partialX z)) (u x y, v x y))
    (hDiffZv : DifferentiableAt ℝ (Function.uncurry (partialY z)) (u x y, v x y))
    (hC2z : ContDiffAt ℝ 2 (Function.uncurry z) (u x y, v x y)) :
    partialYY Z x y =
      -(1 / (8 * (u x y - v x y) ^ 3)) *
          (partialX z (u x y) (v x y) - partialY z (u x y) (v x y)) +
        1 / (16 * (u x y - v x y) ^ 2) *
          (partialXX z (u x y) (v x y) -
            2 * partialXY z (u x y) (v x y) +
            partialYY z (u x y) (v x y)) := by
  have hp : ContinuousAt (fun t : ℝ => (x, t)) y :=
    continuousAt_const.prodMk continuousAt_id
  have hZslice :
      (fun t => partialY Z x t) =ᶠ[nhds y]
        (fun t => 1 / (4 * (u x t - v x t)) *
          (partialX z (u x t) (v x t) -
            partialY z (u x t) (v x t))) :=
    hp.eventually hZy
  have hu : HasDerivAt (fun t => u x t) (partialY u x y) y :=
    (differentiableAt_ySlice hDiffu).hasDerivAt
  have hv : HasDerivAt (fun t => v x t) (partialY v x y) y :=
    (differentiableAt_ySlice hDiffv).hasDerivAt
  have huy :
      partialY u x y = 1 / (4 * (u x y - v x y)) :=
    hUy.self_of_nhds
  have hvy :
      partialY v x y = -(1 / (4 * (u x y - v x y))) :=
    hVy.self_of_nhds
  have hden :
      HasDerivAt (fun t => 4 * (u x t - v x t))
        (4 * (partialY u x y - partialY v x y)) y := by
    simpa using (hu.sub hv).const_mul 4
  have hden_ne : 4 * (u x y - v x y) ≠ 0 :=
    mul_ne_zero (by norm_num) hDifference
  have hcoef :
      HasDerivAt (fun t => 1 / (4 * (u x t - v x t)))
        (-(1 / (8 * (u x y - v x y) ^ 3))) y := by
    have hraw :
        HasDerivAt (fun t => 1 / (4 * (u x t - v x t)))
          (-(4 * (partialY u x y - partialY v x y)) /
            (4 * (u x y - v x y)) ^ 2) y := by
      simpa only [one_div] using hden.inv hden_ne
    convert hraw using 1
    rw [huy, hvy]
    field_simp [hDifference, huy, hvy]
    ring
  have hzx := hasDerivAt_comp₂ (partialX z)
    (fun t => u x t) (fun t => v x t) hDiffZu hu hv
  have hzy := hasDerivAt_comp₂ (partialY z)
    (fun t => u x t) (fun t => v x t) hDiffZv hu hv
  have hmixed :
      partialX (partialY z) (u x y) (v x y) =
        partialXY z (u x y) (v x y) :=
    mixed_partial_comm_C2At hC2z
  have hinner :
      HasDerivAt
        (fun t => partialX z (u x t) (v x t) -
          partialY z (u x t) (v x t))
        (1 / (4 * (u x y - v x y)) *
          (partialXX z (u x y) (v x y) -
            2 * partialXY z (u x y) (v x y) +
            partialYY z (u x y) (v x y))) y := by
    convert hzx.sub hzy using 1
    rw [huy, hvy, hmixed]
    unfold partialXX partialXY partialYY
    ring
  have htotal :
      HasDerivAt
        (fun t => 1 / (4 * (u x t - v x t)) *
          (partialX z (u x t) (v x t) -
            partialY z (u x t) (v x t)))
        (-(1 / (8 * (u x y - v x y) ^ 3)) *
            (partialX z (u x y) (v x y) -
              partialY z (u x y) (v x y)) +
          1 / (4 * (u x y - v x y)) *
            (1 / (4 * (u x y - v x y)) *
              (partialXX z (u x y) (v x y) -
                2 * partialXY z (u x y) (v x y) +
                partialYY z (u x y) (v x y)))) y := by
    simpa only [Pi.mul_apply] using hcoef.mul hinner
  change deriv (fun t => partialY Z x t) y = _
  rw [hZslice.deriv_eq, htotal.deriv]
  field_simp [hDifference]
  ring

theorem gap17 (u v z Z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hSum : u x y + v x y ≠ 0)
    (hDifference : u x y - v x y ≠ 0)
    (hCoordX : x = (u x y + v x y) ^ 2)
    (hCoordY : y = (u x y - v x y) ^ 2)
    (hPDE : x * partialXX Z x y - y * partialYY Z x y = 0)
    (hZxx : partialXX Z x y =
      -(1 / (8 * (u x y + v x y) ^ 3)) *
          (partialX z (u x y) (v x y) + partialY z (u x y) (v x y)) +
        1 / (16 * (u x y + v x y) ^ 2) *
          (partialXX z (u x y) (v x y) +
            2 * partialXY z (u x y) (v x y) +
            partialYY z (u x y) (v x y)))
    (hZyy : partialYY Z x y =
      -(1 / (8 * (u x y - v x y) ^ 3)) *
          (partialX z (u x y) (v x y) - partialY z (u x y) (v x y)) +
        1 / (16 * (u x y - v x y) ^ 2) *
          (partialXX z (u x y) (v x y) -
            2 * partialXY z (u x y) (v x y) +
            partialYY z (u x y) (v x y))) :
    1 / 16 * (4 * v x y / (u x y ^ 2 - v x y ^ 2) *
          partialX z (u x y) (v x y) -
        4 * u x y / (u x y ^ 2 - v x y ^ 2) *
          partialY z (u x y) (v x y) +
        4 * partialXY z (u x y) (v x y)) = 0 := by
  have hDenom : u x y ^ 2 - v x y ^ 2 ≠ 0 := by
    rw [show u x y ^ 2 - v x y ^ 2 =
      (u x y + v x y) * (u x y - v x y) by ring]
    exact mul_ne_zero hSum hDifference
  have hPDE' :
      (u x y + v x y) ^ 2 * partialXX Z x y -
          (u x y - v x y) ^ 2 * partialYY Z x y = 0 := by
    calc
      (u x y + v x y) ^ 2 * partialXX Z x y -
          (u x y - v x y) ^ 2 * partialYY Z x y =
          x * partialXX Z x y -
            (u x y - v x y) ^ 2 * partialYY Z x y :=
        congrArg
          (fun q => q * partialXX Z x y -
            (u x y - v x y) ^ 2 * partialYY Z x y)
          hCoordX.symm
      _ = x * partialXX Z x y - y * partialYY Z x y :=
        congrArg
          (fun q => x * partialXX Z x y - q * partialYY Z x y)
          hCoordY.symm
      _ = 0 := hPDE
  rw [hZxx, hZyy] at hPDE'
  field_simp [hSum, hDifference, hDenom] at hPDE' ⊢
  ring_nf at hPDE' ⊢
  linarith

theorem gap18 (transformedEquation : ℝ → ℝ → ℝ)
    (u v z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hDefinition : transformedEquation x y =
      partialXY z (u x y) (v x y) +
        1 / (u x y ^ 2 - v x y ^ 2) *
          (v x y * partialX z (u x y) (v x y) -
            u x y * partialY z (u x y) (v x y))) :
    transformedEquation x y =
      partialXY z (u x y) (v x y) +
        1 / (u x y ^ 2 - v x y ^ 2) *
          (v x y * partialX z (u x y) (v x y) -
            u x y * partialY z (u x y) (v x y)) := hDefinition

theorem gap19 (u v z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hDenom : u x y ^ 2 - v x y ^ 2 ≠ 0)
    (hScaled : 1 / 16 * (4 * v x y / (u x y ^ 2 - v x y ^ 2) *
          partialX z (u x y) (v x y) -
        4 * u x y / (u x y ^ 2 - v x y ^ 2) *
          partialY z (u x y) (v x y) +
        4 * partialXY z (u x y) (v x y)) = 0) :
    partialXY z (u x y) (v x y) +
      1 / (u x y ^ 2 - v x y ^ 2) *
        (v x y * partialX z (u x y) (v x y) -
          u x y * partialY z (u x y) (v x y)) = 0 := by
  field_simp [hDenom] at hScaled ⊢
  linarith

theorem gap20 (transformedEquation : ℝ → ℝ → ℝ)
    (u v z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hDefinition : transformedEquation x y =
      partialXY z (u x y) (v x y) +
        1 / (u x y ^ 2 - v x y ^ 2) *
          (v x y * partialX z (u x y) (v x y) -
            u x y * partialY z (u x y) (v x y)))
    (hZero : partialXY z (u x y) (v x y) +
      1 / (u x y ^ 2 - v x y ^ 2) *
        (v x y * partialX z (u x y) (v x y) -
          u x y * partialY z (u x y) (v x y)) = 0) :
    transformedEquation x y = 0 :=
  hDefinition.trans hZero

end

end ProofGap.Exercise3499
