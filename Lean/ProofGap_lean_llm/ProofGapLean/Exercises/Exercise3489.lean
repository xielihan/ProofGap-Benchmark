import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3489

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
    simpa [F, ey, Function.comp_def, Function.uncurry] using hs.hasDerivAt.deriv
  have hpartialX : (fun t : ℝ => partialX f x t) =ᶠ[nhds y]
      (fun t : ℝ => (fderiv ℝ F (x, t)) ex) := by
    filter_upwards [hnearY] with t ht
    have hs := (ht.differentiableAt (by decide)).hasFDerivAt.comp x
      ((hasDerivAt_id x).hasFDerivAt.prodMk
        (hasDerivAt_const x t).hasFDerivAt)
    unfold partialX
    simpa [F, ex, Function.comp_def, Function.uncurry] using hs.hasDerivAt.deriv
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

private theorem coordinateX_u
    {u : ℝ → ℝ → ℝ} {x y : ℝ}
    (hU : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      u p.1 p.2 = p.1 + 2 * p.2 + 2) :
    HasDerivAt (fun t => u t y) 1 x := by
  have hu : (fun t : ℝ => u t y) =ᶠ[nhds x]
      (fun t : ℝ => t + 2 * y + 2) := by
    simpa using (continuousAt_id.prodMk continuousAt_const).eventually hU
  exact (((hasDerivAt_id x).add_const _).add_const _).congr_of_eventuallyEq hu

private theorem coordinateX_v
    {v : ℝ → ℝ → ℝ} {x y : ℝ}
    (hV : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      v p.1 p.2 = p.1 - p.2 - 1) :
    HasDerivAt (fun t => v t y) 1 x := by
  have hv : (fun t : ℝ => v t y) =ᶠ[nhds x]
      (fun t : ℝ => t - y - 1) := by
    simpa using (continuousAt_id.prodMk continuousAt_const).eventually hV
  exact (((hasDerivAt_id x).sub_const _).sub_const _).congr_of_eventuallyEq hv

private theorem coordinateY_u
    {u : ℝ → ℝ → ℝ} {x y : ℝ}
    (hU : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      u p.1 p.2 = p.1 + 2 * p.2 + 2) :
    HasDerivAt (fun t => u x t) 2 y := by
  have hu : (fun t : ℝ => u x t) =ᶠ[nhds y]
      (fun t : ℝ => x + 2 * t + 2) := by
    simpa using (continuousAt_const.prodMk continuousAt_id).eventually hU
  have hbase : HasDerivAt (fun t : ℝ => x + 2 * t + 2) 2 y := by
    convert (((hasDerivAt_id y).const_mul 2).const_add x).add_const 2 using 1 <;> ring
  exact hbase.congr_of_eventuallyEq hu

private theorem coordinateY_v
    {v : ℝ → ℝ → ℝ} {x y : ℝ}
    (hV : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      v p.1 p.2 = p.1 - p.2 - 1) :
    HasDerivAt (fun t => v x t) (-1) y := by
  have hv : (fun t : ℝ => v x t) =ᶠ[nhds y]
      (fun t : ℝ => x - t - 1) := by
    simpa using (continuousAt_const.prodMk continuousAt_id).eventually hV
  exact (((hasDerivAt_id y).const_sub x).sub_const _).congr_of_eventuallyEq hv

theorem gap1 (u v z Z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hCompose : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      Z p.1 p.2 = z (u p.1 p.2) (v p.1 p.2))
    (hDiffZ : DifferentiableAt ℝ (Function.uncurry Z) (x, y))
    (hDiffz : DifferentiableAt ℝ (Function.uncurry z) (u x y, v x y))
    (hDiffu : DifferentiableAt ℝ (Function.uncurry u) (x, y))
    (hDiffv : DifferentiableAt ℝ (Function.uncurry v) (x, y)) :
    partialX Z x y =
      partialX z (u x y) (v x y) * partialX u x y +
        partialY z (u x y) (v x y) * partialX v x y := by
  have hu := hasDerivAt_partialX u x y hDiffu
  have hv := hasDerivAt_partialX v x y hDiffv
  have hz : (fun t : ℝ => Z t y) =ᶠ[nhds x]
      (fun t : ℝ => z (u t y) (v t y)) := by
    simpa using (continuousAt_id.prodMk continuousAt_const).eventually hCompose
  change deriv (fun t : ℝ => Z t y) x = _
  calc
    deriv (fun t : ℝ => Z t y) x =
        deriv (fun t : ℝ => z (u t y) (v t y)) x := hz.deriv_eq
    _ = _ := by
      convert (hasDerivAt_comp₂ z (fun t => u t y) (fun t => v t y)
        hDiffz hu hv).deriv using 1 <;> ring

theorem gap2 (u v z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hU : ∀ᶠ p : ℝ × ℝ in nhds (x, y), u p.1 p.2 = p.1 + 2 * p.2 + 2)
    (hV : ∀ᶠ p : ℝ × ℝ in nhds (x, y), v p.1 p.2 = p.1 - p.2 - 1) :
    partialX z (u x y) (v x y) * partialX u x y +
        partialY z (u x y) (v x y) * partialX v x y =
      partialX z (u x y) (v x y) + partialY z (u x y) (v x y) := by
  have hu := (coordinateX_u hU).deriv
  have hv := (coordinateX_v hV).deriv
  change partialX u x y = 1 at hu
  change partialX v x y = 1 at hv
  rw [hu, hv]
  ring

theorem gap3 (u v z Z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hChain :
      partialX Z x y =
        partialX z (u x y) (v x y) * partialX u x y +
          partialY z (u x y) (v x y) * partialX v x y)
    (hCoordinateDerivatives :
      partialX z (u x y) (v x y) * partialX u x y +
          partialY z (u x y) (v x y) * partialX v x y =
        partialX z (u x y) (v x y) + partialY z (u x y) (v x y)) :
    partialX Z x y =
      partialX z (u x y) (v x y) + partialY z (u x y) (v x y) := by
  exact hChain.trans hCoordinateDerivatives

theorem gap4 (u v z Z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hCompose : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      Z p.1 p.2 = z (u p.1 p.2) (v p.1 p.2))
    (hU : ∀ᶠ p : ℝ × ℝ in nhds (x, y), u p.1 p.2 = p.1 + 2 * p.2 + 2)
    (hV : ∀ᶠ p : ℝ × ℝ in nhds (x, y), v p.1 p.2 = p.1 - p.2 - 1)
    (hDiffz : DifferentiableAt ℝ (Function.uncurry z) (u x y, v x y)) :
    partialY Z x y =
      2 * partialX z (u x y) (v x y) - partialY z (u x y) (v x y) := by
  have hu := coordinateY_u hU
  have hv := coordinateY_v hV
  have hz : (fun t : ℝ => Z x t) =ᶠ[nhds y]
      (fun t : ℝ => z (u x t) (v x t)) := by
    simpa using (continuousAt_const.prodMk continuousAt_id).eventually hCompose
  change deriv (fun t : ℝ => Z x t) y = _
  calc
    deriv (fun t : ℝ => Z x t) y =
        deriv (fun t : ℝ => z (u x t) (v x t)) y := hz.deriv_eq
    _ = _ := by
      convert (hasDerivAt_comp₂ z (fun t => u x t) (fun t => v x t)
        hDiffz hu hv).deriv using 1 <;> ring

-- Statement correction: the original statement omitted the C² regularity
-- needed to identify the two mixed partial derivatives.
theorem gap5 (u v z Z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hZx : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      partialX Z p.1 p.2 =
        partialX z (u p.1 p.2) (v p.1 p.2) +
          partialY z (u p.1 p.2) (v p.1 p.2))
    (hU : ∀ᶠ p : ℝ × ℝ in nhds (x, y), u p.1 p.2 = p.1 + 2 * p.2 + 2)
    (hV : ∀ᶠ p : ℝ × ℝ in nhds (x, y), v p.1 p.2 = p.1 - p.2 - 1)
    (hDiffZu :
      DifferentiableAt ℝ (Function.uncurry (partialX z)) (u x y, v x y))
    (hDiffZv :
      DifferentiableAt ℝ (Function.uncurry (partialY z)) (u x y, v x y))
    (hC2z : ContDiffAt ℝ 2 (Function.uncurry z) (u x y, v x y)) :
    partialXX Z x y =
      partialXX z (u x y) (v x y) +
        2 * partialXY z (u x y) (v x y) +
        partialYY z (u x y) (v x y) := by
  have hu := coordinateX_u hU
  have hv := coordinateX_v hV
  have hA := hasDerivAt_comp₂ (partialX z) (fun t => u t y)
    (fun t => v t y) hDiffZu hu hv
  have hB := hasDerivAt_comp₂ (partialY z) (fun t => u t y)
    (fun t => v t y) hDiffZv hu hv
  have hderiv := (hA.add hB).deriv
  rw [mixed_partial_comm hC2z] at hderiv
  have hderiv' :
      deriv (fun t : ℝ =>
        partialX z (u t y) (v t y) + partialY z (u t y) (v t y)) x =
        1 * partialX (partialX z) (u x y) (v x y) +
          1 * partialY (partialX z) (u x y) (v x y) +
          (1 * partialXY z (u x y) (v x y) +
            1 * partialY (partialY z) (u x y) (v x y)) := by
    simpa only using hderiv
  have hz : (fun t : ℝ => partialX Z t y) =ᶠ[nhds x]
      (fun t : ℝ =>
        partialX z (u t y) (v t y) + partialY z (u t y) (v t y)) := by
    simpa using (continuousAt_id.prodMk continuousAt_const).eventually hZx
  change deriv (fun t : ℝ => partialX Z t y) x = _
  rw [hz.deriv_eq, hderiv']
  unfold partialXX partialXY partialYY
  ring

-- Statement correction: the original statement omitted the C² regularity
-- needed to identify the two mixed partial derivatives.
theorem gap6 (u v z Z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hZx : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      partialX Z p.1 p.2 =
        partialX z (u p.1 p.2) (v p.1 p.2) +
          partialY z (u p.1 p.2) (v p.1 p.2))
    (hU : ∀ᶠ p : ℝ × ℝ in nhds (x, y), u p.1 p.2 = p.1 + 2 * p.2 + 2)
    (hV : ∀ᶠ p : ℝ × ℝ in nhds (x, y), v p.1 p.2 = p.1 - p.2 - 1)
    (hDiffZu :
      DifferentiableAt ℝ (Function.uncurry (partialX z)) (u x y, v x y))
    (hDiffZv :
      DifferentiableAt ℝ (Function.uncurry (partialY z)) (u x y, v x y))
    (hC2z : ContDiffAt ℝ 2 (Function.uncurry z) (u x y, v x y)) :
    partialXY Z x y =
      2 * partialXX z (u x y) (v x y) +
        partialXY z (u x y) (v x y) -
        partialYY z (u x y) (v x y) := by
  have hu := coordinateY_u hU
  have hv := coordinateY_v hV
  have hA := hasDerivAt_comp₂ (partialX z) (fun t => u x t)
    (fun t => v x t) hDiffZu hu hv
  have hB := hasDerivAt_comp₂ (partialY z) (fun t => u x t)
    (fun t => v x t) hDiffZv hu hv
  have hderiv := (hA.add hB).deriv
  rw [mixed_partial_comm hC2z] at hderiv
  have hderiv' :
      deriv (fun t : ℝ =>
        partialX z (u x t) (v x t) + partialY z (u x t) (v x t)) y =
        2 * partialX (partialX z) (u x y) (v x y) +
          (-1) * partialY (partialX z) (u x y) (v x y) +
          (2 * partialXY z (u x y) (v x y) +
            (-1) * partialY (partialY z) (u x y) (v x y)) := by
    simpa only using hderiv
  have hz : (fun t : ℝ => partialX Z x t) =ᶠ[nhds y]
      (fun t : ℝ =>
        partialX z (u x t) (v x t) + partialY z (u x t) (v x t)) := by
    simpa using (continuousAt_const.prodMk continuousAt_id).eventually hZx
  change deriv (fun t : ℝ => partialX Z x t) y = _
  rw [hz.deriv_eq, hderiv']
  unfold partialXX partialXY partialYY
  ring

-- Statement correction: the original statement omitted the C² regularity
-- needed to identify the two mixed partial derivatives.
theorem gap7 (u v z Z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hZy : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      partialY Z p.1 p.2 =
        2 * partialX z (u p.1 p.2) (v p.1 p.2) -
          partialY z (u p.1 p.2) (v p.1 p.2))
    (hU : ∀ᶠ p : ℝ × ℝ in nhds (x, y), u p.1 p.2 = p.1 + 2 * p.2 + 2)
    (hV : ∀ᶠ p : ℝ × ℝ in nhds (x, y), v p.1 p.2 = p.1 - p.2 - 1)
    (hDiffZu :
      DifferentiableAt ℝ (Function.uncurry (partialX z)) (u x y, v x y))
    (hDiffZv :
      DifferentiableAt ℝ (Function.uncurry (partialY z)) (u x y, v x y))
    (hC2z : ContDiffAt ℝ 2 (Function.uncurry z) (u x y, v x y)) :
    partialYY Z x y =
      4 * partialXX z (u x y) (v x y) -
        4 * partialXY z (u x y) (v x y) +
        partialYY z (u x y) (v x y) := by
  have hu := coordinateY_u hU
  have hv := coordinateY_v hV
  have hA := hasDerivAt_comp₂ (partialX z) (fun t => u x t)
    (fun t => v x t) hDiffZu hu hv
  have hB := hasDerivAt_comp₂ (partialY z) (fun t => u x t)
    (fun t => v x t) hDiffZv hu hv
  have hderiv := ((hA.const_mul 2).sub hB).deriv
  rw [mixed_partial_comm hC2z] at hderiv
  have hderiv' :
      deriv (fun t : ℝ =>
        2 * partialX z (u x t) (v x t) -
          partialY z (u x t) (v x t)) y =
        2 * (2 * partialX (partialX z) (u x y) (v x y) +
          (-1) * partialY (partialX z) (u x y) (v x y)) -
          (2 * partialXY z (u x y) (v x y) +
            (-1) * partialY (partialY z) (u x y) (v x y)) := by
    simpa only using hderiv
  have hz : (fun t : ℝ => partialY Z x t) =ᶠ[nhds y]
      (fun t : ℝ =>
        2 * partialX z (u x t) (v x t) -
          partialY z (u x t) (v x t)) := by
    simpa using (continuousAt_const.prodMk continuousAt_id).eventually hZy
  change deriv (fun t : ℝ => partialY Z x t) y = _
  rw [hz.deriv_eq, hderiv']
  unfold partialXX partialXY partialYY
  ring

theorem gap8 (u v z Z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hPDE :
      2 * partialXX Z x y + partialXY Z x y - partialYY Z x y +
          partialX Z x y + partialY Z x y = 0)
    (hZx :
      partialX Z x y =
        partialX z (u x y) (v x y) + partialY z (u x y) (v x y))
    (hZy :
      partialY Z x y =
        2 * partialX z (u x y) (v x y) - partialY z (u x y) (v x y))
    (hZxx :
      partialXX Z x y =
        partialXX z (u x y) (v x y) +
          2 * partialXY z (u x y) (v x y) +
          partialYY z (u x y) (v x y))
    (hZxy :
      partialXY Z x y =
        2 * partialXX z (u x y) (v x y) +
          partialXY z (u x y) (v x y) -
          partialYY z (u x y) (v x y))
    (hZyy :
      partialYY Z x y =
        4 * partialXX z (u x y) (v x y) -
          4 * partialXY z (u x y) (v x y) +
          partialYY z (u x y) (v x y)) :
    3 * partialXY z (u x y) (v x y) +
      partialX z (u x y) (v x y) = 0 := by
  rw [hZx, hZy, hZxx, hZxy, hZyy] at hPDE
  linarith

end

end ProofGap.Exercise3489
