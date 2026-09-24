import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3492

noncomputable section

def partialX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ := deriv (fun t => f t y) x
def partialY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ := deriv (fun t => f x t) y
def partialXX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ := partialX (partialX f) x y
def partialXY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ := partialY (partialX f) x y
def partialYX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ := partialX (partialY f) x y
def partialYY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ := partialY (partialY f) x y

def secondChainX (z u v : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  partialXX z (u x y) (v x y) * partialX u x y ^ 2 +
    2 * partialXY z (u x y) (v x y) * partialX u x y * partialX v x y +
    partialYY z (u x y) (v x y) * partialX v x y ^ 2 +
    partialX z (u x y) (v x y) * partialXX u x y +
    partialY z (u x y) (v x y) * partialXX v x y

def secondChainY (z u v : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  partialXX z (u x y) (v x y) * partialY u x y ^ 2 +
    2 * partialXY z (u x y) (v x y) * partialY u x y * partialY v x y +
    partialYY z (u x y) (v x y) * partialY v x y ^ 2 +
    partialX z (u x y) (v x y) * partialYY u x y +
    partialY z (u x y) (v x y) * partialYY v x y

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
    partialYX f x y = partialXY f x y := by
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
  have hlhs : partialYX f x y = D ex ey := by
    unfold partialYX partialX
    exact hpartialY.deriv_eq.trans houtY.deriv
  have hrhs : partialXY f x y = D ey ex := by
    unfold partialXY partialY
    exact hpartialX.deriv_eq.trans houtX.deriv
  have hsymm : D ex ey = D ey ex := by
    simpa [D, F, ex, ey] using
      h.isSymmSndFDerivAt (by norm_num)
        ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ)
  exact hlhs.trans (hsymm.trans hrhs.symm)

theorem gap1 (u v z Z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hCompose : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      Z p.1 p.2 = z (u p.1 p.2) (v p.1 p.2))
    (hDiffz : DifferentiableAt ℝ (Function.uncurry z) (u x y, v x y))
    (hDiffu : DifferentiableAt ℝ (Function.uncurry u) (x, y))
    (hDiffv : DifferentiableAt ℝ (Function.uncurry v) (x, y)) :
    partialX Z x y = partialX z (u x y) (v x y) * partialX u x y +
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

theorem gap2 (u v z Z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hCompose : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      Z p.1 p.2 = z (u p.1 p.2) (v p.1 p.2))
    (hDiffz : DifferentiableAt ℝ (Function.uncurry z) (u x y, v x y))
    (hDiffu : DifferentiableAt ℝ (Function.uncurry u) (x, y))
    (hDiffv : DifferentiableAt ℝ (Function.uncurry v) (x, y)) :
    partialY Z x y = partialX z (u x y) (v x y) * partialY u x y +
      partialY z (u x y) (v x y) * partialY v x y := by
  have hu := hasDerivAt_partialY u x y hDiffu
  have hv := hasDerivAt_partialY v x y hDiffv
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

theorem gap3 (u v z Z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hZx : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      partialX Z p.1 p.2 =
        partialX z (u p.1 p.2) (v p.1 p.2) * partialX u p.1 p.2 +
        partialY z (u p.1 p.2) (v p.1 p.2) * partialX v p.1 p.2)
    (hDiffZu : DifferentiableAt ℝ (Function.uncurry (partialX z)) (u x y, v x y))
    (hDiffZv : DifferentiableAt ℝ (Function.uncurry (partialY z)) (u x y, v x y))
    (hC2z : ContDiffAt ℝ 2 (Function.uncurry z) (u x y, v x y))
    (hDiffu : DifferentiableAt ℝ (Function.uncurry u) (x, y))
    (hDiffv : DifferentiableAt ℝ (Function.uncurry v) (x, y))
    (hDiffUx : DifferentiableAt ℝ (Function.uncurry (partialX u)) (x, y))
    (hDiffVx : DifferentiableAt ℝ (Function.uncurry (partialX v)) (x, y)) :
    partialXX Z x y = secondChainX z u v x y := by
  have hu := hasDerivAt_partialX u x y hDiffu
  have hv := hasDerivAt_partialX v x y hDiffv
  have hux := hasDerivAt_partialX (partialX u) x y hDiffUx
  have hvx := hasDerivAt_partialX (partialX v) x y hDiffVx
  have hA := hasDerivAt_comp₂ (partialX z) (fun t => u t y)
    (fun t => v t y) hDiffZu hu hv
  have hB := hasDerivAt_comp₂ (partialY z) (fun t => u t y)
    (fun t => v t y) hDiffZv hu hv
  have hR := (hA.mul hux).add (hB.mul hvx)
  change HasDerivAt
    (fun t : ℝ =>
      partialX z (u t y) (v t y) * partialX u t y +
        partialY z (u t y) (v t y) * partialX v t y) _ x at hR
  have hdR := hR.deriv
  have hmix : partialX (partialY z) (u x y) (v x y) =
      partialY (partialX z) (u x y) (v x y) := by
    simpa [partialYX, partialXY] using mixed_partial_comm hC2z
  rw [hmix] at hdR
  have hz : (fun t : ℝ => partialX Z t y) =ᶠ[nhds x]
      (fun t : ℝ =>
        partialX z (u t y) (v t y) * partialX u t y +
          partialY z (u t y) (v t y) * partialX v t y) := by
    simpa using (continuousAt_id.prodMk continuousAt_const).eventually hZx
  change deriv (fun t : ℝ => partialX Z t y) x = _
  calc
    deriv (fun t : ℝ => partialX Z t y) x =
        deriv (fun t : ℝ =>
          partialX z (u t y) (v t y) * partialX u t y +
            partialY z (u t y) (v t y) * partialX v t y) x := hz.deriv_eq
    _ = _ := by
      rw [hdR]
      unfold secondChainX partialXX partialXY partialYY
      ring

theorem gap4 (u v z Z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hZy : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      partialY Z p.1 p.2 =
        partialX z (u p.1 p.2) (v p.1 p.2) * partialY u p.1 p.2 +
        partialY z (u p.1 p.2) (v p.1 p.2) * partialY v p.1 p.2)
    (hDiffZu : DifferentiableAt ℝ (Function.uncurry (partialX z)) (u x y, v x y))
    (hDiffZv : DifferentiableAt ℝ (Function.uncurry (partialY z)) (u x y, v x y))
    (hC2z : ContDiffAt ℝ 2 (Function.uncurry z) (u x y, v x y))
    (hDiffu : DifferentiableAt ℝ (Function.uncurry u) (x, y))
    (hDiffv : DifferentiableAt ℝ (Function.uncurry v) (x, y))
    (hDiffUy : DifferentiableAt ℝ (Function.uncurry (partialY u)) (x, y))
    (hDiffVy : DifferentiableAt ℝ (Function.uncurry (partialY v)) (x, y)) :
    partialYY Z x y = secondChainY z u v x y := by
  have hu := hasDerivAt_partialY u x y hDiffu
  have hv := hasDerivAt_partialY v x y hDiffv
  have huy := hasDerivAt_partialY (partialY u) x y hDiffUy
  have hvy := hasDerivAt_partialY (partialY v) x y hDiffVy
  have hA := hasDerivAt_comp₂ (partialX z) (fun t => u x t)
    (fun t => v x t) hDiffZu hu hv
  have hB := hasDerivAt_comp₂ (partialY z) (fun t => u x t)
    (fun t => v x t) hDiffZv hu hv
  have hR := (hA.mul huy).add (hB.mul hvy)
  change HasDerivAt
    (fun t : ℝ =>
      partialX z (u x t) (v x t) * partialY u x t +
        partialY z (u x t) (v x t) * partialY v x t) _ y at hR
  have hdR := hR.deriv
  have hmix : partialX (partialY z) (u x y) (v x y) =
      partialY (partialX z) (u x y) (v x y) := by
    simpa [partialYX, partialXY] using mixed_partial_comm hC2z
  rw [hmix] at hdR
  have hz : (fun t : ℝ => partialY Z x t) =ᶠ[nhds y]
      (fun t : ℝ =>
        partialX z (u x t) (v x t) * partialY u x t +
          partialY z (u x t) (v x t) * partialY v x t) := by
    simpa using (continuousAt_const.prodMk continuousAt_id).eventually hZy
  change deriv (fun t : ℝ => partialY Z x t) y = _
  calc
    deriv (fun t : ℝ => partialY Z x t) y =
        deriv (fun t : ℝ =>
          partialX z (u x t) (v x t) * partialY u x t +
            partialY z (u x t) (v x t) * partialY v x t) y := hz.deriv_eq
    _ = _ := by
      rw [hdR]
      unfold secondChainY partialXX partialXY partialYY
      ring

theorem gap5 (u : ℝ → ℝ → ℝ) (x y : ℝ)
    (hNonzero : x ^ 2 + y ^ 2 ≠ 0)
    (hU : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      u p.1 p.2 = p.1 / (p.1 ^ 2 + p.2 ^ 2)) :
    partialX u x y = (y ^ 2 - x ^ 2) / (x ^ 2 + y ^ 2) ^ 2 := by
  have hu : (fun t : ℝ => u t y) =ᶠ[nhds x]
      (fun t : ℝ => t / (t ^ 2 + y ^ 2)) := by
    simpa using (continuousAt_id.prodMk continuousAt_const).eventually hU
  have hd : HasDerivAt (fun t : ℝ => t / (t ^ 2 + y ^ 2))
      ((1 * (x ^ 2 + y ^ 2) - x * (2 * x)) /
        (x ^ 2 + y ^ 2) ^ 2) x := by
    convert (hasDerivAt_id x).div
      (((hasDerivAt_id x).pow 2).add_const (y ^ 2)) hNonzero using 1 <;>
      norm_num <;> ring
  unfold partialX
  rw [hu.deriv_eq, hd.deriv]
  congr 1
  ring

theorem gap6 (v : ℝ → ℝ → ℝ) (x y : ℝ)
    (hNonzero : x ^ 2 + y ^ 2 ≠ 0)
    (hV : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      v p.1 p.2 = -p.2 / (p.1 ^ 2 + p.2 ^ 2)) :
    partialX v x y = 2 * x * y / (x ^ 2 + y ^ 2) ^ 2 := by
  have hv : (fun t : ℝ => v t y) =ᶠ[nhds x]
      (fun t : ℝ => -y / (t ^ 2 + y ^ 2)) := by
    simpa using (continuousAt_id.prodMk continuousAt_const).eventually hV
  have hd : HasDerivAt (fun t : ℝ => -y / (t ^ 2 + y ^ 2))
      ((0 * (x ^ 2 + y ^ 2) - (-y) * (2 * x)) /
        (x ^ 2 + y ^ 2) ^ 2) x := by
    convert (hasDerivAt_const x (-y)).div
      (((hasDerivAt_id x).pow 2).add_const (y ^ 2)) hNonzero using 1 <;>
      norm_num <;> ring
  unfold partialX
  rw [hv.deriv_eq, hd.deriv]
  congr 1
  ring

theorem gap7 (u : ℝ → ℝ → ℝ) (x y : ℝ)
    (hNonzero : x ^ 2 + y ^ 2 ≠ 0)
    (hU : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      u p.1 p.2 = p.1 / (p.1 ^ 2 + p.2 ^ 2)) :
    partialY u x y = -(2 * x * y / (x ^ 2 + y ^ 2) ^ 2) := by
  have hu : (fun t : ℝ => u x t) =ᶠ[nhds y]
      (fun t : ℝ => x / (x ^ 2 + t ^ 2)) := by
    simpa using (continuousAt_const.prodMk continuousAt_id).eventually hU
  have hd : HasDerivAt (fun t : ℝ => x / (x ^ 2 + t ^ 2))
      ((0 * (x ^ 2 + y ^ 2) - x * (2 * y)) /
        (x ^ 2 + y ^ 2) ^ 2) y := by
    convert (hasDerivAt_const y x).div
      ((hasDerivAt_const y (x ^ 2)).add ((hasDerivAt_id y).pow 2))
      hNonzero using 1 <;> norm_num <;> ring
  unfold partialY
  rw [hu.deriv_eq, hd.deriv]
  congr 1
  ring

theorem gap8 (v : ℝ → ℝ → ℝ) (x y : ℝ)
    (hVx : partialX v x y = 2 * x * y / (x ^ 2 + y ^ 2) ^ 2) :
    -(2 * x * y / (x ^ 2 + y ^ 2) ^ 2) = -partialX v x y := by
  rw [hVx]

theorem gap9 (u v : ℝ → ℝ → ℝ) (x y : ℝ)
    (hUy : partialY u x y = -(2 * x * y / (x ^ 2 + y ^ 2) ^ 2))
    (hNegVx : -(2 * x * y / (x ^ 2 + y ^ 2) ^ 2) = -partialX v x y) :
    partialY u x y = -partialX v x y := by
  exact hUy.trans hNegVx

theorem gap10 (v : ℝ → ℝ → ℝ) (x y : ℝ)
    (hNonzero : x ^ 2 + y ^ 2 ≠ 0)
    (hV : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      v p.1 p.2 = -p.2 / (p.1 ^ 2 + p.2 ^ 2)) :
    partialY v x y = (y ^ 2 - x ^ 2) / (x ^ 2 + y ^ 2) ^ 2 := by
  have hv : (fun t : ℝ => v x t) =ᶠ[nhds y]
      (fun t : ℝ => -t / (x ^ 2 + t ^ 2)) := by
    simpa using (continuousAt_const.prodMk continuousAt_id).eventually hV
  have hd : HasDerivAt (fun t : ℝ => -t / (x ^ 2 + t ^ 2))
      ((-1 * (x ^ 2 + y ^ 2) - (-y) * (2 * y)) /
        (x ^ 2 + y ^ 2) ^ 2) y := by
    convert (hasDerivAt_id y).neg.div
      ((hasDerivAt_const y (x ^ 2)).add ((hasDerivAt_id y).pow 2))
      hNonzero using 1 <;> norm_num <;> ring
  unfold partialY
  rw [hv.deriv_eq, hd.deriv]
  congr 1
  ring

theorem gap11 (u : ℝ → ℝ → ℝ) (x y : ℝ)
    (hUx : partialX u x y = (y ^ 2 - x ^ 2) / (x ^ 2 + y ^ 2) ^ 2) :
    (y ^ 2 - x ^ 2) / (x ^ 2 + y ^ 2) ^ 2 = partialX u x y := by
  exact hUx.symm

theorem gap12 (u v : ℝ → ℝ → ℝ) (x y : ℝ)
    (hVy : partialY v x y = (y ^ 2 - x ^ 2) / (x ^ 2 + y ^ 2) ^ 2)
    (hUx : (y ^ 2 - x ^ 2) / (x ^ 2 + y ^ 2) ^ 2 = partialX u x y) :
    partialY v x y = partialX u x y := by
  exact hVy.trans hUx

theorem gap13 (u v : ℝ → ℝ → ℝ) (x y : ℝ)
    (hCR : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      partialY v p.1 p.2 = partialX u p.1 p.2) :
    partialXX u x y = partialYX v x y := by
  have hline : (fun t : ℝ => partialY v t y) =ᶠ[nhds x]
      (fun t : ℝ => partialX u t y) := by
    simpa using (continuousAt_id.prodMk continuousAt_const).eventually hCR
  simpa [partialXX, partialYX, partialX] using hline.deriv_eq.symm

theorem gap14 (v : ℝ → ℝ → ℝ) (x y : ℝ)
    (hC2 : ContDiffAt ℝ 2 (Function.uncurry v) (x, y)) :
    partialYX v x y = partialXY v x y := by
  exact mixed_partial_comm hC2

theorem gap15 (u v : ℝ → ℝ → ℝ) (x y : ℝ)
    (hCR : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      partialX v p.1 p.2 = -partialY u p.1 p.2) :
    partialXY v x y = partialY (fun a b => -partialY u a b) x y := by
  have hline : (fun t : ℝ => partialX v x t) =ᶠ[nhds y]
      (fun t : ℝ => -partialY u x t) := by
    simpa using (continuousAt_const.prodMk continuousAt_id).eventually hCR
  simpa [partialXY, partialY] using hline.deriv_eq

theorem gap16 (u : ℝ → ℝ → ℝ) (x y : ℝ) :
    partialY (fun a b => -partialY u a b) x y = -partialYY u x y := by
  change deriv (fun t : ℝ => -partialY u x t) y =
    -deriv (fun t : ℝ => partialY u x t) y
  change deriv (-(fun t : ℝ => partialY u x t)) y =
    -deriv (fun t : ℝ => partialY u x t) y
  exact deriv.neg

theorem gap17 (u v : ℝ → ℝ → ℝ) (x y : ℝ)
    (h1 : partialXX u x y = partialYX v x y)
    (h2 : partialYX v x y = partialXY v x y)
    (h3 : partialXY v x y = partialY (fun a b => -partialY u a b) x y)
    (h4 : partialY (fun a b => -partialY u a b) x y = -partialYY u x y) :
    partialXX u x y = -partialYY u x y := by
  exact h1.trans (h2.trans (h3.trans h4))

theorem gap18 (u v : ℝ → ℝ → ℝ) (x y : ℝ)
    (hCR : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      partialY u p.1 p.2 = -partialX v p.1 p.2)
    (hC2 : ContDiffAt ℝ 2 (Function.uncurry u) (x, y)) :
    partialXY u x y = -partialXX v x y := by
  have hline : (fun t : ℝ => partialY u t y) =ᶠ[nhds x]
      (fun t : ℝ => -partialX v t y) := by
    simpa using (continuousAt_id.prodMk continuousAt_const).eventually hCR
  have hd :
      partialYX u x y = -partialXX v x y := by
    calc
      partialYX u x y =
          deriv (fun t : ℝ => partialY u t y) x := by rfl
      _ = deriv (fun t : ℝ => -partialX v t y) x := hline.deriv_eq
      _ = -partialXX v x y := by
        simpa [partialXX, partialX] using
          (deriv.neg (f := fun t : ℝ => partialX v t y) (x := x))
  exact (mixed_partial_comm hC2).symm.trans hd

theorem gap19 (v : ℝ → ℝ → ℝ) (x y : ℝ)
    (hHarmonic : partialXX v x y + partialYY v x y = 0) :
    -partialXX v x y = partialYY v x y := by
  linarith

theorem gap20 (u v : ℝ → ℝ → ℝ) (x y : ℝ)
    (h1 : partialXY u x y = -partialXX v x y)
    (h2 : -partialXX v x y = partialYY v x y) :
    partialXY u x y = partialYY v x y := by
  exact h1.trans h2

theorem gap21 (u v : ℝ → ℝ → ℝ) (x y : ℝ)
    (hCR1 : partialY u x y = -partialX v x y)
    (hCR2 : partialY v x y = partialX u x y) :
    partialX u x y ^ 2 + partialY u x y ^ 2 =
      partialX v x y ^ 2 + partialY v x y ^ 2 := by
  rw [hCR1, hCR2]
  ring

theorem gap22 (u v : ℝ → ℝ → ℝ) (x y : ℝ)
    (hCR1 : partialY u x y = -partialX v x y)
    (hCR2 : partialY v x y = partialX u x y) :
    partialX u x y * partialX v x y =
      -partialY u x y * partialY v x y := by
  rw [hCR1, hCR2]
  ring

theorem gap23 (u : ℝ → ℝ → ℝ) (x y : ℝ)
    (hHarmonic : partialXX u x y = -partialYY u x y) :
    partialXX u x y + partialYY u x y = 0 := by
  linarith

theorem gap24 (v : ℝ → ℝ → ℝ) (x y : ℝ)
    (hNegSecond : -partialXX v x y = partialYY v x y) :
    partialXX v x y + partialYY v x y = 0 := by
  linarith

theorem gap25 (u v z Z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hZxx : partialXX Z x y = secondChainX z u v x y)
    (hZyy : partialYY Z x y = secondChainY z u v x y)
    (hCR1 : partialY u x y = -partialX v x y)
    (hCR2 : partialY v x y = partialX u x y)
    (hHarmonicU : partialXX u x y + partialYY u x y = 0)
    (hHarmonicV : partialXX v x y + partialYY v x y = 0) :
    partialXX Z x y + partialYY Z x y =
      (partialX u x y ^ 2 + partialY u x y ^ 2) *
        (partialXX z (u x y) (v x y) + partialYY z (u x y) (v x y)) := by
  have hvx : partialX v x y = -partialY u x y := by
    linarith [hCR1]
  have huu : partialYY u x y = -partialXX u x y := by
    linarith [hHarmonicU]
  have hvv : partialYY v x y = -partialXX v x y := by
    linarith [hHarmonicV]
  rw [hZxx, hZyy]
  unfold secondChainX secondChainY
  rw [hvx, hCR2, huu, hvv]
  ring

theorem gap26 (u v z Z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hPDE : partialXX Z x y + partialYY Z x y = 0)
    (hTransform : partialXX Z x y + partialYY Z x y =
      (partialX u x y ^ 2 + partialY u x y ^ 2) *
        (partialXX z (u x y) (v x y) + partialYY z (u x y) (v x y))) :
    (partialX u x y ^ 2 + partialY u x y ^ 2) *
      (partialXX z (u x y) (v x y) + partialYY z (u x y) (v x y)) = 0 := by
  exact hTransform.symm.trans hPDE

theorem gap27 (Z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hPDE : partialXX Z x y + partialYY Z x y = 0) :
    partialXX Z x y + partialYY Z x y = 0 := by
  exact hPDE

theorem gap28 (u v z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hScale : partialX u x y ^ 2 + partialY u x y ^ 2 ≠ 0)
    (hProduct : (partialX u x y ^ 2 + partialY u x y ^ 2) *
      (partialXX z (u x y) (v x y) + partialYY z (u x y) (v x y)) = 0) :
    partialXX z (u x y) (v x y) + partialYY z (u x y) (v x y) = 0 := by
  exact (mul_eq_zero.mp hProduct).resolve_left hScale

end

end ProofGap.Exercise3492
