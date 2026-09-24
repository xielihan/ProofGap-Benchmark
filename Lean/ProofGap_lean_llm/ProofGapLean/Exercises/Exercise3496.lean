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

namespace ProofGap.Exercise3496

noncomputable section

def partialX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ := deriv (fun t => f t y) x
def partialY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ := deriv (fun t => f x t) y
def partialXX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ := partialX (partialX f) x y
def partialXY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ := partialY (partialX f) x y
def partialYY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ := partialY (partialY f) x y

private theorem hasDerivAt_const_div_sq
    (a t : ℝ) (ht : t ≠ 0) :
    HasDerivAt (fun s : ℝ => a / s ^ 2) (-(2 * a / t ^ 3)) t := by
  have hsq : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
    convert (hasDerivAt_id t).pow 2 using 1 <;> norm_num <;> ring
  have hquot : HasDerivAt (fun s : ℝ => a / s ^ 2)
      ((0 * t ^ 2 - a * (2 * t)) / (t ^ 2) ^ 2) t := by
    exact (hasDerivAt_const t a).div hsq (pow_ne_zero 2 ht)
  convert hquot using 1 <;> field_simp [ht] <;> ring

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

theorem gap1 (u v z Z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hx : x ≠ 0)
    (hCompose : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      Z p.1 p.2 = z (u p.1 p.2) (v p.1 p.2))
    (hU : ∀ᶠ p : ℝ × ℝ in nhds (x, y), u p.1 p.2 = p.1 + p.2)
    (hV : ∀ᶠ p : ℝ × ℝ in nhds (x, y), v p.1 p.2 = 1 / p.1 + 1 / p.2)
    (hDiffz : DifferentiableAt ℝ (Function.uncurry z) (u x y, v x y)) :
    partialX Z x y = partialX z (u x y) (v x y) -
      1 / x ^ 2 * partialY z (u x y) (v x y) := by
  have hu : (fun t : ℝ => u t y) =ᶠ[nhds x] (fun t : ℝ => t + y) := by
    simpa using (continuousAt_id.prodMk continuousAt_const).eventually hU
  have hv : (fun t : ℝ => v t y) =ᶠ[nhds x]
      (fun t : ℝ => 1 / t + 1 / y) := by
    simpa using (continuousAt_id.prodMk continuousAt_const).eventually hV
  have hdu0 : HasDerivAt (fun t : ℝ => t + y) 1 x :=
    (hasDerivAt_id x).add_const y
  have hdv0 : HasDerivAt (fun t : ℝ => 1 / t + 1 / y) (-1 / x ^ 2) x := by
    have hi : HasDerivAt (fun t : ℝ => 1 / t) (-1 / x ^ 2) x := by
      simpa [one_div, pow_two] using (hasDerivAt_id x).inv hx
    exact hi.add_const (1 / y)
  have hdu : HasDerivAt (fun t : ℝ => u t y) 1 x :=
    hdu0.congr_of_eventuallyEq hu
  have hdv : HasDerivAt (fun t : ℝ => v t y) (-1 / x ^ 2) x :=
    hdv0.congr_of_eventuallyEq hv
  have hz : (fun t : ℝ => Z t y) =ᶠ[nhds x]
      (fun t : ℝ => z (u t y) (v t y)) := by
    simpa using
      (continuousAt_id.prodMk continuousAt_const).eventually hCompose
  change deriv (fun t : ℝ => Z t y) x = _
  calc
    deriv (fun t : ℝ => Z t y) x =
        deriv (fun t : ℝ => z (u t y) (v t y)) x := hz.deriv_eq
    _ = _ := by
      convert (hasDerivAt_comp₂ z (fun t => u t y) (fun t => v t y)
        hDiffz hdu hdv).deriv using 1 <;> ring

theorem gap2 (u v z Z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hy : y ≠ 0)
    (hCompose : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      Z p.1 p.2 = z (u p.1 p.2) (v p.1 p.2))
    (hU : ∀ᶠ p : ℝ × ℝ in nhds (x, y), u p.1 p.2 = p.1 + p.2)
    (hV : ∀ᶠ p : ℝ × ℝ in nhds (x, y), v p.1 p.2 = 1 / p.1 + 1 / p.2)
    (hDiffz : DifferentiableAt ℝ (Function.uncurry z) (u x y, v x y)) :
    partialY Z x y = partialX z (u x y) (v x y) -
      1 / y ^ 2 * partialY z (u x y) (v x y) := by
  have hu : (fun t : ℝ => u x t) =ᶠ[nhds y] (fun t : ℝ => x + t) := by
    simpa using (continuousAt_const.prodMk continuousAt_id).eventually hU
  have hv : (fun t : ℝ => v x t) =ᶠ[nhds y]
      (fun t : ℝ => 1 / x + 1 / t) := by
    simpa using (continuousAt_const.prodMk continuousAt_id).eventually hV
  have hdu0 : HasDerivAt (fun t : ℝ => x + t) 1 y :=
    (hasDerivAt_id y).const_add x
  have hdv0 : HasDerivAt (fun t : ℝ => 1 / x + 1 / t) (-1 / y ^ 2) y := by
    have hi : HasDerivAt (fun t : ℝ => 1 / t) (-1 / y ^ 2) y := by
      simpa [one_div, pow_two] using (hasDerivAt_id y).inv hy
    exact hi.const_add (1 / x)
  have hdu : HasDerivAt (fun t : ℝ => u x t) 1 y :=
    hdu0.congr_of_eventuallyEq hu
  have hdv : HasDerivAt (fun t : ℝ => v x t) (-1 / y ^ 2) y :=
    hdv0.congr_of_eventuallyEq hv
  have hz : (fun t : ℝ => Z x t) =ᶠ[nhds y]
      (fun t : ℝ => z (u x t) (v x t)) := by
    simpa using
      (continuousAt_const.prodMk continuousAt_id).eventually hCompose
  change deriv (fun t : ℝ => Z x t) y = _
  calc
    deriv (fun t : ℝ => Z x t) y =
        deriv (fun t : ℝ => z (u x t) (v x t)) y := hz.deriv_eq
    _ = _ := by
      convert (hasDerivAt_comp₂ z (fun t => u x t) (fun t => v x t)
        hDiffz hdu hdv).deriv using 1 <;> ring

theorem gap3 (u v z Z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hx : x ≠ 0)
    (hZx : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      partialX Z p.1 p.2 = partialX z (u p.1 p.2) (v p.1 p.2) -
        1 / p.1 ^ 2 * partialY z (u p.1 p.2) (v p.1 p.2))
    (hDiffZu : DifferentiableAt ℝ (Function.uncurry (partialX z)) (u x y, v x y))
    (hDiffZv : DifferentiableAt ℝ (Function.uncurry (partialY z)) (u x y, v x y))
    (hC2z : ContDiffAt ℝ 2 (Function.uncurry z) (u x y, v x y))
    (hU : ∀ᶠ p : ℝ × ℝ in nhds (x, y), u p.1 p.2 = p.1 + p.2)
    (hV : ∀ᶠ p : ℝ × ℝ in nhds (x, y), v p.1 p.2 = 1 / p.1 + 1 / p.2) :
    partialXX Z x y = partialXX z (u x y) (v x y) -
      2 / x ^ 2 * partialXY z (u x y) (v x y) +
      1 / x ^ 4 * partialYY z (u x y) (v x y) +
      2 / x ^ 3 * partialY z (u x y) (v x y) := by
  have hu : (fun t : ℝ => u t y) =ᶠ[nhds x] (fun t : ℝ => t + y) := by
    simpa using (continuousAt_id.prodMk continuousAt_const).eventually hU
  have hv : (fun t : ℝ => v t y) =ᶠ[nhds x]
      (fun t : ℝ => 1 / t + 1 / y) := by
    simpa using (continuousAt_id.prodMk continuousAt_const).eventually hV
  have hdu : HasDerivAt (fun t : ℝ => u t y) 1 x :=
    ((hasDerivAt_id x).add_const y).congr_of_eventuallyEq hu
  have hdv0 : HasDerivAt (fun t : ℝ => 1 / t + 1 / y) (-1 / x ^ 2) x := by
    have hi : HasDerivAt (fun t : ℝ => 1 / t) (-1 / x ^ 2) x := by
      simpa [one_div, pow_two] using (hasDerivAt_id x).inv hx
    exact hi.add_const (1 / y)
  have hdv : HasDerivAt (fun t : ℝ => v t y) (-1 / x ^ 2) x :=
    hdv0.congr_of_eventuallyEq hv
  have hmix : partialX (partialY z) (u x y) (v x y) =
      partialXY z (u x y) (v x y) :=
    mixed_partial_comm hC2z
  have hA := hasDerivAt_comp₂ (partialX z) (fun t => u t y)
    (fun t => v t y) hDiffZu hdu hdv
  have hB := hasDerivAt_comp₂ (partialY z) (fun t => u t y)
    (fun t => v t y) hDiffZv hdu hdv
  have hq : HasDerivAt (fun t : ℝ => 1 / t ^ 2)
      (-(2 / x ^ 3)) x := by
    simpa using hasDerivAt_const_div_sq 1 x hx
  have hR := hA.sub (hq.mul hB)
  change HasDerivAt
    (fun t : ℝ =>
      partialX z (u t y) (v t y) -
        1 / t ^ 2 * partialY z (u t y) (v t y)) _ x at hR
  have hdR := hR.deriv
  rw [hmix] at hdR
  have hz : (fun t : ℝ => partialX Z t y) =ᶠ[nhds x]
      (fun t : ℝ =>
        partialX z (u t y) (v t y) -
          1 / t ^ 2 * partialY z (u t y) (v t y)) := by
    simpa using (continuousAt_id.prodMk continuousAt_const).eventually hZx
  change deriv (fun t : ℝ => partialX Z t y) x = _
  calc
    deriv (fun t : ℝ => partialX Z t y) x =
        deriv (fun t : ℝ =>
          partialX z (u t y) (v t y) -
            1 / t ^ 2 * partialY z (u t y) (v t y)) x := hz.deriv_eq
    _ = _ := by
      rw [hdR]
      simp only [partialXX, partialXY, partialYY]
      field_simp [hx]
      ring

theorem gap4 (u v z Z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hy : y ≠ 0)
    (hZy : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      partialY Z p.1 p.2 = partialX z (u p.1 p.2) (v p.1 p.2) -
        1 / p.2 ^ 2 * partialY z (u p.1 p.2) (v p.1 p.2))
    (hDiffZu : DifferentiableAt ℝ (Function.uncurry (partialX z)) (u x y, v x y))
    (hDiffZv : DifferentiableAt ℝ (Function.uncurry (partialY z)) (u x y, v x y))
    (hC2z : ContDiffAt ℝ 2 (Function.uncurry z) (u x y, v x y))
    (hU : ∀ᶠ p : ℝ × ℝ in nhds (x, y), u p.1 p.2 = p.1 + p.2)
    (hV : ∀ᶠ p : ℝ × ℝ in nhds (x, y), v p.1 p.2 = 1 / p.1 + 1 / p.2) :
    partialYY Z x y = partialXX z (u x y) (v x y) -
      2 / y ^ 2 * partialXY z (u x y) (v x y) +
      1 / y ^ 4 * partialYY z (u x y) (v x y) +
      2 / y ^ 3 * partialY z (u x y) (v x y) := by
  have hu : (fun t : ℝ => u x t) =ᶠ[nhds y] (fun t : ℝ => x + t) := by
    simpa using (continuousAt_const.prodMk continuousAt_id).eventually hU
  have hv : (fun t : ℝ => v x t) =ᶠ[nhds y]
      (fun t : ℝ => 1 / x + 1 / t) := by
    simpa using (continuousAt_const.prodMk continuousAt_id).eventually hV
  have hdu : HasDerivAt (fun t : ℝ => u x t) 1 y :=
    ((hasDerivAt_id y).const_add x).congr_of_eventuallyEq hu
  have hdv0 : HasDerivAt (fun t : ℝ => 1 / x + 1 / t) (-1 / y ^ 2) y := by
    have hi : HasDerivAt (fun t : ℝ => 1 / t) (-1 / y ^ 2) y := by
      simpa [one_div, pow_two] using (hasDerivAt_id y).inv hy
    exact hi.const_add (1 / x)
  have hdv : HasDerivAt (fun t : ℝ => v x t) (-1 / y ^ 2) y :=
    hdv0.congr_of_eventuallyEq hv
  have hmix : partialX (partialY z) (u x y) (v x y) =
      partialXY z (u x y) (v x y) :=
    mixed_partial_comm hC2z
  have hA := hasDerivAt_comp₂ (partialX z) (fun t => u x t)
    (fun t => v x t) hDiffZu hdu hdv
  have hB := hasDerivAt_comp₂ (partialY z) (fun t => u x t)
    (fun t => v x t) hDiffZv hdu hdv
  have hq : HasDerivAt (fun t : ℝ => 1 / t ^ 2)
      (-(2 / y ^ 3)) y := by
    simpa using hasDerivAt_const_div_sq 1 y hy
  have hR := hA.sub (hq.mul hB)
  change HasDerivAt
    (fun t : ℝ =>
      partialX z (u x t) (v x t) -
        1 / t ^ 2 * partialY z (u x t) (v x t)) _ y at hR
  have hdR := hR.deriv
  rw [hmix] at hdR
  have hz : (fun t : ℝ => partialY Z x t) =ᶠ[nhds y]
      (fun t : ℝ =>
        partialX z (u x t) (v x t) -
          1 / t ^ 2 * partialY z (u x t) (v x t)) := by
    simpa using (continuousAt_const.prodMk continuousAt_id).eventually hZy
  change deriv (fun t : ℝ => partialY Z x t) y = _
  calc
    deriv (fun t : ℝ => partialY Z x t) y =
        deriv (fun t : ℝ =>
          partialX z (u x t) (v x t) -
            1 / t ^ 2 * partialY z (u x t) (v x t)) y := hz.deriv_eq
    _ = _ := by
      rw [hdR]
      simp only [partialXX, partialXY, partialYY]
      field_simp [hy]
      ring

theorem gap5 (u v z Z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hx : x ≠ 0) (hy : y ≠ 0)
    (hZx : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      partialX Z p.1 p.2 = partialX z (u p.1 p.2) (v p.1 p.2) -
        1 / p.1 ^ 2 * partialY z (u p.1 p.2) (v p.1 p.2))
    (hDiffZu : DifferentiableAt ℝ (Function.uncurry (partialX z)) (u x y, v x y))
    (hDiffZv : DifferentiableAt ℝ (Function.uncurry (partialY z)) (u x y, v x y))
    (hC2z : ContDiffAt ℝ 2 (Function.uncurry z) (u x y, v x y))
    (hU : ∀ᶠ p : ℝ × ℝ in nhds (x, y), u p.1 p.2 = p.1 + p.2)
    (hV : ∀ᶠ p : ℝ × ℝ in nhds (x, y), v p.1 p.2 = 1 / p.1 + 1 / p.2) :
    partialXY Z x y = partialXX z (u x y) (v x y) -
      (1 / x ^ 2 + 1 / y ^ 2) * partialXY z (u x y) (v x y) +
      1 / (x ^ 2 * y ^ 2) * partialYY z (u x y) (v x y) := by
  have hu : (fun t : ℝ => u x t) =ᶠ[nhds y] (fun t : ℝ => x + t) := by
    simpa using (continuousAt_const.prodMk continuousAt_id).eventually hU
  have hv : (fun t : ℝ => v x t) =ᶠ[nhds y]
      (fun t : ℝ => 1 / x + 1 / t) := by
    simpa using (continuousAt_const.prodMk continuousAt_id).eventually hV
  have hdu : HasDerivAt (fun t : ℝ => u x t) 1 y :=
    ((hasDerivAt_id y).const_add x).congr_of_eventuallyEq hu
  have hdv0 : HasDerivAt (fun t : ℝ => 1 / x + 1 / t) (-1 / y ^ 2) y := by
    have hi : HasDerivAt (fun t : ℝ => 1 / t) (-1 / y ^ 2) y := by
      simpa [one_div, pow_two] using (hasDerivAt_id y).inv hy
    exact hi.const_add (1 / x)
  have hdv : HasDerivAt (fun t : ℝ => v x t) (-1 / y ^ 2) y :=
    hdv0.congr_of_eventuallyEq hv
  have hmix : partialX (partialY z) (u x y) (v x y) =
      partialXY z (u x y) (v x y) :=
    mixed_partial_comm hC2z
  have hA := hasDerivAt_comp₂ (partialX z) (fun t => u x t)
    (fun t => v x t) hDiffZu hdu hdv
  have hB := hasDerivAt_comp₂ (partialY z) (fun t => u x t)
    (fun t => v x t) hDiffZv hdu hdv
  have hR := hA.sub (hB.const_mul (1 / x ^ 2))
  change HasDerivAt
    (fun t : ℝ =>
      partialX z (u x t) (v x t) -
        1 / x ^ 2 * partialY z (u x t) (v x t)) _ y at hR
  have hdR := hR.deriv
  rw [hmix] at hdR
  have hz : (fun t : ℝ => partialX Z x t) =ᶠ[nhds y]
      (fun t : ℝ =>
        partialX z (u x t) (v x t) -
          1 / x ^ 2 * partialY z (u x t) (v x t)) := by
    simpa using (continuousAt_const.prodMk continuousAt_id).eventually hZx
  change deriv (fun t : ℝ => partialX Z x t) y = _
  calc
    deriv (fun t : ℝ => partialX Z x t) y =
        deriv (fun t : ℝ =>
          partialX z (u x t) (v x t) -
            1 / x ^ 2 * partialY z (u x t) (v x t)) y := hz.deriv_eq
    _ = _ := by
      rw [hdR]
      simp only [partialXX, partialXY, partialYY]
      field_simp [hx, hy]
      ring

theorem gap6 (u v z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hx : x ≠ 0) (hy : y ≠ 0)
    (Z : ℝ → ℝ → ℝ)
    (hPDE : x ^ 2 * partialXX Z x y -
      (x ^ 2 + y ^ 2) * partialXY Z x y + y ^ 2 * partialYY Z x y = 0)
    (hZxx : partialXX Z x y = partialXX z (u x y) (v x y) -
      2 / x ^ 2 * partialXY z (u x y) (v x y) +
      1 / x ^ 4 * partialYY z (u x y) (v x y) +
      2 / x ^ 3 * partialY z (u x y) (v x y))
    (hZyy : partialYY Z x y = partialXX z (u x y) (v x y) -
      2 / y ^ 2 * partialXY z (u x y) (v x y) +
      1 / y ^ 4 * partialYY z (u x y) (v x y) +
      2 / y ^ 3 * partialY z (u x y) (v x y))
    (hZxy : partialXY Z x y = partialXX z (u x y) (v x y) -
      (1 / x ^ 2 + 1 / y ^ 2) * partialXY z (u x y) (v x y) +
      1 / (x ^ 2 * y ^ 2) * partialYY z (u x y) (v x y)) :
    (x ^ 2 - y ^ 2) ^ 2 / (x ^ 2 * y ^ 2) *
        partialXY z (u x y) (v x y) +
      2 * (1 / x + 1 / y) * partialY z (u x y) (v x y) = 0 := by
  rw [hZxx, hZyy, hZxy] at hPDE
  field_simp [hx, hy] at hPDE ⊢
  linarith

theorem gap7 (v : ℝ → ℝ → ℝ) (x y : ℝ)
    (hV : v x y = 1 / x + 1 / y) :
    v x y = 1 / x + 1 / y := by
  exact hV

theorem gap8 (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
    1 / x + 1 / y = (x + y) / (x * y) := by
  field_simp [hx, hy]
  ring

theorem gap9 (u : ℝ → ℝ → ℝ) (x y : ℝ)
    (hU : u x y = x + y) :
    (x + y) / (x * y) = u x y / (x * y) := by
  rw [hU]

theorem gap10 (u v : ℝ → ℝ → ℝ) (x y : ℝ)
    (h1 : v x y = 1 / x + 1 / y)
    (h2 : 1 / x + 1 / y = (x + y) / (x * y))
    (h3 : (x + y) / (x * y) = u x y / (x * y)) :
    v x y = u x y / (x * y) := by
  exact h1.trans (h2.trans h3)

theorem gap11 (u v : ℝ → ℝ → ℝ) (x y : ℝ)
    (hxy : x * y ≠ 0) (hv : v x y ≠ 0)
    (hV : v x y = u x y / (x * y)) :
    x * y = u x y / v x y := by
  rcases mul_ne_zero_iff.mp hxy with ⟨hx, hy⟩
  apply (eq_div_iff hv).2
  rw [hV]
  field_simp [hx, hy]

theorem gap12 (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
    (x ^ 2 - y ^ 2) ^ 2 / (x ^ 2 * y ^ 2) =
      (x + y) ^ 2 / (x ^ 2 * y ^ 2) * (x - y) ^ 2 := by
  field_simp [hx, hy]
  ring

theorem gap13 (x y : ℝ) (hx : x ≠ 0) (hy : y ≠ 0) :
    (x + y) ^ 2 / (x ^ 2 * y ^ 2) * (x - y) ^ 2 =
      (1 / x + 1 / y) ^ 2 * ((x + y) ^ 2 - 4 * x * y) := by
  field_simp [hx, hy]
  ring

theorem gap14 (u v : ℝ → ℝ → ℝ) (x y : ℝ)
    (hv : v x y ≠ 0)
    (hU : u x y = x + y)
    (hV : v x y = 1 / x + 1 / y)
    (hxy : x * y = u x y / v x y) :
    (1 / x + 1 / y) ^ 2 * ((x + y) ^ 2 - 4 * x * y) =
      v x y ^ 2 * (u x y ^ 2 - 4 * (u x y / v x y)) := by
  have h4 : 4 * x * y = 4 * (u x y / v x y) := by
    rw [mul_assoc, hxy]
  rw [← hV, ← hU, h4]

theorem gap15 (u v : ℝ → ℝ → ℝ) (x y : ℝ)
    (hv : v x y ≠ 0) :
    v x y ^ 2 * (u x y ^ 2 - 4 * (u x y / v x y)) =
      u x y * v x y * (u x y * v x y - 4) := by
  field_simp [hv]

theorem gap16 (u v : ℝ → ℝ → ℝ) (x y : ℝ)
    (h12 : (x ^ 2 - y ^ 2) ^ 2 / (x ^ 2 * y ^ 2) =
      (x + y) ^ 2 / (x ^ 2 * y ^ 2) * (x - y) ^ 2)
    (h13 : (x + y) ^ 2 / (x ^ 2 * y ^ 2) * (x - y) ^ 2 =
      (1 / x + 1 / y) ^ 2 * ((x + y) ^ 2 - 4 * x * y))
    (h14 : (1 / x + 1 / y) ^ 2 * ((x + y) ^ 2 - 4 * x * y) =
      v x y ^ 2 * (u x y ^ 2 - 4 * (u x y / v x y)))
    (h15 : v x y ^ 2 * (u x y ^ 2 - 4 * (u x y / v x y)) =
      u x y * v x y * (u x y * v x y - 4)) :
    (x ^ 2 - y ^ 2) ^ 2 / (x ^ 2 * y ^ 2) =
      u x y * v x y * (u x y * v x y - 4) := by
  exact h12.trans (h13.trans (h14.trans h15))

theorem gap17 (transformedEquation : ℝ → ℝ → ℝ)
    (u v z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hDefinition : transformedEquation x y = partialXY z (u x y) (v x y)) :
    transformedEquation x y = partialXY z (u x y) (v x y) := by
  exact hDefinition

theorem gap18 (u v z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hDenom : u x y * (4 - u x y * v x y) ≠ 0)
    (hv : v x y ≠ 0)
    (hV : v x y = 1 / x + 1 / y)
    (hCoefficient :
      (x ^ 2 - y ^ 2) ^ 2 / (x ^ 2 * y ^ 2) =
        u x y * v x y * (u x y * v x y - 4))
    (hEquation :
      (x ^ 2 - y ^ 2) ^ 2 / (x ^ 2 * y ^ 2) *
          partialXY z (u x y) (v x y) +
        2 * (1 / x + 1 / y) * partialY z (u x y) (v x y) = 0) :
    partialXY z (u x y) (v x y) =
      2 / (u x y * (4 - u x y * v x y)) *
        partialY z (u x y) (v x y) := by
  rw [hCoefficient, ← hV] at hEquation
  have hfactor :
      v x y * (u x y * (u x y * v x y - 4) *
          partialXY z (u x y) (v x y) +
        2 * partialY z (u x y) (v x y)) = 0 := by
    nlinarith [hEquation]
  have hcore :
      u x y * (u x y * v x y - 4) *
          partialXY z (u x y) (v x y) +
        2 * partialY z (u x y) (v x y) = 0 :=
    (mul_eq_zero.mp hfactor).resolve_left hv
  calc
    partialXY z (u x y) (v x y) =
        (2 * partialY z (u x y) (v x y)) /
          (u x y * (4 - u x y * v x y)) := by
      apply (eq_div_iff hDenom).2
      linear_combination -hcore
    _ = 2 / (u x y * (4 - u x y * v x y)) *
          partialY z (u x y) (v x y) := by
      field_simp [hDenom]

theorem gap19 (transformedEquation : ℝ → ℝ → ℝ)
    (u v z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hDefinition : transformedEquation x y = partialXY z (u x y) (v x y))
    (hSolved : partialXY z (u x y) (v x y) =
      2 / (u x y * (4 - u x y * v x y)) *
        partialY z (u x y) (v x y)) :
    transformedEquation x y =
      2 / (u x y * (4 - u x y * v x y)) *
        partialY z (u x y) (v x y) := by
  exact hDefinition.trans hSolved

end

end ProofGap.Exercise3496
