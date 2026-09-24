import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3306

noncomputable section

abbrev RealFunction3 := ℝ → ℝ → ℝ → ℝ

def partialX (u : RealFunction3) (x y z : ℝ) : ℝ :=
  deriv (fun t => u t y z) x

def partialY (u : RealFunction3) (x y z : ℝ) : ℝ :=
  deriv (fun t => u x t z) y

def partialZ (u : RealFunction3) (x y z : ℝ) : ℝ :=
  deriv (fun t => u x y t) z

def partialXX (u : RealFunction3) (x y z : ℝ) : ℝ :=
  (deriv^[2]) (fun t => u t y z) x

def partialYY (u : RealFunction3) (x y z : ℝ) : ℝ :=
  (deriv^[2]) (fun t => u x t z) y

def partialZZ (u : RealFunction3) (x y z : ℝ) : ℝ :=
  (deriv^[2]) (fun t => u x y t) z

def laplacian (u : RealFunction3) (x y z : ℝ) : ℝ :=
  partialXX u x y z + partialYY u x y z + partialZZ u x y z

def gradientDot (u v : RealFunction3) (x y z : ℝ) : ℝ :=
  partialX u x y z * partialX v x y z +
    partialY u x y z * partialY v x y z +
    partialZ u x y z * partialZ v x y z

def uncurry₃ (f : RealFunction3) : ℝ × ℝ × ℝ → ℝ :=
  fun p => f p.1 p.2.1 p.2.2

def expandedProductLaplacian (u v : RealFunction3)
    (x y z : ℝ) : ℝ :=
  u x y z * partialXX v x y z +
    v x y z * partialXX u x y z +
    2 * partialX u x y z * partialX v x y z +
    u x y z * partialYY v x y z +
    v x y z * partialYY u x y z +
    2 * partialY u x y z * partialY v x y z +
    u x y z * partialZZ v x y z +
    v x y z * partialZZ u x y z +
    2 * partialZ u x y z * partialZ v x y z

private theorem secondDeriv_mul (f g : ℝ → ℝ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x : ℝ) :
    (deriv^[2]) (fun t => f t * g t) x =
      f x * (deriv^[2]) g x + g x * (deriv^[2]) f x +
        2 * deriv f x * deriv g x := by
  have hf0 : Differentiable ℝ f :=
    hf.differentiable (by decide)
  have hg0 : Differentiable ℝ g :=
    hg.differentiable (by decide)
  have hfF : ContDiff ℝ 1 (fderiv ℝ f) :=
    hf.fderiv_right (m := 1) (by norm_num)
  have hgF : ContDiff ℝ 1 (fderiv ℝ g) :=
    hg.fderiv_right (m := 1) (by norm_num)
  have hdfc : ContDiff ℝ 1 (deriv f) := by
    simpa only [deriv] using
      hfF.clm_apply (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => (1 : ℝ)))
  have hdgc : ContDiff ℝ 1 (deriv g) := by
    simpa only [deriv] using
      hgF.clm_apply (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => (1 : ℝ)))
  have hdf : Differentiable ℝ (deriv f) :=
    hdfc.differentiable one_ne_zero
  have hdg : Differentiable ℝ (deriv g) :=
    hdgc.differentiable one_ne_zero
  change deriv (deriv (fun t => f t * g t)) x =
    f x * deriv (deriv g) x + g x * deriv (deriv f) x +
      2 * deriv f x * deriv g x
  have hfirst :
      deriv (fun t => f t * g t) =
        fun t => deriv f t * g t + f t * deriv g t := by
    funext t
    exact (((hf0 t).hasDerivAt).mul ((hg0 t).hasDerivAt)).deriv
  calc
    deriv (deriv (fun t => f t * g t)) x =
        deriv (fun t => deriv f t * g t + f t * deriv g t) x := by
      rw [hfirst]
    _ = (deriv (deriv f) x * g x + deriv f x * deriv g x) +
          (deriv f x * deriv g x + f x * deriv (deriv g) x) :=
      ((((hdf x).hasDerivAt).mul ((hg0 x).hasDerivAt)).add
        (((hf0 x).hasDerivAt).mul ((hdg x).hasDerivAt))).deriv
    _ = f x * deriv (deriv g) x + g x * deriv (deriv f) x +
          2 * deriv f x * deriv g x := by
      ring

theorem gap1 (u v : RealFunction3)
    (hu : ContDiff ℝ 2 (uncurry₃ u))
    (hv : ContDiff ℝ 2 (uncurry₃ v)) (x y z : ℝ) :
    laplacian (fun a b c => u a b c * v a b c) x y z =
      expandedProductLaplacian u v x y z := by
  have hmapX : ContDiff ℝ 2 (fun t : ℝ => (t, (y, z))) :=
    contDiff_id.prodMk (contDiff_const.prodMk contDiff_const)
  have hmapY : ContDiff ℝ 2 (fun t : ℝ => (x, (t, z))) :=
    contDiff_const.prodMk (contDiff_id.prodMk contDiff_const)
  have hmapZ : ContDiff ℝ 2 (fun t : ℝ => (x, (y, t))) :=
    contDiff_const.prodMk (contDiff_const.prodMk contDiff_id)
  have hux : ContDiff ℝ 2 (fun t : ℝ => u t y z) := by
    simpa [uncurry₃] using hu.comp hmapX
  have hvx : ContDiff ℝ 2 (fun t : ℝ => v t y z) := by
    simpa [uncurry₃] using hv.comp hmapX
  have huy : ContDiff ℝ 2 (fun t : ℝ => u x t z) := by
    simpa [uncurry₃] using hu.comp hmapY
  have hvy : ContDiff ℝ 2 (fun t : ℝ => v x t z) := by
    simpa [uncurry₃] using hv.comp hmapY
  have huz : ContDiff ℝ 2 (fun t : ℝ => u x y t) := by
    simpa [uncurry₃] using hu.comp hmapZ
  have hvz : ContDiff ℝ 2 (fun t : ℝ => v x y t) := by
    simpa [uncurry₃] using hv.comp hmapZ
  simp only [laplacian, expandedProductLaplacian, partialXX, partialYY,
    partialZZ, partialX, partialY, partialZ]
  rw [secondDeriv_mul (fun t : ℝ => u t y z) (fun t : ℝ => v t y z) hux hvx x]
  rw [secondDeriv_mul (fun t : ℝ => u x t z) (fun t : ℝ => v x t z) huy hvy y]
  rw [secondDeriv_mul (fun t : ℝ => u x y t) (fun t : ℝ => v x y t) huz hvz z]
  ring

theorem gap2 (u v : RealFunction3)
    (hu : ContDiff ℝ 2 (uncurry₃ u))
    (hv : ContDiff ℝ 2 (uncurry₃ v)) (x y z : ℝ) :
    laplacian (fun a b c => u a b c * v a b c) x y z =
      u x y z * laplacian v x y z +
        v x y z * laplacian u x y z +
        2 * gradientDot u v x y z := by
  rw [gap1 u v hu hv x y z]
  simp only [expandedProductLaplacian, laplacian, gradientDot]
  ring

theorem gap3 (u v : RealFunction3)
    (hu : ContDiff ℝ 2 (uncurry₃ u))
    (hv : ContDiff ℝ 2 (uncurry₃ v)) (x y z : ℝ) :
    laplacian (fun a b c => u a b c * v a b c) x y z =
      u x y z * laplacian v x y z +
        v x y z * laplacian u x y z +
        2 * gradientDot u v x y z := by
  exact gap2 u v hu hv x y z

end

end ProofGap.Exercise3306
