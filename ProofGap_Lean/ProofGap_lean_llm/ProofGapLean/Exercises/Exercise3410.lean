import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3410

noncomputable section

def partialX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f t y) x

def partialY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f x t) y

def partialXX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialX f t y) x

def partialXY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialX f x t) y

def partialYY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialY f x t) y

def differential (f : ℝ → ℝ → ℝ) (x y dx dy : ℝ) : ℝ :=
  partialX f x y * dx + partialY f x y * dy

def secondDifferential (f : ℝ → ℝ → ℝ) (x y dx dy : ℝ) : ℝ :=
  partialXX f x y * dx ^ 2 +
    2 * partialXY f x y * dx * dy +
    partialYY f x y * dy ^ 2

private theorem fderiv_apply_eq_differential
    (f : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (hf : DifferentiableAt ℝ (Function.uncurry f) (x, y)) :
    fderiv ℝ (Function.uncurry f) (x, y) (dx, dy) =
      differential f x y dx dy := by
  let L := fderiv ℝ (Function.uncurry f) (x, y)
  have hx : L (1, 0) = partialX f x y := by
    have hc : HasFDerivAt
        (Function.uncurry f ∘ fun t : ℝ => (t, y))
        ((fderiv ℝ (Function.uncurry f) (x, y)).comp
          (ContinuousLinearMap.inl ℝ ℝ ℝ)) x :=
      hf.hasFDerivAt.comp x (hasFDerivAt_prodMk_left x y)
    have hd := hc.hasDerivAt.deriv
    simpa [L, partialX] using hd.symm
  have hy : L (0, 1) = partialY f x y := by
    have hc : HasFDerivAt
        (Function.uncurry f ∘ fun t : ℝ => (x, t))
        ((fderiv ℝ (Function.uncurry f) (x, y)).comp
          (ContinuousLinearMap.inr ℝ ℝ ℝ)) y :=
      hf.hasFDerivAt.comp y (hasFDerivAt_prodMk_right x y)
    have hd := hc.hasDerivAt.deriv
    simpa [L, partialY] using hd.symm
  change L (dx, dy) = _
  have hp : (dx, dy) = dx • (1, 0) + dy • (0, 1) := by
    ext <;> simp
  rw [hp, L.map_add, L.map_smul, L.map_smul, hx, hy]
  simp only [smul_eq_mul, differential]
  ring

private theorem hasDerivAt_line
    (f : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (hf : DifferentiableAt ℝ (Function.uncurry f) (x, y)) :
    HasDerivAt (fun t => f (x + t * dx) (y + t * dy))
      (differential f x y dx dy) 0 := by
  have hxline : HasDerivAt (fun t : ℝ => x + t * dx) dx 0 :=
    by convert (hasDerivAt_const 0 x).add ((hasDerivAt_id 0).mul_const dx) using 1 <;> simp
  have hyline : HasDerivAt (fun t : ℝ => y + t * dy) dy 0 :=
    by convert (hasDerivAt_const 0 y).add ((hasDerivAt_id 0).mul_const dy) using 1 <;> simp
  have hf0 : HasFDerivAt (Function.uncurry f)
      (fderiv ℝ (Function.uncurry f) (x, y))
      (x + 0 * dx, y + 0 * dy) := by simpa using hf.hasFDerivAt
  have hc := hf0.comp 0
    (hxline.hasFDerivAt.prodMk hyline.hasFDerivAt)
  have hd : HasDerivAt (fun t => f (x + t * dx) (y + t * dy))
      (fderiv ℝ (Function.uncurry f) (x, y) (dx, dy)) 0 := by
    convert hc.hasDerivAt using 1 <;> simp
  rw [fderiv_apply_eq_differential f x y dx dy hf] at hd
  exact hd

private theorem tendsto_line (x y dx dy : ℝ) :
    Filter.Tendsto (fun t : ℝ => (x + t * dx, y + t * dy))
      (nhds 0) (nhds (x, y)) := by
  have hcont : ContinuousAt (fun t : ℝ => (x + t * dx, y + t * dy)) 0 := by
    fun_prop
  simpa using hcont.tendsto

private theorem deriv_affine_line_at
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (p v : E) (t : ℝ)
    (hf : DifferentiableAt ℝ f (p + t • v)) :
    deriv (fun s : ℝ => f (p + s • v)) t =
      fderiv ℝ f (p + t • v) v := by
  have hc : HasDerivAt (fun s : ℝ => p + s • v) v t := by
    simpa only [id_eq, one_smul] using
      ((hasDerivAt_id t).smul_const v).const_add p
  exact (hf.hasFDerivAt.comp_hasDerivAt t hc).deriv

private theorem second_deriv_affine_line_at
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (p v : E) (hf : ContDiffAt ℝ 2 f p) :
    deriv (deriv (fun t : ℝ => f (p + t • v))) 0 =
      (fderiv ℝ (fderiv ℝ f) p v) v := by
  have hp : p + (0 : ℝ) • v = p := by simp
  have hline : Filter.Tendsto (fun t : ℝ => p + t • v)
      (nhds 0) (nhds p) := by
    have hc : ContinuousAt (fun t : ℝ => p + t • v) 0 := by fun_prop
    simpa using hc.tendsto
  have hev := hline.eventually (hf.eventually (by norm_num))
  have hfirst :
      deriv (fun t : ℝ => f (p + t • v)) =ᶠ[nhds 0]
        (fun t => fderiv ℝ f (p + t • v) v) := by
    filter_upwards [hev] with t ht
    exact deriv_affine_line_at f p v t (ht.differentiableAt (by decide))
  rw [hfirst.deriv_eq]
  have hDf : DifferentiableAt ℝ (fderiv ℝ f) p :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by decide)
  have hc : HasDerivAt (fun t : ℝ => p + t • v) v 0 := by
    simpa only [id_eq, one_smul] using
      ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add p
  have hDf0 : DifferentiableAt ℝ (fderiv ℝ f) (p + (0 : ℝ) • v) := by
    simpa using hDf
  have hcomp : HasDerivAt
      (fun t : ℝ => fderiv ℝ f (p + t • v))
      (fderiv ℝ (fderiv ℝ f) p v) 0 := by
    simpa using hDf0.hasFDerivAt.comp_hasDerivAt 0 hc
  simpa using (hcomp.clm_apply (hasDerivAt_const (x := 0) v)).deriv

private theorem secondDifferential_eq_secondLine
    (f : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (hf : ContDiffAt ℝ 2 (Function.uncurry f) (x, y)) :
    secondDifferential f x y dx dy =
      deriv
        (deriv (fun t : ℝ => f (x + t * dx) (y + t * dy))) 0 := by
  let F : ℝ × ℝ → ℝ := Function.uncurry f
  let ex : ℝ × ℝ := (1, 0)
  let ey : ℝ × ℝ := (0, 1)
  let d : ℝ × ℝ := (dx, dy)
  let H := fderiv ℝ (fderiv ℝ F) (x, y)
  have hF : ContDiffAt ℝ 2 F (x, y) := hf
  have hFd : DifferentiableAt ℝ F (x, y) := hF.differentiableAt (by decide)
  have hsec :
      deriv (deriv (fun t : ℝ => F ((x, y) + t • d))) 0 = H d d := by
    simpa [H] using second_deriv_affine_line_at F (x, y) d hF
  have hDf : DifferentiableAt ℝ (fderiv ℝ F) (x, y) :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by decide)
  have hxEvent : ∀ᶠ a : ℝ in nhds x,
      partialX f a y = fderiv ℝ F (a, y) ex := by
    have ht : Filter.Tendsto (fun a : ℝ => (a, y)) (nhds x) (nhds (x, y)) := by
      simpa using (continuousAt_id.prodMk continuousAt_const).tendsto
    have hev := ht.eventually (hF.eventually (by norm_num))
    filter_upwards [hev] with a ha
    unfold partialX
    simpa [F, ex, smul_eq_mul] using
      deriv_affine_line_at F (0, y) ex a
        (by simpa [ex, smul_eq_mul] using ha.differentiableAt (by decide))
  have hyEvent : ∀ᶠ b : ℝ in nhds y,
      partialY f x b = fderiv ℝ F (x, b) ey := by
    have ht : Filter.Tendsto (fun b : ℝ => (x, b)) (nhds y) (nhds (x, y)) := by
      simpa using (continuousAt_const.prodMk continuousAt_id).tendsto
    have hev := ht.eventually (hF.eventually (by norm_num))
    filter_upwards [hev] with b hb
    unfold partialY
    simpa [F, ey, smul_eq_mul] using
      deriv_affine_line_at F (x, 0) ey b
        (by simpa [ey, smul_eq_mul] using hb.differentiableAt (by decide))
  have hentry (p w q : ℝ × ℝ) (t : ℝ)
      (hpt : p + t • w = (x, y)) :
      deriv (fun s : ℝ => fderiv ℝ F (p + s • w) q) t = H w q := by
    have hc : HasDerivAt (fun s : ℝ => p + s • w) w t := by
      simpa only [id_eq, one_smul] using
        ((hasDerivAt_id t).smul_const w).const_add p
    have hDf' : DifferentiableAt ℝ (fderiv ℝ F) (p + t • w) := by
      simpa [hpt] using hDf
    have hcomp : HasDerivAt
        (fun s : ℝ => fderiv ℝ F (p + s • w))
        (fderiv ℝ (fderiv ℝ F) (p + t • w) w) t := by
      simpa using hDf'.hasFDerivAt.comp_hasDerivAt t hc
    simpa [H, hpt] using (hcomp.clm_apply (hasDerivAt_const (x := t) q)).deriv
  have hxx : partialXX f x y = H ex ex := by
    unfold partialXX
    have hxEq : (fun a => partialX f a y) =ᶠ[nhds x]
        (fun a => fderiv ℝ F (a, y) ex) := hxEvent
    rw [hxEq.deriv_eq]
    simpa [ex, smul_eq_mul] using
      hentry (0, y) ex ex x (by simp [ex, smul_eq_mul])
  have hxy : partialXY f x y = H ey ex := by
    unfold partialXY
    have hev : (fun b => partialX f x b) =ᶠ[nhds y]
        (fun b => fderiv ℝ F (x, b) ex) := by
      have ht : Filter.Tendsto (fun b : ℝ => (x, b)) (nhds y) (nhds (x, y)) := by
        simpa using (continuousAt_const.prodMk continuousAt_id).tendsto
      have hnear := ht.eventually (hF.eventually (by norm_num))
      filter_upwards [hnear] with b hb
      unfold partialX
      simpa [F, ex, smul_eq_mul] using
        deriv_affine_line_at F (0, b) ex x
          (by simpa [ex, smul_eq_mul] using hb.differentiableAt (by decide))
    rw [hev.deriv_eq]
    simpa [ey, ex, smul_eq_mul] using
      hentry (x, 0) ey ex y (by simp [ey, smul_eq_mul])
  have hyy : partialYY f x y = H ey ey := by
    unfold partialYY
    have hyEq : (fun b => partialY f x b) =ᶠ[nhds y]
        (fun b => fderiv ℝ F (x, b) ey) := hyEvent
    rw [hyEq.deriv_eq]
    simpa [ey, smul_eq_mul] using
      hentry (x, 0) ey ey y (by simp [ey, smul_eq_mul])
  have hsymm : H ex ey = H ey ex := by
    simpa [H] using
      hF.isSymmSndFDerivAt (by norm_num [minSmoothness]) ex ey
  have hd : d = dx • ex + dy • ey := by
    ext <;> simp [d, ex, ey]
  change secondDifferential f x y dx dy =
    deriv (deriv (fun t : ℝ => F ((x, y) + t • d))) 0
  rw [hsec, hd]
  simp only [map_add, map_smul, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply]
  rw [hsymm, ← hxx, ← hxy, ← hyy]
  simp [secondDifferential, F, d, ex, ey, smul_eq_mul]
  ring

theorem gap1 (u v : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (huDiff : DifferentiableAt ℝ (Function.uncurry u) (x, y))
    (hvDiff : DifferentiableAt ℝ (Function.uncurry v) (x, y))
    (hu0 : u x y = 0) (hv0 : v x y = 0)
    (hX : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      p.1 = Real.exp (u p.1 p.2 + v p.1 p.2)) :
    dx = Real.exp (u x y + v x y) *
      (differential u x y dx dy + differential v x y dx dy) := by
  have huLine := hasDerivAt_line u x y dx dy huDiff
  have hvLine := hasDerivAt_line v x y dx dy hvDiff
  have hExpLine := (Real.hasDerivAt_exp _).comp 0 (huLine.add hvLine)
  have hLeft : HasDerivAt (fun t : ℝ => x + t * dx) dx 0 :=
    by convert (hasDerivAt_const 0 x).add ((hasDerivAt_id 0).mul_const dx) using 1 <;> simp
  have hEqProd : (fun p : ℝ × ℝ => p.1) =ᶠ[nhds (x, y)]
      (fun p => Real.exp (u p.1 p.2 + v p.1 p.2)) := hX
  have hEqLine : (fun t : ℝ => x + t * dx) =ᶠ[nhds 0]
      (fun t => Real.exp
        (u (x + t * dx) (y + t * dy) +
          v (x + t * dx) (y + t * dy))) := by
    simpa only [Function.comp_apply] using
      hEqProd.comp_tendsto
        (tendsto_line x y dx dy)
  have hSame := hLeft.congr_of_eventuallyEq hEqLine.symm
  simpa using hSame.unique hExpLine

theorem gap2 (u v : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (hu0 : u x y = 0) (hv0 : v x y = 0) :
    Real.exp (u x y + v x y) *
        (differential u x y dx dy + differential v x y dx dy) =
      differential u x y dx dy + differential v x y dx dy := by
  rw [hu0, hv0]
  norm_num

theorem gap3 (u v : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (hX : dx = Real.exp (u x y + v x y) *
      (differential u x y dx dy + differential v x y dx dy))
    (hExp : Real.exp (u x y + v x y) *
        (differential u x y dx dy + differential v x y dx dy) =
      differential u x y dx dy + differential v x y dx dy) :
    dx = differential u x y dx dy + differential v x y dx dy :=
  hX.trans hExp

theorem gap4 (u v : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (huDiff : DifferentiableAt ℝ (Function.uncurry u) (x, y))
    (hvDiff : DifferentiableAt ℝ (Function.uncurry v) (x, y))
    (hu0 : u x y = 0) (hv0 : v x y = 0)
    (hY : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      p.2 = Real.exp (u p.1 p.2 - v p.1 p.2)) :
    dy = Real.exp (u x y - v x y) *
      (differential u x y dx dy - differential v x y dx dy) := by
  have huLine := hasDerivAt_line u x y dx dy huDiff
  have hvLine := hasDerivAt_line v x y dx dy hvDiff
  have hExpLine := (Real.hasDerivAt_exp _).comp 0 (huLine.sub hvLine)
  have hLeft : HasDerivAt (fun t : ℝ => y + t * dy) dy 0 :=
    by convert (hasDerivAt_const 0 y).add ((hasDerivAt_id 0).mul_const dy) using 1 <;> simp
  have hEqProd : (fun p : ℝ × ℝ => p.2) =ᶠ[nhds (x, y)]
      (fun p => Real.exp (u p.1 p.2 - v p.1 p.2)) := hY
  have hEqLine : (fun t : ℝ => y + t * dy) =ᶠ[nhds 0]
      (fun t => Real.exp
        (u (x + t * dx) (y + t * dy) -
          v (x + t * dx) (y + t * dy))) := by
    simpa only [Function.comp_apply] using
      hEqProd.comp_tendsto
        (tendsto_line x y dx dy)
  have hSame := hLeft.congr_of_eventuallyEq hEqLine.symm
  simpa using hSame.unique hExpLine

theorem gap5 (u v : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (hu0 : u x y = 0) (hv0 : v x y = 0) :
    Real.exp (u x y - v x y) *
        (differential u x y dx dy - differential v x y dx dy) =
      differential u x y dx dy - differential v x y dx dy := by
  rw [hu0, hv0]
  norm_num

theorem gap6 (u v : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (hY : dy = Real.exp (u x y - v x y) *
      (differential u x y dx dy - differential v x y dx dy))
    (hExp : Real.exp (u x y - v x y) *
        (differential u x y dx dy - differential v x y dx dy) =
      differential u x y dx dy - differential v x y dx dy) :
    dy = differential u x y dx dy - differential v x y dx dy :=
  hY.trans hExp

theorem gap7 (u v : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (hX : dx = differential u x y dx dy + differential v x y dx dy)
    (hY : dy = differential u x y dx dy - differential v x y dx dy) :
    differential u x y dx dy = (dx + dy) / 2 := by
  linarith

theorem gap8 (u v : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (hX : dx = differential u x y dx dy + differential v x y dx dy)
    (hY : dy = differential u x y dx dy - differential v x y dx dy) :
    differential v x y dx dy = (dx - dy) / 2 := by
  linarith

theorem gap9 (u v z : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (huDiff : DifferentiableAt ℝ (Function.uncurry u) (x, y))
    (hvDiff : DifferentiableAt ℝ (Function.uncurry v) (x, y))
    (hzDiff : DifferentiableAt ℝ (Function.uncurry z) (x, y))
    (hu0 : u x y = 0) (hv0 : v x y = 0)
    (hZ : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      z p.1 p.2 = u p.1 p.2 * v p.1 p.2) :
    differential z x y dx dy =
      u x y * differential v x y dx dy +
        v x y * differential u x y dx dy := by
  have huLine := hasDerivAt_line u x y dx dy huDiff
  have hvLine := hasDerivAt_line v x y dx dy hvDiff
  have hzLine := hasDerivAt_line z x y dx dy hzDiff
  have hProdLine := huLine.mul hvLine
  have hEqProd : (fun p : ℝ × ℝ => z p.1 p.2) =ᶠ[nhds (x, y)]
      (fun p => u p.1 p.2 * v p.1 p.2) := hZ
  have hEqLine : (fun t : ℝ => z (x + t * dx) (y + t * dy)) =ᶠ[nhds 0]
      (fun t => u (x + t * dx) (y + t * dy) *
        v (x + t * dx) (y + t * dy)) := by
    simpa only [Function.comp_apply] using
      hEqProd.comp_tendsto
        (tendsto_line x y dx dy)
  have hzProd := hzLine.congr_of_eventuallyEq hEqLine.symm
  have hder := hzProd.unique hProdLine
  convert hder using 1 <;> ring

theorem gap10 (u v : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (hu0 : u x y = 0) (hv0 : v x y = 0) :
    u x y * differential v x y dx dy +
        v x y * differential u x y dx dy = 0 := by
  simp [hu0, hv0]

theorem gap11 (u v z : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (hZ : differential z x y dx dy =
      u x y * differential v x y dx dy +
        v x y * differential u x y dx dy)
    (hZero : u x y * differential v x y dx dy +
        v x y * differential u x y dx dy = 0) :
    differential z x y dx dy = 0 := by aesop

theorem gap12 (u v z : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (huC2 : ContDiffAt ℝ 2 (Function.uncurry u) (x, y))
    (hvC2 : ContDiffAt ℝ 2 (Function.uncurry v) (x, y))
    (hzC2 : ContDiffAt ℝ 2 (Function.uncurry z) (x, y))
    (hu0 : u x y = 0) (hv0 : v x y = 0)
    (hZ : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      z p.1 p.2 = u p.1 p.2 * v p.1 p.2) :
    secondDifferential z x y dx dy =
      u x y * secondDifferential v x y dx dy +
        2 * differential u x y dx dy * differential v x y dx dy +
        v x y * secondDifferential u x y dx dy := by
  let ul : ℝ → ℝ := fun t => u (x + t * dx) (y + t * dy)
  let vl : ℝ → ℝ := fun t => v (x + t * dx) (y + t * dy)
  let zl : ℝ → ℝ := fun t => z (x + t * dx) (y + t * dy)
  have hpath : ContDiffAt ℝ 2 (fun t : ℝ => (x + t * dx, y + t * dy)) 0 := by
    fun_prop
  have huLineC2 : ContDiffAt ℝ 2 ul 0 := by
    have huC20 : ContDiffAt ℝ 2 (Function.uncurry u)
        (x + 0 * dx, y + 0 * dy) := by simpa using huC2
    exact huC20.comp 0 hpath
  have hvLineC2 : ContDiffAt ℝ 2 vl 0 := by
    have hvC20 : ContDiffAt ℝ 2 (Function.uncurry v)
        (x + 0 * dx, y + 0 * dy) := by simpa using hvC2
    exact hvC20.comp 0 hpath
  have huLine : HasDerivAt ul (differential u x y dx dy) 0 := by
    simpa [ul] using
      hasDerivAt_line u x y dx dy (huC2.differentiableAt (by decide))
  have hvLine : HasDerivAt vl (differential v x y dx dy) 0 := by
    simpa [vl] using
      hasDerivAt_line v x y dx dy (hvC2.differentiableAt (by decide))
  have huSecond : HasDerivAt (deriv ul)
      (secondDifferential u x y dx dy) 0 := by
    have hd := (huLineC2.derivWithin (m := 1) (by norm_num)).differentiableAt (by decide)
    have hs := hd.hasDerivAt
    rw [secondDifferential_eq_secondLine u x y dx dy huC2]
    simpa [ul] using hs
  have hvSecond : HasDerivAt (deriv vl)
      (secondDifferential v x y dx dy) 0 := by
    have hd := (hvLineC2.derivWithin (m := 1) (by norm_num)).differentiableAt (by decide)
    have hs := hd.hasDerivAt
    rw [secondDifferential_eq_secondLine v x y dx dy hvC2]
    simpa [vl] using hs
  have hEqProd : (fun p : ℝ × ℝ => z p.1 p.2) =ᶠ[nhds (x, y)]
      (fun p => u p.1 p.2 * v p.1 p.2) := hZ
  have hEqLine : zl =ᶠ[nhds 0] fun t => ul t * vl t := by
    simpa only [zl, ul, vl, Function.comp_apply] using
      hEqProd.comp_tendsto (tendsto_line x y dx dy)
  have hFirstProduct :
      deriv (fun t => ul t * vl t) =ᶠ[nhds 0]
        (fun t => deriv ul t * vl t + ul t * deriv vl t) := by
    have heu := huLineC2.eventually (by norm_num)
    have hev := hvLineC2.eventually (by norm_num)
    filter_upwards [heu, hev] with t htu htv
    simpa using
      ((htu.differentiableAt (by decide)).hasDerivAt.mul
        (htv.differentiableAt (by decide)).hasDerivAt).deriv
  have hSecondProduct : deriv (deriv (fun t => ul t * vl t)) 0 =
      secondDifferential u x y dx dy * v x y +
        differential u x y dx dy * differential v x y dx dy +
        (differential u x y dx dy * differential v x y dx dy +
          u x y * secondDifferential v x y dx dy) := by
    rw [hFirstProduct.deriv_eq]
    have hs := (huSecond.mul hvLine).add (huLine.mul hvSecond)
    have huD : deriv ul 0 = differential u x y dx dy := huLine.deriv
    have hvD : deriv vl 0 = differential v x y dx dy := hvLine.deriv
    simpa [ul, vl, huD, hvD] using hs.deriv
  rw [secondDifferential_eq_secondLine z x y dx dy hzC2]
  have hzprod : deriv (deriv zl) 0 =
      deriv (deriv (fun t => ul t * vl t)) 0 := by
    exact hEqLine.deriv.deriv_eq
  change deriv (deriv zl) 0 = _
  rw [hzprod, hSecondProduct]
  ring

theorem gap13 (u v : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (hu0 : u x y = 0) (hv0 : v x y = 0) :
    u x y * secondDifferential v x y dx dy +
        2 * differential u x y dx dy * differential v x y dx dy +
        v x y * secondDifferential u x y dx dy =
      2 * differential u x y dx dy * differential v x y dx dy := by
  simp [hu0, hv0]

theorem gap14 (u v z : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (hSecond : secondDifferential z x y dx dy =
      u x y * secondDifferential v x y dx dy +
        2 * differential u x y dx dy * differential v x y dx dy +
        v x y * secondDifferential u x y dx dy)
    (hZero :
      u x y * secondDifferential v x y dx dy +
          2 * differential u x y dx dy * differential v x y dx dy +
          v x y * secondDifferential u x y dx dy =
        2 * differential u x y dx dy * differential v x y dx dy) :
    secondDifferential z x y dx dy =
      2 * differential u x y dx dy * differential v x y dx dy := by aesop

theorem gap15 (u v z : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (hSecond : secondDifferential z x y dx dy =
      2 * differential u x y dx dy * differential v x y dx dy)
    (hU : differential u x y dx dy = (dx + dy) / 2)
    (hV : differential v x y dx dy = (dx - dy) / 2) :
    secondDifferential z x y dx dy =
      2 * ((dx + dy) / 2) * ((dx - dy) / 2) := by aesop

theorem gap16 (dx dy : ℝ) :
    2 * ((dx + dy) / 2) * ((dx - dy) / 2) =
      (1 / 2 : ℝ) * (dx ^ 2 - dy ^ 2) := by
  ring

theorem gap17 (z : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (hSub : secondDifferential z x y dx dy =
      2 * ((dx + dy) / 2) * ((dx - dy) / 2))
    (hAlgebra : 2 * ((dx + dy) / 2) * ((dx - dy) / 2) =
      (1 / 2 : ℝ) * (dx ^ 2 - dy ^ 2)) :
    secondDifferential z x y dx dy =
      (1 / 2 : ℝ) * (dx ^ 2 - dy ^ 2) := by aesop

end

end ProofGap.Exercise3410
