import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod

namespace ProofGap.Exercise3470

noncomputable section

def partialY (f : ℝ → ℝ → ℝ) (y z : ℝ) : ℝ :=
  deriv (fun t => f t z) y

def partialZ (f : ℝ → ℝ → ℝ) (y z : ℝ) : ℝ :=
  deriv (fun t => f y t) z

def differential (f : ℝ → ℝ → ℝ) (y z dy dz : ℝ) : ℝ :=
  partialY f y z * dy + partialZ f y z * dz

theorem gap1 (xMap : ℝ → ℝ → ℝ) (y z dy dz : ℝ) :
    differential xMap y z dy dz =
      partialY xMap y z * dy + partialZ xMap y z * dz := by
  rfl

theorem gap2 (xMap : ℝ → ℝ → ℝ) (y z dy dz : ℝ)
    (hxz : partialZ xMap y z ≠ 0)
    (hDx : differential xMap y z dy dz =
      partialY xMap y z * dy + partialZ xMap y z * dz) :
    dz = (1 / partialZ xMap y z) * differential xMap y z dy dz -
      (partialY xMap y z / partialZ xMap y z) * dy := by
  rw [hDx]
  field_simp [hxz]
  ring

theorem gap3 (xMap zInv : ℝ → ℝ → ℝ) (y z : ℝ)
    (hxz : partialZ xMap y z ≠ 0)
    (hxDiff : DifferentiableAt ℝ (Function.uncurry xMap) (y, z))
    (hzDiff : DifferentiableAt ℝ (Function.uncurry zInv) (y, xMap y z))
    (hInverse : ∀ᶠ p : ℝ × ℝ in nhds (y, z),
      zInv p.1 (xMap p.1 p.2) = p.2) :
    partialZ zInv y (xMap y z) = 1 / partialZ xMap y z := by
  have hxLine : DifferentiableAt ℝ (fun t : ℝ => (y, t)) z := by
    simpa only [id_eq] using
      (differentiableAt_const (𝕜 := ℝ) y).prodMk differentiableAt_id
  have hxSlice : DifferentiableAt ℝ (fun t => xMap y t) z := by
    simpa only [Function.comp_apply] using hxDiff.comp z hxLine
  have hzLine :
      DifferentiableAt ℝ (fun t : ℝ => (y, t)) (xMap y z) := by
    simpa only [id_eq] using
      (differentiableAt_const (𝕜 := ℝ) y).prodMk differentiableAt_id
  have hzSlice :
      DifferentiableAt ℝ (fun t => zInv y t) (xMap y z) := by
    simpa only [Function.comp_apply] using
      hzDiff.comp (xMap y z) hzLine
  have hxDer :
      HasDerivAt (fun t => xMap y t) (partialZ xMap y z) z := by
    simpa only [partialZ] using hxSlice.hasDerivAt
  have hzDer : HasDerivAt (fun t => zInv y t)
      (partialZ zInv y (xMap y z)) (xMap y z) := by
    simpa only [partialZ] using hzSlice.hasDerivAt
  have hcomp : HasDerivAt (fun t => zInv y (xMap y t))
      (partialZ zInv y (xMap y z) * partialZ xMap y z) z := by
    simpa only [Function.comp_apply] using hzDer.comp z hxDer
  have hinvEq :
      (fun p : ℝ × ℝ => zInv p.1 (xMap p.1 p.2)) =ᶠ[nhds (y, z)]
        (fun p => p.2) := hInverse
  have hline :
      Filter.Tendsto (fun t : ℝ => (y, t))
        (nhds z) (nhds (y, z)) := by
    simpa only [id_eq] using
      (continuousAt_const.prodMk continuousAt_id).tendsto
  have heq := hinvEq.comp_tendsto hline
  have hid : HasDerivAt (fun t => zInv y (xMap y t)) 1 z := by
    apply (hasDerivAt_id z).congr_of_eventuallyEq
    simpa only [Function.comp_apply, id_eq] using heq
  have hprod := hcomp.unique hid
  apply (eq_div_iff hxz).2
  exact hprod

theorem gap4 (xMap zInv : ℝ → ℝ → ℝ) (y z : ℝ)
    (hxz : partialZ xMap y z ≠ 0)
    (hxDiff : DifferentiableAt ℝ (Function.uncurry xMap) (y, z))
    (hzDiff : DifferentiableAt ℝ (Function.uncurry zInv) (y, xMap y z))
    (hInverse : ∀ᶠ p : ℝ × ℝ in nhds (y, z),
      zInv p.1 (xMap p.1 p.2) = p.2) :
    partialY zInv y (xMap y z) =
      -partialY xMap y z / partialZ xMap y z := by
  let X := xMap y z
  let L := fderiv ℝ (Function.uncurry zInv) (y, X)
  have hxLine : DifferentiableAt ℝ (fun t : ℝ => (t, z)) y := by
    simpa only [id_eq] using
      differentiableAt_id.prodMk (differentiableAt_const (𝕜 := ℝ) z)
  have hxSlice : DifferentiableAt ℝ (fun t => xMap t z) y := by
    simpa only [Function.comp_apply] using hxDiff.comp y hxLine
  have hxDer :
      HasDerivAt (fun t => xMap t z) (partialY xMap y z) y := by
    simpa only [partialY] using hxSlice.hasDerivAt
  have hpath : HasDerivAt (fun t : ℝ => (t, xMap t z))
      (1, partialY xMap y z) y := by
    simpa only [id_eq] using (hasDerivAt_id y).prodMk hxDer
  have hzF : HasFDerivAt (Function.uncurry zInv) L (y, X) :=
    hzDiff.hasFDerivAt
  have hcomp : HasDerivAt (fun t => zInv t (xMap t z))
      (L (1, partialY xMap y z)) y := by
    simpa only [Function.comp_apply, X] using
      hzF.comp_hasDerivAt y hpath
  have hinvEq :
      (fun p : ℝ × ℝ => zInv p.1 (xMap p.1 p.2)) =ᶠ[nhds (y, z)]
        (fun p => p.2) := hInverse
  have hline :
      Filter.Tendsto (fun t : ℝ => (t, z))
        (nhds y) (nhds (y, z)) := by
    simpa only [id_eq] using
      (continuousAt_id.prodMk continuousAt_const).tendsto
  have heq := hinvEq.comp_tendsto hline
  have hzero : HasDerivAt (fun t => zInv t (xMap t z)) 0 y := by
    apply (hasDerivAt_const y z).congr_of_eventuallyEq
    simpa only [Function.comp_apply] using heq
  have hdirzero : L (1, partialY xMap y z) = 0 :=
    hcomp.unique hzero
  have hlineY : HasDerivAt (fun t : ℝ => (t, X)) (1, 0) y := by
    simpa only [id_eq] using
      (hasDerivAt_id y).prodMk (hasDerivAt_const y X)
  have hsliceY : HasDerivAt (fun t => zInv t X) (L (1, 0)) y := by
    simpa only [Function.comp_apply] using
      hzF.comp_hasDerivAt y hlineY
  have hPY : partialY zInv y X = L (1, 0) := by
    simpa only [partialY] using hsliceY.deriv
  have hlineZ : HasDerivAt (fun t : ℝ => (y, t)) (0, 1) X := by
    simpa only [id_eq] using
      (hasDerivAt_const X y).prodMk (hasDerivAt_id X)
  have hsliceZ : HasDerivAt (fun t => zInv y t) (L (0, 1)) X := by
    simpa only [Function.comp_apply] using
      hzF.comp_hasDerivAt X hlineZ
  have hPZ : partialZ zInv y X = L (0, 1) := by
    simpa only [partialZ] using hsliceZ.deriv
  have hlinear :
      L (1, partialY xMap y z) =
        L (1, 0) + partialY xMap y z * L (0, 1) := by
    rw [show (1, partialY xMap y z) =
      ((1, 0) : ℝ × ℝ) +
        partialY xMap y z • ((0, 1) : ℝ × ℝ) by ext <;> simp]
    rw [map_add, map_smul]
    simp only [smul_eq_mul]
  have hrel :
      partialY zInv y X +
        partialY xMap y z * partialZ zInv y X = 0 := by
    rw [hPY, hPZ, ← hlinear]
    exact hdirzero
  have hInvZ := gap3 xMap zInv y z hxz hxDiff hzDiff hInverse
  dsimp only [X] at hrel ⊢
  rw [hInvZ] at hrel
  field_simp [hxz] at hrel ⊢
  linarith

theorem gap5 (xMap zInv : ℝ → ℝ → ℝ) (y z : ℝ)
    (hPDE :
      (xMap y z - z) * partialZ zInv y (xMap y z) +
        y * partialY zInv y (xMap y z) = 0)
    (hInvX : partialZ zInv y (xMap y z) = 1 / partialZ xMap y z)
    (hInvY : partialY zInv y (xMap y z) =
      -partialY xMap y z / partialZ xMap y z) :
    (xMap y z - z) * (1 / partialZ xMap y z) -
      y * (partialY xMap y z / partialZ xMap y z) = 0 := by
  rw [hInvX, hInvY] at hPDE
  convert hPDE using 1 <;> ring

theorem gap6 (xMap : ℝ → ℝ → ℝ) (y z : ℝ)
    (hy : y ≠ 0)
    (hxz : partialZ xMap y z ≠ 0)
    (hEquation :
      (xMap y z - z) * (1 / partialZ xMap y z) -
        y * (partialY xMap y z / partialZ xMap y z) = 0) :
    partialY xMap y z = (xMap y z - z) / y := by
  field_simp [hxz] at hEquation
  apply (eq_div_iff hy).2
  linarith

end

end ProofGap.Exercise3470
