import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3400

noncomputable section

def uncurry3 (F : ℝ → ℝ → ℝ → ℝ) (p : ℝ × ℝ × ℝ) : ℝ :=
  F p.1 p.2.1 p.2.2

def partial1 (F : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => F t y z) x

def partial2 (F : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => F x t z) y

def partial3 (F : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => F x y t) z

def partialFirst (g : ℝ → ℝ → ℝ) (a b : ℝ) : ℝ :=
  deriv (fun t => g t b) a

private theorem implicitDerivativeRatio
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : ℝ → ℝ) (t : ℝ) (L : E →L[ℝ] ℝ)
    (d eMain eOther : E) (v a b : ℝ)
    (hg : HasDerivAt g (L d) t)
    (hzero : ∀ᶠ s : ℝ in nhds t, g s = 0)
    (hd : d = v • eMain + eOther)
    (hMain : L eMain = a)
    (hOther : L eOther = b)
    (ha : a ≠ 0) :
    v = -b / a := by
  have hzero' : (fun _ : ℝ => (0 : ℝ)) =ᶠ[nhds t] g :=
    Filter.EventuallyEq.symm hzero
  have hg0 : HasDerivAt (fun _ : ℝ => (0 : ℝ)) (L d) t := by
    exact hg.congr_of_eventuallyEq hzero'
  have hLd : L d = 0 :=
    hg0.unique (hasDerivAt_const t (0 : ℝ))
  have hvab : v * a + b = 0 := by
    simpa [hd, hMain, hOther, smul_eq_mul] using hLd
  apply (eq_div_iff ha).2
  linarith

theorem gap1 (F : ℝ → ℝ → ℝ → ℝ)
    (xOfYZ : ℝ → ℝ → ℝ) (x y z : ℝ)
    (hValue : xOfYZ y z = x)
    (hFDiff : DifferentiableAt ℝ (uncurry3 F) (x, y, z))
    (hxDiff : DifferentiableAt ℝ (Function.uncurry xOfYZ) (y, z))
    (hImplicit :
      ∀ᶠ p : ℝ × ℝ in nhds (y, z),
        F (xOfYZ p.1 p.2) p.1 p.2 = 0)
    (hF1 : partial1 F x y z ≠ 0) :
    partialFirst xOfYZ y z =
      -partial2 F x y z / partial1 F x y z := by
  let L : (ℝ × ℝ × ℝ) →L[ℝ] ℝ :=
    fderiv ℝ (uncurry3 F) (x, y, z)
  have hyz :
      HasDerivAt (fun t : ℝ => (t, z)) (1, 0) y :=
    (hasDerivAt_id y).prodMk (hasDerivAt_const y z)
  have hxSliceDiff :
      DifferentiableAt ℝ (fun t : ℝ => xOfYZ t z) y := by
    simpa [Function.uncurry] using
      hxDiff.comp y hyz.differentiableAt
  have hxSlice :
      HasDerivAt (fun t : ℝ => xOfYZ t z)
        (partialFirst xOfYZ y z) y := by
    simpa [partialFirst] using hxSliceDiff.hasDerivAt
  have hpath :
      HasDerivAt
        (fun t : ℝ => (xOfYZ t z, t, z))
        (partialFirst xOfYZ y z, (1, 0)) y := by
    exact hxSlice.prodMk hyz
  have hFat :
      HasFDerivAt (uncurry3 F) L (xOfYZ y z, y, z) := by
    simpa [L, hValue] using hFDiff.hasFDerivAt
  have hcomp :
      HasDerivAt (fun t : ℝ => F (xOfYZ t z) t z)
        (L (partialFirst xOfYZ y z, (1, 0))) y := by
    simpa [uncurry3] using hFat.comp_hasDerivAt y hpath
  have hzero :
      ∀ᶠ t : ℝ in nhds y, F (xOfYZ t z) t z = 0 := by
    simpa using hyz.continuousAt.eventually hImplicit
  have he1 :
      HasDerivAt (fun t : ℝ => (t, y, z)) (1, (0, 0)) x :=
    (hasDerivAt_id x).prodMk
      ((hasDerivAt_const x y).prodMk (hasDerivAt_const x z))
  have he2 :
      HasDerivAt (fun t : ℝ => (x, t, z)) (0, (1, 0)) y :=
    (hasDerivAt_const y x).prodMk
      ((hasDerivAt_id y).prodMk (hasDerivAt_const y z))
  have hderiv1 :
      HasDerivAt (fun t : ℝ => F t y z) (L (1, (0, 0))) x := by
    simpa [L, uncurry3] using
      hFDiff.hasFDerivAt.comp_hasDerivAt x he1
  have hderiv2 :
      HasDerivAt (fun t : ℝ => F x t z) (L (0, (1, 0))) y := by
    simpa [L, uncurry3] using
      hFDiff.hasFDerivAt.comp_hasDerivAt y he2
  have hL1 : L (1, (0, 0)) = partial1 F x y z := by
    simpa [partial1] using hderiv1.deriv.symm
  have hL2 : L (0, (1, 0)) = partial2 F x y z := by
    simpa [partial2] using hderiv2.deriv.symm
  exact implicitDerivativeRatio
    (g := fun t : ℝ => F (xOfYZ t z) t z)
    (t := y) (L := L)
    (d := (partialFirst xOfYZ y z, (1, 0)))
    (eMain := (1, (0, 0))) (eOther := (0, (1, 0)))
    (v := partialFirst xOfYZ y z)
    (a := partial1 F x y z) (b := partial2 F x y z)
    hcomp hzero (by simp [smul_eq_mul]) hL1 hL2 hF1

theorem gap2 (F : ℝ → ℝ → ℝ → ℝ)
    (yOfZX : ℝ → ℝ → ℝ) (x y z : ℝ)
    (hValue : yOfZX z x = y)
    (hFDiff : DifferentiableAt ℝ (uncurry3 F) (x, y, z))
    (hyDiff : DifferentiableAt ℝ (Function.uncurry yOfZX) (z, x))
    (hImplicit :
      ∀ᶠ p : ℝ × ℝ in nhds (z, x),
        F p.2 (yOfZX p.1 p.2) p.1 = 0)
    (hF2 : partial2 F x y z ≠ 0) :
    partialFirst yOfZX z x =
      -partial3 F x y z / partial2 F x y z := by
  let L : (ℝ × ℝ × ℝ) →L[ℝ] ℝ :=
    fderiv ℝ (uncurry3 F) (x, y, z)
  have hzx :
      HasDerivAt (fun t : ℝ => (t, x)) (1, 0) z :=
    (hasDerivAt_id z).prodMk (hasDerivAt_const z x)
  have hySliceDiff :
      DifferentiableAt ℝ (fun t : ℝ => yOfZX t x) z := by
    simpa [Function.uncurry] using
      hyDiff.comp z hzx.differentiableAt
  have hySlice :
      HasDerivAt (fun t : ℝ => yOfZX t x)
        (partialFirst yOfZX z x) z := by
    simpa [partialFirst] using hySliceDiff.hasDerivAt
  have hpath :
      HasDerivAt
        (fun t : ℝ => (x, yOfZX t x, t))
        (0, (partialFirst yOfZX z x, 1)) z := by
    exact (hasDerivAt_const z x).prodMk
      (hySlice.prodMk (hasDerivAt_id z))
  have hFat :
      HasFDerivAt (uncurry3 F) L (x, yOfZX z x, z) := by
    simpa [L, hValue] using hFDiff.hasFDerivAt
  have hcomp :
      HasDerivAt (fun t : ℝ => F x (yOfZX t x) t)
        (L (0, (partialFirst yOfZX z x, 1))) z := by
    simpa [uncurry3] using hFat.comp_hasDerivAt z hpath
  have hzero :
      ∀ᶠ t : ℝ in nhds z, F x (yOfZX t x) t = 0 := by
    simpa using hzx.continuousAt.eventually hImplicit
  have he2 :
      HasDerivAt (fun t : ℝ => (x, t, z)) (0, (1, 0)) y :=
    (hasDerivAt_const y x).prodMk
      ((hasDerivAt_id y).prodMk (hasDerivAt_const y z))
  have he3 :
      HasDerivAt (fun t : ℝ => (x, y, t)) (0, (0, 1)) z :=
    (hasDerivAt_const z x).prodMk
      ((hasDerivAt_const z y).prodMk (hasDerivAt_id z))
  have hderiv2 :
      HasDerivAt (fun t : ℝ => F x t z) (L (0, (1, 0))) y := by
    simpa [L, uncurry3] using
      hFDiff.hasFDerivAt.comp_hasDerivAt y he2
  have hderiv3 :
      HasDerivAt (fun t : ℝ => F x y t) (L (0, (0, 1))) z := by
    simpa [L, uncurry3] using
      hFDiff.hasFDerivAt.comp_hasDerivAt z he3
  have hL2 : L (0, (1, 0)) = partial2 F x y z := by
    simpa [partial2] using hderiv2.deriv.symm
  have hL3 : L (0, (0, 1)) = partial3 F x y z := by
    simpa [partial3] using hderiv3.deriv.symm
  exact implicitDerivativeRatio
    (g := fun t : ℝ => F x (yOfZX t x) t)
    (t := z) (L := L)
    (d := (0, (partialFirst yOfZX z x, 1)))
    (eMain := (0, (1, 0))) (eOther := (0, (0, 1)))
    (v := partialFirst yOfZX z x)
    (a := partial2 F x y z) (b := partial3 F x y z)
    hcomp hzero (by simp [smul_eq_mul]) hL2 hL3 hF2

theorem gap3 (F : ℝ → ℝ → ℝ → ℝ)
    (zOfXY : ℝ → ℝ → ℝ) (x y z : ℝ)
    (hValue : zOfXY x y = z)
    (hFDiff : DifferentiableAt ℝ (uncurry3 F) (x, y, z))
    (hzDiff : DifferentiableAt ℝ (Function.uncurry zOfXY) (x, y))
    (hImplicit :
      ∀ᶠ p : ℝ × ℝ in nhds (x, y),
        F p.1 p.2 (zOfXY p.1 p.2) = 0)
    (hF3 : partial3 F x y z ≠ 0) :
    partialFirst zOfXY x y =
      -partial1 F x y z / partial3 F x y z := by
  let L : (ℝ × ℝ × ℝ) →L[ℝ] ℝ :=
    fderiv ℝ (uncurry3 F) (x, y, z)
  have hxy :
      HasDerivAt (fun t : ℝ => (t, y)) (1, 0) x :=
    (hasDerivAt_id x).prodMk (hasDerivAt_const x y)
  have hzSliceDiff :
      DifferentiableAt ℝ (fun t : ℝ => zOfXY t y) x := by
    simpa [Function.uncurry] using
      hzDiff.comp x hxy.differentiableAt
  have hzSlice :
      HasDerivAt (fun t : ℝ => zOfXY t y)
        (partialFirst zOfXY x y) x := by
    simpa [partialFirst] using hzSliceDiff.hasDerivAt
  have hpath :
      HasDerivAt
        (fun t : ℝ => (t, y, zOfXY t y))
        (1, (0, partialFirst zOfXY x y)) x := by
    exact (hasDerivAt_id x).prodMk
      ((hasDerivAt_const x y).prodMk hzSlice)
  have hFat :
      HasFDerivAt (uncurry3 F) L (x, y, zOfXY x y) := by
    simpa [L, hValue] using hFDiff.hasFDerivAt
  have hcomp :
      HasDerivAt (fun t : ℝ => F t y (zOfXY t y))
        (L (1, (0, partialFirst zOfXY x y))) x := by
    simpa [uncurry3] using hFat.comp_hasDerivAt x hpath
  have hzero :
      ∀ᶠ t : ℝ in nhds x, F t y (zOfXY t y) = 0 := by
    simpa using hxy.continuousAt.eventually hImplicit
  have he1 :
      HasDerivAt (fun t : ℝ => (t, y, z)) (1, (0, 0)) x :=
    (hasDerivAt_id x).prodMk
      ((hasDerivAt_const x y).prodMk (hasDerivAt_const x z))
  have he3 :
      HasDerivAt (fun t : ℝ => (x, y, t)) (0, (0, 1)) z :=
    (hasDerivAt_const z x).prodMk
      ((hasDerivAt_const z y).prodMk (hasDerivAt_id z))
  have hderiv1 :
      HasDerivAt (fun t : ℝ => F t y z) (L (1, (0, 0))) x := by
    simpa [L, uncurry3] using
      hFDiff.hasFDerivAt.comp_hasDerivAt x he1
  have hderiv3 :
      HasDerivAt (fun t : ℝ => F x y t) (L (0, (0, 1))) z := by
    simpa [L, uncurry3] using
      hFDiff.hasFDerivAt.comp_hasDerivAt z he3
  have hL1 : L (1, (0, 0)) = partial1 F x y z := by
    simpa [partial1] using hderiv1.deriv.symm
  have hL3 : L (0, (0, 1)) = partial3 F x y z := by
    simpa [partial3] using hderiv3.deriv.symm
  exact implicitDerivativeRatio
    (g := fun t : ℝ => F t y (zOfXY t y))
    (t := x) (L := L)
    (d := (1, (0, partialFirst zOfXY x y)))
    (eMain := (0, (0, 1))) (eOther := (1, (0, 0)))
    (v := partialFirst zOfXY x y)
    (a := partial3 F x y z) (b := partial1 F x y z)
    hcomp hzero (by simp [smul_eq_mul]) hL3 hL1 hF3

theorem gap4 (F : ℝ → ℝ → ℝ → ℝ)
    (xOfYZ yOfZX zOfXY : ℝ → ℝ → ℝ) (x y z : ℝ)
    (hF1 : partial1 F x y z ≠ 0)
    (hF2 : partial2 F x y z ≠ 0)
    (hF3 : partial3 F x y z ≠ 0)
    (hx :
      partialFirst xOfYZ y z =
        -partial2 F x y z / partial1 F x y z)
    (hy :
      partialFirst yOfZX z x =
        -partial3 F x y z / partial2 F x y z)
    (hz :
      partialFirst zOfXY x y =
        -partial1 F x y z / partial3 F x y z) :
    partialFirst xOfYZ y z *
        partialFirst yOfZX z x *
        partialFirst zOfXY x y = -1 := by
  rw [hx, hy, hz]
  field_simp [hF1, hF2, hF3]

theorem gap5 (xOfYZ yOfZX zOfXY : ℝ → ℝ → ℝ)
    (x y z : ℝ)
    (hProduct :
      partialFirst xOfYZ y z *
          partialFirst yOfZX z x *
          partialFirst zOfXY x y = -1) :
    partialFirst xOfYZ y z *
        partialFirst yOfZX z x *
        partialFirst zOfXY x y = -1 := by
  exact hProduct

end

end ProofGap.Exercise3400
