import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3523

noncomputable section

def partialX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f t y) x

def partialY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f x t) y

def partialXX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialX f t y) x

def partialXY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialX f x t) y

def partialYX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialY f t y) x

def partialYY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialY f x t) y

def C2 (f : ℝ → ℝ → ℝ) : Prop :=
  Differentiable ℝ (Function.uncurry f) ∧
    Differentiable ℝ (Function.uncurry (partialX f)) ∧
    Differentiable ℝ (Function.uncurry (partialY f))

def differential (f : ℝ → ℝ → ℝ) (x y dx dy : ℝ) : ℝ :=
  partialX f x y * dx + partialY f x y * dy

def secondDifferential (f : ℝ → ℝ → ℝ) (x y dx dy : ℝ) : ℝ :=
  partialXX f x y * dx ^ 2 + 2 * partialXY f x y * dx * dy +
    partialYY f x y * dy ^ 2

def coordU (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ := x + z x y

def coordV (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ := y + z x y

def physicalW (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ := x + y + z x y

def jacobianFactor (z W : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  1 - partialX W (coordU z x y) (coordV z x y) -
    partialY W (coordU z x y) (coordV z x y)

def physicalOperator (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  partialY z x y * (1 + partialY z x y) * partialXX z x y -
    (1 + partialX z x y + partialY z x y +
      2 * partialX z x y * partialY z x y) * partialXY z x y +
    partialX z x y * (1 + partialX z x y) * partialYY z x y

private theorem differentiableAt_xSlice
    {f : ℝ → ℝ → ℝ} (hf : Differentiable ℝ (Function.uncurry f))
    (x y : ℝ) :
    DifferentiableAt ℝ (fun t => f t y) x := by
  have hp : DifferentiableAt ℝ (fun t : ℝ => (t, y)) x :=
    differentiableAt_id.prodMk (hasDerivAt_const x y).differentiableAt
  simpa only [Function.comp_apply, Function.uncurry_apply_pair] using
    (hf (x, y)).comp x hp

private theorem differentiableAt_ySlice
    {f : ℝ → ℝ → ℝ} (hf : Differentiable ℝ (Function.uncurry f))
    (x y : ℝ) :
    DifferentiableAt ℝ (fun t => f x t) y := by
  have hp : DifferentiableAt ℝ (fun t : ℝ => (x, t)) y :=
    (hasDerivAt_const y x).differentiableAt.prodMk differentiableAt_id
  simpa only [Function.comp_apply, Function.uncurry_apply_pair] using
    (hf (x, y)).comp y hp

private theorem partialX_coordU
    {z : ℝ → ℝ → ℝ} (hz : Differentiable ℝ (Function.uncurry z))
    (x y : ℝ) :
    partialX (coordU z) x y = 1 + partialX z x y := by
  unfold partialX coordU
  have h := (hasDerivAt_id x).add
    (differentiableAt_xSlice hz x y).hasDerivAt
  simpa only [Pi.add_apply, id_eq] using h.deriv

private theorem partialY_coordU (z : ℝ → ℝ → ℝ) (x y : ℝ) :
    partialY (coordU z) x y = partialY z x y := by
  unfold partialY coordU
  exact deriv_const_add x

private theorem partialX_coordV (z : ℝ → ℝ → ℝ) (x y : ℝ) :
    partialX (coordV z) x y = partialX z x y := by
  unfold partialX coordV
  exact deriv_const_add y

private theorem partialY_coordV
    {z : ℝ → ℝ → ℝ} (hz : Differentiable ℝ (Function.uncurry z))
    (x y : ℝ) :
    partialY (coordV z) x y = 1 + partialY z x y := by
  unfold partialY coordV
  have h := (hasDerivAt_id y).add
    (differentiableAt_ySlice hz x y).hasDerivAt
  simpa only [Pi.add_apply, id_eq] using h.deriv

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

private theorem hasDerivAt_lineX (x dx t : ℝ) :
    HasDerivAt (fun s : ℝ => x + s * dx) dx t := by
  convert (hasDerivAt_const t x).add ((hasDerivAt_id t).mul_const dx) using 1 <;>
    ring

private theorem hasDerivAt_differential_along
    (f : ℝ → ℝ → ℝ) (hf : C2 f) (x y dx dy : ℝ)
    (hMixed : partialYX f x y = partialXY f x y) :
    HasDerivAt
      (fun t : ℝ =>
        differential f (x + t * dx) (y + t * dy) dx dy)
      (secondDifferential f x y dx dy) 0 := by
  have hX := hasDerivAt_lineX x dx 0
  have hY := hasDerivAt_lineX y dy 0
  have hpx := hasDerivAt_comp₂ (partialX f)
    (fun t : ℝ => x + t * dx) (fun t : ℝ => y + t * dy)
    (t := 0) (by simpa using hf.2.1 (x, y)) hX hY
  have hpy := hasDerivAt_comp₂ (partialY f)
    (fun t : ℝ => x + t * dx) (fun t : ℝ => y + t * dy)
    (t := 0) (by simpa using hf.2.2 (x, y)) hX hY
  have h := hpx.mul_const dx |>.add (hpy.mul_const dy)
  convert h using 1
  simp only [zero_mul, add_zero]
  change secondDifferential f x y dx dy =
    (partialXX f x y * dx + partialXY f x y * dy) * dx +
      (partialYX f x y * dx + partialYY f x y * dy) * dy
  rw [hMixed]
  unfold secondDifferential
  ring

theorem gap1 (z : ℝ → ℝ → ℝ) :
    ∀ x y dx dy,
      differential z x y dx dy =
        partialX z x y * dx + partialY z x y * dy := by
  intro x y dx dy
  rfl

-- Statement correction: differentiability is needed for the differential identity.
theorem gap2 (z : ℝ → ℝ → ℝ)
    (hz : Differentiable ℝ (Function.uncurry z)) :
    ∀ x y dx dy,
      differential (coordU z) x y dx dy = dx + differential z x y dx dy := by
  intro x y dx dy
  rw [differential, differential, partialX_coordU hz, partialY_coordU]
  ring

theorem gap3 (z : ℝ → ℝ → ℝ) :
    ∀ x y dx dy,
      dx + differential z x y dx dy =
        (1 + partialX z x y) * dx + partialY z x y * dy := by
  intro x y dx dy
  rw [differential]
  ring

-- Statement correction: differentiability is needed for the differential formula.
theorem gap4 (z : ℝ → ℝ → ℝ)
    (hz : Differentiable ℝ (Function.uncurry z)) :
    ∀ x y dx dy,
      differential (coordU z) x y dx dy =
        (1 + partialX z x y) * dx + partialY z x y * dy := by
  intro x y dx dy
  exact (gap2 z hz x y dx dy).trans (gap3 z x y dx dy)

-- Statement correction: differentiability is needed for the differential identity.
theorem gap5 (z : ℝ → ℝ → ℝ)
    (hz : Differentiable ℝ (Function.uncurry z)) :
    ∀ x y dx dy,
      differential (coordV z) x y dx dy = dy + differential z x y dx dy := by
  intro x y dx dy
  rw [differential, differential, partialX_coordV, partialY_coordV hz]
  ring

theorem gap6 (z : ℝ → ℝ → ℝ) :
    ∀ x y dx dy,
      dy + differential z x y dx dy =
        partialX z x y * dx + (1 + partialY z x y) * dy := by
  intro x y dx dy
  rw [differential]
  ring

-- Statement correction: differentiability is needed for the differential formula.
theorem gap7 (z : ℝ → ℝ → ℝ)
    (hz : Differentiable ℝ (Function.uncurry z)) :
    ∀ x y dx dy,
      differential (coordV z) x y dx dy =
        partialX z x y * dx + (1 + partialY z x y) * dy := by
  intro x y dx dy
  exact (gap5 z hz x y dx dy).trans (gap6 z x y dx dy)

-- Statement correction: C² regularity is needed for equality of mixed partials.
theorem gap8 (z : ℝ → ℝ → ℝ) (hz : C2 z) :
    ∀ x y dx dy,
      secondDifferential (coordU z) x y dx dy =
        secondDifferential (coordV z) x y dx dy := by
  intro x y dx dy
  have hxxU : partialXX (coordU z) x y = partialXX z x y := by
    unfold partialXX
    rw [show (fun t => partialX (coordU z) t y) =
        fun t => 1 + partialX z t y by
      funext t
      exact partialX_coordU hz.1 t y]
    exact deriv_const_add 1
  have hxyU : partialXY (coordU z) x y = partialXY z x y := by
    unfold partialXY
    rw [show (fun t => partialX (coordU z) x t) =
        fun t => 1 + partialX z x t by
      funext t
      exact partialX_coordU hz.1 x t]
    exact deriv_const_add 1
  have hyyU : partialYY (coordU z) x y = partialYY z x y := by
    unfold partialYY
    rw [show (fun t => partialY (coordU z) x t) =
        fun t => partialY z x t by
      funext t
      exact partialY_coordU z x t]
  have hxxV : partialXX (coordV z) x y = partialXX z x y := by
    unfold partialXX
    rw [show (fun t => partialX (coordV z) t y) =
        fun t => partialX z t y by
      funext t
      exact partialX_coordV z t y]
  have hxyV : partialXY (coordV z) x y = partialXY z x y := by
    unfold partialXY
    rw [show (fun t => partialX (coordV z) x t) =
        fun t => partialX z x t by
      funext t
      exact partialX_coordV z x t]
  have hyyV : partialYY (coordV z) x y = partialYY z x y := by
    unfold partialYY
    rw [show (fun t => partialY (coordV z) x t) =
        fun t => 1 + partialY z x t by
      funext t
      exact partialY_coordV hz.1 x t]
    exact deriv_const_add 1
  simp only [secondDifferential, hxxU, hxyU, hyyU, hxxV, hxyV, hyyV]

private theorem secondDifferential_coordV_eq
    {z : ℝ → ℝ → ℝ} (hz : C2 z) (x y dx dy : ℝ) :
    secondDifferential (coordV z) x y dx dy =
      secondDifferential z x y dx dy := by
  have hxx : partialXX (coordV z) x y = partialXX z x y := by
    unfold partialXX
    rw [show (fun t => partialX (coordV z) t y) =
        fun t => partialX z t y by
      funext t
      exact partialX_coordV z t y]
  have hxy : partialXY (coordV z) x y = partialXY z x y := by
    unfold partialXY
    rw [show (fun t => partialX (coordV z) x t) =
        fun t => partialX z x t by
      funext t
      exact partialX_coordV z x t]
  have hyy : partialYY (coordV z) x y = partialYY z x y := by
    unfold partialYY
    rw [show (fun t => partialY (coordV z) x t) =
        fun t => 1 + partialY z x t by
      funext t
      exact partialY_coordV hz.1 x t]
    exact deriv_const_add 1
  simp only [secondDifferential, hxx, hxy, hyy]

private theorem partialX_physicalW
    {z : ℝ → ℝ → ℝ} (hz : Differentiable ℝ (Function.uncurry z))
    (x y : ℝ) :
    partialX (physicalW z) x y = 1 + partialX z x y := by
  unfold partialX physicalW
  rw [show (fun t : ℝ => t + y + z t y) =
      fun t => (t + z t y) + y by
    funext t
    ring]
  rw [deriv_add_const]
  exact partialX_coordU hz x y

private theorem partialY_physicalW
    {z : ℝ → ℝ → ℝ} (hz : Differentiable ℝ (Function.uncurry z))
    (x y : ℝ) :
    partialY (physicalW z) x y = 1 + partialY z x y := by
  unfold partialY physicalW
  rw [show (fun t : ℝ => x + t + z x t) =
      fun t => x + (t + z x t) by
    funext t
    ring]
  rw [deriv_const_add]
  exact partialY_coordV hz x y

private theorem secondDifferential_physicalW_eq
    {z : ℝ → ℝ → ℝ} (hz : C2 z) (x y dx dy : ℝ) :
    secondDifferential (physicalW z) x y dx dy =
      secondDifferential z x y dx dy := by
  have hxx : partialXX (physicalW z) x y = partialXX z x y := by
    unfold partialXX
    rw [show (fun t => partialX (physicalW z) t y) =
        fun t => 1 + partialX z t y by
      funext t
      exact partialX_physicalW hz.1 t y]
    exact deriv_const_add 1
  have hxy : partialXY (physicalW z) x y = partialXY z x y := by
    unfold partialXY
    rw [show (fun t => partialX (physicalW z) x t) =
        fun t => 1 + partialX z x t by
      funext t
      exact partialX_physicalW hz.1 x t]
    exact deriv_const_add 1
  have hyy : partialYY (physicalW z) x y = partialYY z x y := by
    unfold partialYY
    rw [show (fun t => partialY (physicalW z) x t) =
        fun t => 1 + partialY z x t by
      funext t
      exact partialY_physicalW hz.1 x t]
    exact deriv_const_add 1
  simp only [secondDifferential, hxx, hxy, hyy]

theorem gap9 (z W : ℝ → ℝ → ℝ)
    (hz : C2 z) (hW : C2 W)
    (hRelation : ∀ x y,
      W (coordU z x y) (coordV z x y) = physicalW z x y) :
    ∀ x y dx dy,
      secondDifferential (coordV z) x y dx dy =
        secondDifferential (fun a b => W (coordU z a b) (coordV z a b))
          x y dx dy := by
  intro x y dx dy
  rw [secondDifferential_coordV_eq hz]
  rw [show (fun a b => W (coordU z a b) (coordV z a b)) =
      physicalW z by
    funext a b
    exact hRelation a b]
  exact (secondDifferential_physicalW_eq hz x y dx dy).symm

theorem gap10 (z W : ℝ → ℝ → ℝ)
    (hz : C2 z) (hW : C2 W)
    (hRelation : ∀ x y,
      W (coordU z x y) (coordV z x y) = physicalW z x y) :
    ∀ x y dx dy,
      secondDifferential (fun a b => W (coordU z a b) (coordV z a b))
          x y dx dy =
        secondDifferential z x y dx dy := by
  intro x y dx dy
  rw [show (fun a b => W (coordU z a b) (coordV z a b)) =
      physicalW z by
    funext a b
    exact hRelation a b]
  exact secondDifferential_physicalW_eq hz x y dx dy

theorem gap11 (z W : ℝ → ℝ → ℝ)
    (hz : C2 z) (hW : C2 W)
    (hRelation : ∀ x y,
      W (coordU z x y) (coordV z x y) = physicalW z x y) :
    ∀ x y dx dy,
      secondDifferential (coordU z) x y dx dy =
        secondDifferential z x y dx dy := by
  intro x y dx dy
  exact (gap8 z hz x y dx dy).trans
    (secondDifferential_coordV_eq hz x y dx dy)

theorem gap12 (z W : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (hz : C2 z) (hW : C2 W)
    (hMixedZ : partialYX z x y = partialXY z x y)
    (hMixedW : partialYX W (coordU z x y) (coordV z x y) =
      partialXY W (coordU z x y) (coordV z x y))
    (hRelation : ∀ a b,
      W (coordU z a b) (coordV z a b) = physicalW z a b) :
    jacobianFactor z W x y * secondDifferential z x y dx dy =
      partialXX W (coordU z x y) (coordV z x y) *
          ((partialX z x y + 1) * dx + partialY z x y * dy) ^ 2 +
        2 * partialXY W (coordU z x y) (coordV z x y) *
          ((partialX z x y + 1) * dx + partialY z x y * dy) *
          (partialX z x y * dx + (partialY z x y + 1) * dy) +
        partialYY W (coordU z x y) (coordV z x y) *
          (partialX z x y * dx + (partialY z x y + 1) * dy) ^ 2 := by
  let X : ℝ → ℝ := fun t => x + t * dx
  let Y : ℝ → ℝ := fun t => y + t * dy
  let Z : ℝ → ℝ := fun t => z (X t) (Y t)
  let U : ℝ → ℝ := fun t => coordU z (X t) (Y t)
  let V : ℝ → ℝ := fun t => coordV z (X t) (Y t)
  let H : ℝ → ℝ := fun t => W (U t) (V t)
  let UP : ℝ → ℝ := fun t =>
    dx + differential z (X t) (Y t) dx dy
  let VP : ℝ → ℝ := fun t =>
    dy + differential z (X t) (Y t) dx dy
  let z2 : ℝ := secondDifferential z x y dx dy
  let du : ℝ :=
    (partialX z x y + 1) * dx + partialY z x y * dy
  let dv : ℝ :=
    partialX z x y * dx + (partialY z x y + 1) * dy
  have hX (t : ℝ) : HasDerivAt X dx t := by
    simpa [X] using hasDerivAt_lineX x dx t
  have hY (t : ℝ) : HasDerivAt Y dy t := by
    simpa [Y] using hasDerivAt_lineX y dy t
  have hZ (t : ℝ) :
      HasDerivAt Z (differential z (X t) (Y t) dx dy) t := by
    simpa [Z, differential] using
      hasDerivAt_comp₂ z X Y (hz.1 (X t, Y t)) (hX t) (hY t)
  have hZprime :
      (fun t => deriv Z t) =
        fun t => differential z (X t) (Y t) dx dy := by
    funext t
    exact (hZ t).deriv
  have hz2model :
      HasDerivAt
        (fun t => differential z (X t) (Y t) dx dy) z2 0 := by
    simpa [X, Y, z2] using
      hasDerivAt_differential_along z hz x y dx dy hMixedZ
  have hZsecond : HasDerivAt (fun t => deriv Z t) z2 0 := by
    rw [hZprime]
    exact hz2model
  have hU (t : ℝ) : HasDerivAt U (UP t) t := by
    simpa [U, UP, Z, coordU] using (hX t).add (hZ t)
  have hV (t : ℝ) : HasDerivAt V (VP t) t := by
    simpa [V, VP, Z, coordV] using (hY t).add (hZ t)
  have hUprime : (fun t => deriv U t) = UP := by
    funext t
    exact (hU t).deriv
  have hVprime : (fun t => deriv V t) = VP := by
    funext t
    exact (hV t).deriv
  have hUPsecond : HasDerivAt UP z2 0 := by
    simpa only [UP, Pi.add_apply, zero_add] using
      (hasDerivAt_const 0 dx).add hz2model
  have hVPsecond : HasDerivAt VP z2 0 := by
    simpa only [VP, Pi.add_apply, zero_add] using
      (hasDerivAt_const 0 dy).add hz2model
  have hUP0 : UP 0 = du := by
    simp [UP, X, Y, du, differential]
    ring
  have hVP0 : VP 0 = dv := by
    simp [VP, X, Y, dv, differential]
    ring
  have hU0 : HasDerivAt U du 0 := by
    rw [← hUP0]
    exact hU 0
  have hV0 : HasDerivAt V dv 0 := by
    rw [← hVP0]
    exact hV 0
  have hH (t : ℝ) :
      HasDerivAt H
        (partialX W (U t) (V t) * UP t +
          partialY W (U t) (V t) * VP t) t := by
    simpa [H] using
      hasDerivAt_comp₂ W U V (hW.1 (U t, V t)) (hU t) (hV t)
  have hHprime :
      (fun t => deriv H t) =
        fun t =>
          partialX W (U t) (V t) * UP t +
            partialY W (U t) (V t) * VP t := by
    funext t
    exact (hH t).deriv
  have hA := hasDerivAt_comp₂ (partialX W) U V
    (t := 0) (by
      simpa [U, V, X, Y] using
        hW.2.1 (coordU z x y, coordV z x y))
    hU0 hV0
  have hB := hasDerivAt_comp₂ (partialY W) U V
    (t := 0) (by
      simpa [U, V, X, Y] using
        hW.2.2 (coordU z x y, coordV z x y))
    hU0 hV0
  have hHmodelRaw :=
    (hA.mul hUPsecond).add (hB.mul hVPsecond)
  have hHsecondModel :
      HasDerivAt (fun t => deriv H t)
        (partialXX W (coordU z x y) (coordV z x y) * du ^ 2 +
          2 * partialXY W (coordU z x y) (coordV z x y) * du * dv +
          partialYY W (coordU z x y) (coordV z x y) * dv ^ 2 +
          (partialX W (coordU z x y) (coordV z x y) +
            partialY W (coordU z x y) (coordV z x y)) * z2) 0 := by
    rw [hHprime]
    convert hHmodelRaw using 1
    rw [hUP0, hVP0]
    simp only [U, V, X, Y, zero_mul, add_zero]
    change
      partialXX W (coordU z x y) (coordV z x y) * du ^ 2 +
            2 * partialXY W (coordU z x y) (coordV z x y) * du * dv +
          partialYY W (coordU z x y) (coordV z x y) * dv ^ 2 +
        (partialX W (coordU z x y) (coordV z x y) +
            partialY W (coordU z x y) (coordV z x y)) * z2 =
      ((partialXX W (coordU z x y) (coordV z x y) * du +
            partialXY W (coordU z x y) (coordV z x y) * dv) * du +
          partialX W (coordU z x y) (coordV z x y) * z2) +
        ((partialYX W (coordU z x y) (coordV z x y) * du +
            partialYY W (coordU z x y) (coordV z x y) * dv) * dv +
          partialY W (coordU z x y) (coordV z x y) * z2)
    rw [hMixedW]
    ring
  have hHeq :
      H = fun t => X t + Y t + Z t := by
    funext t
    dsimp [H, U, V, Z]
    simpa [physicalW] using hRelation (X t) (Y t)
  have hHprimeRelation :
      (fun t => deriv H t) =
        fun t => dx + dy + deriv Z t := by
    funext t
    rw [hHeq]
    have h := ((hX t).add (hY t)).add (hZ t)
    convert h.deriv using 1
    rw [(hZ t).deriv]
  have hHsecondRelation :
      HasDerivAt (fun t => deriv H t) z2 0 := by
    rw [hHprimeRelation]
    simpa only [Pi.add_apply, zero_add] using
      (hasDerivAt_const 0 (dx + dy)).add hZsecond
  have hkey := hHsecondModel.unique hHsecondRelation
  dsimp [jacobianFactor, z2, du, dv] at hkey ⊢
  ring_nf at hkey ⊢
  linarith

theorem gap13 (z W : ℝ → ℝ → ℝ) (x y : ℝ)
    (hS : jacobianFactor z W x y ≠ 0)
    (hz : C2 z) (hW : C2 W)
    (hMixedZ : partialYX z x y = partialXY z x y)
    (hMixedW : partialYX W (coordU z x y) (coordV z x y) =
      partialXY W (coordU z x y) (coordV z x y))
    (hRelation : ∀ a b,
      W (coordU z a b) (coordV z a b) = physicalW z a b) :
    partialXX z x y =
      1 / jacobianFactor z W x y *
        ((1 + partialX z x y) ^ 2 *
            partialXX W (coordU z x y) (coordV z x y) +
          2 * partialX z x y * (1 + partialX z x y) *
            partialXY W (coordU z x y) (coordV z x y) +
          partialX z x y ^ 2 *
            partialYY W (coordU z x y) (coordV z x y)) := by
  have h := gap12 z W x y 1 0 hz hW hMixedZ hMixedW hRelation
  simp only [secondDifferential, one_pow, zero_pow, mul_one, mul_zero, add_zero] at h
  field_simp [hS]
  ring_nf at h ⊢
  linarith

theorem gap14 (z W : ℝ → ℝ → ℝ) (x y : ℝ)
    (hS : jacobianFactor z W x y ≠ 0)
    (hz : C2 z) (hW : C2 W)
    (hMixedZ : partialYX z x y = partialXY z x y)
    (hMixedW : partialYX W (coordU z x y) (coordV z x y) =
      partialXY W (coordU z x y) (coordV z x y))
    (hRelation : ∀ a b,
      W (coordU z a b) (coordV z a b) = physicalW z a b) :
    partialXY z x y =
      1 / jacobianFactor z W x y *
        (partialY z x y * (partialX z x y + 1) *
            partialXX W (coordU z x y) (coordV z x y) +
          (1 + partialX z x y + partialY z x y +
            2 * partialX z x y * partialY z x y) *
            partialXY W (coordU z x y) (coordV z x y) +
          partialX z x y * (partialY z x y + 1) *
            partialYY W (coordU z x y) (coordV z x y)) := by
  have h10 := gap12 z W x y 1 0 hz hW hMixedZ hMixedW hRelation
  have h01 := gap12 z W x y 0 1 hz hW hMixedZ hMixedW hRelation
  have h11 := gap12 z W x y 1 1 hz hW hMixedZ hMixedW hRelation
  simp only [secondDifferential, one_pow, zero_pow, mul_one, mul_zero, add_zero,
    zero_add] at h10 h01 h11
  field_simp [hS]
  ring_nf at h10 h01 h11 ⊢
  linarith

theorem gap15 (z W : ℝ → ℝ → ℝ) (x y : ℝ)
    (hS : jacobianFactor z W x y ≠ 0)
    (hz : C2 z) (hW : C2 W)
    (hMixedZ : partialYX z x y = partialXY z x y)
    (hMixedW : partialYX W (coordU z x y) (coordV z x y) =
      partialXY W (coordU z x y) (coordV z x y))
    (hRelation : ∀ a b,
      W (coordU z a b) (coordV z a b) = physicalW z a b) :
    partialYY z x y =
      1 / jacobianFactor z W x y *
        (partialY z x y ^ 2 *
            partialXX W (coordU z x y) (coordV z x y) +
          2 * partialY z x y * (partialY z x y + 1) *
            partialXY W (coordU z x y) (coordV z x y) +
          (partialY z x y + 1) ^ 2 *
            partialYY W (coordU z x y) (coordV z x y)) := by
  have h := gap12 z W x y 0 1 hz hW hMixedZ hMixedW hRelation
  simp only [secondDifferential, one_pow, zero_pow, mul_one, mul_zero, add_zero,
    zero_add] at h
  field_simp [hS]
  ring_nf at h ⊢
  linarith

theorem gap16 (p q : ℝ) :
    q * (1 + q) * (1 + p) ^ 2 -
        (1 + p + q + 2 * p * q) * q * (p + 1) +
        p * (1 + p) * q ^ 2 = 0 := by
  ring

theorem gap17 (p q : ℝ) :
    p ^ 2 * q * (1 + q) -
        (1 + p + q + 2 * p * q) * p * (q + 1) +
        p * (1 + p) * (q + 1) ^ 2 = 0 := by
  ring

theorem gap18 (p q : ℝ) :
    2 * p * (1 + p) * q * (1 + q) -
        (1 + p + q + 2 * p * q) ^ 2 +
        2 * q * (q + 1) * p * (1 + p) =
      -(1 + p + q) ^ 2 := by
  ring

theorem gap19 (z W : ℝ → ℝ → ℝ) (x y : ℝ)
    (hS : jacobianFactor z W x y ≠ 0)
    (hz : C2 z) (hW : C2 W)
    (hMixedZ : partialYX z x y = partialXY z x y)
    (hMixedW : partialYX W (coordU z x y) (coordV z x y) =
      partialXY W (coordU z x y) (coordV z x y))
    (hRelation : ∀ a b,
      W (coordU z a b) (coordV z a b) = physicalW z a b) :
    physicalOperator z x y =
      -(1 + partialX z x y + partialY z x y) ^ 2 /
          jacobianFactor z W x y *
        partialXY W (coordU z x y) (coordV z x y) := by
  rw [physicalOperator,
    gap13 z W x y hS hz hW hMixedZ hMixedW hRelation,
    gap14 z W x y hS hz hW hMixedZ hMixedW hRelation,
    gap15 z W x y hS hz hW hMixedZ hMixedW hRelation]
  field_simp [hS]
  ring

theorem gap20 (z W : ℝ → ℝ → ℝ) (x y : ℝ)
    (hS : jacobianFactor z W x y ≠ 0)
    (hz : C2 z) (hW : C2 W)
    (hMixedZ : partialYX z x y = partialXY z x y)
    (hMixedW : partialYX W (coordU z x y) (coordV z x y) =
      partialXY W (coordU z x y) (coordV z x y))
    (hRelation : ∀ a b,
      W (coordU z a b) (coordV z a b) = physicalW z a b)
    (hPDE : physicalOperator z x y = 0) :
    -(1 + partialX z x y + partialY z x y) ^ 2 /
        jacobianFactor z W x y *
      partialXY W (coordU z x y) (coordV z x y) = 0 := by
  exact (gap19 z W x y hS hz hW hMixedZ hMixedW hRelation).symm.trans hPDE

theorem gap21 (z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hPDE : physicalOperator z x y = 0) :
    partialY z x y * (1 + partialY z x y) * partialXX z x y -
        (1 + partialX z x y + partialY z x y +
          2 * partialX z x y * partialY z x y) * partialXY z x y +
        partialX z x y * (1 + partialX z x y) * partialYY z x y = 0 := by
  exact hPDE

theorem gap22 (z W : ℝ → ℝ → ℝ) (x y : ℝ)
    (hS : jacobianFactor z W x y ≠ 0)
    (hJac : 1 + partialX z x y + partialY z x y ≠ 0)
    (hz : C2 z) (hW : C2 W)
    (hMixedZ : partialYX z x y = partialXY z x y)
    (hMixedW : partialYX W (coordU z x y) (coordV z x y) =
      partialXY W (coordU z x y) (coordV z x y))
    (hRelation : ∀ a b,
      W (coordU z a b) (coordV z a b) = physicalW z a b)
    (hPDE : physicalOperator z x y = 0) :
    partialXY W (coordU z x y) (coordV z x y) = 0 := by
  have hzero := gap20 z W x y hS hz hW hMixedZ hMixedW hRelation hPDE
  have hcoeff :
      -(1 + partialX z x y + partialY z x y) ^ 2 /
          jacobianFactor z W x y ≠ 0 := by
    exact div_ne_zero (neg_ne_zero.mpr (pow_ne_zero 2 hJac)) hS
  exact (mul_eq_zero.mp hzero).resolve_left hcoeff

end

end ProofGap.Exercise3523
