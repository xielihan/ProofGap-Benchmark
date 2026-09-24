import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise3357

noncomputable section

def uncurry3 (u : ℝ → ℝ → ℝ → ℝ) (p : ℝ × ℝ × ℝ) : ℝ :=
  u p.1 p.2.1 p.2.2

def IsC3 (u : ℝ → ℝ → ℝ → ℝ) : Prop :=
  ContDiff ℝ 3 (uncurry3 u)

def partialX (u : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun s => u s y z) x

def partialXY (u : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun s => partialX u x s z) y

def partialXYZ (u : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun s => partialXY u x y s) z

def HasZeroMixedDerivative (u : ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∀ x y z, partialXYZ u x y z = 0

def HasSeparatedForm (u : ℝ → ℝ → ℝ → ℝ) : Prop :=
  ∃ φ ψ χ : ℝ → ℝ → ℝ,
    ∀ x y z, u x y z = φ x y + ψ x z + χ y z

private abbrev Point3 := ℝ × ℝ × ℝ

private def eX : Point3 := (1, 0, 0)
private def eY : Point3 := (0, 1, 0)

private def dX (F : Point3 → ℝ) (p : Point3) : ℝ :=
  fderiv ℝ F p eX

private def dXY (F : Point3 → ℝ) (p : Point3) : ℝ :=
  fderiv ℝ (dX F) p eY

private theorem deriv_coordX
    (F : Point3 → ℝ) (hF : Differentiable ℝ F) (x y z : ℝ) :
    deriv (fun s => F (s, y, z)) x = dX F (x, y, z) := by
  have hc :
      HasDerivAt (fun s : ℝ => (s, y, z)) eX x := by
    simpa [eX] using
      (hasDerivAt_id x).prodMk
        ((hasDerivAt_const x y).prodMk (hasDerivAt_const x z))
  have h := hF.differentiableAt.hasFDerivAt.comp_hasDerivAt x hc
  simpa [dX, Function.comp_def] using h.deriv

private theorem deriv_coordY
    (F : Point3 → ℝ) (hF : Differentiable ℝ F) (x y z : ℝ) :
    deriv (fun s => F (x, s, z)) y =
      fderiv ℝ F (x, y, z) eY := by
  have hc :
      HasDerivAt (fun s : ℝ => (x, s, z)) eY y := by
    simpa [eY] using
      (hasDerivAt_const y x).prodMk
        ((hasDerivAt_id y).prodMk (hasDerivAt_const y z))
  have h := hF.differentiableAt.hasFDerivAt.comp_hasDerivAt y hc
  simpa [Function.comp_def] using h.deriv

private theorem deriv_coordZ
    (F : Point3 → ℝ) (hF : Differentiable ℝ F) (x y z : ℝ) :
    deriv (fun s => F (x, y, s)) z =
      fderiv ℝ F (x, y, z) (0, 0, 1) := by
  have hc :
      HasDerivAt (fun s : ℝ => (x, y, s)) (0, 0, 1) z := by
    simpa using
      (hasDerivAt_const z x).prodMk
        ((hasDerivAt_const z y).prodMk (hasDerivAt_id z))
  have h := hF.differentiableAt.hasFDerivAt.comp_hasDerivAt z hc
  simpa [Function.comp_def] using h.deriv

private theorem contDiff_dX (u : ℝ → ℝ → ℝ → ℝ) (hu : IsC3 u) :
    ContDiff ℝ 2 (dX (uncurry3 u)) := by
  unfold IsC3 at hu
  exact (hu.fderiv_right (m := 2) (by norm_num)).clm_apply contDiff_const

private theorem contDiff_dXY (u : ℝ → ℝ → ℝ → ℝ) (hu : IsC3 u) :
    ContDiff ℝ 1 (dXY (uncurry3 u)) := by
  unfold dXY
  exact ((contDiff_dX u hu).fderiv_right (m := 1) (by norm_num)).clm_apply
    contDiff_const

private theorem partialX_eq_dX (u : ℝ → ℝ → ℝ → ℝ)
    (hu : IsC3 u) (x y z : ℝ) :
    partialX u x y z = dX (uncurry3 u) (x, y, z) := by
  unfold partialX
  simpa [uncurry3] using
    deriv_coordX (uncurry3 u) (hu.differentiable (by decide)) x y z

private theorem partialXY_eq_dXY (u : ℝ → ℝ → ℝ → ℝ)
    (hu : IsC3 u) (x y z : ℝ) :
    partialXY u x y z = dXY (uncurry3 u) (x, y, z) := by
  unfold partialXY
  rw [show (fun s => partialX u x s z) =
      fun s => dX (uncurry3 u) (x, s, z) by
    funext s
    exact partialX_eq_dX u hu x s z]
  exact deriv_coordY _ ((contDiff_dX u hu).differentiable (by decide)) x y z

private theorem partialX_y_differentiable
    (u : ℝ → ℝ → ℝ → ℝ) (hu : IsC3 u) (x z : ℝ) :
    Differentiable ℝ (fun y => partialX u x y z) := by
  rw [show (fun y => partialX u x y z) =
      fun y => dX (uncurry3 u) (x, y, z) by
    funext y
    exact partialX_eq_dX u hu x y z]
  exact (contDiff_dX u hu).differentiable (by decide) |>.fun_comp (by fun_prop)

private theorem partialXY_z_differentiable
    (u : ℝ → ℝ → ℝ → ℝ) (hu : IsC3 u) (x y : ℝ) :
    Differentiable ℝ (fun z => partialXY u x y z) := by
  rw [show (fun z => partialXY u x y z) =
      fun z => dXY (uncurry3 u) (x, y, z) by
    funext z
    exact partialXY_eq_dXY u hu x y z]
  exact (contDiff_dXY u hu).differentiable_one.fun_comp (by fun_prop)

private theorem u_x_differentiable
    (u : ℝ → ℝ → ℝ → ℝ) (hu : IsC3 u) (y z : ℝ) :
    Differentiable ℝ (fun x => u x y z) := by
  have hU : Differentiable ℝ (uncurry3 u) :=
    hu.differentiable (by decide)
  simpa [uncurry3] using hU.fun_comp
    (show Differentiable ℝ (fun x : ℝ => (x, y, z)) by fun_prop)

private theorem hasDerivAt_u_x
    (u : ℝ → ℝ → ℝ → ℝ) (hu : IsC3 u) (x y z : ℝ) :
    HasDerivAt (fun s => u s y z) (partialX u x y z) x := by
  simpa [partialX] using
    (u_x_differentiable u hu y z).differentiableAt.hasDerivAt

private theorem hasDerivAt_partialX_y
    (u : ℝ → ℝ → ℝ → ℝ) (hu : IsC3 u) (x y z : ℝ) :
    HasDerivAt (fun s => partialX u x s z) (partialXY u x y z) y := by
  simpa [partialXY] using
    (partialX_y_differentiable u hu x z).differentiableAt.hasDerivAt

private theorem hasDerivAt_partialXY_z
    (u : ℝ → ℝ → ℝ → ℝ) (hu : IsC3 u) (x y z : ℝ) :
    HasDerivAt (fun s => partialXY u x y s) (partialXYZ u x y z) z := by
  simpa [partialXYZ] using
    (partialXY_z_differentiable u hu x y).differentiableAt.hasDerivAt

theorem gap1 (u : ℝ → ℝ → ℝ → ℝ)
    (hu : IsC3 u) (hpde : HasZeroMixedDerivative u) :
    ∃ φ : ℝ → ℝ → ℝ, ∀ x y z, partialXY u x y z = φ x y := by
  refine ⟨fun x y => partialXY u x y 0, ?_⟩
  intro x y z
  exact is_const_of_deriv_eq_zero
    (partialXY_z_differentiable u hu x y)
    (fun t => hpde x y t) z 0

theorem gap2 (u : ℝ → ℝ → ℝ → ℝ)
    (hu : IsC3 u) (hpde : HasZeroMixedDerivative u) :
    ∃ φ ψ : ℝ → ℝ → ℝ,
      ∀ x y z, partialX u x y z = φ x y + ψ x z := by
  rcases gap1 u hu hpde with ⟨θ, hθ⟩
  refine ⟨fun x y => partialX u x y 0,
    fun x z => partialX u x 0 z - partialX u x 0 0, ?_⟩
  intro x y z
  let q : ℝ → ℝ := fun t =>
    partialX u x t z - partialX u x t 0
  have hqdiff : Differentiable ℝ q := by
    dsimp [q]
    exact (partialX_y_differentiable u hu x z).sub
      (partialX_y_differentiable u hu x 0)
  have hqzero : ∀ t, deriv q t = 0 := by
    intro t
    have hd := (hasDerivAt_partialX_y u hu x t z).sub
      (hasDerivAt_partialX_y u hu x t 0)
    have hderiv :
        deriv q t = partialXY u x t z - partialXY u x t 0 := by
      simpa [q] using hd.deriv
    rw [hderiv, hθ x t z, hθ x t 0]
    ring
  have hconst := is_const_of_deriv_eq_zero hqdiff hqzero y 0
  dsimp [q] at hconst
  linarith

theorem gap3 (u : ℝ → ℝ → ℝ → ℝ)
    (hu : IsC3 u) :
    HasZeroMixedDerivative u → HasSeparatedForm u := by
  intro hpde
  rcases gap2 u hu hpde with ⟨a, b, hab⟩
  refine ⟨fun x y => u x y 0,
    fun x z => u x 0 z - u x 0 0,
    fun y z => u 0 y z - u 0 y 0 - (u 0 0 z - u 0 0 0), ?_⟩
  intro x y z
  let q : ℝ → ℝ := fun t =>
    u t y z - u t y 0 - (u t 0 z - u t 0 0)
  have hqdiff : Differentiable ℝ q := by
    dsimp [q]
    exact ((u_x_differentiable u hu y z).sub
      (u_x_differentiable u hu y 0)).sub
      ((u_x_differentiable u hu 0 z).sub
        (u_x_differentiable u hu 0 0))
  have hqzero : ∀ t, deriv q t = 0 := by
    intro t
    have hd := ((hasDerivAt_u_x u hu t y z).sub
      (hasDerivAt_u_x u hu t y 0)).sub
      ((hasDerivAt_u_x u hu t 0 z).sub
        (hasDerivAt_u_x u hu t 0 0))
    have hderiv :
        deriv q t =
          partialX u t y z - partialX u t y 0 -
            (partialX u t 0 z - partialX u t 0 0) := by
      simpa [q] using hd.deriv
    rw [hderiv, hab t y z, hab t y 0, hab t 0 z, hab t 0 0]
    ring
  have hconst := is_const_of_deriv_eq_zero hqdiff hqzero x 0
  dsimp [q] at hconst
  linarith

theorem gap4 (u : ℝ → ℝ → ℝ → ℝ)
    (hu : IsC3 u) :
    HasSeparatedForm u → HasZeroMixedDerivative u := by
  rintro ⟨a, b, c, habc⟩
  have hXcancel : ∀ t r s,
      partialX u t r s - partialX u t r 0 -
        (partialX u t 0 s - partialX u t 0 0) = 0 := by
    intro t r s
    let q : ℝ → ℝ := fun v =>
      u v r s - u v r 0 - (u v 0 s - u v 0 0)
    have hqfun : q =
        fun _ : ℝ => c r s - c r 0 - (c 0 s - c 0 0) := by
      funext v
      dsimp [q]
      rw [habc v r s, habc v r 0, habc v 0 s, habc v 0 0]
      ring
    have hzero : deriv q t = 0 := by
      rw [hqfun]
      exact deriv_const t _
    have hd := ((hasDerivAt_u_x u hu t r s).sub
      (hasDerivAt_u_x u hu t r 0)).sub
      ((hasDerivAt_u_x u hu t 0 s).sub
        (hasDerivAt_u_x u hu t 0 0))
    have hderiv :
        deriv q t =
          partialX u t r s - partialX u t r 0 -
            (partialX u t 0 s - partialX u t 0 0) := by
      simpa [q] using hd.deriv
    rw [hderiv] at hzero
    exact hzero
  have hXYeq : ∀ t r s,
      partialXY u t r s = partialXY u t r 0 := by
    intro t r s
    let q : ℝ → ℝ := fun v =>
      partialX u t v s - partialX u t v 0
    have hqfun : q =
        fun _ : ℝ => partialX u t 0 s - partialX u t 0 0 := by
      funext v
      dsimp [q]
      linarith [hXcancel t v s]
    have hzero : deriv q r = 0 := by
      rw [hqfun]
      exact deriv_const r _
    have hd := (hasDerivAt_partialX_y u hu t r s).sub
      (hasDerivAt_partialX_y u hu t r 0)
    have hderiv :
        deriv q r =
          partialXY u t r s - partialXY u t r 0 := by
      simpa [q] using hd.deriv
    rw [hderiv] at hzero
    linarith
  intro x y z
  unfold partialXYZ
  rw [show (fun s => partialXY u x y s) =
      fun _ : ℝ => partialXY u x y 0 by
    funext s
    exact hXYeq x y s]
  exact deriv_const z _

end

end ProofGap.Exercise3357
