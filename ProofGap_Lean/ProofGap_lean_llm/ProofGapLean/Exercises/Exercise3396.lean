import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3396

noncomputable section

def uncurry3 (F : ℝ → ℝ → ℝ → ℝ) (p : ℝ × ℝ × ℝ) : ℝ :=
  F p.1 p.2.1 p.2.2

def partial1 (F : ℝ → ℝ → ℝ → ℝ) (a b c : ℝ) : ℝ :=
  deriv (fun t => F t b c) a

def partial2 (F : ℝ → ℝ → ℝ → ℝ) (a b c : ℝ) : ℝ :=
  deriv (fun t => F a t c) b

def partial3 (F : ℝ → ℝ → ℝ → ℝ) (a b c : ℝ) : ℝ :=
  deriv (fun t => F a b t) c

def partialX (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => z t y) x

def partialY (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => z x t) y

def arg1 (x y : ℝ) : ℝ := x - y

def arg2 (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ := y - z x y

def arg3 (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ := z x y - x

def F1At (F : ℝ → ℝ → ℝ → ℝ) (z : ℝ → ℝ → ℝ)
    (x y : ℝ) : ℝ :=
  partial1 F (arg1 x y) (arg2 z x y) (arg3 z x y)

def F2At (F : ℝ → ℝ → ℝ → ℝ) (z : ℝ → ℝ → ℝ)
    (x y : ℝ) : ℝ :=
  partial2 F (arg1 x y) (arg2 z x y) (arg3 z x y)

def F3At (F : ℝ → ℝ → ℝ → ℝ) (z : ℝ → ℝ → ℝ)
    (x y : ℝ) : ℝ :=
  partial3 F (arg1 x y) (arg2 z x y) (arg3 z x y)

private theorem hasDerivAt_uncurry3_comp
    (F : ℝ → ℝ → ℝ → ℝ) (u v w : ℝ → ℝ) (t u' v' w' : ℝ)
    (hF : DifferentiableAt ℝ (uncurry3 F) (u t, v t, w t))
    (hu : HasDerivAt u u' t) (hv : HasDerivAt v v' t)
    (hw : HasDerivAt w w' t) :
    HasDerivAt (fun s => F (u s) (v s) (w s))
      (partial1 F (u t) (v t) (w t) * u' +
        partial2 F (u t) (v t) (w t) * v' +
        partial3 F (u t) (v t) (w t) * w') t := by
  let L := fderiv ℝ (uncurry3 F) (u t, v t, w t)
  have hFL : HasFDerivAt (uncurry3 F) L (u t, v t, w t) := by
    simpa [L] using hF.hasFDerivAt
  have hline1 :
      HasDerivAt (fun s : ℝ => (s, (v t, w t)))
        ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) (u t) :=
    (hasDerivAt_id (u t)).prodMk
      ((hasDerivAt_const (u t) (v t)).prodMk
        (hasDerivAt_const (u t) (w t)))
  have hline2 :
      HasDerivAt (fun s : ℝ => (u t, (s, w t)))
        ((0 : ℝ), ((1 : ℝ), (0 : ℝ))) (v t) :=
    (hasDerivAt_const (v t) (u t)).prodMk
      ((hasDerivAt_id (v t)).prodMk
        (hasDerivAt_const (v t) (w t)))
  have hline3 :
      HasDerivAt (fun s : ℝ => (u t, (v t, s)))
        ((0 : ℝ), ((0 : ℝ), (1 : ℝ))) (w t) :=
    (hasDerivAt_const (w t) (u t)).prodMk
      ((hasDerivAt_const (w t) (v t)).prodMk
        (hasDerivAt_id (w t)))
  have h1 :
      partial1 F (u t) (v t) (w t) =
        L ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) := by
    simpa [partial1, uncurry3, Function.comp_def] using
      (hFL.comp_hasDerivAt (u t) hline1).deriv
  have h2 :
      partial2 F (u t) (v t) (w t) =
        L ((0 : ℝ), ((1 : ℝ), (0 : ℝ))) := by
    simpa [partial2, uncurry3, Function.comp_def] using
      (hFL.comp_hasDerivAt (v t) hline2).deriv
  have h3 :
      partial3 F (u t) (v t) (w t) =
        L ((0 : ℝ), ((0 : ℝ), (1 : ℝ))) := by
    simpa [partial3, uncurry3, Function.comp_def] using
      (hFL.comp_hasDerivAt (w t) hline3).deriv
  have hvec :
      (u', (v', w')) =
        u' • ((1 : ℝ), ((0 : ℝ), (0 : ℝ))) +
          v' • ((0 : ℝ), ((1 : ℝ), (0 : ℝ))) +
          w' • ((0 : ℝ), ((0 : ℝ), (1 : ℝ))) := by
    ext <;> simp
  have hL :
      L (u', (v', w')) =
        partial1 F (u t) (v t) (w t) * u' +
          partial2 F (u t) (v t) (w t) * v' +
          partial3 F (u t) (v t) (w t) * w' := by
    rw [hvec]
    simp only [map_add, map_smul, smul_eq_mul]
    rw [← h1, ← h2, ← h3]
    ring
  have hpath :
      HasDerivAt (fun s : ℝ => (u s, (v s, w s)))
        (u', (v', w')) t :=
    hu.prodMk (hv.prodMk hw)
  have hcomp := hFL.comp_hasDerivAt t hpath
  rw [hL] at hcomp
  simpa [uncurry3, Function.comp_def] using hcomp

theorem gap1 (F : ℝ → ℝ → ℝ → ℝ) (z : ℝ → ℝ → ℝ)
    (x y : ℝ)
    (hFDiff :
      DifferentiableAt ℝ (uncurry3 F)
        (arg1 x y, arg2 z x y, arg3 z x y))
    (hzDiff : DifferentiableAt ℝ (Function.uncurry z) (x, y))
    (hImplicit :
      ∀ᶠ p : ℝ × ℝ in nhds (x, y),
        F (arg1 p.1 p.2) (arg2 z p.1 p.2) (arg3 z p.1 p.2) = 0) :
    F1At F z x y +
        F2At F z x y * (-partialX z x y) +
        F3At F z x y * (partialX z x y - 1) = 0 := by
  have hlineDeriv :
      HasDerivAt (fun t : ℝ => (t, y)) ((1 : ℝ), (0 : ℝ)) x :=
    (hasDerivAt_id x).prodMk (hasDerivAt_const x y)
  have hzXDiff : DifferentiableAt ℝ (fun t : ℝ => z t y) x := by
    simpa [Function.uncurry] using
      hzDiff.comp x hlineDeriv.differentiableAt
  have hzX : HasDerivAt (fun t : ℝ => z t y) (partialX z x y) x := by
    simpa [partialX] using hzXDiff.hasDerivAt
  have harg1 : HasDerivAt (fun t : ℝ => arg1 t y) 1 x := by
    change HasDerivAt (fun t : ℝ => t - y) 1 x
    exact (hasDerivAt_id x).sub_const y
  have harg2 :
      HasDerivAt (fun t : ℝ => arg2 z t y) (-partialX z x y) x := by
    change HasDerivAt (fun t : ℝ => y - z t y) (-partialX z x y) x
    simpa only [Pi.sub_apply, zero_sub] using
      (hasDerivAt_const x y).sub hzX
  have harg3 :
      HasDerivAt (fun t : ℝ => arg3 z t y) (partialX z x y - 1) x := by
    change HasDerivAt (fun t : ℝ => z t y - t) (partialX z x y - 1) x
    simpa only [Pi.sub_apply, id_eq] using hzX.sub (hasDerivAt_id x)
  have hchain := hasDerivAt_uncurry3_comp
    (F := F)
    (u := fun t : ℝ => arg1 t y)
    (v := fun t : ℝ => arg2 z t y)
    (w := fun t : ℝ => arg3 z t y)
    (t := x)
    (u' := 1)
    (v' := -partialX z x y)
    (w' := partialX z x y - 1)
    hFDiff harg1 harg2 harg3
  have hzero :
      ∀ᶠ t : ℝ in nhds x,
        F (arg1 t y) (arg2 z t y) (arg3 z t y) = 0 := by
    exact hlineDeriv.continuousAt.eventually hImplicit
  have hzeroEq :
      (fun t : ℝ => F (arg1 t y) (arg2 z t y) (arg3 z t y)) =ᶠ[nhds x]
        (fun _ : ℝ => 0) := hzero
  have hzeroDeriv :
      HasDerivAt
        (fun t : ℝ => F (arg1 t y) (arg2 z t y) (arg3 z t y)) 0 x :=
    (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq hzeroEq
  have hid := hchain.unique hzeroDeriv
  simpa [F1At, F2At, F3At] using hid

theorem gap2 (F : ℝ → ℝ → ℝ → ℝ) (z : ℝ → ℝ → ℝ)
    (x y : ℝ)
    (hDenominator : F2At F z x y - F3At F z x y ≠ 0)
    (hXIdentity :
      F1At F z x y +
          F2At F z x y * (-partialX z x y) +
          F3At F z x y * (partialX z x y - 1) = 0) :
    partialX z x y =
      (F1At F z x y - F3At F z x y) /
        (F2At F z x y - F3At F z x y) := by
  apply (eq_div_iff hDenominator).2
  nlinarith [hXIdentity]

theorem gap3 (F : ℝ → ℝ → ℝ → ℝ) (z : ℝ → ℝ → ℝ)
    (x y : ℝ)
    (hFDiff :
      DifferentiableAt ℝ (uncurry3 F)
        (arg1 x y, arg2 z x y, arg3 z x y))
    (hzDiff : DifferentiableAt ℝ (Function.uncurry z) (x, y))
    (hImplicit :
      ∀ᶠ p : ℝ × ℝ in nhds (x, y),
        F (arg1 p.1 p.2) (arg2 z p.1 p.2) (arg3 z p.1 p.2) = 0)
    (hDenominator : F2At F z x y - F3At F z x y ≠ 0) :
    partialY z x y =
      (F2At F z x y - F1At F z x y) /
        (F2At F z x y - F3At F z x y) := by
  have hlineDeriv :
      HasDerivAt (fun t : ℝ => (x, t)) ((0 : ℝ), (1 : ℝ)) y :=
    (hasDerivAt_const y x).prodMk (hasDerivAt_id y)
  have hzYDiff : DifferentiableAt ℝ (fun t : ℝ => z x t) y := by
    simpa [Function.uncurry] using
      hzDiff.comp y hlineDeriv.differentiableAt
  have hzY : HasDerivAt (fun t : ℝ => z x t) (partialY z x y) y := by
    simpa [partialY] using hzYDiff.hasDerivAt
  have harg1 : HasDerivAt (fun t : ℝ => arg1 x t) (-1) y := by
    change HasDerivAt (fun t : ℝ => x - t) (-1) y
    simpa only [Pi.sub_apply, id_eq, zero_sub] using
      (hasDerivAt_const y x).sub (hasDerivAt_id y)
  have harg2 :
      HasDerivAt (fun t : ℝ => arg2 z x t) (1 - partialY z x y) y := by
    change HasDerivAt (fun t : ℝ => t - z x t) (1 - partialY z x y) y
    simpa only [Pi.sub_apply, id_eq] using (hasDerivAt_id y).sub hzY
  have harg3 :
      HasDerivAt (fun t : ℝ => arg3 z x t) (partialY z x y) y := by
    change HasDerivAt (fun t : ℝ => z x t - x) (partialY z x y) y
    exact hzY.sub_const x
  have hchain := hasDerivAt_uncurry3_comp
    (F := F)
    (u := fun t : ℝ => arg1 x t)
    (v := fun t : ℝ => arg2 z x t)
    (w := fun t : ℝ => arg3 z x t)
    (t := y)
    (u' := -1)
    (v' := 1 - partialY z x y)
    (w' := partialY z x y)
    hFDiff harg1 harg2 harg3
  have hzero :
      ∀ᶠ t : ℝ in nhds y,
        F (arg1 x t) (arg2 z x t) (arg3 z x t) = 0 := by
    exact hlineDeriv.continuousAt.eventually hImplicit
  have hzeroEq :
      (fun t : ℝ => F (arg1 x t) (arg2 z x t) (arg3 z x t)) =ᶠ[nhds y]
        (fun _ : ℝ => 0) := hzero
  have hzeroDeriv :
      HasDerivAt
        (fun t : ℝ => F (arg1 x t) (arg2 z x t) (arg3 z x t)) 0 y :=
    (hasDerivAt_const y (0 : ℝ)).congr_of_eventuallyEq hzeroEq
  have hYIdentity := hchain.unique hzeroDeriv
  apply (eq_div_iff hDenominator).2
  simp only [F1At, F2At, F3At] at hYIdentity ⊢
  nlinarith [hYIdentity]

end

end ProofGap.Exercise3396
