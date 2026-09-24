import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Topology.Defs.Filter
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ProofGap.Exercise3413

noncomputable section

def partialX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f t y) x

def partialY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f x t) y

def jacobian (φ ψ u v : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  partialX φ (u x y) (v x y) * partialY ψ (u x y) (v x y) -
    partialX ψ (u x y) (v x y) * partialY φ (u x y) (v x y)

private theorem partialX_chain (χ u v z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hχDiff : DifferentiableAt ℝ (Function.uncurry χ) (u x y, v x y))
    (huDiff : DifferentiableAt ℝ (Function.uncurry u) (x, y))
    (hvDiff : DifferentiableAt ℝ (Function.uncurry v) (x, y))
    (hZ : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      z p.1 p.2 = χ (u p.1 p.2) (v p.1 p.2)) :
    partialX z x y =
      partialX χ (u x y) (v x y) * partialX u x y +
        partialY χ (u x y) (v x y) * partialX v x y := by
  have hcurve : DifferentiableAt ℝ (fun t : ℝ => (t, y)) x := by
    exact differentiableAt_id.prodMk (differentiableAt_const (c := y))
  have huX : DifferentiableAt ℝ (fun t : ℝ => u t y) x := by
    simpa [Function.comp_def] using huDiff.comp x hcurve
  have hvX : DifferentiableAt ℝ (fun t : ℝ => v t y) x := by
    simpa [Function.comp_def] using hvDiff.comp x hcurve
  let eX : ℝ →L[ℝ] (ℝ × ℝ) :=
    (ContinuousLinearMap.id ℝ ℝ).prod (0 : ℝ →L[ℝ] ℝ)
  let eY : ℝ →L[ℝ] (ℝ × ℝ) :=
    (0 : ℝ →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ ℝ)
  have huPair : HasDerivAt (fun t : ℝ => eX (u t y))
      (eX (partialX u x y)) x := by
    simpa [partialX] using
      eX.hasFDerivAt.comp_hasDerivAt x huX.hasDerivAt
  have hvPair : HasDerivAt (fun t : ℝ => eY (v t y))
      (eY (partialX v x y)) x := by
    simpa [partialX] using
      eY.hasFDerivAt.comp_hasDerivAt x hvX.hasDerivAt
  have hinner : HasDerivAt (fun t : ℝ => (u t y, v t y))
      (partialX u x y, partialX v x y) x := by
    have hsum := huPair.add hvPair
    have hsum_fun :
        ((fun t : ℝ => eX (u t y)) + (fun t : ℝ => eY (v t y))) =
          (fun t : ℝ => (u t y, v t y)) := by
      funext t
      change eX (u t y) + eY (v t y) = (u t y, v t y)
      simp [eX, eY]
    rw [hsum_fun] at hsum
    simpa [eX, eY] using hsum
  let A : (ℝ × ℝ) →L[ℝ] ℝ :=
    fderiv ℝ (Function.uncurry χ) (u x y, v x y)
  have hcomp : HasDerivAt (fun t : ℝ => χ (u t y) (v t y))
      (A (partialX u x y, partialX v x y)) x := by
    simpa [A, Function.comp_def] using
      hχDiff.hasFDerivAt.comp_hasDerivAt x hinner
  have hcoordX : HasDerivAt (fun t : ℝ => (t, v x y))
      (1, 0) (u x y) := by
    have hxPair : HasDerivAt (fun t : ℝ => eX t) (eX 1) (u x y) := by
      simpa using
        eX.hasFDerivAt.comp_hasDerivAt (u x y) (hasDerivAt_id (u x y))
    have hcPair : HasDerivAt (fun _ : ℝ => eY (v x y))
        (0 : ℝ × ℝ) (u x y) := by
      exact hasDerivAt_const (x := u x y) (c := eY (v x y))
    have hsum := hxPair.add hcPair
    have hsum_fun :
        ((fun t : ℝ => eX t) + (fun _ : ℝ => eY (v x y))) =
          (fun t : ℝ => (t, v x y)) := by
      funext t
      change eX t + eY (v x y) = (t, v x y)
      simp [eX, eY]
    rw [hsum_fun] at hsum
    simpa [eX, eY] using hsum
  have hχX : HasDerivAt (fun t : ℝ => χ t (v x y))
      (A (1, 0)) (u x y) := by
    simpa [A, Function.comp_def] using
      hχDiff.hasFDerivAt.comp_hasDerivAt (u x y) hcoordX
  have hcoordY : HasDerivAt (fun t : ℝ => (u x y, t))
      (0, 1) (v x y) := by
    have hcPair : HasDerivAt (fun _ : ℝ => eX (u x y))
        (0 : ℝ × ℝ) (v x y) := by
      exact hasDerivAt_const (x := v x y) (c := eX (u x y))
    have hyPair : HasDerivAt (fun t : ℝ => eY t) (eY 1) (v x y) := by
      simpa using
        eY.hasFDerivAt.comp_hasDerivAt (v x y) (hasDerivAt_id (v x y))
    have hsum := hcPair.add hyPair
    have hsum_fun :
        ((fun _ : ℝ => eX (u x y)) + (fun t : ℝ => eY t)) =
          (fun t : ℝ => (u x y, t)) := by
      funext t
      change eX (u x y) + eY t = (u x y, t)
      simp [eX, eY]
    rw [hsum_fun] at hsum
    simpa [eX, eY] using hsum
  have hχY : HasDerivAt (fun t : ℝ => χ (u x y) t)
      (A (0, 1)) (v x y) := by
    simpa [A, Function.comp_def] using
      hχDiff.hasFDerivAt.comp_hasDerivAt (v x y) hcoordY
  have hpx : partialX χ (u x y) (v x y) = A (1, 0) := by
    simpa [partialX] using hχX.deriv
  have hpy : partialY χ (u x y) (v x y) = A (0, 1) := by
    simpa [partialY] using hχY.deriv
  have hlin (a b : ℝ) :
      A (a, b) = A (1, 0) * a + A (0, 1) * b := by
    have hp :
        (a, b) = a • ((1 : ℝ), (0 : ℝ)) + b • ((0 : ℝ), (1 : ℝ)) := by
      ext <;> simp
    rw [hp, map_add, map_smul, map_smul]
    simp [smul_eq_mul, mul_comm]
  have hEq : (fun t : ℝ => z t y) =ᶠ[nhds x]
      (fun t : ℝ => χ (u t y) (v t y)) := by
    simpa using hcurve.continuousAt hZ
  calc
    partialX z x y = deriv (fun t : ℝ => χ (u t y) (v t y)) x := by
      unfold partialX
      exact hEq.deriv_eq
    _ = A (partialX u x y, partialX v x y) := hcomp.deriv
    _ = A (1, 0) * partialX u x y + A (0, 1) * partialX v x y :=
      hlin _ _
    _ = partialX χ (u x y) (v x y) * partialX u x y +
        partialY χ (u x y) (v x y) * partialX v x y := by
      rw [hpx, hpy]

theorem gap1 (φ u v : ℝ → ℝ → ℝ) (x y : ℝ)
    (hφDiff : DifferentiableAt ℝ (Function.uncurry φ) (u x y, v x y))
    (huDiff : DifferentiableAt ℝ (Function.uncurry u) (x, y))
    (hvDiff : DifferentiableAt ℝ (Function.uncurry v) (x, y))
    (hX : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      p.1 = φ (u p.1 p.2) (v p.1 p.2)) :
    1 =
      partialX φ (u x y) (v x y) * partialX u x y +
        partialY φ (u x y) (v x y) * partialX v x y := by
  have h := partialX_chain φ u v (fun a : ℝ => fun _ : ℝ => a) x y
    hφDiff huDiff hvDiff hX
  simpa [partialX] using h

theorem gap2 (ψ u v : ℝ → ℝ → ℝ) (x y : ℝ)
    (hψDiff : DifferentiableAt ℝ (Function.uncurry ψ) (u x y, v x y))
    (huDiff : DifferentiableAt ℝ (Function.uncurry u) (x, y))
    (hvDiff : DifferentiableAt ℝ (Function.uncurry v) (x, y))
    (hY : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      p.2 = ψ (u p.1 p.2) (v p.1 p.2)) :
    0 =
      partialX ψ (u x y) (v x y) * partialX u x y +
        partialY ψ (u x y) (v x y) * partialX v x y := by
  have h := partialX_chain ψ u v (fun _ : ℝ => fun b : ℝ => b) x y
    hψDiff huDiff hvDiff hY
  simpa [partialX] using h

theorem gap3 (χ u v z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hχDiff : DifferentiableAt ℝ (Function.uncurry χ) (u x y, v x y))
    (huDiff : DifferentiableAt ℝ (Function.uncurry u) (x, y))
    (hvDiff : DifferentiableAt ℝ (Function.uncurry v) (x, y))
    (hzDiff : DifferentiableAt ℝ (Function.uncurry z) (x, y))
    (hZ : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      z p.1 p.2 = χ (u p.1 p.2) (v p.1 p.2)) :
    partialX z x y =
      partialX χ (u x y) (v x y) * partialX u x y +
        partialY χ (u x y) (v x y) * partialX v x y := by
  exact partialX_chain χ u v z x y hχDiff huDiff hvDiff hZ

theorem gap4 (φ ψ u v : ℝ → ℝ → ℝ) (x y : ℝ)
    (hJac : jacobian φ ψ u v x y ≠ 0)
    (hφ : 1 =
      partialX φ (u x y) (v x y) * partialX u x y +
        partialY φ (u x y) (v x y) * partialX v x y)
    (hψ : 0 =
      partialX ψ (u x y) (v x y) * partialX u x y +
        partialY ψ (u x y) (v x y) * partialX v x y) :
    partialX u x y =
      partialY ψ (u x y) (v x y) / jacobian φ ψ u v x y := by
  have hdet :
      partialY ψ (u x y) (v x y) =
        jacobian φ ψ u v x y * partialX u x y := by
    calc
      partialY ψ (u x y) (v x y) =
          partialY ψ (u x y) (v x y) * 1 -
            partialY φ (u x y) (v x y) * 0 := by ring
      _ = partialY ψ (u x y) (v x y) *
            (partialX φ (u x y) (v x y) * partialX u x y +
              partialY φ (u x y) (v x y) * partialX v x y) -
          partialY φ (u x y) (v x y) *
            (partialX ψ (u x y) (v x y) * partialX u x y +
              partialY ψ (u x y) (v x y) * partialX v x y) := by
            rw [hφ, hψ]
      _ = jacobian φ ψ u v x y * partialX u x y := by
            unfold jacobian
            ring
  apply (eq_div_iff hJac).2
  simpa [mul_comm] using hdet.symm

theorem gap5 (φ ψ u v : ℝ → ℝ → ℝ) (x y : ℝ)
    (hJac : jacobian φ ψ u v x y ≠ 0)
    (hφ : 1 =
      partialX φ (u x y) (v x y) * partialX u x y +
        partialY φ (u x y) (v x y) * partialX v x y)
    (hψ : 0 =
      partialX ψ (u x y) (v x y) * partialX u x y +
        partialY ψ (u x y) (v x y) * partialX v x y) :
    partialX v x y =
      -partialX ψ (u x y) (v x y) / jacobian φ ψ u v x y := by
  have hdet :
      -partialX ψ (u x y) (v x y) =
        jacobian φ ψ u v x y * partialX v x y := by
    calc
      -partialX ψ (u x y) (v x y) =
          partialX φ (u x y) (v x y) * 0 -
            partialX ψ (u x y) (v x y) * 1 := by ring
      _ = partialX φ (u x y) (v x y) *
            (partialX ψ (u x y) (v x y) * partialX u x y +
              partialY ψ (u x y) (v x y) * partialX v x y) -
          partialX ψ (u x y) (v x y) *
            (partialX φ (u x y) (v x y) * partialX u x y +
              partialY φ (u x y) (v x y) * partialX v x y) := by
            rw [hψ, hφ]
      _ = jacobian φ ψ u v x y * partialX v x y := by
            unfold jacobian
            ring
  apply (eq_div_iff hJac).2
  simpa [mul_comm] using hdet.symm

theorem gap6 (φ ψ χ u v z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hJac : jacobian φ ψ u v x y ≠ 0)
    (hZ : partialX z x y =
      partialX χ (u x y) (v x y) * partialX u x y +
        partialY χ (u x y) (v x y) * partialX v x y)
    (hU : partialX u x y =
      partialY ψ (u x y) (v x y) / jacobian φ ψ u v x y)
    (hV : partialX v x y =
      -partialX ψ (u x y) (v x y) / jacobian φ ψ u v x y) :
    partialX z x y =
      -(1 / jacobian φ ψ u v x y) *
        (partialX ψ (u x y) (v x y) * partialY χ (u x y) (v x y) -
          partialY ψ (u x y) (v x y) * partialX χ (u x y) (v x y)) := by
  rw [hZ, hU, hV]
  ring

theorem gap7 (φ ψ χ u v z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hJac : jacobian φ ψ u v x y ≠ 0)
    (hφ : 0 =
      partialX φ (u x y) (v x y) * partialY u x y +
        partialY φ (u x y) (v x y) * partialY v x y)
    (hψ : 1 =
      partialX ψ (u x y) (v x y) * partialY u x y +
        partialY ψ (u x y) (v x y) * partialY v x y)
    (hZ : partialY z x y =
      partialX χ (u x y) (v x y) * partialY u x y +
        partialY χ (u x y) (v x y) * partialY v x y) :
    partialY z x y =
      -(1 / jacobian φ ψ u v x y) *
        (partialY φ (u x y) (v x y) * partialX χ (u x y) (v x y) -
          partialX φ (u x y) (v x y) * partialY χ (u x y) (v x y)) := by
  have hU :
      partialY u x y =
        -partialY φ (u x y) (v x y) / jacobian φ ψ u v x y := by
    apply (eq_div_iff hJac).2
    have hdet :
        -partialY φ (u x y) (v x y) =
          jacobian φ ψ u v x y * partialY u x y := by
      calc
        -partialY φ (u x y) (v x y) =
            partialY ψ (u x y) (v x y) * 0 -
              partialY φ (u x y) (v x y) * 1 := by ring
        _ = partialY ψ (u x y) (v x y) *
              (partialX φ (u x y) (v x y) * partialY u x y +
                partialY φ (u x y) (v x y) * partialY v x y) -
            partialY φ (u x y) (v x y) *
              (partialX ψ (u x y) (v x y) * partialY u x y +
                partialY ψ (u x y) (v x y) * partialY v x y) := by
              rw [hφ, hψ]
        _ = jacobian φ ψ u v x y * partialY u x y := by
              unfold jacobian
              ring
    simpa [mul_comm] using hdet.symm
  have hV :
      partialY v x y =
        partialX φ (u x y) (v x y) / jacobian φ ψ u v x y := by
    apply (eq_div_iff hJac).2
    have hdet :
        partialX φ (u x y) (v x y) =
          jacobian φ ψ u v x y * partialY v x y := by
      calc
        partialX φ (u x y) (v x y) =
            partialX φ (u x y) (v x y) * 1 -
              partialX ψ (u x y) (v x y) * 0 := by ring
        _ = partialX φ (u x y) (v x y) *
              (partialX ψ (u x y) (v x y) * partialY u x y +
                partialY ψ (u x y) (v x y) * partialY v x y) -
            partialX ψ (u x y) (v x y) *
              (partialX φ (u x y) (v x y) * partialY u x y +
                partialY φ (u x y) (v x y) * partialY v x y) := by
              rw [hψ, hφ]
        _ = jacobian φ ψ u v x y * partialY v x y := by
              unfold jacobian
              ring
    simpa [mul_comm] using hdet.symm
  rw [hZ, hU, hV]
  ring

end

end ProofGap.Exercise3413
