import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Order.Filter.Tendsto
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3468

noncomputable section

def partialX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f t y) x

def partialY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f x t) y

def differential (f : ℝ → ℝ → ℝ) (x y dx dy : ℝ) : ℝ :=
  partialX f x y * dx + partialY f x y * dy

def xCoord (u v : ℝ) : ℝ := u * v
def yCoord (u v : ℝ) : ℝ := (u ^ 2 - v ^ 2) / 2
def radiusSq (u v : ℝ) : ℝ := u ^ 2 + v ^ 2

private abbrev Tendsto {α β : Type} (f : α → β) (l₁ : Filter α) (l₂ : Filter β) : Prop :=
  Filter.Tendsto f l₁ l₂

theorem gap1 (x : ℝ → ℝ → ℝ) (u v du dv : ℝ)
    (hxDiff : DifferentiableAt ℝ (Function.uncurry x) (u, v))
    (hX : ∀ᶠ p : ℝ × ℝ in nhds (u, v), x p.1 p.2 = xCoord p.1 p.2) :
    differential x u v du dv = v * du + u * dv := by
  have hpairX :
      Tendsto (fun t : ℝ => (t, v)) (nhds u) (nhds (u, v)) := by
    simpa using
      (continuousAt_id.prodMk
        (continuousAt_const : ContinuousAt (fun _ : ℝ => v) u))
  have hpairY :
      Tendsto (fun t : ℝ => (u, t)) (nhds v) (nhds (u, v)) := by
    simpa using
      ((continuousAt_const : ContinuousAt (fun _ : ℝ => u) v).prodMk
        continuousAt_id)
  have hX₁ :
      (fun t : ℝ => x t v) =ᶠ[nhds u] (fun t : ℝ => xCoord t v) :=
    hpairX.eventually hX
  have hX₂ :
      (fun t : ℝ => x u t) =ᶠ[nhds v] (fun t : ℝ => xCoord u t) :=
    hpairY.eventually hX
  have hcoordX : HasDerivAt (fun t : ℝ => xCoord t v) v u := by
    simpa [xCoord] using (hasDerivAt_id u).mul_const v
  have hcoordY : HasDerivAt (fun t : ℝ => xCoord u t) u v := by
    simpa [xCoord] using (hasDerivAt_id v).const_mul u
  have hpx : partialX x u v = v := by
    unfold partialX
    calc
      deriv (fun t => x t v) u = deriv (fun t => xCoord t v) u := hX₁.deriv_eq
      _ = v := hcoordX.deriv
  have hpy : partialY x u v = u := by
    unfold partialY
    calc
      deriv (fun t => x u t) v = deriv (fun t => xCoord u t) v := hX₂.deriv_eq
      _ = u := hcoordY.deriv
  simp [differential, hpx, hpy]

theorem gap2 (y : ℝ → ℝ → ℝ) (u v du dv : ℝ)
    (hyDiff : DifferentiableAt ℝ (Function.uncurry y) (u, v))
    (hY : ∀ᶠ p : ℝ × ℝ in nhds (u, v), y p.1 p.2 = yCoord p.1 p.2) :
    differential y u v du dv = u * du - v * dv := by
  have hpairX :
      Tendsto (fun t : ℝ => (t, v)) (nhds u) (nhds (u, v)) := by
    simpa using
      (continuousAt_id.prodMk
        (continuousAt_const : ContinuousAt (fun _ : ℝ => v) u))
  have hpairY :
      Tendsto (fun t : ℝ => (u, t)) (nhds v) (nhds (u, v)) := by
    simpa using
      ((continuousAt_const : ContinuousAt (fun _ : ℝ => u) v).prodMk
        continuousAt_id)
  have hY₁ :
      (fun t : ℝ => y t v) =ᶠ[nhds u] (fun t : ℝ => yCoord t v) :=
    hpairX.eventually hY
  have hY₂ :
      (fun t : ℝ => y u t) =ᶠ[nhds v] (fun t : ℝ => yCoord u t) :=
    hpairY.eventually hY
  have hcoordX : HasDerivAt (fun t : ℝ => yCoord t v) u u := by
    convert
      ((((hasDerivAt_id u).mul (hasDerivAt_id u)).sub_const (v ^ 2)).mul_const
        (1 / 2))
      using 1 <;> norm_num [yCoord] <;> ring_nf
    funext t
    ring
  have hcoordY : HasDerivAt (fun t : ℝ => yCoord u t) (-v) v := by
    convert
      (((((hasDerivAt_id v).mul (hasDerivAt_id v)).sub_const (u ^ 2)).neg).mul_const
        (1 / 2))
      using 1 <;> norm_num [yCoord] <;> ring_nf
  have hpx : partialX y u v = u := by
    unfold partialX
    calc
      deriv (fun t => y t v) u = deriv (fun t => yCoord t v) u := hY₁.deriv_eq
      _ = u := hcoordX.deriv
  have hpy : partialY y u v = -v := by
    unfold partialY
    calc
      deriv (fun t => y u t) v = deriv (fun t => yCoord u t) v := hY₂.deriv_eq
      _ = -v := hcoordY.deriv
  simp only [differential, hpx, hpy]
  ring

theorem gap3 (x y : ℝ → ℝ → ℝ) (u v du dv : ℝ)
    (hRadius : radiusSq u v ≠ 0)
    (hDx : differential x u v du dv = v * du + u * dv)
    (hDy : differential y u v du dv = u * du - v * dv) :
    du = (v * differential x u v du dv +
      u * differential y u v du dv) / radiusSq u v := by
  unfold radiusSq at hRadius ⊢
  rw [hDx, hDy]
  field_simp [hRadius] <;> ring

theorem gap4 (x y : ℝ → ℝ → ℝ) (u v du dv : ℝ)
    (hRadius : radiusSq u v ≠ 0)
    (hDx : differential x u v du dv = v * du + u * dv)
    (hDy : differential y u v du dv = u * du - v * dv) :
    dv = (u * differential x u v du dv -
      v * differential y u v du dv) / radiusSq u v := by
  unfold radiusSq at hRadius ⊢
  rw [hDx, hDy]
  field_simp [hRadius] <;> ring

theorem gap5 (z : ℝ → ℝ → ℝ) (u v du dv : ℝ) :
    differential z u v du dv =
      partialX z u v * du + partialY z u v * dv := by
  rfl

theorem gap6 (x y z : ℝ → ℝ → ℝ) (u v du dv : ℝ)
    (hRadius : radiusSq u v ≠ 0)
    (hDu : du = (v * differential x u v du dv +
      u * differential y u v du dv) / radiusSq u v)
    (hDv : dv = (u * differential x u v du dv -
      v * differential y u v du dv) / radiusSq u v) :
    partialX z u v * du + partialY z u v * dv =
      (1 / radiusSq u v) *
        (partialX z u v *
            (v * differential x u v du dv + u * differential y u v du dv) +
          partialY z u v *
            (u * differential x u v du dv - v * differential y u v du dv)) := by
  calc
    partialX z u v * du + partialY z u v * dv =
        partialX z u v *
            ((v * differential x u v du dv +
                u * differential y u v du dv) / radiusSq u v) +
          partialY z u v *
            ((u * differential x u v du dv -
                v * differential y u v du dv) / radiusSq u v) := by
      exact congrArg₂ (fun a b : ℝ => a + b)
        (congrArg (fun q : ℝ => partialX z u v * q) hDu)
        (congrArg (fun q : ℝ => partialY z u v * q) hDv)
    _ = (1 / radiusSq u v) *
        (partialX z u v *
            (v * differential x u v du dv +
              u * differential y u v du dv) +
          partialY z u v *
            (u * differential x u v du dv -
              v * differential y u v du dv)) := by
      field_simp [hRadius] <;> ring

theorem gap7 (x y z : ℝ → ℝ → ℝ) (u v du dv : ℝ)
    (hDz : differential z u v du dv =
      partialX z u v * du + partialY z u v * dv)
    (hSubstitution :
      partialX z u v * du + partialY z u v * dv =
        (1 / radiusSq u v) *
          (partialX z u v *
              (v * differential x u v du dv + u * differential y u v du dv) +
            partialY z u v *
              (u * differential x u v du dv - v * differential y u v du dv))) :
    differential z u v du dv =
      (1 / radiusSq u v) *
        (partialX z u v *
            (v * differential x u v du dv + u * differential y u v du dv) +
          partialY z u v *
            (u * differential x u v du dv - v * differential y u v du dv)) := by
  exact hDz.trans hSubstitution

theorem gap8 (x y z : ℝ → ℝ → ℝ) (u v du dv : ℝ)
    (hDifferential :
      differential z u v du dv =
        (1 / radiusSq u v) *
          (partialX z u v *
              (v * differential x u v du dv + u * differential y u v du dv) +
            partialY z u v *
              (u * differential x u v du dv - v * differential y u v du dv))) :
    differential z u v du dv =
      (1 / radiusSq u v) *
        ((v * partialX z u v + u * partialY z u v) *
            differential x u v du dv +
          (u * partialX z u v - v * partialY z u v) *
            differential y u v du dv) := by
  rw [hDifferential]
  ring

theorem gap9 (Z z : ℝ → ℝ → ℝ) (u v : ℝ)
    (hZx : partialX Z (xCoord u v) (yCoord u v) =
      (v * partialX z u v + u * partialY z u v) / radiusSq u v)
    (hZy : partialY Z (xCoord u v) (yCoord u v) =
      (u * partialX z u v - v * partialY z u v) / radiusSq u v) :
    partialX Z (xCoord u v) (yCoord u v) ^ 2 +
        partialY Z (xCoord u v) (yCoord u v) ^ 2 =
      (1 / radiusSq u v ^ 2) *
        ((v * partialX z u v + u * partialY z u v) ^ 2 +
          (u * partialX z u v - v * partialY z u v) ^ 2) := by
  rw [hZx, hZy]
  simp only [div_pow]
  ring

theorem gap10 (z : ℝ → ℝ → ℝ) (u v : ℝ)
    (hRadius : radiusSq u v ≠ 0) :
    (1 / radiusSq u v ^ 2) *
        ((v * partialX z u v + u * partialY z u v) ^ 2 +
          (u * partialX z u v - v * partialY z u v) ^ 2) =
      (1 / radiusSq u v) *
        (partialX z u v ^ 2 + partialY z u v ^ 2) := by
  unfold radiusSq at hRadius ⊢
  field_simp [hRadius] <;> ring

theorem gap11 (Z z : ℝ → ℝ → ℝ) (u v : ℝ)
    (hExpanded :
      partialX Z (xCoord u v) (yCoord u v) ^ 2 +
          partialY Z (xCoord u v) (yCoord u v) ^ 2 =
        (1 / radiusSq u v ^ 2) *
          ((v * partialX z u v + u * partialY z u v) ^ 2 +
            (u * partialX z u v - v * partialY z u v) ^ 2))
    (hSimplified :
      (1 / radiusSq u v ^ 2) *
          ((v * partialX z u v + u * partialY z u v) ^ 2 +
            (u * partialX z u v - v * partialY z u v) ^ 2) =
        (1 / radiusSq u v) *
          (partialX z u v ^ 2 + partialY z u v ^ 2)) :
    partialX Z (xCoord u v) (yCoord u v) ^ 2 +
        partialY Z (xCoord u v) (yCoord u v) ^ 2 =
      (1 / radiusSq u v) *
        (partialX z u v ^ 2 + partialY z u v ^ 2) := by
  exact hExpanded.trans hSimplified

end

end ProofGap.Exercise3468
