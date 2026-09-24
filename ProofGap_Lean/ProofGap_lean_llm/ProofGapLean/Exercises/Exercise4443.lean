import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise4443

noncomputable section

open scoped Interval

abbrev Vec3 := ℝ × ℝ × ℝ

def dot (a b : Vec3) : ℝ :=
  a.1 * b.1 + a.2.1 * b.2.1 + a.2.2 * b.2.2

def partialX (f : Vec3 → ℝ) (p : Vec3) : ℝ :=
  deriv (fun x => f (x, p.2.1, p.2.2)) p.1

def partialY (f : Vec3 → ℝ) (p : Vec3) : ℝ :=
  deriv (fun y => f (p.1, y, p.2.2)) p.2.1

def partialZ (f : Vec3 → ℝ) (p : Vec3) : ℝ :=
  deriv (fun z => f (p.1, p.2.1, z)) p.2.2

def divergence (f : Vec3 → Vec3) (p : Vec3) : ℝ :=
  partialX (fun q => (f q).1) p +
    partialY (fun q => (f q).2.1) p +
    partialZ (fun q => (f q).2.2) p

def radialField (p : Vec3) : Vec3 := p

def sidePoint (ρ φ : ℝ) : Vec3 :=
  (ρ * Real.cos φ, ρ * Real.sin φ, 1 - ρ)

def sideAreaVector (ρ φ : ℝ) : Vec3 :=
  (ρ * Real.cos φ, ρ * Real.sin φ, ρ)

def basePoint (ρ φ : ℝ) : Vec3 :=
  (ρ * Real.cos φ, ρ * Real.sin φ, 0)

def baseNormal : Vec3 := (0, 0, -1)

def baseNormalIntegrand (ρ φ : ℝ) : ℝ :=
  dot (radialField (basePoint ρ φ)) baseNormal * ρ

def baseFlux : ℝ :=
  ∫ φ in (0 : ℝ)..2 * Real.pi,
    ∫ ρ in (0 : ℝ)..1, baseNormalIntegrand ρ φ

def sideFlux : ℝ :=
  ∫ φ in (0 : ℝ)..2 * Real.pi,
    ∫ ρ in (0 : ℝ)..1,
      dot (radialField (sidePoint ρ φ)) (sideAreaVector ρ φ)

def coneDivergenceIntegral : ℝ :=
  ∫ φ in (0 : ℝ)..2 * Real.pi,
    ∫ ρ in (0 : ℝ)..1,
      ∫ z in (0 : ℝ)..1 - ρ,
        divergence radialField (ρ * Real.cos φ, ρ * Real.sin φ, z) * ρ

def closedBoundaryFlux : ℝ := sideFlux + baseFlux

private theorem radial_divergence_eq_three (p : Vec3) :
    divergence radialField p = 3 := by
  simp [divergence, partialX, partialY, partialZ, radialField] <;> norm_num

private theorem cone_scaled_volume :
    coneDivergenceIntegral =
      3 *
        ∫ φ in (0 : ℝ)..2 * Real.pi,
          ∫ ρ in (0 : ℝ)..1,
            ∫ _z in (0 : ℝ)..1 - ρ, ρ := by
  unfold coneDivergenceIntegral
  simp_rw [radial_divergence_eq_three]
  simp_rw [intervalIntegral.integral_const_mul]

private theorem integral_mul_one_sub_zero_one :
    (∫ x in (0 : ℝ)..1, x * (1 - x)) = (1 : ℝ) / 6 := by
  let F : ℝ → ℝ := fun x => x ^ 2 / 2 - x ^ 3 / 3
  have hF (x : ℝ) : HasDerivAt F (x * (1 - x)) x := by
    dsimp [F]
    convert
      (((hasDerivAt_id x).mul (hasDerivAt_id x)).div_const 2).sub
        ((((hasDerivAt_id x).mul (hasDerivAt_id x)).mul
          (hasDerivAt_id x)).div_const 3) using 1
    · funext y
      dsimp [id]
      ring
    · dsimp [id]
      ring
  calc
    (∫ x in (0 : ℝ)..1, x * (1 - x)) = F 1 - F 0 := by
      apply intervalIntegral.integral_deriv_eq_sub' F
      · exact funext fun x => (hF x).deriv
      · intro x _hx
        exact (hF x).differentiableAt
      · exact
          (continuous_id.mul (continuous_const.sub continuous_id)).continuousOn
    _ = (1 : ℝ) / 6 := by norm_num [F]

private theorem cone_volume_integral_eq :
    (∫ φ in (0 : ℝ)..2 * Real.pi,
      ∫ ρ in (0 : ℝ)..1,
        ∫ _z in (0 : ℝ)..1 - ρ, ρ) = Real.pi / 3 := by
  have hz (ρ : ℝ) :
      (∫ _z in (0 : ℝ)..1 - ρ, ρ) = ρ * (1 - ρ) := by
    simp [intervalIntegral.integral_const] <;> ring
  simp_rw [hz]
  simp_rw [integral_mul_one_sub_zero_one]
  norm_num [intervalIntegral.integral_const] <;> ring

private theorem coneDivergenceIntegral_eq_pi :
    coneDivergenceIntegral = Real.pi := by
  rw [cone_scaled_volume, cone_volume_integral_eq]
  ring

private theorem base_normal_integrand_eq_zero (ρ φ : ℝ) :
    baseNormalIntegrand ρ φ = 0 := by
  simp [baseNormalIntegrand, dot, radialField, basePoint, baseNormal]

private theorem baseFlux_eq_zero : baseFlux = 0 := by
  simp [baseFlux, base_normal_integrand_eq_zero]

private theorem side_dot_eq_rho (ρ φ : ℝ) :
    dot (radialField (sidePoint ρ φ)) (sideAreaVector ρ φ) = ρ := by
  dsimp [dot, radialField, sidePoint, sideAreaVector]
  nlinarith [Real.sin_sq_add_cos_sq φ]

private theorem integral_id_zero_one :
    (∫ x in (0 : ℝ)..1, x) = (1 : ℝ) / 2 := by
  let F : ℝ → ℝ := fun x => x ^ 2 / 2
  have hF (x : ℝ) : HasDerivAt F x x := by
    dsimp [F]
    convert ((hasDerivAt_id x).mul (hasDerivAt_id x)).div_const 2 using 1
    · funext y
      dsimp [id]
      ring
    · dsimp [id]
      ring
  calc
    (∫ x in (0 : ℝ)..1, x) = F 1 - F 0 := by
      apply intervalIntegral.integral_deriv_eq_sub' F
      · exact funext fun x => (hF x).deriv
      · intro x _hx
        exact (hF x).differentiableAt
      · exact continuous_id.continuousOn
    _ = (1 : ℝ) / 2 := by norm_num [F]

private theorem sideFlux_eq_pi : sideFlux = Real.pi := by
  unfold sideFlux
  simp_rw [side_dot_eq_rho]
  simp_rw [integral_id_zero_one]
  norm_num [intervalIntegral.integral_const] <;> ring

theorem gap1 :
    closedBoundaryFlux = coneDivergenceIntegral := by
  simp [closedBoundaryFlux, sideFlux_eq_pi, baseFlux_eq_zero,
    coneDivergenceIntegral_eq_pi]

theorem gap2 :
    coneDivergenceIntegral =
      3 *
        ∫ φ in (0 : ℝ)..2 * Real.pi,
          ∫ ρ in (0 : ℝ)..1,
            ∫ _z in (0 : ℝ)..1 - ρ, ρ := by
  exact cone_scaled_volume

theorem gap3 :
    coneDivergenceIntegral = Real.pi := by
  exact coneDivergenceIntegral_eq_pi

theorem gap4 :
    closedBoundaryFlux = Real.pi := by
  simp [closedBoundaryFlux, sideFlux_eq_pi, baseFlux_eq_zero]

theorem gap5 (ρ φ : ℝ) (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    baseNormalIntegrand ρ φ = 0 := by
  exact base_normal_integrand_eq_zero ρ φ

theorem gap6 :
    baseFlux = 0 := by
  exact baseFlux_eq_zero

theorem gap7 :
    sideFlux = Real.pi := by
  exact sideFlux_eq_pi

end

end ProofGap.Exercise4443
