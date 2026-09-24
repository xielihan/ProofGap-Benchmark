import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace ProofGap.Exercise4388

noncomputable section

open scoped Interval

abbrev Vec3 := ℝ × ℝ × ℝ

def dot (u v : Vec3) : ℝ :=
  u.1 * v.1 + u.2.1 * v.2.1 + u.2.2 * v.2.2

def divergence (F : Vec3 → Vec3) (p : Vec3) : ℝ :=
  deriv (fun x => (F (x, p.2.1, p.2.2)).1) p.1 +
    deriv (fun y => (F (p.1, y, p.2.2)).2.1) p.2.1 +
      deriv (fun z => (F (p.1, p.2.1, z)).2.2) p.2.2

def cubicField (p : Vec3) : Vec3 :=
  (p.1 ^ 3, p.2.1 ^ 3, p.2.2 ^ 3)

def sphericalPoint (r φ ψ : ℝ) : Vec3 :=
  (r * Real.cos ψ * Real.cos φ,
    r * Real.cos ψ * Real.sin φ,
    r * Real.sin ψ)

def outwardUnitNormal (φ ψ : ℝ) : Vec3 :=
  (Real.cos ψ * Real.cos φ,
    Real.cos ψ * Real.sin φ,
    Real.sin ψ)

def sphereBoundaryFlux (a : ℝ) (F : Vec3 → Vec3) : ℝ :=
  ∫ φ in (0 : ℝ)..2 * Real.pi,
    ∫ ψ in -Real.pi / 2..Real.pi / 2,
      dot (F (sphericalPoint a φ ψ)) (outwardUnitNormal φ ψ) *
        (a ^ 2 * Real.cos ψ)

def ballDivergenceIntegral (a : ℝ) (F : Vec3 → Vec3) : ℝ :=
  ∫ φ in (0 : ℝ)..2 * Real.pi,
    ∫ ψ in -Real.pi / 2..Real.pi / 2,
      ∫ r in (0 : ℝ)..a,
        divergence F (sphericalPoint r φ ψ) * (r ^ 2 * Real.cos ψ)

def SatisfiesBallDivergenceTheorem (a : ℝ) : Prop :=
  ∀ F : Vec3 → Vec3, ContDiff ℝ 1 F →
    sphereBoundaryFlux a F = ballDivergenceIntegral a F

def boundaryFlux (a : ℝ) : ℝ :=
  sphereBoundaryFlux a cubicField

def sphericalVolumeMoment (a : ℝ) : ℝ :=
  ballDivergenceIntegral a cubicField

def separatedMoment (a : ℝ) : ℝ :=
  6 * Real.pi *
    (∫ ψ in -Real.pi / 2..Real.pi / 2, Real.cos ψ) *
      ∫ r in (0 : ℝ)..a, r ^ 4

theorem gap1 (a : ℝ) (ha : 0 < a)
    (hGauss : SatisfiesBallDivergenceTheorem a) :
    boundaryFlux a = sphericalVolumeMoment a := by
  have hcubic : ContDiff ℝ 1 cubicField := by
    unfold cubicField
    fun_prop
  exact hGauss cubicField hcubic

theorem gap2 (a : ℝ) (ha : 0 < a) :
    sphericalVolumeMoment a =
      3 *
        ∫ φ in (0 : ℝ)..2 * Real.pi,
          ∫ ψ in -Real.pi / 2..Real.pi / 2,
            ∫ r in (0 : ℝ)..a, r ^ 4 * Real.cos ψ := by
  have hcube (x : ℝ) :
      deriv (fun t : ℝ => t ^ 3) x = 3 * x ^ 2 := by
    simpa using ((hasDerivAt_id x).pow 3).deriv
  have hdiv (p : Vec3) :
      divergence cubicField p =
        3 * (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2) := by
    change
      deriv (fun x : ℝ => x ^ 3) p.1 +
          deriv (fun y : ℝ => y ^ 3) p.2.1 +
            deriv (fun z : ℝ => z ^ 3) p.2.2 =
        3 * (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2)
    rw [hcube, hcube, hcube]
    ring
  have hsphere (r φ ψ : ℝ) :
      divergence cubicField (sphericalPoint r φ ψ) *
          (r ^ 2 * Real.cos ψ) =
        3 * (r ^ 4 * Real.cos ψ) := by
    have hφ : Real.cos φ ^ 2 + Real.sin φ ^ 2 = 1 := by
      simpa [add_comm] using Real.sin_sq_add_cos_sq φ
    have hψ : Real.cos ψ ^ 2 + Real.sin ψ ^ 2 = 1 := by
      simpa [add_comm] using Real.sin_sq_add_cos_sq ψ
    have hradius :
        (r * Real.cos ψ * Real.cos φ) ^ 2 +
              (r * Real.cos ψ * Real.sin φ) ^ 2 +
            (r * Real.sin ψ) ^ 2 =
          r ^ 2 := by
      calc
        (r * Real.cos ψ * Real.cos φ) ^ 2 +
                (r * Real.cos ψ * Real.sin φ) ^ 2 +
              (r * Real.sin ψ) ^ 2 =
            r ^ 2 * Real.cos ψ ^ 2 *
                (Real.cos φ ^ 2 + Real.sin φ ^ 2) +
              r ^ 2 * Real.sin ψ ^ 2 := by ring
        _ = r ^ 2 * Real.cos ψ ^ 2 + r ^ 2 * Real.sin ψ ^ 2 := by
          rw [hφ]
          ring
        _ = r ^ 2 * (Real.cos ψ ^ 2 + Real.sin ψ ^ 2) := by ring
        _ = r ^ 2 := by rw [hψ]; ring
    rw [hdiv]
    change
      3 * ((r * Real.cos ψ * Real.cos φ) ^ 2 +
              (r * Real.cos ψ * Real.sin φ) ^ 2 +
                (r * Real.sin ψ) ^ 2) *
            (r ^ 2 * Real.cos ψ) =
        3 * (r ^ 4 * Real.cos ψ)
    rw [hradius]
    ring
  unfold sphericalVolumeMoment ballDivergenceIntegral
  simp_rw [hsphere]
  simp_rw [intervalIntegral.integral_const_mul]

theorem gap3 (a : ℝ) (ha : 0 < a) :
    sphericalVolumeMoment a = separatedMoment a := by
  rw [gap2 a ha]
  unfold separatedMoment
  simp_rw [intervalIntegral.integral_mul_const]
  rw [intervalIntegral.integral_const_mul]
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  ring

theorem gap4 (a : ℝ) (ha : 0 < a) :
    separatedMoment a = 12 / 5 * Real.pi * a ^ 5 := by
  have hcos :
      (∫ ψ in -Real.pi / 2..Real.pi / 2, Real.cos ψ) = 2 := by
    calc
      (∫ ψ in -Real.pi / 2..Real.pi / 2, Real.cos ψ) =
          Real.sin (Real.pi / 2) - Real.sin (-Real.pi / 2) := by
        apply intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun x _ => Real.hasDerivAt_sin x)
        exact Real.continuous_cos.intervalIntegrable _ _
      _ = 2 := by
        rw [show -Real.pi / 2 = -(Real.pi / 2) by ring,
          Real.sin_neg, Real.sin_pi_div_two]
        norm_num
  have hpow (x : ℝ) :
      HasDerivAt (fun t : ℝ => t ^ 5) (5 * x ^ 4) x := by
    convert ((hasDerivAt_id x).pow 5) using 1 <;> norm_num
  have hfive :
      5 * (∫ r in (0 : ℝ)..a, r ^ 4) = a ^ 5 := by
    rw [← intervalIntegral.integral_const_mul]
    calc
      (∫ r in (0 : ℝ)..a, 5 * r ^ 4) = a ^ 5 - (0 : ℝ) ^ 5 := by
        apply intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun x _ => hpow x)
        exact (continuous_const.mul (continuous_id.pow 4)).intervalIntegrable _ _
      _ = a ^ 5 := by ring
  have hr :
      (∫ r in (0 : ℝ)..a, r ^ 4) = a ^ 5 / 5 := by
    calc
      (∫ r in (0 : ℝ)..a, r ^ 4) =
          5 * (∫ r in (0 : ℝ)..a, r ^ 4) / 5 := by ring
      _ = a ^ 5 / 5 := by rw [hfive]
  unfold separatedMoment
  rw [hcos, hr]
  ring

end

end ProofGap.Exercise4388
