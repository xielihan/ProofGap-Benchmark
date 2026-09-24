import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4442_2

noncomputable section

open scoped Interval

abbrev Vec3 := ℝ × ℝ × ℝ

def partialX (f : Vec3 → ℝ) (p : Vec3) : ℝ :=
  deriv (fun x => f (x, p.2.1, p.2.2)) p.1

def partialY (f : Vec3 → ℝ) (p : Vec3) : ℝ :=
  deriv (fun y => f (p.1, y, p.2.2)) p.2.1

def partialZ (f : Vec3 → ℝ) (p : Vec3) : ℝ :=
  deriv (fun z => f (p.1, p.2.1, z)) p.2.2

def vectorField (p : Vec3) : Vec3 :=
  (p.2.1 * p.2.2, p.2.2 * p.1, p.1 * p.2.1)

def divergence (f : Vec3 → Vec3) (p : Vec3) : ℝ :=
  partialX (fun q => (f q).1) p +
    partialY (fun q => (f q).2.1) p +
    partialZ (fun q => (f q).2.2) p

def cylinderDivergenceIntegral (R h : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..2 * Real.pi,
    ∫ ρ in (0 : ℝ)..R,
      ∫ z in (0 : ℝ)..h,
        divergence vectorField (ρ * Real.cos θ, ρ * Real.sin θ, z) * ρ

def topFlux (R h : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..2 * Real.pi,
    ∫ ρ in (0 : ℝ)..R,
      ((vectorField (ρ * Real.cos θ, ρ * Real.sin θ, h)).2.2) * ρ

def bottomFlux (R : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..2 * Real.pi,
    ∫ ρ in (0 : ℝ)..R,
      -((vectorField (ρ * Real.cos θ, ρ * Real.sin θ, 0)).2.2) * ρ

def sideFlux (R h : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..2 * Real.pi,
    ∫ z in (0 : ℝ)..h,
      ((vectorField (R * Real.cos θ, R * Real.sin θ, z)).1 * Real.cos θ +
        (vectorField (R * Real.cos θ, R * Real.sin θ, z)).2.1 * Real.sin θ) * R

def closedBoundaryFlux (R h : ℝ) : ℝ :=
  sideFlux R h + topFlux R h + bottomFlux R

private theorem sin_mul_cos_full_period :
    (∫ x in (0 : ℝ)..2 * Real.pi, Real.sin x * Real.cos x) = 0 := by
  have hderiv (x : ℝ) :
      HasDerivAt
        (fun y : ℝ => Real.sin y * Real.sin y / 2)
        (Real.sin x * Real.cos x) x := by
    convert
      ((Real.hasDerivAt_sin x).mul (Real.hasDerivAt_sin x)).div_const 2
      using 1 <;> ring
  have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hderiv x)
    ((Real.continuous_sin.mul Real.continuous_cos).intervalIntegrable
      (0 : ℝ) (2 * Real.pi))
  simpa using hfund

theorem gap1 (R h : ℝ) (hR : 0 < R) (hh : 0 < h) :
    closedBoundaryFlux R h = cylinderDivergenceIntegral R h := by
  have hside : sideFlux R h = 0 := by
    unfold sideFlux
    change
      (∫ θ in (0 : ℝ)..2 * Real.pi,
        ∫ z in (0 : ℝ)..h,
          ((R * Real.sin θ * z) * Real.cos θ +
            (z * (R * Real.cos θ)) * Real.sin θ) * R) = 0
    calc
      _ = ∫ θ in (0 : ℝ)..2 * Real.pi,
          (2 * R ^ 2 * (∫ z in (0 : ℝ)..h, z)) *
            (Real.sin θ * Real.cos θ) := by
        apply intervalIntegral.integral_congr
        intro θ _
        calc
          (∫ z in (0 : ℝ)..h,
              ((R * Real.sin θ * z) * Real.cos θ +
                (z * (R * Real.cos θ)) * Real.sin θ) * R) =
              ∫ z in (0 : ℝ)..h,
                (2 * R ^ 2 * (Real.sin θ * Real.cos θ)) * z := by
            apply intervalIntegral.integral_congr
            intro z _
            ring
          _ = (2 * R ^ 2 * (∫ z in (0 : ℝ)..h, z)) *
                (Real.sin θ * Real.cos θ) := by
            rw [intervalIntegral.integral_const_mul]
            ring
      _ = (2 * R ^ 2 * (∫ z in (0 : ℝ)..h, z)) *
            (∫ θ in (0 : ℝ)..2 * Real.pi,
              Real.sin θ * Real.cos θ) := by
        rw [intervalIntegral.integral_const_mul]
      _ = 0 := by
        rw [sin_mul_cos_full_period]
        ring
  have hbottom : bottomFlux R = -topFlux R h := by
    unfold bottomFlux topFlux
    change
      (∫ θ in (0 : ℝ)..2 * Real.pi,
        ∫ ρ in (0 : ℝ)..R,
          -(ρ * Real.cos θ * (ρ * Real.sin θ)) * ρ) =
        -(∫ θ in (0 : ℝ)..2 * Real.pi,
          ∫ ρ in (0 : ℝ)..R,
            (ρ * Real.cos θ * (ρ * Real.sin θ)) * ρ)
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro θ _
    change
      (∫ ρ in (0 : ℝ)..R,
        -(ρ * Real.cos θ * (ρ * Real.sin θ)) * ρ) =
      -(∫ ρ in (0 : ℝ)..R,
        (ρ * Real.cos θ * (ρ * Real.sin θ)) * ρ)
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro ρ _
    ring
  have hcyl : cylinderDivergenceIntegral R h = 0 := by
    simp [cylinderDivergenceIntegral, divergence, partialX, partialY,
      partialZ, vectorField]
  rw [closedBoundaryFlux, hside, hbottom, hcyl]
  ring

theorem gap2 (R h : ℝ) (hR : 0 < R) (hh : 0 < h) :
    cylinderDivergenceIntegral R h =
      ∫ θ in (0 : ℝ)..2 * Real.pi,
        ∫ ρ in (0 : ℝ)..R,
          ∫ z in (0 : ℝ)..h, (0 : ℝ) * ρ := by
  simp [cylinderDivergenceIntegral, divergence, partialX, partialY,
    partialZ, vectorField]

theorem gap3 (R h : ℝ) (hR : 0 < R) (hh : 0 < h) :
    (∫ θ in (0 : ℝ)..2 * Real.pi,
      ∫ ρ in (0 : ℝ)..R,
        ∫ z in (0 : ℝ)..h, (0 : ℝ) * ρ) = 0 := by
  simp

theorem gap4 (R h : ℝ) (hR : 0 < R) (hh : 0 < h) :
    closedBoundaryFlux R h = 0 := by
  rw [gap1 R h hR hh, gap2 R h hR hh, gap3 R h hR hh]

end

end ProofGap.Exercise4442_2
