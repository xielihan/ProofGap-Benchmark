import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace ProofGap.Exercise4131

noncomputable section

open MeasureTheory
open scoped Interval

abbrev Point3 := ℝ × ℝ × ℝ

def unitCube : Set Point3 :=
  Set.Icc 0 1 ×ˢ (Set.Icc 0 1 ×ˢ Set.Icc 0 1)

def density (p : Point3) : ℝ :=
  p.1 + p.2.1 + p.2.2

def mass : ℝ :=
  ∫ p in unitCube, density p

private theorem setIntegral_Icc_eq_interval (g : ℝ → ℝ) :
    (∫ t in Set.Icc (0 : ℝ) 1, g t) =
      ∫ t in (0 : ℝ)..1, g t := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le (by norm_num)]

private theorem integral_const_add_id (c : ℝ) :
    (∫ t in (0 : ℝ)..1, c + t) = c + (1 : ℝ) / 2 := by
  have hconst :
      IntervalIntegrable (fun _t : ℝ => c) volume 0 1 :=
    intervalIntegrable_const
  have hid :
      IntervalIntegrable (fun t : ℝ => t) volume 0 1 :=
    continuous_id.intervalIntegrable 0 1
  calc
    (∫ t in (0 : ℝ)..1, c + t) =
        (∫ _t in (0 : ℝ)..1, c) + ∫ t in (0 : ℝ)..1, t := by
      simpa [id] using
        intervalIntegral.integral_add hconst hid
    _ = c + (1 : ℝ) / 2 := by
      simp [intervalIntegral.integral_const, integral_id]

private theorem integral_affine (a b : ℝ) :
    (∫ t in (0 : ℝ)..1, a + t + b) =
      a + b + (1 : ℝ) / 2 := by
  have heq :
      (fun t : ℝ => a + t + b) = fun t : ℝ => (a + b) + t := by
    funext t
    ring
  rw [heq, integral_const_add_id]

theorem gap1 :
    mass =
      ∫ x in (0 : ℝ)..1,
        ∫ y in (0 : ℝ)..1,
          ∫ z in (0 : ℝ)..1, x + y + z := by
  have hCubeCompact : IsCompact unitCube := by
    rw [unitCube]
    exact isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hDensityContinuous : Continuous density := by
    unfold density
    fun_prop
  have hCubeIntegrable :
      IntegrableOn density unitCube
        ((volume : Measure ℝ).prod (volume : Measure (ℝ × ℝ))) :=
    hDensityContinuous.continuousOn.integrableOn_compact hCubeCompact
  have hFubiniCube :
      (∫ p in unitCube, density p) =
        ∫ x in Set.Icc (0 : ℝ) 1,
          ∫ yz in Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1,
            density (x, yz) := by
    rw [Measure.volume_eq_prod ℝ (ℝ × ℝ)]
    exact MeasureTheory.setIntegral_prod density hCubeIntegrable
  have hFubiniSquare (x : ℝ) :
      (∫ yz in Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1,
          density (x, yz)) =
        ∫ y in Set.Icc (0 : ℝ) 1,
          ∫ z in Set.Icc (0 : ℝ) 1, x + y + z := by
    have hSquareCompact :
        IsCompact (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) :=
      isCompact_Icc.prod isCompact_Icc
    have hSquareIntegrable :
        IntegrableOn (fun yz : ℝ × ℝ => density (x, yz))
          (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)
          ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
      apply ContinuousOn.integrableOn_compact hSquareCompact
      unfold density
      fun_prop
    rw [Measure.volume_eq_prod ℝ ℝ]
    simpa [density] using
      MeasureTheory.setIntegral_prod
        (fun yz : ℝ × ℝ => density (x, yz)) hSquareIntegrable
  rw [mass, hFubiniCube]
  simp_rw [hFubiniSquare, setIntegral_Icc_eq_interval]

theorem gap2 :
    (∫ x in (0 : ℝ)..1,
        ∫ y in (0 : ℝ)..1,
          ∫ z in (0 : ℝ)..1, x + y + z) =
      (3 : ℝ) / 2 := by
  calc
    (∫ x in (0 : ℝ)..1,
        ∫ y in (0 : ℝ)..1,
          ∫ z in (0 : ℝ)..1, x + y + z) =
        ∫ x in (0 : ℝ)..1,
          ∫ y in (0 : ℝ)..1, x + y + (1 : ℝ) / 2 := by
      congr 1
      funext x
      congr 1
      funext y
      exact integral_const_add_id (x + y)
    _ = ∫ x in (0 : ℝ)..1, x + (1 : ℝ) / 2 + (1 : ℝ) / 2 := by
      congr 1
      funext x
      exact integral_affine x ((1 : ℝ) / 2)
    _ = ∫ x in (0 : ℝ)..1, x + 1 := by
      congr 1
      funext x
      ring
    _ = (3 : ℝ) / 2 := by
      convert integral_affine (0 : ℝ) 1 using 1 <;> norm_num

theorem gap3 :
    mass = (3 : ℝ) / 2 := by
  exact gap1.trans gap2

end

end ProofGap.Exercise4131
