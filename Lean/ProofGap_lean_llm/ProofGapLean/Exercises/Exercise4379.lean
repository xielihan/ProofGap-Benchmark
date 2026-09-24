import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace ProofGap.Exercise4379

noncomputable section

open MeasureTheory

abbrev Vec3 := ℝ × ℝ × ℝ

def divergenceOfGradient (secondPartials : Vec3 → Vec3) (p : Vec3) : ℝ :=
  (secondPartials p).1 + (secondPartials p).2.1 +
    (secondPartials p).2.2

def laplacian (secondPartials : Vec3 → Vec3) (p : Vec3) : ℝ :=
  (secondPartials p).1 + (secondPartials p).2.1 +
    (secondPartials p).2.2

def laplacianVolumeIntegral (V : Set Vec3)
    (secondPartials : Vec3 → Vec3) : ℝ :=
  ∫ p in V, laplacian secondPartials p

theorem gap1 (secondPartials : Vec3 → Vec3) (p : Vec3) :
    divergenceOfGradient secondPartials p =
      (secondPartials p).1 + (secondPartials p).2.1 +
        (secondPartials p).2.2 := by
  rfl

theorem gap2 (secondPartials : Vec3 → Vec3) (p : Vec3) :
    (secondPartials p).1 + (secondPartials p).2.1 +
        (secondPartials p).2.2 =
      laplacian secondPartials p := by
  rfl

theorem gap3 (V : Set Vec3) (secondPartials : Vec3 → Vec3)
    (normalDerivativeBoundaryIntegral : ℝ)
    (hGauss :
      normalDerivativeBoundaryIntegral =
        ∫ p in V, divergenceOfGradient secondPartials p) :
    normalDerivativeBoundaryIntegral =
      laplacianVolumeIntegral V secondPartials := by
  simpa [laplacianVolumeIntegral, divergenceOfGradient, laplacian] using hGauss

end

end ProofGap.Exercise4379
