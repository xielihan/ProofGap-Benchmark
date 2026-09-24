import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace ProofGap.Exercise4376

noncomputable section

open MeasureTheory

abbrev Vec3 := ℝ × ℝ × ℝ

def cubicField (p : Vec3) : Vec3 :=
  (p.1 ^ 3, p.2.1 ^ 3, p.2.2 ^ 3)

def cubicDivergence (p : Vec3) : ℝ :=
  3 * (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2)

def quadraticVolumeMoment (V : Set Vec3) : ℝ :=
  ∫ p in V, p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2

theorem gap1 (p : Vec3) :
    (cubicField p).1 = p.1 ^ 3 := by
  rfl

theorem gap2 (p : Vec3) :
    (cubicField p).2.1 = p.2.1 ^ 3 := by
  rfl

theorem gap3 (p : Vec3) :
    (cubicField p).2.2 = p.2.2 ^ 3 := by
  rfl

theorem gap4 (p : Vec3) :
    cubicDivergence p =
      3 * (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2) := by
  rfl

theorem gap5 (V : Set Vec3) (boundaryFlux : ℝ)
    (hGauss :
      boundaryFlux = ∫ p in V, cubicDivergence p) :
    boundaryFlux = 3 * quadraticVolumeMoment V := by
  rw [hGauss]
  simp only [cubicDivergence, quadraticVolumeMoment]
  rw [MeasureTheory.integral_const_mul]

end

end ProofGap.Exercise4376
