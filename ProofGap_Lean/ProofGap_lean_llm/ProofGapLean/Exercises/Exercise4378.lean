import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise4378

noncomputable section

open MeasureTheory

abbrev Vec3 := ℝ × ℝ × ℝ

def radius (p : Vec3) : ℝ :=
  Real.sqrt (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2)

def radialUnitField (p : Vec3) : Vec3 :=
  (p.1 / radius p, p.2.1 / radius p, p.2.2 / radius p)

def computedDivergence (p : Vec3) : ℝ :=
  (p.2.1 ^ 2 + p.2.2 ^ 2) / radius p ^ 3 +
    (p.1 ^ 2 + p.2.2 ^ 2) / radius p ^ 3 +
    (p.1 ^ 2 + p.2.1 ^ 2) / radius p ^ 3

def inverseRadiusVolumeIntegral (V : Set Vec3) : ℝ :=
  ∫ p in V, 1 / radius p

theorem gap1 (p : Vec3) (hp : p ≠ (0, 0, 0)) :
    computedDivergence p = 2 / radius p := by
  rcases p with ⟨x, y, z⟩
  have hcoords : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0 := by
    by_cases hx : x = 0
    · by_cases hy : y = 0
      · by_cases hz : z = 0
        · exfalso
          apply hp
          simp [hx, hy, hz]
        · exact Or.inr (Or.inr hz)
      · exact Or.inr (Or.inl hy)
    · exact Or.inl hx
  have hsum : 0 < x ^ 2 + y ^ 2 + z ^ 2 := by
    rcases hcoords with hx | hy | hz
    · have hx2 : 0 < x ^ 2 := sq_pos_of_ne_zero hx
      nlinarith [sq_nonneg y, sq_nonneg z]
    · have hy2 : 0 < y ^ 2 := sq_pos_of_ne_zero hy
      nlinarith [sq_nonneg x, sq_nonneg z]
    · have hz2 : 0 < z ^ 2 := sq_pos_of_ne_zero hz
      nlinarith [sq_nonneg x, sq_nonneg y]
  have hr2 : radius (x, y, z) ^ 2 = x ^ 2 + y ^ 2 + z ^ 2 := by
    unfold radius
    rw [Real.sq_sqrt (le_of_lt hsum)]
  have hrne : radius (x, y, z) ≠ 0 := by
    unfold radius
    exact ne_of_gt (Real.sqrt_pos.2 hsum)
  calc
    computedDivergence (x, y, z) =
        (2 * (x ^ 2 + y ^ 2 + z ^ 2)) / radius (x, y, z) ^ 3 := by
      unfold computedDivergence
      ring
    _ = 2 / radius (x, y, z) := by
      rw [← hr2]
      field_simp [hrne] <;> ring

theorem gap2 (V : Set Vec3) (boundaryFlux : ℝ)
    (hGauss :
      boundaryFlux = ∫ p in V, computedDivergence p) :
    boundaryFlux = 2 * inverseRadiusVolumeIntegral V := by
  have hdiv (p : Vec3) :
      computedDivergence p = 2 * (1 / radius p) := by
    by_cases hp : p = (0, 0, 0)
    · subst p
      simp [computedDivergence, radius]
    · rw [gap1 p hp]
      simp [div_eq_mul_inv]
  calc
    boundaryFlux = ∫ p in V, computedDivergence p := hGauss
    _ = ∫ p in V, 2 * (1 / radius p) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall hdiv
    _ = 2 * ∫ p in V, 1 / radius p := by
      rw [integral_const_mul]
    _ = 2 * inverseRadiusVolumeIntegral V := by
      rfl

end

end ProofGap.Exercise4378
