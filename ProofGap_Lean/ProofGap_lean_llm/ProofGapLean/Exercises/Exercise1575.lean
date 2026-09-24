import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

namespace ProofGap.Exercise1575

noncomputable section

def distanceSquared (x : ℝ) : ℝ := 5 - 4 * x

def OnUnitCircle (p : ℝ × ℝ) : Prop := p.1 ^ 2 + p.2 ^ 2 = 1

def distance (p : ℝ × ℝ) : ℝ :=
  Real.sqrt ((p.1 - 2) ^ 2 + p.2 ^ 2)

private theorem unitCircle_first_bounds {x y : ℝ}
    (h : x ^ 2 + y ^ 2 = 1) : -1 ≤ x ∧ x ≤ 1 := by
  constructor
  · nlinarith [sq_nonneg y, sq_nonneg (x + 1)]
  · nlinarith [sq_nonneg y, sq_nonneg (x - 1)]

private theorem sqrt_nine : Real.sqrt (9 : ℝ) = 3 := by
  have hsqrt_nonneg : 0 ≤ Real.sqrt (9 : ℝ) := Real.sqrt_nonneg _
  have hsqrt_sq : (Real.sqrt (9 : ℝ)) ^ 2 = 9 := Real.sq_sqrt (by norm_num)
  nlinarith

theorem gap1 :
    IsLeast {d : ℝ | ∃ p, OnUnitCircle p ∧ d = distance p} 1 := by
  constructor
  · refine ⟨((1 : ℝ), (0 : ℝ)), ?_, ?_⟩
    · norm_num [OnUnitCircle]
    · norm_num [distance]
  · rintro d ⟨⟨x, y⟩, hcircle, rfl⟩
    change x ^ 2 + y ^ 2 = 1 at hcircle
    change 1 ≤ Real.sqrt ((x - 2) ^ 2 + y ^ 2)
    have hx := unitCircle_first_bounds hcircle
    have hrad : 1 ≤ (x - 2) ^ 2 + y ^ 2 := by
      nlinarith
    calc
      1 = Real.sqrt 1 := by norm_num
      _ ≤ Real.sqrt ((x - 2) ^ 2 + y ^ 2) := Real.sqrt_le_sqrt hrad

theorem gap2 :
    IsGreatest {d : ℝ | ∃ p, OnUnitCircle p ∧ d = distance p} 3 := by
  constructor
  · refine ⟨((-1 : ℝ), (0 : ℝ)), ?_, ?_⟩
    · norm_num [OnUnitCircle]
    · norm_num [distance, sqrt_nine]
  · rintro d ⟨⟨x, y⟩, hcircle, rfl⟩
    change x ^ 2 + y ^ 2 = 1 at hcircle
    change Real.sqrt ((x - 2) ^ 2 + y ^ 2) ≤ 3
    have hx := unitCircle_first_bounds hcircle
    have hrad : (x - 2) ^ 2 + y ^ 2 ≤ 9 := by
      nlinarith
    calc
      Real.sqrt ((x - 2) ^ 2 + y ^ 2) ≤ Real.sqrt 9 := Real.sqrt_le_sqrt hrad
      _ = 3 := sqrt_nine

theorem gap3 (x : ℝ) :
    distanceSquared x = 5 - 4 * x := by
  rfl

theorem gap4 (x : ℝ) :
    deriv distanceSquared x = -4 := by
  have h : HasDerivAt distanceSquared (-4) x := by
    simpa only [distanceSquared, zero_mul, zero_add, mul_one, zero_sub] using
      ((hasDerivAt_const (x : ℝ) (5 : ℝ)).sub
        ((hasDerivAt_const (x : ℝ) (4 : ℝ)).mul (hasDerivAt_id x)))
  exact h.deriv

theorem gap5 :
    (-4 : ℝ) < 0 := by
  norm_num

theorem gap6 (x : ℝ) :
    deriv distanceSquared x < 0 := by
  rw [gap4]
  exact gap5

theorem gap7 :
    StrictAnti distanceSquared := by
  intro a b hab
  unfold distanceSquared
  linarith

theorem gap8 :
    Real.sqrt (distanceSquared (-1)) = 3 := by
  norm_num [distanceSquared, sqrt_nine]

theorem gap9 :
    Real.sqrt (distanceSquared 1) = 1 := by
  norm_num [distanceSquared]

end

end ProofGap.Exercise1575
