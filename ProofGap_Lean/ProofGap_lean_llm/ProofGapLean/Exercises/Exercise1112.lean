import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace ProofGap.Exercise1112

noncomputable section

def y (x : ℝ) : ℝ := x / Real.sqrt (1 - x ^ 2)

def secondDeriv (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv (fun t => deriv f t) x

def threeHalves (x : ℝ) : ℝ := Real.rpow x (3 / 2 : ℝ)
def fiveHalves (x : ℝ) : ℝ := Real.rpow x (5 / 2 : ℝ)

private lemma threeHalves_eq_mul_sqrt (u : ℝ) (hu : 0 < u) :
    threeHalves u = u * Real.sqrt u := by
  unfold threeHalves
  change u ^ (3 / 2 : ℝ) = u * Real.sqrt u
  rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num]
  rw [Real.rpow_add hu, Real.rpow_one, ← Real.sqrt_eq_rpow]

theorem gap1 (x : ℝ) (hx : |x| < 1) :
    deriv y x =
      (Real.sqrt (1 - x ^ 2) + x ^ 2 / Real.sqrt (1 - x ^ 2)) /
        (1 - x ^ 2) := by
  have hx2 : x ^ 2 < 1 := by
    have h := (sq_lt_sq₀ (abs_nonneg x) zero_le_one).2 hx
    simpa [sq_abs] using h
  have hq : 0 < 1 - x ^ 2 := sub_pos.mpr hx2
  have hs0 : Real.sqrt (1 - x ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hq)
  have hs2 : Real.sqrt (1 - x ^ 2) ^ 2 = 1 - x ^ 2 :=
    Real.sq_sqrt hq.le
  have hinner :
      HasDerivAt (fun z : ℝ => 1 - z ^ 2) (-2 * x) x := by
    convert HasDerivAt.sub (hasDerivAt_const x (1 : ℝ))
      ((hasDerivAt_id x).pow 2) using 1 <;>
      simp only [id_eq] <;> ring
  have hsqrt :
      HasDerivAt (fun z : ℝ => Real.sqrt (1 - z ^ 2))
        (-x / Real.sqrt (1 - x ^ 2)) x := by
    convert (Real.hasDerivAt_sqrt hq.ne').comp x hinner using 1 <;>
      field_simp [hs0] <;> ring
  unfold y
  convert (HasDerivAt.div (hasDerivAt_id x) hsqrt hs0).deriv using 1 <;>
    simp only [id_eq] <;>
    field_simp [hs0, hq.ne'] <;> rw [hs2] <;> ring

theorem gap2 (x : ℝ) (hx : |x| < 1) :
    (Real.sqrt (1 - x ^ 2) + x ^ 2 / Real.sqrt (1 - x ^ 2)) /
        (1 - x ^ 2) =
      1 / threeHalves (1 - x ^ 2) := by
  have hx2 : x ^ 2 < 1 := by
    have h := (sq_lt_sq₀ (abs_nonneg x) zero_le_one).2 hx
    simpa [sq_abs] using h
  have hq : 0 < 1 - x ^ 2 := sub_pos.mpr hx2
  have hs0 : Real.sqrt (1 - x ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hq)
  have hs2 : Real.sqrt (1 - x ^ 2) ^ 2 = 1 - x ^ 2 :=
    Real.sq_sqrt hq.le
  rw [threeHalves_eq_mul_sqrt (1 - x ^ 2) hq]
  field_simp [hq.ne', hs0] <;> rw [hs2] <;> ring

theorem gap3 (x : ℝ) (hx : |x| < 1) :
    deriv y x = 1 / threeHalves (1 - x ^ 2) := by
  rw [gap1 x hx, gap2 x hx]

theorem gap4 (x : ℝ) (hx : |x| < 1) :
    secondDeriv y x =
      (3 / 2 : ℝ) * 2 * x * (1 / fiveHalves (1 - x ^ 2)) := by
  have hx2 : x ^ 2 < 1 := by
    have h := (sq_lt_sq₀ (abs_nonneg x) zero_le_one).2 hx
    simpa [sq_abs] using h
  have hq : 0 < 1 - x ^ 2 := sub_pos.mpr hx2
  have hinner :
      HasDerivAt (fun z : ℝ => 1 - z ^ 2) (-2 * x) x := by
    convert HasDerivAt.sub (hasDerivAt_const x (1 : ℝ))
      ((hasDerivAt_id x).pow 2) using 1 <;>
      simp only [id_eq] <;> ring
  have hgraw :
      HasDerivAt
        (fun z : ℝ => (1 - z ^ 2) ^ (-3 / 2 : ℝ))
        ((-3 / 2 : ℝ) * (1 - x ^ 2) ^ (-5 / 2 : ℝ) *
          (-2 * x)) x := by
    convert
      (Real.hasDerivAt_rpow_const
        (x := 1 - x ^ 2) (p := (-3 / 2 : ℝ))
        (Or.inl hq.ne')).comp x hinner using 1 <;> ring
  have hneg :
      (1 - x ^ 2) ^ (-5 / 2 : ℝ) =
        (Real.rpow (1 - x ^ 2) (5 / 2 : ℝ))⁻¹ := by
    rw [← Real.rpow_eq_pow]
    rw [show (-5 / 2 : ℝ) = -(5 / 2 : ℝ) by ring]
    exact Real.rpow_neg hq.le (5 / 2 : ℝ)
  have hg :
      HasDerivAt
        (fun z : ℝ => (1 - z ^ 2) ^ (-3 / 2 : ℝ))
        ((3 / 2 : ℝ) * 2 * x *
          (1 / fiveHalves (1 - x ^ 2))) x := by
    unfold fiveHalves
    convert hgraw using 1
    rw [hneg]
    ring
  have hev : ∀ᶠ z in nhds x, |z| < 1 := by
    exact (isOpen_lt continuous_abs continuous_const).mem_nhds hx
  have heq :
      (fun z : ℝ => deriv y z) =ᶠ[nhds x]
        (fun z : ℝ => (1 - z ^ 2) ^ (-3 / 2 : ℝ)) := by
    filter_upwards [hev] with z hz
    have hz2 : z ^ 2 < 1 := by
      have h := (sq_lt_sq₀ (abs_nonneg z) zero_le_one).2 hz
      simpa [sq_abs] using h
    have hzq : 0 < 1 - z ^ 2 := sub_pos.mpr hz2
    calc
      deriv y z = 1 / threeHalves (1 - z ^ 2) := gap3 z hz
      _ = (1 - z ^ 2) ^ (-3 / 2 : ℝ) := by
        unfold threeHalves
        rw [one_div, ← Real.rpow_eq_pow]
        rw [show (-3 / 2 : ℝ) = -(3 / 2 : ℝ) by ring]
        exact (Real.rpow_neg hzq.le (3 / 2 : ℝ)).symm
  unfold secondDeriv
  exact (hg.congr_of_eventuallyEq heq).deriv

theorem gap5 (x : ℝ) (hx : |x| < 1) :
    (3 / 2 : ℝ) * 2 * x * (1 / fiveHalves (1 - x ^ 2)) =
      3 * x / fiveHalves (1 - x ^ 2) := by ring

theorem gap6 (x : ℝ) (hx : |x| < 1) :
    secondDeriv y x = 3 * x / fiveHalves (1 - x ^ 2) := by
  rw [gap4 x hx, gap5 x hx]

end

end ProofGap.Exercise1112
