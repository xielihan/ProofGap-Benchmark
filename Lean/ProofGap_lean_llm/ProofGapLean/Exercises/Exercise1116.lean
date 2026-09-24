import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise1116

noncomputable section

def y (x : ℝ) : ℝ := Real.arcsin x / Real.sqrt (1 - x ^ 2)

def secondDeriv (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv (fun t => deriv f t) x

def threeHalves (x : ℝ) : ℝ := Real.rpow x (3 / 2 : ℝ)
def fiveHalves (x : ℝ) : ℝ := Real.rpow x (5 / 2 : ℝ)

def expanded (x : ℝ) : ℝ :=
  2 * x / (1 - x ^ 2) ^ 2 +
    (((x / Real.sqrt (1 - x ^ 2) + Real.arcsin x) *
          threeHalves (1 - x ^ 2) +
        3 * x ^ 2 * Real.sqrt (1 - x ^ 2) * Real.arcsin x) /
      (1 - x ^ 2) ^ 3)

def finalForm (x : ℝ) : ℝ :=
  3 * x / (1 - x ^ 2) ^ 2 +
    (1 + 2 * x ^ 2) * Real.arcsin x / fiveHalves (1 - x ^ 2)

private lemma interior_base_pos (x : ℝ) (hx : |x| < 1) :
    0 < 1 - x ^ 2 := by
  rcases abs_lt.mp hx with ⟨hlo, hhi⟩
  have hleft : 0 < 1 + x := by linarith
  have hright : 0 < 1 - x := by linarith
  nlinarith [mul_pos hleft hright]

private lemma sqrt_cube_eq_mul (u : ℝ) (hu : 0 ≤ u) :
    Real.sqrt u ^ 3 = u * Real.sqrt u := by
  calc
    Real.sqrt u ^ 3 = Real.sqrt u ^ 2 * Real.sqrt u := by ring
    _ = u * Real.sqrt u := by rw [Real.sq_sqrt hu]

private lemma threeHalves_eq_mul_sqrt (u : ℝ) (hu : 0 < u) :
    threeHalves u = u * Real.sqrt u := by
  unfold threeHalves
  have hthree :
      Real.rpow u (3 / 2 : ℝ) =
        Real.exp (Real.log u * (3 / 2 : ℝ)) :=
    Real.rpow_def_of_pos hu (3 / 2 : ℝ)
  have hhalf :
      Real.rpow u (1 / 2 : ℝ) =
        Real.exp (Real.log u * (1 / 2 : ℝ)) :=
    Real.rpow_def_of_pos hu (1 / 2 : ℝ)
  have hsqrt :
      Real.sqrt u = Real.exp (Real.log u * (1 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow]
    exact hhalf
  rw [hthree, hsqrt]
  calc
    Real.exp (Real.log u * (3 / 2 : ℝ)) =
        Real.exp (Real.log u) *
          Real.exp (Real.log u * (1 / 2 : ℝ)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ = u * Real.exp (Real.log u * (1 / 2 : ℝ)) := by
      rw [Real.exp_log hu]

private lemma fiveHalves_eq_sq_mul_sqrt (u : ℝ) (hu : 0 < u) :
    fiveHalves u = u ^ 2 * Real.sqrt u := by
  unfold fiveHalves
  have hfive :
      Real.rpow u (5 / 2 : ℝ) =
        Real.exp (Real.log u * (5 / 2 : ℝ)) :=
    Real.rpow_def_of_pos hu (5 / 2 : ℝ)
  have hhalf :
      Real.rpow u (1 / 2 : ℝ) =
        Real.exp (Real.log u * (1 / 2 : ℝ)) :=
    Real.rpow_def_of_pos hu (1 / 2 : ℝ)
  have hsqrt :
      Real.sqrt u = Real.exp (Real.log u * (1 / 2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow]
    exact hhalf
  rw [hfive, hsqrt]
  calc
    Real.exp (Real.log u * (5 / 2 : ℝ)) =
        Real.exp (Real.log u) ^ 2 *
          Real.exp (Real.log u * (1 / 2 : ℝ)) := by
      rw [pow_two, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ = u ^ 2 * Real.exp (Real.log u * (1 / 2 : ℝ)) := by
      rw [Real.exp_log hu]

private def firstForm (x : ℝ) : ℝ :=
  1 / (1 - x ^ 2) +
    x * Real.arcsin x /
      ((1 - x ^ 2) * Real.sqrt (1 - x ^ 2))

private theorem hasDerivAt_y_firstForm (x : ℝ) (hx : |x| < 1) :
    HasDerivAt y (firstForm x) x := by
  unfold y firstForm
  have hu := interior_base_pos x hx
  rcases abs_lt.mp hx with ⟨hlo, hhi⟩
  have hu' : HasDerivAt (fun t : ℝ => 1 - t ^ 2) (-2 * x) x := by
    simpa [id, pow_two, mul_comm, mul_left_comm, mul_assoc] using
      (hasDerivAt_const (x := x) (c := (1 : ℝ))).sub
        ((hasDerivAt_id x).pow 2)
  have ha :
      HasDerivAt Real.arcsin
        (1 / Real.sqrt (1 - x ^ 2)) x :=
    Real.hasDerivAt_arcsin (by linarith) (by linarith)
  have hs :
      HasDerivAt (fun t : ℝ => Real.sqrt (1 - t ^ 2))
        (1 / (2 * Real.sqrt (1 - x ^ 2)) * (-2 * x)) x := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_sqrt hu.ne').comp x hu'
  have hs0 : Real.sqrt (1 - x ^ 2) ≠ 0 :=
    (Real.sqrt_pos.2 hu).ne'
  have hs_sq : Real.sqrt (1 - x ^ 2) ^ 2 = 1 - x ^ 2 :=
    Real.sq_sqrt hu.le
  have hs_cube : Real.sqrt (1 - x ^ 2) ^ 3 =
      (1 - x ^ 2) * Real.sqrt (1 - x ^ 2) :=
    sqrt_cube_eq_mul (1 - x ^ 2) hu.le
  convert ha.div hs hs0 using 1 <;>
    field_simp [hu.ne', hs0] <;>
    ring_nf
  all_goals simp only [hs_cube, hs_sq]
  all_goals ring

private theorem hasDerivAt_firstForm (x : ℝ) (hx : |x| < 1) :
    HasDerivAt firstForm (expanded x) x := by
  unfold firstForm
  have hu := interior_base_pos x hx
  rcases abs_lt.mp hx with ⟨hlo, hhi⟩
  have hu' : HasDerivAt (fun t : ℝ => 1 - t ^ 2) (-2 * x) x := by
    simpa [id, pow_two, mul_comm, mul_left_comm, mul_assoc] using
      (hasDerivAt_const (x := x) (c := (1 : ℝ))).sub
        ((hasDerivAt_id x).pow 2)
  have ha :
      HasDerivAt Real.arcsin
        (1 / Real.sqrt (1 - x ^ 2)) x :=
    Real.hasDerivAt_arcsin (by linarith) (by linarith)
  have hs :
      HasDerivAt (fun t : ℝ => Real.sqrt (1 - t ^ 2))
        (1 / (2 * Real.sqrt (1 - x ^ 2)) * (-2 * x)) x := by
    simpa [Function.comp_def] using
      (Real.hasDerivAt_sqrt hu.ne').comp x hu'
  have hs0 : Real.sqrt (1 - x ^ 2) ≠ 0 :=
    (Real.sqrt_pos.2 hu).ne'
  have hs_sq : Real.sqrt (1 - x ^ 2) ^ 2 = 1 - x ^ 2 :=
    Real.sq_sqrt hu.le
  have hs_cube : Real.sqrt (1 - x ^ 2) ^ 3 =
      (1 - x ^ 2) * Real.sqrt (1 - x ^ 2) :=
    sqrt_cube_eq_mul (1 - x ^ 2) hu.le
  have hs_four : Real.sqrt (1 - x ^ 2) ^ 4 =
      (1 - x ^ 2) ^ 2 := by
    calc
      Real.sqrt (1 - x ^ 2) ^ 4 =
          (Real.sqrt (1 - x ^ 2) ^ 2) ^ 2 := by ring
      _ = (1 - x ^ 2) ^ 2 := by rw [hs_sq]
  have hrecip :=
    (hasDerivAt_const (x := x) (c := (1 : ℝ))).div hu' hu.ne'
  have hnum := (hasDerivAt_id x).mul ha
  have hden := hu'.mul hs
  convert hrecip.add
    (hnum.div hden (mul_ne_zero hu.ne' hs0)) using 1
  unfold expanded
  rw [threeHalves_eq_mul_sqrt (1 - x ^ 2) hu]
  simp only [Pi.mul_apply, id_eq]
  field_simp [hu.ne', hs0] <;> ring_nf
  all_goals simp only [hs_cube, hs_four, hs_sq]
  all_goals ring

theorem gap1 (x : ℝ) (hx : |x| < 1) :
    deriv y x =
      1 / (1 - x ^ 2) +
        x * Real.arcsin x / threeHalves (1 - x ^ 2) := by
  have hu := interior_base_pos x hx
  have h := (hasDerivAt_y_firstForm x hx).deriv
  rw [h]
  unfold firstForm
  rw [threeHalves_eq_mul_sqrt (1 - x ^ 2) hu]

theorem gap2 (x : ℝ) (hx : |x| < 1) :
    secondDeriv y x = expanded x := by
  unfold secondDeriv
  have hmem : {t : ℝ | |t| < 1} ∈ nhds x :=
    (isOpen_lt continuous_abs continuous_const).mem_nhds hx
  have heq :
      (fun t : ℝ => deriv y t) =ᶠ[nhds x] firstForm := by
    refine Filter.mem_of_superset hmem ?_
    intro t ht
    exact (hasDerivAt_y_firstForm t ht).deriv
  exact ((hasDerivAt_firstForm x hx).congr_of_eventuallyEq heq).deriv

theorem gap3 (x : ℝ) (hx : |x| < 1) :
    expanded x = finalForm x := by
  have hu := interior_base_pos x hx
  have hs0 : Real.sqrt (1 - x ^ 2) ≠ 0 :=
    (Real.sqrt_pos.2 hu).ne'
  have hs_sq : Real.sqrt (1 - x ^ 2) ^ 2 = 1 - x ^ 2 :=
    Real.sq_sqrt hu.le
  have hs_cube : Real.sqrt (1 - x ^ 2) ^ 3 =
      (1 - x ^ 2) * Real.sqrt (1 - x ^ 2) :=
    sqrt_cube_eq_mul (1 - x ^ 2) hu.le
  unfold expanded finalForm
  rw [threeHalves_eq_mul_sqrt (1 - x ^ 2) hu,
    fiveHalves_eq_sq_mul_sqrt (1 - x ^ 2) hu]
  field_simp [hu.ne', hs0] <;> ring_nf
  all_goals simp only [hs_cube, hs_sq]
  all_goals ring

theorem gap4 (x : ℝ) (hx : |x| < 1) :
    secondDeriv y x = finalForm x := by
  exact (gap2 x hx).trans (gap3 x hx)

end

end ProofGap.Exercise1116
