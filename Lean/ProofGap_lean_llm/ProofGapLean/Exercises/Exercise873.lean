import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise873

noncomputable section

/-- The signed real cube root, valid for negative as well as positive inputs. -/
def cubeRoot (x : ℝ) : ℝ :=
  Real.sign x * Real.rpow |x| (1 / 3 : ℝ)

def cot (x : ℝ) : ℝ := Real.cos x / Real.sin x
def csc (x : ℝ) : ℝ := 1 / Real.sin x

def y (x : ℝ) : ℝ :=
  4 * cubeRoot (cot x ^ 2) + cubeRoot (cot x ^ 8)

def expandedDerivative (x : ℝ) : ℝ :=
  (8 / 3 : ℝ) * (1 / cubeRoot (cot x)) * (-(csc x ^ 2)) +
    (8 / 3 : ℝ) * cubeRoot (cot x) ^ 5 * (-(csc x ^ 2))

def finalDerivative (x : ℝ) : ℝ :=
  -8 / (3 * Real.sin x ^ 4 * cubeRoot (cot x))

/-- Source: `proof_gap/exercise_873/1.txt`; interpret all fractional powers
through a signed cube root and exclude the nondifferentiable zero of `cot`. -/
private theorem rpow_one_third_cube (x : ℝ) (hx : 0 ≤ x) :
    (Real.rpow x (1 / 3 : ℝ)) ^ 3 = x := by
  have hmul :
      Real.rpow x ((1 / 3 : ℝ) * (3 : ℝ)) =
        Real.rpow (Real.rpow x (1 / 3 : ℝ)) (3 : ℝ) := by
    exact Real.rpow_mul hx (1 / 3 : ℝ) (3 : ℝ)
  calc
    (Real.rpow x (1 / 3 : ℝ)) ^ 3 =
        Real.rpow (Real.rpow x (1 / 3 : ℝ)) (3 : ℝ) := by
      symm
      apply Real.rpow_natCast
    _ = Real.rpow x ((1 / 3 : ℝ) * (3 : ℝ)) := hmul.symm
    _ = x := by norm_num

private theorem cubeRoot_pow_three (x : ℝ) : cubeRoot x ^ 3 = x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [cubeRoot, Real.sign_of_neg hx, abs_of_neg hx]
    change (-1 * Real.rpow (-x) (1 / 3 : ℝ)) ^ 3 = x
    calc
      (-1 * Real.rpow (-x) (1 / 3 : ℝ)) ^ 3 =
          -(Real.rpow (-x) (1 / 3 : ℝ) ^ 3) := by ring
      _ = -(-x) := by
        rw [rpow_one_third_cube (-x) (le_of_lt (neg_pos.mpr hx))]
      _ = x := by ring
  · norm_num [cubeRoot]
  · rw [cubeRoot, Real.sign_of_pos hx, abs_of_pos hx]
    simp only [one_mul]
    exact rpow_one_third_cube x (le_of_lt hx)

private theorem cubeRoot_ne_zero {x : ℝ} (hx : x ≠ 0) : cubeRoot x ≠ 0 := by
  intro hroot
  apply hx
  have hc := cubeRoot_pow_three x
  rw [hroot] at hc
  simpa using hc.symm

private theorem cubeRoot_sq (x : ℝ) :
    cubeRoot (x ^ 2) = cubeRoot x ^ 2 := by
  by_cases hx : x = 0
  · subst x
    norm_num [cubeRoot]
  · let a := cubeRoot (x ^ 2)
    let b := cubeRoot x ^ 2
    change a = b
    have ha : 0 ≤ a := by
      dsimp [a]
      have hx2 : 0 < x ^ 2 := sq_pos_of_ne_zero hx
      rw [cubeRoot, Real.sign_of_pos hx2, abs_of_pos hx2]
      simp only [one_mul]
      exact Real.rpow_nonneg (le_of_lt hx2) _
    have hb : 0 ≤ b := by
      dsimp [b]
      exact sq_nonneg (cubeRoot x)
    have hb0 : b ≠ 0 := by
      dsimp [b]
      exact pow_ne_zero 2 (cubeRoot_ne_zero hx)
    have hc : a ^ 3 = b ^ 3 := by
      calc
        a ^ 3 = x ^ 2 := by
          dsimp [a]
          exact cubeRoot_pow_three (x ^ 2)
        _ = (cubeRoot x ^ 3) ^ 2 := by rw [cubeRoot_pow_three]
        _ = b ^ 3 := by
          dsimp [b]
          ring
    have hfac : (a - b) * (a ^ 2 + a * b + b ^ 2) = 0 := by
      calc
        (a - b) * (a ^ 2 + a * b + b ^ 2) = a ^ 3 - b ^ 3 := by ring
        _ = 0 := by rw [hc]; ring
    have hq : 0 < a ^ 2 + a * b + b ^ 2 := by
      have hb2 : 0 < b ^ 2 := sq_pos_of_ne_zero hb0
      have hab : 0 ≤ a * b := mul_nonneg ha hb
      nlinarith [sq_nonneg a]
    rcases mul_eq_zero.mp hfac with hab | hzero
    · exact sub_eq_zero.mp hab
    · exact (ne_of_gt hq hzero).elim

private theorem cubeRoot_pow_eight (x : ℝ) :
    cubeRoot (x ^ 8) = cubeRoot x ^ 8 := by
  calc
    cubeRoot (x ^ 8) = cubeRoot ((x ^ 4) ^ 2) := by
      congr 1
      ring
    _ = cubeRoot (x ^ 4) ^ 2 := cubeRoot_sq (x ^ 4)
    _ = (cubeRoot (x ^ 2) ^ 2) ^ 2 := by
      rw [show x ^ 4 = (x ^ 2) ^ 2 by ring, cubeRoot_sq]
    _ = ((cubeRoot x ^ 2) ^ 2) ^ 2 := by rw [cubeRoot_sq]
    _ = cubeRoot x ^ 8 := by ring

private theorem hasDerivAt_cubeRoot_of_pos (x : ℝ) (hx : 0 < x) :
    HasDerivAt cubeRoot (1 / (3 * cubeRoot x ^ 2)) x := by
  let r : ℝ := Real.rpow x (1 / 3 : ℝ)
  have hroot : cubeRoot x = r := by
    simp [cubeRoot, Real.sign_of_pos hx, abs_of_pos hx, r]
  have hr0 : r ≠ 0 := by
    rw [← hroot]
    exact cubeRoot_ne_zero (ne_of_gt hx)
  have hcube : r ^ 3 = x := by
    dsimp [r]
    exact rpow_one_third_cube x (le_of_lt hx)
  have hp :
      HasDerivAt (fun z : ℝ => Real.rpow z (1 / 3 : ℝ))
        ((1 / 3 : ℝ) * Real.rpow x ((1 / 3 : ℝ) - 1)) x :=
    Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hx))
  have heq :
      (fun z : ℝ => cubeRoot z) =ᶠ[nhds x]
        (fun z : ℝ => Real.rpow z (1 / 3 : ℝ)) := by
    filter_upwards [Ioi_mem_nhds hx] with z hz
    have hz' : 0 < z := hz
    rw [cubeRoot, Real.sign_of_pos hz', abs_of_pos hz']
    simp only [one_mul]
  have hcraw := heq.hasDerivAt_iff.mpr hp
  have hsub :
      Real.rpow x ((1 / 3 : ℝ) - 1) = r / x := by
    dsimp [r]
    rw [Real.rpow_sub hx, Real.rpow_one]
  have hraw :
      (1 / 3 : ℝ) * Real.rpow x ((1 / 3 : ℝ) - 1) =
        1 / (3 * cubeRoot x ^ 2) := by
    rw [hsub, hroot]
    calc
      (1 / 3 : ℝ) * (r / x) =
          (1 / 3 : ℝ) * (r / r ^ 3) := by rw [← hcube]
      _ = 1 / (3 * r ^ 2) := by
        field_simp [hr0]
  exact hraw ▸ hcraw

theorem gap1 (x : ℝ) (hsin : Real.sin x ≠ 0) (hcot : cot x ≠ 0) :
    deriv y x = expandedDerivative x := by
  have hcot' : HasDerivAt cot (-(csc x ^ 2)) x := by
    unfold cot csc
    convert (Real.hasDerivAt_cos x).div (Real.hasDerivAt_sin x) hsin using 1
    field_simp [hsin] <;>
      nlinarith [Real.sin_sq_add_cos_sq x]
  have hx2 : 0 < cot x ^ 2 := sq_pos_of_ne_zero hcot
  have hx8 : 0 < cot x ^ 8 := by
    rw [show cot x ^ 8 = (cot x ^ 2) ^ 4 by ring]
    exact pow_pos hx2 4
  have hroot2 :=
    (hasDerivAt_cubeRoot_of_pos (cot x ^ 2) hx2).comp x (hcot'.pow 2)
  have hroot8 :=
    (hasDerivAt_cubeRoot_of_pos (cot x ^ 8) hx8).comp x (hcot'.pow 8)
  have hpoly := (hroot2.const_mul 4).add hroot8
  have hpoly' : HasDerivAt y (expandedDerivative x) x := by
    unfold y
    convert hpoly using 1
    unfold expandedDerivative
    rw [cubeRoot_sq, cubeRoot_pow_eight]
    set r := cubeRoot (cot x) with hr
    have hr0 : r ≠ 0 := by
      rw [hr]
      exact cubeRoot_ne_zero hcot
    have hu : cot x = r ^ 3 := by
      rw [hr, cubeRoot_pow_three]
    rw [hu]
    field_simp [hr0] <;> ring
  exact hpoly'.deriv

/-- Source: `proof_gap/exercise_873/2.txt`; use the signed real cube root and
retain the source function's domain. -/
theorem gap2 (x : ℝ) (hsin : Real.sin x ≠ 0) (hcot : cot x ≠ 0) :
    expandedDerivative x = finalDerivative x := by
  have hroot0 : cubeRoot (cot x) ≠ 0 := cubeRoot_ne_zero hcot
  have hrel : cubeRoot (cot x) ^ 3 * Real.sin x = Real.cos x := by
    rw [cubeRoot_pow_three]
    unfold cot
    field_simp [hsin]
  have hsq :
      cubeRoot (cot x) ^ 6 * Real.sin x ^ 2 = Real.cos x ^ 2 := by
    calc
      cubeRoot (cot x) ^ 6 * Real.sin x ^ 2 =
          (cubeRoot (cot x) ^ 3 * Real.sin x) ^ 2 := by ring
      _ = Real.cos x ^ 2 := by rw [hrel]
  unfold expandedDerivative finalDerivative csc
  field_simp [hsin, hroot0] <;>
    nlinarith [Real.sin_sq_add_cos_sq x, hsq]

/-- Source: `proof_gap/exercise_873/3.txt`; use the signed real cube root and
exclude singular/nondifferentiable points. -/
theorem gap3 (x : ℝ) (hsin : Real.sin x ≠ 0) (hcot : cot x ≠ 0) :
    deriv y x = finalDerivative x := by
  exact (gap1 x hsin hcot).trans (gap2 x hsin hcot)

end

end ProofGap.Exercise873
