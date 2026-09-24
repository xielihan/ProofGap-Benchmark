import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

namespace ProofGap.Exercise1070

noncomputable section

def cubeRoot (x : ℝ) : ℝ :=
  Real.sign x * Real.rpow |x| (1 / 3 : ℝ)

def twoThirdPower (x : ℝ) : ℝ := cubeRoot x ^ 2

def astroidEquation (a x y : ℝ) : Prop :=
  twoThirdPower x + twoThirdPower y = twoThirdPower a

def xIntercept (x₀ y₀ : ℝ) : ℝ :=
  x₀ + cubeRoot (x₀ * y₀ ^ 2)

def yIntercept (x₀ y₀ : ℝ) : ℝ :=
  y₀ + cubeRoot (x₀ ^ 2 * y₀)

def interceptLength (x₀ y₀ : ℝ) : ℝ :=
  Real.sqrt (xIntercept x₀ y₀ ^ 2 + yIntercept x₀ y₀ ^ 2)

def tangentLineAt (x₀ y₀ : ℝ) : Set (ℝ × ℝ) :=
  {p | p.2 - y₀ = -cubeRoot (y₀ / x₀) * (p.1 - x₀)}

private theorem rpow_third_cube (x : ℝ) (hx : 0 ≤ x) :
    Real.rpow x (1 / 3 : ℝ) ^ 3 = x := by
  calc
    Real.rpow x (1 / 3 : ℝ) ^ 3 =
        Real.rpow (Real.rpow x (1 / 3 : ℝ)) (3 : ℝ) := by
      exact (Real.rpow_natCast _ 3).symm
    _ = Real.rpow x ((1 / 3 : ℝ) * 3) := by
      exact (Real.rpow_mul hx _ _).symm
    _ = x := by norm_num

private theorem cubeRoot_cube (x : ℝ) : cubeRoot x ^ 3 = x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [cubeRoot, Real.sign_of_neg hx, abs_of_neg hx]
    change (-1 * Real.rpow (-x) (1 / 3 : ℝ)) ^ 3 = x
    rw [show (-1 * Real.rpow (-x) (1 / 3 : ℝ)) ^ 3 =
      -(Real.rpow (-x) (1 / 3 : ℝ) ^ 3) by ring,
      rpow_third_cube (-x) (by linarith)]
    ring
  · norm_num [cubeRoot]
  · rw [cubeRoot, Real.sign_of_pos hx, abs_of_pos hx, one_mul]
    exact rpow_third_cube x hx.le

private theorem cube_pow_injective {u v : ℝ} (h : u ^ 3 = v ^ 3) : u = v :=
  (show Odd 3 by decide).strictMono_pow.injective h

private theorem cubeRoot_mul (u v : ℝ) :
    cubeRoot (u * v) = cubeRoot u * cubeRoot v := by
  apply cube_pow_injective
  rw [cubeRoot_cube, mul_pow, cubeRoot_cube, cubeRoot_cube]

private theorem cubeRoot_div (u v : ℝ) (hv : v ≠ 0) :
    cubeRoot (u / v) = cubeRoot u / cubeRoot v := by
  apply cube_pow_injective
  rw [cubeRoot_cube, div_pow, cubeRoot_cube, cubeRoot_cube]

private theorem cubeRoot_sq (u : ℝ) :
    cubeRoot (u ^ 2) = cubeRoot u ^ 2 := by
  apply cube_pow_injective
  calc
    cubeRoot (u ^ 2) ^ 3 = u ^ 2 := cubeRoot_cube _
    _ = (cubeRoot u ^ 3) ^ 2 := by rw [cubeRoot_cube]
    _ = (cubeRoot u ^ 2) ^ 3 := by ring

private theorem cubeRoot_pow_six (u : ℝ) :
    cubeRoot u ^ 6 = u ^ 2 := by
  rw [show cubeRoot u ^ 6 = (cubeRoot u ^ 3) ^ 2 by ring, cubeRoot_cube]

private theorem twoThird_cube (u : ℝ) :
    twoThirdPower u ^ 3 = u ^ 2 := by
  unfold twoThirdPower
  rw [show (cubeRoot u ^ 2) ^ 3 = cubeRoot u ^ 6 by ring,
    cubeRoot_pow_six]

private theorem twoThird_mul (u v : ℝ) :
    twoThirdPower (u * v) = twoThirdPower u * twoThirdPower v := by
  unfold twoThirdPower
  rw [cubeRoot_mul]
  ring

private theorem cubeRoot_ne_zero {u : ℝ} (hu : u ≠ 0) : cubeRoot u ≠ 0 := by
  intro h
  have hc := cubeRoot_cube u
  rw [h] at hc
  apply hu
  simpa using hc.symm

private theorem hasDerivAt_twoThird {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt twoThirdPower (2 / (3 * cubeRoot u)) u := by
  have hu2 : 0 < u ^ 2 := sq_pos_of_ne_zero hu
  have hsquare : HasDerivAt (fun z : ℝ => z ^ 2) (2 * u) u := by
    simpa [id, mul_comm] using (hasDerivAt_id u).pow 2
  have houter :
      HasDerivAt (fun w : ℝ => Real.rpow w (1 / 3 : ℝ))
        ((1 / 3 : ℝ) * Real.rpow (u ^ 2) ((1 / 3 : ℝ) - 1))
        (u ^ 2) :=
    Real.hasDerivAt_rpow_const (Or.inl hu2.ne')
  have hraw :
      HasDerivAt (fun z : ℝ => Real.rpow (z ^ 2) (1 / 3 : ℝ))
        (((1 / 3 : ℝ) * Real.rpow (u ^ 2) ((1 / 3 : ℝ) - 1)) *
          (2 * u)) u := by
    convert
      houter.comp_of_eq u hsquare rfl
      using 1 <;> simp [id, pow_two] <;> ring
  have hfun :
      twoThirdPower = fun z : ℝ => Real.rpow (z ^ 2) (1 / 3 : ℝ) := by
    funext z
    unfold twoThirdPower
    rw [← cubeRoot_sq]
    have hz2 : 0 ≤ z ^ 2 := sq_nonneg z
    by_cases hz : z = 0
    · subst z
      norm_num [cubeRoot]
    · simp [cubeRoot, Real.sign_of_pos (sq_pos_of_ne_zero hz),
        abs_of_nonneg hz2]
  rw [hfun]
  convert hraw using 1
  have hr1 :
      Real.rpow (u ^ 2) (1 / 3 : ℝ) = cubeRoot u ^ 2 := by
    rw [← cubeRoot_sq]
    simp [cubeRoot, Real.sign_of_pos hu2, abs_of_pos hu2]
  have hr2 :
      Real.rpow (u ^ 2) (2 / 3 : ℝ) = (cubeRoot u ^ 2) ^ 2 := by
    calc
      Real.rpow (u ^ 2) (2 / 3 : ℝ) =
          Real.rpow (u ^ 2) ((1 / 3 : ℝ) * 2) := by congr 1 <;> ring
      _ = Real.rpow (Real.rpow (u ^ 2) (1 / 3 : ℝ)) (2 : ℝ) :=
        Real.rpow_mul hu2.le _ _
      _ = (cubeRoot u ^ 2) ^ 2 := by
        rw [hr1]
        exact Real.rpow_two _
  have hneg :
      Real.rpow (u ^ 2) (-(2 / 3 : ℝ)) =
        (Real.rpow (u ^ 2) (2 / 3 : ℝ))⁻¹ :=
    Real.rpow_neg hu2.le _
  rw [show (1 / 3 : ℝ) - 1 = -(2 / 3 : ℝ) by ring, hneg, hr2]
  field_simp [cubeRoot_ne_zero hu]
  have hc := cubeRoot_cube u
  nlinarith

theorem gap1 (a : ℝ) (y : ℝ → ℝ) (x : ℝ)
    (hcurve : ∀ t, astroidEquation a t (y t))
    (hdiff : DifferentiableAt ℝ y x) (hx : x ≠ 0) (hy : y x ≠ 0) :
    deriv y x = -cubeRoot (y x / x) := by
  have hxder := hasDerivAt_twoThird hx
  have hyder :=
    (hasDerivAt_twoThird hy).comp x hdiff.hasDerivAt
  have hsum :
      HasDerivAt
        (fun t : ℝ => twoThirdPower t + twoThirdPower (y t))
        (2 / (3 * cubeRoot x) +
          2 / (3 * cubeRoot (y x)) * deriv y x) x := by
    convert hxder.add hyder using 1 <;>
      simp only [Function.comp_apply, Pi.add_apply] <;> ring
  have heq :
      (fun t : ℝ => twoThirdPower t + twoThirdPower (y t)) =
        fun _ : ℝ => twoThirdPower a := by
    funext t
    exact hcurve t
  have hzero :
      HasDerivAt
        (fun t : ℝ => twoThirdPower t + twoThirdPower (y t)) 0 x := by
    rw [heq]
    exact hasDerivAt_const x _
  have hcoeff :
      2 / (3 * cubeRoot x) +
          2 / (3 * cubeRoot (y x)) * deriv y x = 0 :=
    hsum.unique hzero
  rw [cubeRoot_div (y x) x hx]
  field_simp [cubeRoot_ne_zero hx, cubeRoot_ne_zero hy] at hcoeff ⊢
  nlinarith

theorem gap2 (a x y x₀ y₀ : ℝ)
    (hpoint : astroidEquation a x₀ y₀) (hx₀ : x₀ ≠ 0) :
    (x, y) ∈ tangentLineAt x₀ y₀ ↔
      y - y₀ = -cubeRoot (y₀ / x₀) * (x - x₀) := by
  rfl

theorem gap3 (a x₀ y₀ : ℝ)
    (hpoint : astroidEquation a x₀ y₀) (hx₀ : x₀ ≠ 0) :
    xIntercept x₀ y₀ = x₀ + cubeRoot (x₀ * y₀ ^ 2) := by
  rfl

theorem gap4 (a x₀ y₀ : ℝ)
    (hpoint : astroidEquation a x₀ y₀) (hx₀ : x₀ ≠ 0) :
    yIntercept x₀ y₀ = y₀ + cubeRoot (x₀ ^ 2 * y₀) := by
  rfl

theorem gap5 (a x₀ y₀ : ℝ)
    (hpoint : astroidEquation a x₀ y₀) (hx₀ : x₀ ≠ 0) :
    interceptLength x₀ y₀ =
      Real.sqrt (xIntercept x₀ y₀ ^ 2 + yIntercept x₀ y₀ ^ 2) := by
  rfl

theorem gap6 (x₀ y₀ : ℝ) :
    xIntercept x₀ y₀ ^ 2 + yIntercept x₀ y₀ ^ 2 =
      x₀ ^ 2 + y₀ ^ 2 +
        3 * x₀ * cubeRoot (x₀ * y₀ ^ 2) +
        3 * y₀ * cubeRoot (x₀ ^ 2 * y₀) := by
  have hA :
      cubeRoot (x₀ * y₀ ^ 2) ^ 2 =
        y₀ * cubeRoot (x₀ ^ 2 * y₀) := by
    apply cube_pow_injective
    calc
      (cubeRoot (x₀ * y₀ ^ 2) ^ 2) ^ 3 =
          cubeRoot (x₀ * y₀ ^ 2) ^ 6 := by ring
      _ = (x₀ * y₀ ^ 2) ^ 2 := cubeRoot_pow_six _
      _ = y₀ ^ 3 * cubeRoot (x₀ ^ 2 * y₀) ^ 3 := by
        rw [cubeRoot_cube]
        ring
      _ = (y₀ * cubeRoot (x₀ ^ 2 * y₀)) ^ 3 := by ring
  have hB :
      cubeRoot (x₀ ^ 2 * y₀) ^ 2 =
        x₀ * cubeRoot (x₀ * y₀ ^ 2) := by
    apply cube_pow_injective
    calc
      (cubeRoot (x₀ ^ 2 * y₀) ^ 2) ^ 3 =
          cubeRoot (x₀ ^ 2 * y₀) ^ 6 := by ring
      _ = (x₀ ^ 2 * y₀) ^ 2 := cubeRoot_pow_six _
      _ = x₀ ^ 3 * cubeRoot (x₀ * y₀ ^ 2) ^ 3 := by
        rw [cubeRoot_cube]
        ring
      _ = (x₀ * cubeRoot (x₀ * y₀ ^ 2)) ^ 3 := by ring
  unfold xIntercept yIntercept
  calc
    (x₀ + cubeRoot (x₀ * y₀ ^ 2)) ^ 2 +
        (y₀ + cubeRoot (x₀ ^ 2 * y₀)) ^ 2 =
      x₀ ^ 2 + y₀ ^ 2 +
        2 * x₀ * cubeRoot (x₀ * y₀ ^ 2) +
        cubeRoot (x₀ * y₀ ^ 2) ^ 2 +
        2 * y₀ * cubeRoot (x₀ ^ 2 * y₀) +
        cubeRoot (x₀ ^ 2 * y₀) ^ 2 := by ring
    _ = _ := by rw [hA, hB] <;> ring

theorem gap7 (x₀ y₀ : ℝ) :
    xIntercept x₀ y₀ ^ 2 + yIntercept x₀ y₀ ^ 2 =
      x₀ ^ 2 + y₀ ^ 2 +
        3 * cubeRoot (x₀ ^ 2 * y₀ ^ 2) *
          (cubeRoot (x₀ ^ 2) + cubeRoot (y₀ ^ 2)) := by
  have hxterm :
      x₀ * cubeRoot (x₀ * y₀ ^ 2) =
        cubeRoot (x₀ ^ 2 * y₀ ^ 2) * cubeRoot (x₀ ^ 2) := by
    apply cube_pow_injective
    rw [mul_pow, mul_pow, cubeRoot_cube, cubeRoot_cube, cubeRoot_cube]
    ring
  have hyterm :
      y₀ * cubeRoot (x₀ ^ 2 * y₀) =
        cubeRoot (x₀ ^ 2 * y₀ ^ 2) * cubeRoot (y₀ ^ 2) := by
    apply cube_pow_injective
    rw [mul_pow, mul_pow, cubeRoot_cube, cubeRoot_cube, cubeRoot_cube]
    ring
  rw [gap6]
  linear_combination 3 * hxterm + 3 * hyterm

theorem gap8 (a x₀ y₀ : ℝ) (hpoint : astroidEquation a x₀ y₀) :
    xIntercept x₀ y₀ ^ 2 + yIntercept x₀ y₀ ^ 2 =
      x₀ ^ 2 + y₀ ^ 2 + 3 * cubeRoot (a ^ 2 * x₀ ^ 2 * y₀ ^ 2) := by
  have hsum :
      cubeRoot (x₀ ^ 2) + cubeRoot (y₀ ^ 2) = cubeRoot (a ^ 2) := by
    simpa [astroidEquation, twoThirdPower, cubeRoot_sq] using hpoint
  have hprod :
      cubeRoot (x₀ ^ 2 * y₀ ^ 2) * cubeRoot (a ^ 2) =
        cubeRoot (a ^ 2 * x₀ ^ 2 * y₀ ^ 2) := by
    rw [← cubeRoot_mul]
    congr 1
    ring
  rw [gap7, hsum]
  linear_combination 3 * hprod

theorem gap9 (a x₀ y₀ : ℝ) (hpoint : astroidEquation a x₀ y₀) :
    xIntercept x₀ y₀ ^ 2 + yIntercept x₀ y₀ ^ 2 =
      (twoThirdPower a - twoThirdPower y₀) ^ 3 + y₀ ^ 2 +
        3 * twoThirdPower (a * x₀ * y₀) := by
  have hx :
      x₀ ^ 2 = (twoThirdPower a - twoThirdPower y₀) ^ 3 := by
    have hxy :
        twoThirdPower x₀ =
          twoThirdPower a - twoThirdPower y₀ := by
      unfold astroidEquation at hpoint
      linarith
    rw [← twoThird_cube x₀, hxy]
  have hroot :
      cubeRoot (a ^ 2 * x₀ ^ 2 * y₀ ^ 2) =
        twoThirdPower (a * x₀ * y₀) := by
    rw [show a ^ 2 * x₀ ^ 2 * y₀ ^ 2 = (a * x₀ * y₀) ^ 2 by ring,
      cubeRoot_sq]
    rfl
  rw [gap8 a x₀ y₀ hpoint, hroot, hx]

theorem gap10 (a x₀ y₀ : ℝ) (hpoint : astroidEquation a x₀ y₀) :
    xIntercept x₀ y₀ ^ 2 + yIntercept x₀ y₀ ^ 2 =
      a ^ 2 - 3 * twoThirdPower a ^ 2 * twoThirdPower y₀ +
        3 * twoThirdPower a * twoThirdPower y₀ ^ 2 +
        3 * twoThirdPower (a * x₀ * y₀) := by
  rw [gap9 a x₀ y₀ hpoint]
  rw [show
    (twoThirdPower a - twoThirdPower y₀) ^ 3 =
      twoThirdPower a ^ 3 -
        3 * twoThirdPower a ^ 2 * twoThirdPower y₀ +
        3 * twoThirdPower a * twoThirdPower y₀ ^ 2 -
        twoThirdPower y₀ ^ 3 by ring,
    twoThird_cube, twoThird_cube]
  ring

theorem gap11 (a x₀ y₀ : ℝ) (hpoint : astroidEquation a x₀ y₀) :
    xIntercept x₀ y₀ ^ 2 + yIntercept x₀ y₀ ^ 2 =
      a ^ 2 -
        3 * twoThirdPower a * twoThirdPower y₀ *
          (twoThirdPower a - twoThirdPower y₀) +
        3 * twoThirdPower (a * x₀ * y₀) := by
  rw [gap10 a x₀ y₀ hpoint]
  ring

theorem gap12 (a x₀ y₀ : ℝ) (hpoint : astroidEquation a x₀ y₀) :
    xIntercept x₀ y₀ ^ 2 + yIntercept x₀ y₀ ^ 2 =
      a ^ 2 - 3 * twoThirdPower (a * x₀ * y₀) +
        3 * twoThirdPower (a * x₀ * y₀) := by
  have hx :
      twoThirdPower a - twoThirdPower y₀ = twoThirdPower x₀ := by
    unfold astroidEquation at hpoint
    linarith
  have hprod :
      twoThirdPower a * twoThirdPower y₀ *
          (twoThirdPower a - twoThirdPower y₀) =
        twoThirdPower (a * x₀ * y₀) := by
    rw [hx, show a * x₀ * y₀ = (a * y₀) * x₀ by ring,
      twoThird_mul, twoThird_mul]
  rw [gap11 a x₀ y₀ hpoint]
  linear_combination -3 * hprod

theorem gap13 (a x₀ y₀ : ℝ) :
    a ^ 2 - 3 * twoThirdPower (a * x₀ * y₀) +
        3 * twoThirdPower (a * x₀ * y₀) =
      a ^ 2 := by
  ring

theorem gap14 (a x₀ y₀ : ℝ) (hpoint : astroidEquation a x₀ y₀) :
    xIntercept x₀ y₀ ^ 2 + yIntercept x₀ y₀ ^ 2 = a ^ 2 := by
  rw [gap12 a x₀ y₀ hpoint, gap13]

theorem gap15 (a x₀ y₀ : ℝ) (ha : 0 < a)
    (hpoint : astroidEquation a x₀ y₀) :
    interceptLength x₀ y₀ = a := by
  unfold interceptLength
  rw [gap14 a x₀ y₀ hpoint, Real.sqrt_sq_eq_abs, abs_of_pos ha]

theorem gap16 (l : ℝ) : ∃ c : ℝ, l = c := by
  exact ⟨l, rfl⟩

theorem gap17 (a x : ℝ) (y : ℝ → ℝ)
    (hcurve : astroidEquation a x (y x)) (ha : 0 < a) :
    interceptLength x (y x) = a := by
  exact gap15 a x (y x) ha hcurve

end

end ProofGap.Exercise1070
