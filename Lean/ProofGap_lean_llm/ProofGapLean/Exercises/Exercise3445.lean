import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace ProofGap.Exercise3445

noncomputable section

def d1 (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv f x

def d2 (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv (deriv f) x

def dydx (φ y : ℝ → ℝ) (ξ : ℝ) : ℝ :=
  d1 y ξ / d1 φ ξ

def d2ydx2 (φ y : ℝ → ℝ) (ξ : ℝ) : ℝ :=
  1 / (d1 φ ξ) ^ 2 * d2 y ξ -
    d2 φ ξ / (d1 φ ξ) ^ 3 * d1 y ξ

def transformedP (p φ : ℝ → ℝ) (ξ : ℝ) : ℝ :=
  p (φ ξ) * d1 φ ξ - d2 φ ξ / d1 φ ξ

def transformedQ (q φ : ℝ → ℝ) (ξ : ℝ) : ℝ :=
  q (φ ξ) * (d1 φ ξ) ^ 2

def invThreeHalves (r : ℝ) : ℝ :=
  Real.rpow r (-(3 / 2 : ℝ))

def invariant (P Q : ℝ → ℝ) (ξ : ℝ) : ℝ :=
  (2 * P ξ * Q ξ + d1 Q ξ) * invThreeHalves (Q ξ)

def expandedInvariant (p q x φ : ℝ → ℝ) (ξ : ℝ) : ℝ :=
  (2 * (p (x ξ) * d1 φ ξ - d2 φ ξ / d1 φ ξ) *
          q (x ξ) * (d1 φ ξ) ^ 2 +
        d1 q (x ξ) * (d1 φ ξ) ^ 3 +
        2 * q (x ξ) * d1 φ ξ * d2 φ ξ) *
    invThreeHalves (q (x ξ) * (d1 φ ξ) ^ 2)

def baseInvariant (p q x : ℝ → ℝ) (ξ : ℝ) : ℝ :=
  (2 * p (x ξ) * q (x ξ) + d1 q (x ξ)) *
    invThreeHalves (q (x ξ))

theorem gap1 (x φ : ℝ → ℝ)
    (hParam : ∀ ξ, x ξ = φ ξ) :
    ∀ ξ, d1 x ξ = d1 φ ξ := by
  have hx : x = φ := funext hParam
  subst x
  intro ξ
  rfl

theorem gap2 (x φ : ℝ → ℝ)
    (hParam : ∀ ξ, x ξ = φ ξ) :
    ∀ ξ, d2 x ξ = d2 φ ξ := by
  have hx : x = φ := funext hParam
  subst x
  intro ξ
  rfl

theorem gap3 (φ y : ℝ → ℝ)
    (hPositive : ∀ ξ, 0 < d1 φ ξ) :
    ∀ ξ, dydx φ y ξ = d1 y ξ / d1 φ ξ := by
  intro ξ
  rfl

theorem gap4 (φ y : ℝ → ℝ)
    (hPositive : ∀ ξ, 0 < d1 φ ξ) :
    ∀ ξ,
      d2ydx2 φ y ξ =
        1 / (d1 φ ξ) ^ 2 * d2 y ξ -
          d2 φ ξ / (d1 φ ξ) ^ 3 * d1 y ξ := by
  intro ξ
  rfl

theorem gap5 (p q φ y : ℝ → ℝ)
    (hODE :
      ∀ ξ,
        d2ydx2 φ y ξ +
            p (φ ξ) * dydx φ y ξ +
            q (φ ξ) * y ξ =
          0)
    (hFirst :
      ∀ ξ, dydx φ y ξ = d1 y ξ / d1 φ ξ)
    (hSecond :
      ∀ ξ,
        d2ydx2 φ y ξ =
          1 / (d1 φ ξ) ^ 2 * d2 y ξ -
            d2 φ ξ / (d1 φ ξ) ^ 3 * d1 y ξ)
    (hPositive : ∀ ξ, 0 < d1 φ ξ) :
    ∀ ξ,
      d2 y ξ +
          transformedP p φ ξ * d1 y ξ +
          transformedQ q φ ξ * y ξ =
        0 := by
  intro ξ
  have hφ_ne : d1 φ ξ ≠ 0 := ne_of_gt (hPositive ξ)
  have h := hODE ξ
  rw [hSecond ξ, hFirst ξ] at h
  unfold transformedP transformedQ
  field_simp [hφ_ne] at h ⊢
  nlinarith

theorem gap6 (p P φ : ℝ → ℝ)
    (hCoefficient :
      ∀ ξ, P ξ = transformedP p φ ξ) :
    ∀ ξ,
      P ξ =
        p (φ ξ) * d1 φ ξ - d2 φ ξ / d1 φ ξ := by
  intro ξ
  simpa [transformedP] using hCoefficient ξ

theorem gap7 (q Q φ : ℝ → ℝ)
    (hCoefficient :
      ∀ ξ, Q ξ = transformedQ q φ ξ) :
    ∀ ξ,
      Q ξ = q (φ ξ) * (d1 φ ξ) ^ 2 := by
  intro ξ
  simpa [transformedQ] using hCoefficient ξ

theorem gap8 (q Q x φ : ℝ → ℝ)
    (hParam : ∀ ξ, x ξ = φ ξ)
    (hQ : ∀ ξ, Q ξ = q (φ ξ) * (d1 φ ξ) ^ 2)
    (hq : ContDiff ℝ 1 q)
    (hφ : ContDiff ℝ 2 φ) :
    ∀ ξ,
      d1 Q ξ =
        d1 q (x ξ) * (d1 φ ξ) ^ 3 +
          2 * q (x ξ) * d1 φ ξ * d2 φ ξ := by
  intro ξ
  have hqDiff : Differentiable ℝ q := hq.differentiable (by simp)
  have hφDiff : Differentiable ℝ φ := hφ.differentiable (by decide)
  have hqAt : HasDerivAt q (d1 q (φ ξ)) (φ ξ) := by
    simpa only [d1] using hqDiff.differentiableAt.hasDerivAt
  have hφAt : HasDerivAt φ (d1 φ ξ) ξ := by
    simpa only [d1] using hφDiff.differentiableAt.hasDerivAt
  have hdφAt : HasDerivAt (d1 φ) (d2 φ ξ) ξ := by
    simpa only [d1, d2] using
      hφ.differentiable_deriv_two.differentiableAt.hasDerivAt
  have hcomp :
      HasDerivAt (fun t => q (φ t)) (d1 q (φ ξ) * d1 φ ξ) ξ := by
    simpa [Function.comp_def] using hqAt.comp ξ hφAt
  have hprod := hcomp.mul (hdφAt.pow 2)
  have hderiv := hprod.deriv
  rw [show Q = fun t => q (φ t) * (d1 φ t) ^ 2 from funext hQ]
  rw [hParam ξ]
  change deriv ((fun t => q (φ t)) * (d1 φ) ^ 2) ξ =
    d1 q (φ ξ) * d1 φ ξ ^ 3 + 2 * q (φ ξ) * d1 φ ξ * d2 φ ξ
  rw [hderiv]
  simp only [Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one]
  ring

theorem gap9 (p q P Q x φ : ℝ → ℝ)
    (hParam : ∀ ξ, x ξ = φ ξ)
    (hP :
      ∀ ξ,
        P ξ =
          p (φ ξ) * d1 φ ξ - d2 φ ξ / d1 φ ξ)
    (hQ :
      ∀ ξ, Q ξ = q (φ ξ) * (d1 φ ξ) ^ 2)
    (hQDerivative :
      ∀ ξ,
        d1 Q ξ =
          d1 q (x ξ) * (d1 φ ξ) ^ 3 +
            2 * q (x ξ) * d1 φ ξ * d2 φ ξ) :
    ∀ ξ,
      invariant P Q ξ = expandedInvariant p q x φ ξ := by
  intro ξ
  simp only [invariant, expandedInvariant, hP ξ, hQ ξ, hQDerivative ξ,
    hParam ξ]
  ring

theorem gap10 (p q x φ : ℝ → ℝ)
    (hqPositive : ∀ ξ, 0 < q (x ξ))
    (hφPositive : ∀ ξ, 0 < d1 φ ξ) :
    ∀ ξ,
      expandedInvariant p q x φ ξ =
        (2 * p (x ξ) * q (x ξ) + d1 q (x ξ)) *
          (d1 φ ξ) ^ 3 *
          invThreeHalves (q (x ξ)) *
          (1 / (d1 φ ξ) ^ 3) := by
  intro ξ
  have hq0 : 0 ≤ q (x ξ) := le_of_lt (hqPositive ξ)
  have hφ0 : 0 ≤ d1 φ ξ := le_of_lt (hφPositive ξ)
  have hφ_ne : d1 φ ξ ≠ 0 := ne_of_gt (hφPositive ξ)
  have hsq :
      Real.rpow ((d1 φ ξ) ^ 2) (-(3 / 2 : ℝ)) =
        1 / (d1 φ ξ) ^ 3 := by
    calc
      Real.rpow ((d1 φ ξ) ^ 2) (-(3 / 2 : ℝ)) =
          Real.rpow (Real.rpow (d1 φ ξ) (2 : ℝ)) (-(3 / 2 : ℝ)) := by
            exact congrArg (fun v => Real.rpow v (-(3 / 2 : ℝ)))
              (Real.rpow_natCast (d1 φ ξ) 2).symm
      _ = Real.rpow (d1 φ ξ) ((2 : ℝ) * (-(3 / 2 : ℝ))) :=
        (Real.rpow_mul hφ0 _ _).symm
      _ = Real.rpow (d1 φ ξ) (-(3 : ℝ)) := by norm_num
      _ = (Real.rpow (d1 φ ξ) (3 : ℝ))⁻¹ :=
        Real.rpow_neg hφ0 3
      _ = ((d1 φ ξ) ^ 3)⁻¹ :=
        congrArg Inv.inv (Real.rpow_natCast (d1 φ ξ) 3)
      _ = 1 / (d1 φ ξ) ^ 3 := by rw [one_div]
  have hmul :
      invThreeHalves (q (x ξ) * (d1 φ ξ) ^ 2) =
        invThreeHalves (q (x ξ)) * (1 / (d1 φ ξ) ^ 3) := by
    unfold invThreeHalves
    calc
      Real.rpow (q (x ξ) * (d1 φ ξ) ^ 2) (-(3 / 2 : ℝ)) =
          Real.rpow (q (x ξ)) (-(3 / 2 : ℝ)) *
            Real.rpow ((d1 φ ξ) ^ 2) (-(3 / 2 : ℝ)) :=
        Real.mul_rpow hq0 (sq_nonneg (d1 φ ξ))
      _ = Real.rpow (q (x ξ)) (-(3 / 2 : ℝ)) *
          (1 / (d1 φ ξ) ^ 3) := by rw [hsq]
  unfold expandedInvariant
  rw [hmul]
  field_simp [hφ_ne]
  ring

theorem gap11 (p q x φ : ℝ → ℝ)
    (hφPositive : ∀ ξ, 0 < d1 φ ξ) :
    ∀ ξ,
      (2 * p (x ξ) * q (x ξ) + d1 q (x ξ)) *
            (d1 φ ξ) ^ 3 *
            invThreeHalves (q (x ξ)) *
            (1 / (d1 φ ξ) ^ 3) =
        baseInvariant p q x ξ := by
  intro ξ
  have hφ_ne : d1 φ ξ ≠ 0 := ne_of_gt (hφPositive ξ)
  unfold baseInvariant
  field_simp [hφ_ne]

theorem gap12 (p q P Q x φ : ℝ → ℝ)
    (hSubstitute :
      ∀ ξ,
        invariant P Q ξ = expandedInvariant p q x φ ξ)
    (hFactor :
      ∀ ξ,
        expandedInvariant p q x φ ξ =
          (2 * p (x ξ) * q (x ξ) + d1 q (x ξ)) *
            (d1 φ ξ) ^ 3 *
            invThreeHalves (q (x ξ)) *
            (1 / (d1 φ ξ) ^ 3))
    (hCancel :
      ∀ ξ,
        (2 * p (x ξ) * q (x ξ) + d1 q (x ξ)) *
              (d1 φ ξ) ^ 3 *
              invThreeHalves (q (x ξ)) *
              (1 / (d1 φ ξ) ^ 3) =
          baseInvariant p q x ξ) :
    ∀ ξ,
      invariant P Q ξ = baseInvariant p q x ξ := by
  intro ξ
  calc
    invariant P Q ξ = expandedInvariant p q x φ ξ := hSubstitute ξ
    _ = (2 * p (x ξ) * q (x ξ) + d1 q (x ξ)) *
          (d1 φ ξ) ^ 3 *
          invThreeHalves (q (x ξ)) *
          (1 / (d1 φ ξ) ^ 3) := hFactor ξ
    _ = baseInvariant p q x ξ := hCancel ξ

theorem gap13 (p q P Q x : ℝ → ℝ)
    (hResult :
      ∀ ξ,
        invariant P Q ξ = baseInvariant p q x ξ) :
    ∀ ξ,
      invariant P Q ξ = baseInvariant p q x ξ := by
  exact hResult

end

end ProofGap.Exercise3445
