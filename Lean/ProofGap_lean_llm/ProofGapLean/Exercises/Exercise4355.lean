import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ProofGap.Exercise4355

noncomputable section

open scoped Interval

abbrev Point3 := ℝ × (ℝ × ℝ)

def coneHeight (x y : ℝ) : ℝ :=
  Real.sqrt (x ^ 2 + y ^ 2)

def projectionDisk (a : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ^ 2 + p.2 ^ 2 ≤ a * p.1}

def conePatch (a : ℝ) : Set Point3 :=
  {p |
    p.2.2 = coneHeight p.1 p.2.1 ∧
      (p.1, p.2.1) ∈ projectionDisk a}

def halfWidth (a x : ℝ) : ℝ :=
  Real.sqrt (a * x - x ^ 2)

def projectedArea (a : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..a,
    ∫ _y in -halfWidth a x..halfWidth a x, (1 : ℝ)

def mass (a ρ₀ : ℝ) : ℝ :=
  Real.sqrt 2 * ρ₀ * projectedArea a

def centerX (a ρ₀ : ℝ) : ℝ :=
  (Real.sqrt 2 * ρ₀ / mass a ρ₀) *
    ∫ x in (0 : ℝ)..a,
      ∫ _y in -halfWidth a x..halfWidth a x, x

def centerY (a ρ₀ : ℝ) : ℝ :=
  (Real.sqrt 2 * ρ₀ / mass a ρ₀) *
    ∫ x in (0 : ℝ)..a,
      ∫ y in -halfWidth a x..halfWidth a x, y

def projectedZMoment (a : ℝ) : ℝ :=
  ∫ φ in (-Real.pi / 2)..Real.pi / 2,
    ∫ r in (0 : ℝ)..a * Real.cos φ, r ^ 2

def centerZ (a ρ₀ : ℝ) : ℝ :=
  (Real.sqrt 2 * ρ₀ / mass a ρ₀) * projectedZMoment a

def centerOfMass (a ρ₀ : ℝ) : Point3 :=
  (centerX a ρ₀, (centerY a ρ₀, centerZ a ρ₀))

private theorem integralCosSq :
    (∫ t in (-Real.pi / 2)..Real.pi / 2, Real.cos t ^ 2) =
      Real.pi / 2 := by
  let F : ℝ → ℝ := fun t => t / 2 + Real.sin (2 * t) / 4
  have hderiv : ∀ t : ℝ, HasDerivAt F (Real.cos t ^ 2) t := by
    intro t
    have hdouble :
        HasDerivAt (fun s : ℝ => Real.sin (2 * s))
          (2 * Real.cos (2 * t)) t := by
      convert
        (Real.hasDerivAt_sin (2 * t)).comp t
          ((hasDerivAt_id t).const_mul 2) using 1 <;> ring
    convert ((hasDerivAt_id t).div_const 2).add (hdouble.div_const 4) using 1
    rw [Real.cos_two_mul]
    ring
  calc
    (∫ t in (-Real.pi / 2)..Real.pi / 2, Real.cos t ^ 2) =
        F (Real.pi / 2) - F (-Real.pi / 2) := by
          apply intervalIntegral.integral_eq_sub_of_hasDerivAt
          · intro t ht
            exact hderiv t
          · exact (Real.continuous_cos.pow 2).intervalIntegrable _ _
    _ = Real.pi / 2 := by
          dsimp [F]
          rw [show 2 * (Real.pi / 2) = Real.pi by ring,
            show 2 * (-Real.pi / 2) = -Real.pi by ring,
            Real.sin_pi, Real.sin_neg, Real.sin_pi]
          ring

private theorem integralSinMulCosSq :
    (∫ t in (-Real.pi / 2)..Real.pi / 2,
      Real.sin t * Real.cos t ^ 2) = 0 := by
  let F : ℝ → ℝ := fun t => -(Real.cos t ^ 3) / 3
  have hderiv : ∀ t : ℝ,
      HasDerivAt F (Real.sin t * Real.cos t ^ 2) t := by
    intro t
    convert (((Real.hasDerivAt_cos t).pow 3).neg.div_const 3) using 1
    norm_num
    ring
  calc
    (∫ t in (-Real.pi / 2)..Real.pi / 2,
      Real.sin t * Real.cos t ^ 2) =
        F (Real.pi / 2) - F (-Real.pi / 2) := by
          apply intervalIntegral.integral_eq_sub_of_hasDerivAt
          · intro t ht
            exact hderiv t
          · exact
              (Real.continuous_sin.mul (Real.continuous_cos.pow 2)).intervalIntegrable
                _ _
    _ = 0 := by
          dsimp [F]
          rw [show -Real.pi / 2 = -(Real.pi / 2) by ring,
            Real.cos_neg, Real.cos_pi_div_two]
          ring

private theorem integralOnePlusSinCosSq :
    (∫ t in (-Real.pi / 2)..Real.pi / 2,
      (1 + Real.sin t) * Real.cos t ^ 2) = Real.pi / 2 := by
  have hi1 :
      IntervalIntegrable (fun t : ℝ => Real.cos t ^ 2)
        MeasureTheory.volume (-Real.pi / 2) (Real.pi / 2) :=
    (Real.continuous_cos.pow 2).intervalIntegrable _ _
  have hi2 :
      IntervalIntegrable (fun t : ℝ => Real.sin t * Real.cos t ^ 2)
        MeasureTheory.volume (-Real.pi / 2) (Real.pi / 2) :=
    (Real.continuous_sin.mul (Real.continuous_cos.pow 2)).intervalIntegrable _ _
  calc
    (∫ t in (-Real.pi / 2)..Real.pi / 2,
      (1 + Real.sin t) * Real.cos t ^ 2) =
        ∫ t in (-Real.pi / 2)..Real.pi / 2,
          (Real.cos t ^ 2 + Real.sin t * Real.cos t ^ 2) := by
            apply intervalIntegral.integral_congr
            intro t ht
            ring
    _ = (∫ t in (-Real.pi / 2)..Real.pi / 2, Real.cos t ^ 2) +
        ∫ t in (-Real.pi / 2)..Real.pi / 2,
          Real.sin t * Real.cos t ^ 2 := by
            rw [intervalIntegral.integral_add hi1 hi2]
    _ = Real.pi / 2 := by
          rw [integralCosSq, integralSinMulCosSq]
          ring

private theorem sqrtSemicircleParam
    (a t : ℝ) (ha : 0 < a)
    (ht : t ∈ Set.Icc (-Real.pi / 2) (Real.pi / 2)) :
    Real.sqrt
        (a * (a / 2 * (1 + Real.sin t)) -
          (a / 2 * (1 + Real.sin t)) ^ 2) =
      a / 2 * Real.cos t := by
  have hR : 0 ≤ a / 2 := by linarith
  have ht' : t ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    simpa only [neg_div] using ht
  have hcos : 0 ≤ Real.cos t := Real.cos_nonneg_of_mem_Icc ht'
  have htrig : 1 - Real.sin t ^ 2 = Real.cos t ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq t]
  have halg :
      a * (a / 2 * (1 + Real.sin t)) -
          (a / 2 * (1 + Real.sin t)) ^ 2 =
        (a / 2 * Real.cos t) ^ 2 := by
    calc
      a * (a / 2 * (1 + Real.sin t)) -
          (a / 2 * (1 + Real.sin t)) ^ 2 =
          (a ^ 2 / 4) * (1 - Real.sin t ^ 2) := by ring
      _ = (a ^ 2 / 4) * Real.cos t ^ 2 := by rw [htrig]
      _ = (a / 2 * Real.cos t) ^ 2 := by ring
  rw [halg, Real.sqrt_sq_eq_abs, abs_of_nonneg (mul_nonneg hR hcos)]

private theorem semicircleArea (a : ℝ) (ha : 0 < a) :
    (∫ x in (0 : ℝ)..a, Real.sqrt (a * x - x ^ 2)) =
      Real.pi * a ^ 2 / 8 := by
  let R : ℝ := a / 2
  let q : ℝ → ℝ := fun t => R * (1 + Real.sin t)
  let g : ℝ → ℝ := fun x => Real.sqrt (a * x - x ^ 2)
  have hgcont : Continuous g := by
    dsimp [g]
    exact Real.continuous_sqrt.comp
      (continuous_const.mul continuous_id |>.sub (continuous_id.pow 2))
  have hqcont : Continuous q := by
    dsimp [q]
    exact continuous_const.mul (continuous_const.add Real.continuous_sin)
  have hqderiv : ∀ t : ℝ,
      HasDerivAt q (R * Real.cos t) t := by
    intro t
    dsimp [q]
    convert
      (((hasDerivAt_const t (1 : ℝ)).add (Real.hasDerivAt_sin t)).const_mul R)
        using 1 <;> ring
  have hf'cont : Continuous (fun t : ℝ => R * Real.cos t) :=
    continuous_const.mul Real.continuous_cos
  have hqlo : q (-Real.pi / 2) = 0 := by
    dsimp [q, R]
    rw [show -Real.pi / 2 = -(Real.pi / 2) by ring,
      Real.sin_neg, Real.sin_pi_div_two]
    ring
  have hqhi : q (Real.pi / 2) = a := by
    dsimp [q, R]
    rw [Real.sin_pi_div_two]
    ring
  have hraw :
      (∫ t in (-Real.pi / 2)..Real.pi / 2,
        g (q t) * (R * Real.cos t)) =
        ∫ x in q (-Real.pi / 2)..q (Real.pi / 2), g x := by
    simpa only [Function.comp_apply] using
      (intervalIntegral.integral_comp_mul_deriv
        (a := -Real.pi / 2) (b := Real.pi / 2)
        (f := q) (f' := fun t : ℝ => R * Real.cos t) (g := g)
        (fun t _ht => hqderiv t) hf'cont.continuousOn hgcont)
  have hsub :
      (∫ t in (-Real.pi / 2)..Real.pi / 2,
        g (q t) * (R * Real.cos t)) =
        ∫ x in (0 : ℝ)..a, g x := by
    simpa [hqlo, hqhi] using hraw
  have hbounds : -Real.pi / 2 ≤ Real.pi / 2 := by
    linarith [Real.pi_pos]
  calc
    (∫ x in (0 : ℝ)..a, Real.sqrt (a * x - x ^ 2)) =
        ∫ t in (-Real.pi / 2)..Real.pi / 2,
          g (q t) * (R * Real.cos t) := by
            simpa [g] using hsub.symm
    _ = ∫ t in (-Real.pi / 2)..Real.pi / 2,
        R ^ 2 * Real.cos t ^ 2 := by
          apply intervalIntegral.integral_congr
          intro t ht
          have ht' : t ∈ Set.Icc (-Real.pi / 2) (Real.pi / 2) := by
            rw [Set.uIcc_of_le hbounds] at ht
            exact ht
          have hs := sqrtSemicircleParam a t ha ht'
          dsimp [g, q, R]
          rw [hs]
          ring
    _ = R ^ 2 *
        (∫ t in (-Real.pi / 2)..Real.pi / 2, Real.cos t ^ 2) := by
          rw [intervalIntegral.integral_const_mul]
    _ = Real.pi * a ^ 2 / 8 := by
          rw [integralCosSq]
          dsimp [R]
          ring

private theorem semicircleFirstMoment (a : ℝ) (ha : 0 < a) :
    (∫ x in (0 : ℝ)..a, x * Real.sqrt (a * x - x ^ 2)) =
      Real.pi * a ^ 3 / 16 := by
  let R : ℝ := a / 2
  let q : ℝ → ℝ := fun t => R * (1 + Real.sin t)
  let g : ℝ → ℝ := fun x => x * Real.sqrt (a * x - x ^ 2)
  have hsqrtcont : Continuous (fun x : ℝ => Real.sqrt (a * x - x ^ 2)) :=
    Real.continuous_sqrt.comp
      (continuous_const.mul continuous_id |>.sub (continuous_id.pow 2))
  have hgcont : Continuous g := by
    dsimp [g]
    exact continuous_id.mul hsqrtcont
  have hqcont : Continuous q := by
    dsimp [q]
    exact continuous_const.mul (continuous_const.add Real.continuous_sin)
  have hqderiv : ∀ t : ℝ,
      HasDerivAt q (R * Real.cos t) t := by
    intro t
    dsimp [q]
    convert
      (((hasDerivAt_const t (1 : ℝ)).add (Real.hasDerivAt_sin t)).const_mul R)
        using 1 <;> ring
  have hf'cont : Continuous (fun t : ℝ => R * Real.cos t) :=
    continuous_const.mul Real.continuous_cos
  have hqlo : q (-Real.pi / 2) = 0 := by
    dsimp [q, R]
    rw [show -Real.pi / 2 = -(Real.pi / 2) by ring,
      Real.sin_neg, Real.sin_pi_div_two]
    ring
  have hqhi : q (Real.pi / 2) = a := by
    dsimp [q, R]
    rw [Real.sin_pi_div_two]
    ring
  have hraw :
      (∫ t in (-Real.pi / 2)..Real.pi / 2,
        g (q t) * (R * Real.cos t)) =
        ∫ x in q (-Real.pi / 2)..q (Real.pi / 2), g x := by
    simpa only [Function.comp_apply] using
      (intervalIntegral.integral_comp_mul_deriv
        (a := -Real.pi / 2) (b := Real.pi / 2)
        (f := q) (f' := fun t : ℝ => R * Real.cos t) (g := g)
        (fun t _ht => hqderiv t) hf'cont.continuousOn hgcont)
  have hsub :
      (∫ t in (-Real.pi / 2)..Real.pi / 2,
        g (q t) * (R * Real.cos t)) =
        ∫ x in (0 : ℝ)..a, g x := by
    simpa [hqlo, hqhi] using hraw
  have hbounds : -Real.pi / 2 ≤ Real.pi / 2 := by
    linarith [Real.pi_pos]
  calc
    (∫ x in (0 : ℝ)..a, x * Real.sqrt (a * x - x ^ 2)) =
        ∫ t in (-Real.pi / 2)..Real.pi / 2,
          g (q t) * (R * Real.cos t) := by
            simpa [g] using hsub.symm
    _ = ∫ t in (-Real.pi / 2)..Real.pi / 2,
        R ^ 3 * ((1 + Real.sin t) * Real.cos t ^ 2) := by
          apply intervalIntegral.integral_congr
          intro t ht
          have ht' : t ∈ Set.Icc (-Real.pi / 2) (Real.pi / 2) := by
            rw [Set.uIcc_of_le hbounds] at ht
            exact ht
          have hs := sqrtSemicircleParam a t ha ht'
          dsimp [g, q, R]
          rw [hs]
          ring
    _ = R ^ 3 *
        (∫ t in (-Real.pi / 2)..Real.pi / 2,
          (1 + Real.sin t) * Real.cos t ^ 2) := by
            rw [intervalIntegral.integral_const_mul]
    _ = Real.pi * a ^ 3 / 16 := by
          rw [integralOnePlusSinCosSq]
          dsimp [R]
          ring

private theorem integralIdSymm (w : ℝ) :
    (∫ y in -w..w, y) = 0 := by
  calc
    (∫ y in -w..w, y) = w ^ 2 / 2 - (-w) ^ 2 / 2 := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro y hy
        convert ((hasDerivAt_id y).pow 2).div_const 2 using 1 <;>
          norm_num <;> ring
      · exact continuous_id.intervalIntegrable _ _
    _ = 0 := by ring

private theorem integralSquare (b : ℝ) :
    (∫ r in (0 : ℝ)..b, r ^ 2) = b ^ 3 / 3 := by
  have hderiv : ∀ x : ℝ,
      HasDerivAt (fun t : ℝ => t ^ 3 / 3) (x ^ 2) x := by
    intro x
    convert ((hasDerivAt_id x).pow 3).div_const 3 using 1 <;>
      norm_num <;> ring
  calc
    (∫ r in (0 : ℝ)..b, r ^ 2) = b ^ 3 / 3 - 0 ^ 3 / 3 := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro x hx
        exact hderiv x
      · exact (continuous_id.pow 2).intervalIntegrable _ _
    _ = b ^ 3 / 3 := by ring

private theorem integralCosCube :
    (∫ φ in (-Real.pi / 2)..Real.pi / 2, Real.cos φ ^ 3) = 4 / 3 := by
  let F : ℝ → ℝ := fun x => Real.sin x - Real.sin x ^ 3 / 3
  have hderiv : ∀ x : ℝ, HasDerivAt F (Real.cos x ^ 3) x := by
    intro x
    convert
      (Real.hasDerivAt_sin x).sub
        (((Real.hasDerivAt_sin x).pow 3).div_const 3) using 1
    norm_num
    have htrig : Real.sin x ^ 2 = 1 - Real.cos x ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq x]
    rw [htrig]
    ring
  calc
    (∫ φ in (-Real.pi / 2)..Real.pi / 2, Real.cos φ ^ 3) =
        F (Real.pi / 2) - F (-Real.pi / 2) := by
          apply intervalIntegral.integral_eq_sub_of_hasDerivAt
          · intro x hx
            exact hderiv x
          · exact (Real.continuous_cos.pow 3).intervalIntegrable _ _
    _ = 4 / 3 := by
          dsimp [F]
          rw [show -Real.pi / 2 = -(Real.pi / 2) by ring,
            Real.sin_neg, Real.sin_pi_div_two]
          ring

theorem gap1 (a ρ₀ : ℝ) :
    mass a ρ₀ = Real.sqrt 2 * ρ₀ * projectedArea a := by
  rfl

theorem gap2 (a ρ₀ : ℝ) (ha : 0 < a) :
    Real.sqrt 2 * ρ₀ * projectedArea a =
      Real.sqrt 2 * ρ₀ *
        (∫ x in (0 : ℝ)..a,
          ∫ _y in -halfWidth a x..halfWidth a x, (1 : ℝ)) := by
  rfl

theorem gap3 (a ρ₀ : ℝ) (ha : 0 < a) :
    Real.sqrt 2 * ρ₀ *
        (∫ x in (0 : ℝ)..a,
          ∫ _y in -halfWidth a x..halfWidth a x, (1 : ℝ)) =
      Real.sqrt 2 * Real.pi * a ^ 2 * ρ₀ / 4 := by
  have hinner :
      (∫ x in (0 : ℝ)..a,
        ∫ _y in -halfWidth a x..halfWidth a x, (1 : ℝ)) =
        2 * ∫ x in (0 : ℝ)..a, halfWidth a x := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    simp
    ring
  rw [hinner]
  unfold halfWidth
  rw [semicircleArea a ha]
  ring

theorem gap4 (a ρ₀ : ℝ) (ha : 0 < a) :
    mass a ρ₀ = Real.sqrt 2 * Real.pi * a ^ 2 * ρ₀ / 4 := by
  calc
    mass a ρ₀ = Real.sqrt 2 * ρ₀ * projectedArea a := gap1 a ρ₀
    _ = Real.sqrt 2 * Real.pi * a ^ 2 * ρ₀ / 4 := gap3 a ρ₀ ha

theorem gap5
    (a ρ₀ : ℝ) (ha : 0 < a) (hρ : 0 < ρ₀) :
    centerX a ρ₀ =
      (Real.sqrt 2 * ρ₀ / mass a ρ₀) *
        (∫ x in (0 : ℝ)..a,
          ∫ _y in -halfWidth a x..halfWidth a x, x) := by
  rfl

theorem gap6
    (a ρ₀ : ℝ) (ha : 0 < a) (hρ : 0 < ρ₀) :
    centerX a ρ₀ =
      8 / (Real.pi * a ^ 2) *
        (∫ x in (0 : ℝ)..a, x * halfWidth a x) := by
  have hsqrt : Real.sqrt 2 ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hρ0 : ρ₀ ≠ 0 := ne_of_gt hρ
  have hinner :
      (∫ x in (0 : ℝ)..a,
        ∫ _y in -halfWidth a x..halfWidth a x, x) =
        2 * ∫ x in (0 : ℝ)..a, x * halfWidth a x := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    simp
    ring
  unfold centerX
  rw [gap4 a ρ₀ ha, hinner]
  field_simp [hsqrt, hpi, ha0, hρ0]
  ring

theorem gap7 (a : ℝ) (ha : 0 < a) :
    8 / (Real.pi * a ^ 2) *
        (∫ x in (0 : ℝ)..a, x * halfWidth a x) =
      a / 2 := by
  unfold halfWidth
  rw [semicircleFirstMoment a ha]
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have ha0 : a ≠ 0 := ne_of_gt ha
  field_simp [hpi, ha0]
  ring

theorem gap8
    (a ρ₀ : ℝ) (ha : 0 < a) (hρ : 0 < ρ₀) :
    centerX a ρ₀ = a / 2 := by
  rw [gap6 a ρ₀ ha hρ, gap7 a ha]

theorem gap9
    (a ρ₀ : ℝ) (ha : 0 < a) (hρ : 0 < ρ₀) :
    centerY a ρ₀ =
      (Real.sqrt 2 * ρ₀ / mass a ρ₀) *
        (∫ x in (0 : ℝ)..a,
          ∫ y in -halfWidth a x..halfWidth a x, y) := by
  rfl

theorem gap10
    (a ρ₀ : ℝ) (ha : 0 < a) (hρ : 0 < ρ₀) :
    (Real.sqrt 2 * ρ₀ / mass a ρ₀) *
        (∫ x in (0 : ℝ)..a,
          ∫ y in -halfWidth a x..halfWidth a x, y) =
      0 := by
  simp_rw [integralIdSymm]
  simp

theorem gap11
    (a ρ₀ : ℝ) (ha : 0 < a) (hρ : 0 < ρ₀) :
    centerY a ρ₀ = 0 := by
  rw [gap9 a ρ₀ ha hρ, gap10 a ρ₀ ha hρ]

theorem gap12
    (a ρ₀ : ℝ) (ha : 0 < a) (hρ : 0 < ρ₀) :
    centerZ a ρ₀ =
      (Real.sqrt 2 * ρ₀ / mass a ρ₀) * projectedZMoment a := by
  rfl

theorem gap13
    (a ρ₀ : ℝ) (ha : 0 < a) (hρ : 0 < ρ₀) :
    centerZ a ρ₀ =
      4 / (Real.pi * a ^ 2) *
        (∫ φ in (-Real.pi / 2)..Real.pi / 2,
          ∫ r in (0 : ℝ)..a * Real.cos φ, r ^ 2) := by
  have hsqrt : Real.sqrt 2 ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hρ0 : ρ₀ ≠ 0 := ne_of_gt hρ
  unfold centerZ projectedZMoment
  rw [gap4 a ρ₀ ha]
  field_simp [hsqrt, hpi, ha0, hρ0]

theorem gap14 (a : ℝ) (ha : 0 < a) :
    4 / (Real.pi * a ^ 2) *
        (∫ φ in (-Real.pi / 2)..Real.pi / 2,
          ∫ r in (0 : ℝ)..a * Real.cos φ, r ^ 2) =
      16 * a / (9 * Real.pi) := by
  simp_rw [integralSquare]
  have hrewrite :
      (∫ φ in (-Real.pi / 2)..Real.pi / 2,
        (a * Real.cos φ) ^ 3 / 3) =
      (a ^ 3 / 3) *
        (∫ φ in (-Real.pi / 2)..Real.pi / 2, Real.cos φ ^ 3) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro φ hφ
    ring
  rw [hrewrite, integralCosCube]
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have ha0 : a ≠ 0 := ne_of_gt ha
  field_simp [hpi, ha0]
  ring

theorem gap15
    (a ρ₀ : ℝ) (ha : 0 < a) (hρ : 0 < ρ₀) :
    centerZ a ρ₀ = 16 * a / (9 * Real.pi) := by
  rw [gap13 a ρ₀ ha hρ, gap14 a ha]

theorem gap16
    (a ρ₀ : ℝ) (ha : 0 < a) (hρ : 0 < ρ₀) :
    centerOfMass a ρ₀ =
      (a / 2, (0, 16 * a / (9 * Real.pi))) := by
  unfold centerOfMass
  rw [gap8 a ρ₀ ha hρ, gap11 a ρ₀ ha hρ, gap15 a ρ₀ ha hρ]

end

end ProofGap.Exercise4355
