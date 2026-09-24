import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4000

noncomputable section

open MeasureTheory
open scoped Interval

def quadratic (c x y t : ℝ) : ℝ :=
  t ^ 2 - (x ^ 2 + y ^ 2 + c ^ 2) * t +
    c ^ 2 * x ^ 2

def discriminant (c x y : ℝ) : ℝ :=
  (x ^ 2 + y ^ 2 + c ^ 2) ^ 2 -
    4 * c ^ 2 * x ^ 2

def lambdaCoord (c x y : ℝ) : ℝ :=
  (x ^ 2 + y ^ 2 + c ^ 2 +
    Real.sqrt (discriminant c x y)) / 2

def muCoord (c x y : ℝ) : ℝ :=
  (x ^ 2 + y ^ 2 + c ^ 2 -
    Real.sqrt (discriminant c x y)) / 2

def coordinateRegion (c : ℝ) : Set (ℝ × ℝ) :=
  {p |
    0 < p.1 ∧ 0 < p.2 ∧
      4 / 3 * c ^ 2 ≤ lambdaCoord c p.1 p.2 ∧
      lambdaCoord c p.1 p.2 ≤ 5 / 3 * c ^ 2 ∧
      1 / 3 * c ^ 2 ≤ muCoord c p.1 p.2 ∧
      muCoord c p.1 p.2 ≤ 2 / 3 * c ^ 2}

def regionArea (c : ℝ) : ℝ :=
  ∫ _p in coordinateRegion c, (1 : ℝ)

def forwardJacobianAbs (c x y : ℝ) : ℝ :=
  4 * c ^ 2 * x * y /
    Real.sqrt (discriminant c x y)

def coordinateJacobianAbs
    (c lam mu : ℝ) : ℝ :=
  4 * Real.sqrt
      (lam * mu * (c ^ 2 - mu) *
        (lam - c ^ 2)) /
    (lam - mu)

def inverseJacobian (c x y : ℝ) : ℝ :=
  1 / forwardJacobianAbs c x y

theorem gap1 (c x y t : ℝ)
    (ht0 : t ≠ 0) (htc : t ≠ c ^ 2) :
    x ^ 2 / t + y ^ 2 / (t - c ^ 2) = 1 ↔
      quadratic c x y t = 0 := by
  have htc0 : t - c ^ 2 ≠ 0 :=
    sub_ne_zero.mpr htc
  constructor
  · intro h
    field_simp [ht0, htc0] at h
    unfold quadratic
    ring_nf at h ⊢
    nlinarith
  · intro h
    unfold quadratic at h
    field_simp [ht0, htc0]
    ring_nf at h ⊢
    nlinarith

theorem gap2 (c x y t : ℝ)
    (ht0 : t ≠ 0) (htc : t ≠ c ^ 2)
    (hcoord :
      x ^ 2 / t + y ^ 2 / (t - c ^ 2) = 1) :
    quadratic c x y t = 0 := by
  exact (gap1 c x y t ht0 htc).1 hcoord

private lemma discriminant_nonneg
    (c x y : ℝ) :
    0 ≤ discriminant c x y := by
  rw [show
    discriminant c x y =
      ((x - c) ^ 2 + y ^ 2) *
        ((x + c) ^ 2 + y ^ 2) by
    unfold discriminant
    ring]
  positivity

theorem gap3 (c x y t : ℝ) :
    quadratic c x y t = 0 ↔
      t = lambdaCoord c x y ∨
        t = muCoord c x y := by
  let A : ℝ := x ^ 2 + y ^ 2 + c ^ 2
  let D : ℝ := discriminant c x y
  have hD : 0 ≤ D := discriminant_nonneg c x y
  have hsqrt : Real.sqrt D ^ 2 = D :=
    Real.sq_sqrt hD
  have hDdef :
      D = A ^ 2 - 4 * c ^ 2 * x ^ 2 := by
    dsimp [A, D]
    unfold discriminant
    rfl
  constructor
  · intro hq
    have hq' :
        t ^ 2 - A * t + c ^ 2 * x ^ 2 = 0 := by
      simpa [quadratic, A] using hq
    have hsquared :
        (2 * t - A) ^ 2 = Real.sqrt D ^ 2 := by
      rw [hsqrt, hDdef]
      nlinarith
    rcases (sq_eq_sq_iff_eq_or_eq_neg).1 hsquared with h | h
    · left
      unfold lambdaCoord
      dsimp [A] at h ⊢
      dsimp [D] at h
      linarith
    · right
      unfold muCoord
      dsimp [A] at h ⊢
      dsimp [D] at h
      linarith
  · rintro (rfl | rfl)
    · unfold quadratic lambdaCoord
      dsimp [D, A] at hsqrt hDdef
      unfold discriminant at hsqrt ⊢
      nlinarith
    · unfold quadratic muCoord
      dsimp [D, A] at hsqrt hDdef
      unfold discriminant at hsqrt ⊢
      nlinarith

theorem gap4 (c x y : ℝ) :
    muCoord c x y =
      (x ^ 2 + y ^ 2 + c ^ 2 -
        Real.sqrt (discriminant c x y)) / 2 := by
  rfl

theorem gap5 (c x y : ℝ) :
    (lambdaCoord c x y, muCoord c x y) =
      ((x ^ 2 + y ^ 2 + c ^ 2 +
          Real.sqrt (discriminant c x y)) / 2,
        (x ^ 2 + y ^ 2 + c ^ 2 -
          Real.sqrt (discriminant c x y)) / 2) := by
  rfl

theorem gap6 (c x y : ℝ)
    (hc : 0 < c) (hx : 0 < x) (hy : 0 < y)
    (hdisc : 0 < discriminant c x y) :
    forwardJacobianAbs c x y =
      4 * c ^ 2 * x * y /
        Real.sqrt (discriminant c x y) := by
  rfl

private lemma coordinate_algebra
    (c x y lam mu : ℝ)
    (hlam : lam = lambdaCoord c x y)
    (hmu : mu = muCoord c x y) :
    lam - mu = Real.sqrt (discriminant c x y) ∧
      lam * mu = c ^ 2 * x ^ 2 ∧
      (c ^ 2 - mu) * (lam - c ^ 2) =
        c ^ 2 * y ^ 2 := by
  have hD := discriminant_nonneg c x y
  have hsqrt :
      Real.sqrt (discriminant c x y) ^ 2 =
        discriminant c x y :=
    Real.sq_sqrt hD
  have hsum :
      lam + mu = x ^ 2 + y ^ 2 + c ^ 2 := by
    rw [hlam, hmu]
    unfold lambdaCoord muCoord
    ring
  have hdiff :
      lam - mu =
        Real.sqrt (discriminant c x y) := by
    rw [hlam, hmu]
    unfold lambdaCoord muCoord
    ring
  have hprod : lam * mu = c ^ 2 * x ^ 2 := by
    rw [hlam, hmu]
    unfold lambdaCoord muCoord
    unfold discriminant at hsqrt ⊢
    nlinarith
  refine ⟨hdiff, hprod, ?_⟩
  nlinarith

theorem gap7 (c x y lam mu : ℝ)
    (hc : 0 < c) (hx : 0 < x) (hy : 0 < y)
    (hlam : lam = lambdaCoord c x y)
    (hmu : mu = muCoord c x y)
    (hmu0 : 0 < mu) (hmuc : mu < c ^ 2)
    (hlamc : c ^ 2 < lam) :
    forwardJacobianAbs c x y =
      coordinateJacobianAbs c lam mu := by
  rcases coordinate_algebra c x y lam mu hlam hmu with
    ⟨hdiff, hprod, hother⟩
  have hcxy : 0 < c ^ 2 * x * y := by
    positivity
  have hinside :
      lam * mu * (c ^ 2 - mu) * (lam - c ^ 2) =
        (c ^ 2 * x * y) ^ 2 := by
    calc
      lam * mu * (c ^ 2 - mu) * (lam - c ^ 2) =
          (lam * mu) *
            ((c ^ 2 - mu) * (lam - c ^ 2)) := by
        ring
      _ = (c ^ 2 * x ^ 2) * (c ^ 2 * y ^ 2) := by
        rw [hprod, hother]
      _ = (c ^ 2 * x * y) ^ 2 := by
        ring
  have hsqrt :
      Real.sqrt
          (lam * mu * (c ^ 2 - mu) *
            (lam - c ^ 2)) =
        c ^ 2 * x * y := by
    rw [hinside, Real.sqrt_sq_eq_abs,
      abs_of_pos hcxy]
  unfold forwardJacobianAbs coordinateJacobianAbs
  rw [← hdiff, hsqrt]
  ring

theorem gap8 (c x y lam mu : ℝ)
    (hc : 0 < c) (hx : 0 < x) (hy : 0 < y)
    (hlam : lam = lambdaCoord c x y)
    (hmu : mu = muCoord c x y)
    (hmu0 : 0 < mu) (hmuc : mu < c ^ 2)
    (hlamc : c ^ 2 < lam) :
    forwardJacobianAbs c x y =
      4 * Real.sqrt
          (lam * mu * (c ^ 2 - mu) *
            (lam - c ^ 2)) /
        (lam - mu) := by
  rw [gap7 c x y lam mu hc hx hy
    hlam hmu hmu0 hmuc hlamc]
  rfl

theorem gap9 (c x y : ℝ)
    (hJ : forwardJacobianAbs c x y ≠ 0) :
    inverseJacobian c x y =
      1 / forwardJacobianAbs c x y := by
  rfl

theorem gap10 (c lam mu : ℝ)
    (hJ : coordinateJacobianAbs c lam mu ≠ 0) :
    1 / coordinateJacobianAbs c lam mu =
      (lam - mu) /
        (4 * Real.sqrt
          (lam * mu * (c ^ 2 - mu) *
            (lam - c ^ 2))) := by
  unfold coordinateJacobianAbs at hJ ⊢
  field_simp

theorem gap11 (c x y lam mu : ℝ)
    (hlam : lam = lambdaCoord c x y)
    (hmu : mu = muCoord c x y)
    (hforward :
      forwardJacobianAbs c x y =
        coordinateJacobianAbs c lam mu)
    (hJ : coordinateJacobianAbs c lam mu ≠ 0) :
    inverseJacobian c x y =
      (lam - mu) /
        (4 * Real.sqrt
          (lam * mu * (c ^ 2 - mu) *
            (lam - c ^ 2))) := by
  unfold inverseJacobian
  rw [hforward]
  exact gap10 c lam mu hJ

private noncomputable def logPrimitive (u : ℝ) : ℝ :=
  2 * Real.log (Real.sqrt u + Real.sqrt (u - 1))

private lemma logPrimitive_hasDerivAt
    (u : ℝ) (hu : 1 < u) :
    HasDerivAt logPrimitive
      (1 / Real.sqrt (u * (u - 1))) u := by
  have hu0 : 0 < u := lt_trans zero_lt_one hu
  have hum0 : 0 < u - 1 := sub_pos.2 hu
  have hsu0 : Real.sqrt u ≠ 0 :=
    (Real.sqrt_pos.2 hu0).ne'
  have hsum0 : Real.sqrt (u - 1) ≠ 0 :=
    (Real.sqrt_pos.2 hum0).ne'
  have hadd0 :
      Real.sqrt u + Real.sqrt (u - 1) ≠ 0 := by
    positivity
  have hdu :
      HasDerivAt (fun z : ℝ => Real.sqrt z)
        (1 / (2 * Real.sqrt u)) u := by
    simpa [id_eq] using
      (hasDerivAt_id u).sqrt hu0.ne'
  have hdum :
      HasDerivAt (fun z : ℝ => Real.sqrt (z - 1))
        (1 / (2 * Real.sqrt (u - 1))) u := by
    simpa [id_eq] using
      ((hasDerivAt_id u).sub_const 1).sqrt hum0.ne'
  have hlog :=
    (hdu.add hdum).log hadd0
  have hraw := hlog.const_mul 2
  unfold logPrimitive
  simp only [Pi.add_apply] at hraw
  convert hraw using 1
  rw [Real.sqrt_mul' u hum0.le]
  have hsuSq : Real.sqrt u ^ 2 = u :=
    Real.sq_sqrt hu0.le
  have hsumSq :
      Real.sqrt (u - 1) ^ 2 = u - 1 :=
    Real.sq_sqrt hum0.le
  field_simp [hsu0, hsum0, hadd0]
  nlinarith

private lemma logPrimitive_endpoint :
    logPrimitive (5 / 3) - logPrimitive (4 / 3) =
      2 * Real.log
        ((Real.sqrt 5 + Real.sqrt 2) / 3) := by
  have hs3pos : 0 < Real.sqrt 3 :=
    Real.sqrt_pos.2 (by norm_num)
  have hs3sq : Real.sqrt 3 ^ 2 = 3 :=
    Real.sq_sqrt (by norm_num)
  have hu :
      Real.sqrt (5 / 3 : ℝ) +
          Real.sqrt (5 / 3 - 1) =
        (Real.sqrt 5 + Real.sqrt 2) /
          Real.sqrt 3 := by
    rw [show (5 / 3 : ℝ) - 1 = 2 / 3 by norm_num,
      Real.sqrt_div (by norm_num) 3,
      Real.sqrt_div (by norm_num) 3]
    ring
  have hl :
      Real.sqrt (4 / 3 : ℝ) +
          Real.sqrt (4 / 3 - 1) =
        Real.sqrt 3 := by
    rw [show (4 / 3 : ℝ) - 1 = 1 / 3 by norm_num,
      Real.sqrt_div (by norm_num) 3,
      Real.sqrt_div (by norm_num) 3]
    have hs4 : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]
    have hs1 : Real.sqrt 1 = 1 := by norm_num
    rw [hs4, hs1]
    field_simp [hs3pos.ne']
    nlinarith [hs3sq]
  have hnum :
      Real.sqrt 5 + Real.sqrt 2 ≠ 0 := by
    positivity
  have hupper :
      Real.sqrt (5 / 3 : ℝ) +
          Real.sqrt (5 / 3 - 1) ≠ 0 := by
    positivity
  have hlower :
      Real.sqrt (4 / 3 : ℝ) +
          Real.sqrt (4 / 3 - 1) ≠ 0 := by
    positivity
  unfold logPrimitive
  have hlogdiff :
      Real.log
          (Real.sqrt (5 / 3 : ℝ) +
            Real.sqrt (5 / 3 - 1)) -
        Real.log
          (Real.sqrt (4 / 3 : ℝ) +
            Real.sqrt (4 / 3 - 1)) =
      Real.log
        ((Real.sqrt 5 + Real.sqrt 2) / 3) := by
    rw [← Real.log_div hupper hlower, hu, hl]
    congr 1
    field_simp [hs3pos.ne']
    nlinarith
  rw [show
      2 * Real.log
          (Real.sqrt (5 / 3 : ℝ) +
            Real.sqrt (5 / 3 - 1)) -
        2 * Real.log
          (Real.sqrt (4 / 3 : ℝ) +
            Real.sqrt (4 / 3 - 1)) =
        2 *
          (Real.log
              (Real.sqrt (5 / 3 : ℝ) +
                Real.sqrt (5 / 3 - 1)) -
            Real.log
              (Real.sqrt (4 / 3 : ℝ) +
                Real.sqrt (4 / 3 - 1))) by ring,
    hlogdiff]

theorem gap17 :
    (∫ u in (4 / 3 : ℝ)..5 / 3,
        1 / Real.sqrt (u * (u - 1))) =
      2 * Real.log
        ((Real.sqrt 5 + Real.sqrt 2) / 3) := by
  have hderiv :
      ∀ u ∈ Set.uIcc (4 / 3 : ℝ) (5 / 3),
        HasDerivAt logPrimitive
          (1 / Real.sqrt (u * (u - 1))) u := by
    intro u hu
    rw [Set.uIcc_of_le (by norm_num)] at hu
    norm_num at hu
    exact logPrimitive_hasDerivAt u (by linarith)
  have hint :
      IntervalIntegrable
        (fun u : ℝ =>
          1 / Real.sqrt (u * (u - 1)))
        volume (4 / 3) (5 / 3) := by
    apply ContinuousOn.intervalIntegrable
    intro u hu
    rw [Set.uIcc_of_le (by norm_num)] at hu
    norm_num at hu
    have hu0 : 0 < u := by linarith [hu.1]
    have hum0 : 0 < u - 1 := by linarith [hu.1]
    have hprod :
        Real.sqrt (u * (u - 1)) ≠ 0 := by
      exact
        (Real.sqrt_pos.2
          (mul_pos hu0 hum0)).ne'
    apply ContinuousAt.continuousWithinAt
    exact continuousAt_const.div
      (Real.continuous_sqrt.comp
        (continuous_id.mul
          (continuous_id.sub continuous_const))).continuousAt
      hprod
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    hderiv hint, logPrimitive_endpoint]

private noncomputable def asinPrimitive (v : ℝ) : ℝ :=
  2 * Real.arcsin (Real.sqrt v)

private lemma asinPrimitive_hasDerivAt
    (v : ℝ) (hv0 : 0 < v) (hv1 : v < 1) :
    HasDerivAt asinPrimitive
      (1 / Real.sqrt (v * (1 - v))) v := by
  have hsv0 : Real.sqrt v ≠ 0 :=
    (Real.sqrt_pos.2 hv0).ne'
  have hsvLt : Real.sqrt v < 1 := by
    nlinarith [Real.sq_sqrt hv0.le,
      Real.sqrt_nonneg v]
  have hsqrt :
      HasDerivAt (fun z : ℝ => Real.sqrt z)
        (1 / (2 * Real.sqrt v)) v := by
    simpa [id_eq] using
      (hasDerivAt_id v).sqrt hv0.ne'
  have harcsin :=
    (Real.hasDerivAt_arcsin
      (by
        have := Real.sqrt_nonneg v
        linarith)
      (ne_of_lt hsvLt)).comp v hsqrt
  have hraw := harcsin.const_mul 2
  unfold asinPrimitive
  simp only [Function.comp_apply] at hraw
  convert hraw using 1
  have hsvSq : Real.sqrt v ^ 2 = v :=
    Real.sq_sqrt hv0.le
  have hOne : 0 < 1 - v := sub_pos.2 hv1
  rw [show 1 - Real.sqrt v ^ 2 = 1 - v by
    rw [hsvSq],
    Real.sqrt_mul' v hOne.le]
  have hsOne0 : Real.sqrt (1 - v) ≠ 0 :=
    (Real.sqrt_pos.2 hOne).ne'
  field_simp [hsv0, hsOne0]

theorem gap18 :
    (∫ v in (1 / 3 : ℝ)..2 / 3,
        1 / Real.sqrt (v * (1 - v))) =
      2 * Real.arcsin (Real.sqrt (2 / 3)) -
        2 * Real.arcsin (Real.sqrt (1 / 3)) := by
  have hderiv :
      ∀ v ∈ Set.uIcc (1 / 3 : ℝ) (2 / 3),
        HasDerivAt asinPrimitive
          (1 / Real.sqrt (v * (1 - v))) v := by
    intro v hv
    rw [Set.uIcc_of_le (by norm_num)] at hv
    norm_num at hv
    exact asinPrimitive_hasDerivAt v
      (by linarith) (by linarith)
  have hint :
      IntervalIntegrable
        (fun v : ℝ =>
          1 / Real.sqrt (v * (1 - v)))
        volume (1 / 3) (2 / 3) := by
    apply ContinuousOn.intervalIntegrable
    intro v hv
    rw [Set.uIcc_of_le (by norm_num)] at hv
    norm_num at hv
    have hv0 : 0 < v := by linarith [hv.1]
    have hv1 : v < 1 := by linarith [hv.2]
    have hprod :
        Real.sqrt (v * (1 - v)) ≠ 0 := by
      exact
        (Real.sqrt_pos.2
          (mul_pos hv0 (sub_pos.2 hv1))).ne'
    apply ContinuousAt.continuousWithinAt
    exact continuousAt_const.div
      (Real.continuous_sqrt.comp
        (continuous_id.mul
          (continuous_const.sub continuous_id))).continuousAt
      hprod
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    hderiv hint]
  rfl

private noncomputable def sqrtAsinPrimitive (v : ℝ) : ℝ :=
  (1 / 2) * asinPrimitive v -
    Real.sqrt (v * (1 - v))

private lemma sqrtAsinPrimitive_hasDerivAt
    (v : ℝ) (hv0 : 0 < v) (hv1 : v < 1) :
    HasDerivAt sqrtAsinPrimitive
      (Real.sqrt v / Real.sqrt (1 - v)) v := by
  have hOne : 0 < 1 - v := sub_pos.2 hv1
  have hAsin :=
    (asinPrimitive_hasDerivAt v hv0 hv1).const_mul
      (1 / 2)
  have hq :
      HasDerivAt (fun z : ℝ => z * (1 - z))
        (1 - 2 * v) v := by
    convert
      (hasDerivAt_id v).mul
        ((hasDerivAt_const v 1).sub (hasDerivAt_id v))
      using 1 <;> simp [id_eq] <;> ring
  have hq0 : v * (1 - v) ≠ 0 :=
    (mul_pos hv0 hOne).ne'
  have hsqrt :=
    hq.sqrt hq0
  have hraw := hAsin.sub hsqrt
  unfold sqrtAsinPrimitive
  convert hraw using 1
  rw [Real.sqrt_mul' v hOne.le]
  have hsv0 : Real.sqrt v ≠ 0 :=
    (Real.sqrt_pos.2 hv0).ne'
  have hsOne0 : Real.sqrt (1 - v) ≠ 0 :=
    (Real.sqrt_pos.2 hOne).ne'
  have hsvSq : Real.sqrt v ^ 2 = v :=
    Real.sq_sqrt hv0.le
  have hsOneSq : Real.sqrt (1 - v) ^ 2 = 1 - v :=
    Real.sq_sqrt hOne.le
  field_simp [hsv0, hsOne0]
  nlinarith

theorem gap19 :
    (∫ v in (1 / 3 : ℝ)..2 / 3,
        Real.sqrt v / Real.sqrt (1 - v)) =
      Real.arcsin (Real.sqrt (2 / 3)) -
        Real.arcsin (Real.sqrt (1 / 3)) := by
  have hderiv :
      ∀ v ∈ Set.uIcc (1 / 3 : ℝ) (2 / 3),
        HasDerivAt sqrtAsinPrimitive
          (Real.sqrt v / Real.sqrt (1 - v)) v := by
    intro v hv
    rw [Set.uIcc_of_le (by norm_num)] at hv
    norm_num at hv
    exact sqrtAsinPrimitive_hasDerivAt v
      (by linarith) (by linarith)
  have hint :
      IntervalIntegrable
        (fun v : ℝ =>
          Real.sqrt v / Real.sqrt (1 - v))
        volume (1 / 3) (2 / 3) := by
    apply ContinuousOn.intervalIntegrable
    intro v hv
    rw [Set.uIcc_of_le (by norm_num)] at hv
    norm_num at hv
    have hv0 : 0 < v := by linarith [hv.1]
    have hv1 : v < 1 := by linarith [hv.2]
    have hden : Real.sqrt (1 - v) ≠ 0 :=
      (Real.sqrt_pos.2 (sub_pos.2 hv1)).ne'
    apply ContinuousAt.continuousWithinAt
    exact
      (Real.continuous_sqrt.comp continuous_id).continuousAt.div
        (Real.continuous_sqrt.comp
          (continuous_const.sub continuous_id)).continuousAt
        hden
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    hderiv hint]
  unfold sqrtAsinPrimitive asinPrimitive
  have hprod :
      Real.sqrt
          ((2 / 3 : ℝ) * (1 - 2 / 3)) =
        Real.sqrt
          ((1 / 3 : ℝ) * (1 - 1 / 3)) := by
    congr 1
    norm_num
  rw [hprod]
  ring

private noncomputable def sqrtLogPrimitive (u : ℝ) : ℝ :=
  Real.sqrt (u * (u - 1)) +
    (1 / 2) * logPrimitive u

private lemma sqrtLogPrimitive_hasDerivAt
    (u : ℝ) (hu : 1 < u) :
    HasDerivAt sqrtLogPrimitive
      (Real.sqrt u / Real.sqrt (u - 1)) u := by
  have hu0 : 0 < u := lt_trans (by norm_num) hu
  have hum0 : 0 < u - 1 := sub_pos.2 hu
  have hq :
      HasDerivAt (fun z : ℝ => z * (z - 1))
        (2 * u - 1) u := by
    convert
      (hasDerivAt_id u).mul
        ((hasDerivAt_id u).sub (hasDerivAt_const u 1))
      using 1 <;> simp [id_eq] <;> ring
  have hq0 : u * (u - 1) ≠ 0 :=
    (mul_pos hu0 hum0).ne'
  have hsqrt := hq.sqrt hq0
  have hlog :=
    (logPrimitive_hasDerivAt u hu).const_mul (1 / 2)
  have hraw := hsqrt.add hlog
  unfold sqrtLogPrimitive
  convert hraw using 1
  rw [Real.sqrt_mul' u hum0.le]
  have hsu0 : Real.sqrt u ≠ 0 :=
    (Real.sqrt_pos.2 hu0).ne'
  have hsum0 : Real.sqrt (u - 1) ≠ 0 :=
    (Real.sqrt_pos.2 hum0).ne'
  have hsuSq : Real.sqrt u ^ 2 = u :=
    Real.sq_sqrt hu0.le
  have hsumSq : Real.sqrt (u - 1) ^ 2 = u - 1 :=
    Real.sq_sqrt hum0.le
  field_simp [hsu0, hsum0]
  nlinarith

private lemma sqrtLogPrimitive_endpoint :
    sqrtLogPrimitive (5 / 3) -
        sqrtLogPrimitive (4 / 3) =
      Real.sqrt 10 / 3 - 2 / 3 +
        Real.log
          ((Real.sqrt 5 + Real.sqrt 2) / 3) := by
  have hs9 : Real.sqrt 9 = 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  have hs4 : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  have hu :
      Real.sqrt
          ((5 / 3 : ℝ) * (5 / 3 - 1)) =
        Real.sqrt 10 / 3 := by
    rw [show
        (5 / 3 : ℝ) * (5 / 3 - 1) = 10 / 9 by
          norm_num,
      Real.sqrt_div (by norm_num) 9, hs9]
  have hl :
      Real.sqrt
          ((4 / 3 : ℝ) * (4 / 3 - 1)) =
        2 / 3 := by
    rw [show
        (4 / 3 : ℝ) * (4 / 3 - 1) = 4 / 9 by
          norm_num,
      Real.sqrt_div (by norm_num) 9, hs4, hs9]
  unfold sqrtLogPrimitive
  calc
    Real.sqrt ((5 / 3 : ℝ) * (5 / 3 - 1)) +
          1 / 2 * logPrimitive (5 / 3) -
        (Real.sqrt ((4 / 3 : ℝ) * (4 / 3 - 1)) +
          1 / 2 * logPrimitive (4 / 3)) =
        Real.sqrt ((5 / 3 : ℝ) * (5 / 3 - 1)) -
          Real.sqrt ((4 / 3 : ℝ) * (4 / 3 - 1)) +
          1 / 2 *
            (logPrimitive (5 / 3) -
              logPrimitive (4 / 3)) := by ring
    _ = Real.sqrt 10 / 3 - 2 / 3 +
          Real.log
            ((Real.sqrt 5 + Real.sqrt 2) / 3) := by
      rw [hu, hl, logPrimitive_endpoint]
      ring

theorem gap16 :
    (∫ u in (4 / 3 : ℝ)..5 / 3,
        Real.sqrt u / Real.sqrt (u - 1)) =
      Real.sqrt 10 / 3 - 2 / 3 +
        Real.log
          ((Real.sqrt 5 + Real.sqrt 2) / 3) := by
  have hderiv :
      ∀ u ∈ Set.uIcc (4 / 3 : ℝ) (5 / 3),
        HasDerivAt sqrtLogPrimitive
          (Real.sqrt u / Real.sqrt (u - 1)) u := by
    intro u hu
    rw [Set.uIcc_of_le (by norm_num)] at hu
    norm_num at hu
    exact sqrtLogPrimitive_hasDerivAt u
      (by linarith)
  have hint :
      IntervalIntegrable
        (fun u : ℝ =>
          Real.sqrt u / Real.sqrt (u - 1))
        volume (4 / 3) (5 / 3) := by
    apply ContinuousOn.intervalIntegrable
    intro u hu
    rw [Set.uIcc_of_le (by norm_num)] at hu
    norm_num at hu
    have hu0 : 0 < u := by linarith [hu.1]
    have hu1 : 1 < u := by linarith [hu.1]
    have hden : Real.sqrt (u - 1) ≠ 0 :=
      (Real.sqrt_pos.2 (sub_pos.2 hu1)).ne'
    apply ContinuousAt.continuousWithinAt
    exact
      (Real.continuous_sqrt.comp continuous_id).continuousAt.div
        (Real.continuous_sqrt.comp
          (continuous_id.sub continuous_const)).continuousAt
        hden
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    hderiv hint, sqrtLogPrimitive_endpoint]

private lemma separated_integrand
    (u v : ℝ) (hu : 1 < u) (hv0 : 0 < v)
    (hv1 : v < 1) :
    (u - v) /
        Real.sqrt (u * v * (1 - v) * (u - 1)) =
      (Real.sqrt u / Real.sqrt (u - 1)) *
          (1 / Real.sqrt (v * (1 - v))) -
        (1 / Real.sqrt (u * (u - 1))) *
          (Real.sqrt v / Real.sqrt (1 - v)) := by
  have hu0 : 0 < u := lt_trans (by norm_num) hu
  have hum0 : 0 < u - 1 := sub_pos.2 hu
  have hOne : 0 < 1 - v := sub_pos.2 hv1
  rw [Real.sqrt_mul'
      (u * v * (1 - v)) hum0.le,
    Real.sqrt_mul' (u * v) hOne.le,
    Real.sqrt_mul' u hv0.le,
    Real.sqrt_mul' v hOne.le,
    Real.sqrt_mul' u hum0.le]
  have hsu0 : Real.sqrt u ≠ 0 :=
    (Real.sqrt_pos.2 hu0).ne'
  have hsv0 : Real.sqrt v ≠ 0 :=
    (Real.sqrt_pos.2 hv0).ne'
  have hsOne0 : Real.sqrt (1 - v) ≠ 0 :=
    (Real.sqrt_pos.2 hOne).ne'
  have hsum0 : Real.sqrt (u - 1) ≠ 0 :=
    (Real.sqrt_pos.2 hum0).ne'
  have hsuSq : Real.sqrt u ^ 2 = u :=
    Real.sq_sqrt hu0.le
  have hsvSq : Real.sqrt v ^ 2 = v :=
    Real.sq_sqrt hv0.le
  field_simp [hsu0, hsv0, hsOne0, hsum0]
  nlinarith

private lemma intervalIntegrable_sqrtU :
    IntervalIntegrable
      (fun u : ℝ =>
        Real.sqrt u / Real.sqrt (u - 1))
      volume (4 / 3) (5 / 3) := by
  apply ContinuousOn.intervalIntegrable
  intro u hu
  rw [Set.uIcc_of_le (by norm_num)] at hu
  norm_num at hu
  have hu1 : 1 < u := by linarith [hu.1]
  have hden : Real.sqrt (u - 1) ≠ 0 :=
    (Real.sqrt_pos.2 (sub_pos.2 hu1)).ne'
  apply ContinuousAt.continuousWithinAt
  exact
    (Real.continuous_sqrt.comp continuous_id).continuousAt.div
      (Real.continuous_sqrt.comp
        (continuous_id.sub continuous_const)).continuousAt
      hden

private lemma intervalIntegrable_invU :
    IntervalIntegrable
      (fun u : ℝ =>
        1 / Real.sqrt (u * (u - 1)))
      volume (4 / 3) (5 / 3) := by
  apply ContinuousOn.intervalIntegrable
  intro u hu
  rw [Set.uIcc_of_le (by norm_num)] at hu
  norm_num at hu
  have hu0 : 0 < u := by linarith [hu.1]
  have hu1 : 1 < u := by linarith [hu.1]
  have hden : Real.sqrt (u * (u - 1)) ≠ 0 :=
    (Real.sqrt_pos.2
      (mul_pos hu0 (sub_pos.2 hu1))).ne'
  apply ContinuousAt.continuousWithinAt
  exact continuousAt_const.div
    (Real.continuous_sqrt.comp
      (continuous_id.mul
        (continuous_id.sub continuous_const))).continuousAt
    hden

private lemma intervalIntegrable_invV :
    IntervalIntegrable
      (fun v : ℝ =>
        1 / Real.sqrt (v * (1 - v)))
      volume (1 / 3) (2 / 3) := by
  apply ContinuousOn.intervalIntegrable
  intro v hv
  rw [Set.uIcc_of_le (by norm_num)] at hv
  norm_num at hv
  have hv0 : 0 < v := by linarith [hv.1]
  have hv1 : v < 1 := by linarith [hv.2]
  have hden : Real.sqrt (v * (1 - v)) ≠ 0 :=
    (Real.sqrt_pos.2
      (mul_pos hv0 (sub_pos.2 hv1))).ne'
  apply ContinuousAt.continuousWithinAt
  exact continuousAt_const.div
    (Real.continuous_sqrt.comp
      (continuous_id.mul
        (continuous_const.sub continuous_id))).continuousAt
    hden

private lemma intervalIntegrable_sqrtV :
    IntervalIntegrable
      (fun v : ℝ =>
        Real.sqrt v / Real.sqrt (1 - v))
      volume (1 / 3) (2 / 3) := by
  apply ContinuousOn.intervalIntegrable
  intro v hv
  rw [Set.uIcc_of_le (by norm_num)] at hv
  norm_num at hv
  have hv1 : v < 1 := by linarith [hv.2]
  have hden : Real.sqrt (1 - v) ≠ 0 :=
    (Real.sqrt_pos.2 (sub_pos.2 hv1)).ne'
  apply ContinuousAt.continuousWithinAt
  exact
    (Real.continuous_sqrt.comp continuous_id).continuousAt.div
      (Real.continuous_sqrt.comp
        (continuous_const.sub continuous_id)).continuousAt
      hden

private lemma scaled_integrand
    (c u v : ℝ) (hc : 0 < c) (hu : 1 < u)
    (hv0 : 0 < v) (hv1 : v < 1) :
    c ^ 2 *
        ((c ^ 2 * u - c ^ 2 * v) /
          (4 * Real.sqrt
            ((c ^ 2 * u) * (c ^ 2 * v) *
              (c ^ 2 - c ^ 2 * v) *
              (c ^ 2 * u - c ^ 2)))) =
      (1 / 4) *
        ((u - v) /
          Real.sqrt (u * v * (1 - v) * (u - 1))) := by
  have hk : 0 < c ^ 2 := sq_pos_of_pos hc
  have hu0 : 0 < u := lt_trans (by norm_num) hu
  have hum0 : 0 < u - 1 := sub_pos.2 hu
  have hOne : 0 < 1 - v := sub_pos.2 hv1
  have hbase :
      0 < u * v * (1 - v) * (u - 1) := by
    positivity
  rw [show
      (c ^ 2 * u) * (c ^ 2 * v) *
            (c ^ 2 - c ^ 2 * v) *
            (c ^ 2 * u - c ^ 2) =
        (c ^ 2) ^ 4 *
          (u * v * (1 - v) * (u - 1)) by ring,
    Real.sqrt_mul' ((c ^ 2) ^ 4) hbase.le,
    show (c ^ 2) ^ 4 = ((c ^ 2) ^ 2) ^ 2 by ring,
    Real.sqrt_sq (sq_nonneg (c ^ 2))]
  have hsbase :
      Real.sqrt (u * v * (1 - v) * (u - 1)) ≠ 0 :=
    (Real.sqrt_pos.2 hbase).ne'
  field_simp [hk.ne', hsbase]

theorem gap13 (c : ℝ) (hc : 0 < c) :
    (∫ lam in 4 / 3 * c ^ 2..5 / 3 * c ^ 2,
        ∫ mu in 1 / 3 * c ^ 2..2 / 3 * c ^ 2,
          (lam - mu) /
            (4 * Real.sqrt
              (lam * mu * (c ^ 2 - mu) *
                (lam - c ^ 2)))) =
      c ^ 2 / 4 *
        ∫ u in (4 / 3 : ℝ)..5 / 3,
          ∫ v in (1 / 3 : ℝ)..2 / 3,
            (u - v) /
              Real.sqrt
                (u * v * (1 - v) * (u - 1)) := by
  have hk : 0 < c ^ 2 := sq_pos_of_pos hc
  have houter :
      (∫ lam in 4 / 3 * c ^ 2..5 / 3 * c ^ 2,
          ∫ mu in 1 / 3 * c ^ 2..2 / 3 * c ^ 2,
            (lam - mu) /
              (4 * Real.sqrt
                (lam * mu * (c ^ 2 - mu) *
                  (lam - c ^ 2)))) =
        c ^ 2 *
          ∫ u in (4 / 3 : ℝ)..5 / 3,
            ∫ mu in 1 / 3 * c ^ 2..2 / 3 * c ^ 2,
              (c ^ 2 * u - mu) /
                (4 * Real.sqrt
                  ((c ^ 2 * u) * mu *
                    (c ^ 2 - mu) *
                    (c ^ 2 * u - c ^ 2))) := by
    rw [show 4 / 3 * c ^ 2 =
          c ^ 2 * (4 / 3 : ℝ) by ring,
      show 5 / 3 * c ^ 2 =
          c ^ 2 * (5 / 3 : ℝ) by ring]
    exact
      (intervalIntegral.mul_integral_comp_mul_left
        (f := fun lam : ℝ =>
          ∫ mu in 1 / 3 * c ^ 2..2 / 3 * c ^ 2,
            (lam - mu) /
              (4 * Real.sqrt
                (lam * mu * (c ^ 2 - mu) *
                  (lam - c ^ 2))))
        (c ^ 2)).symm
  rw [houter]
  have hinner :
      ∀ u ∈ Set.uIcc (4 / 3 : ℝ) (5 / 3),
        (∫ mu in 1 / 3 * c ^ 2..2 / 3 * c ^ 2,
            (c ^ 2 * u - mu) /
              (4 * Real.sqrt
                ((c ^ 2 * u) * mu *
                  (c ^ 2 - mu) *
                  (c ^ 2 * u - c ^ 2))) =
          c ^ 2 *
            ∫ v in (1 / 3 : ℝ)..2 / 3,
              (c ^ 2 * u - c ^ 2 * v) /
                (4 * Real.sqrt
                  ((c ^ 2 * u) * (c ^ 2 * v) *
                    (c ^ 2 - c ^ 2 * v) *
                    (c ^ 2 * u - c ^ 2)))) := by
    intro u _hu
    rw [show 1 / 3 * c ^ 2 =
          c ^ 2 * (1 / 3 : ℝ) by ring,
      show 2 / 3 * c ^ 2 =
          c ^ 2 * (2 / 3 : ℝ) by ring]
    exact
      (intervalIntegral.mul_integral_comp_mul_left
        (f := fun mu : ℝ =>
          (c ^ 2 * u - mu) /
            (4 * Real.sqrt
              ((c ^ 2 * u) * mu *
                (c ^ 2 - mu) *
                (c ^ 2 * u - c ^ 2))))
        (c ^ 2)).symm
  rw [intervalIntegral.integral_congr hinner]
  have hscaled :
      ∀ u ∈ Set.uIcc (4 / 3 : ℝ) (5 / 3),
        c ^ 2 *
            (∫ v in (1 / 3 : ℝ)..2 / 3,
              (c ^ 2 * u - c ^ 2 * v) /
                (4 * Real.sqrt
                  ((c ^ 2 * u) * (c ^ 2 * v) *
                    (c ^ 2 - c ^ 2 * v) *
                    (c ^ 2 * u - c ^ 2)))) =
          (1 / 4) *
            (∫ v in (1 / 3 : ℝ)..2 / 3,
              (u - v) /
                Real.sqrt
                  (u * v * (1 - v) * (u - 1))) := by
    intro u hu
    rw [← intervalIntegral.integral_const_mul]
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro v hv
    rw [Set.uIcc_of_le (by norm_num)] at hu hv
    exact scaled_integrand c u v hc
      (by linarith [hu.1])
      (by linarith [hv.1])
      (by linarith [hv.2])
  rw [intervalIntegral.integral_congr hscaled]
  simp only [intervalIntegral.integral_const_mul]
  ring

private lemma arcsin_sqrt_difference :
    Real.arcsin (Real.sqrt (2 / 3)) -
        Real.arcsin (Real.sqrt (1 / 3)) =
      Real.arcsin (1 / 3) := by
  have hs1nonneg :
      0 ≤ Real.sqrt (1 / 3 : ℝ) :=
    Real.sqrt_nonneg _
  have hs2nonneg :
      0 ≤ Real.sqrt (2 / 3 : ℝ) :=
    Real.sqrt_nonneg _
  have hs1sq :
      Real.sqrt (1 / 3 : ℝ) ^ 2 = 1 / 3 :=
    Real.sq_sqrt (by norm_num)
  have hs2sq :
      Real.sqrt (2 / 3 : ℝ) ^ 2 = 2 / 3 :=
    Real.sq_sqrt (by norm_num)
  have hsle :
      Real.sqrt (1 / 3 : ℝ) ≤
        Real.sqrt (2 / 3 : ℝ) := by
    exact Real.sqrt_le_sqrt (by norm_num)
  have hs1le : Real.sqrt (1 / 3 : ℝ) ≤ 1 := by
    nlinarith
  have hs2le : Real.sqrt (2 / 3 : ℝ) ≤ 1 := by
    nlinarith
  have hdelta0 :
      0 ≤
        Real.arcsin (Real.sqrt (2 / 3)) -
          Real.arcsin (Real.sqrt (1 / 3)) := by
    exact sub_nonneg.2 (Real.arcsin_le_arcsin hsle)
  have hdeltaUpper :
      Real.arcsin (Real.sqrt (2 / 3)) -
          Real.arcsin (Real.sqrt (1 / 3)) ≤
        Real.pi / 2 := by
    have hb0 :
        0 ≤ Real.arcsin (Real.sqrt (1 / 3)) :=
      Real.arcsin_nonneg.2 hs1nonneg
    linarith [Real.arcsin_le_pi_div_two
      (Real.sqrt (2 / 3))]
  have hsin :
      Real.sin
          (Real.arcsin (Real.sqrt (2 / 3)) -
            Real.arcsin (Real.sqrt (1 / 3))) =
        1 / 3 := by
    rw [Real.sin_sub,
      Real.sin_arcsin (by linarith) hs2le,
      Real.sin_arcsin (by linarith) hs1le,
      Real.cos_arcsin, Real.cos_arcsin,
      hs1sq, hs2sq]
    nlinarith [hs1sq, hs2sq]
  calc
    Real.arcsin (Real.sqrt (2 / 3)) -
          Real.arcsin (Real.sqrt (1 / 3)) =
        Real.arcsin
          (Real.sin
            (Real.arcsin (Real.sqrt (2 / 3)) -
              Real.arcsin (Real.sqrt (1 / 3)))) := by
      symm
      exact Real.arcsin_sin
        (by
          have hp : 0 < Real.pi := Real.pi_pos
          linarith)
        hdeltaUpper
    _ = Real.arcsin (1 / 3) := by rw [hsin]

private def coordRectangle (c : ℝ) :
    Set (ℝ × ℝ) :=
  Set.Icc (4 / 3 * c ^ 2) (5 / 3 * c ^ 2) ×ˢ
    Set.Icc (1 / 3 * c ^ 2) (2 / 3 * c ^ 2)

private noncomputable def inverseCoordMap
    (c : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (Real.sqrt (p.1 * p.2) / c,
    Real.sqrt
      ((c ^ 2 - p.2) * (p.1 - c ^ 2)) / c)

private lemma coordRectangle_bounds
    (c : ℝ) (hc : 0 < c) (p : ℝ × ℝ)
    (hp : p ∈ coordRectangle c) :
    0 < p.2 ∧ p.2 < c ^ 2 ∧
      c ^ 2 < p.1 ∧ 0 < p.1 - p.2 := by
  rcases hp with ⟨hlam, hmu⟩
  have hk : 0 < c ^ 2 := sq_pos_of_pos hc
  constructor
  · nlinarith [hmu.1]
  constructor
  · nlinarith [hmu.2]
  constructor
  · nlinarith [hlam.1]
  · nlinarith [hlam.1, hmu.2]

private lemma inverseCoordMap_coordinates
    (c : ℝ) (hc : 0 < c) (p : ℝ × ℝ)
    (hp : p ∈ coordRectangle c) :
    lambdaCoord c (inverseCoordMap c p).1
          (inverseCoordMap c p).2 = p.1 ∧
      muCoord c (inverseCoordMap c p).1
          (inverseCoordMap c p).2 = p.2 := by
  rcases coordRectangle_bounds c hc p hp with
    ⟨hmu0, hmuc, hlamc, hdiff⟩
  let lam := p.1
  let mu := p.2
  have hlam0 : 0 < lam := lt_trans
    (sq_pos_of_pos hc) hlamc
  have hq1 : 0 ≤ lam * mu :=
    (mul_pos hlam0 hmu0).le
  have hq2 :
      0 ≤ (c ^ 2 - mu) * (lam - c ^ 2) :=
    (mul_pos (sub_pos.2 hmuc)
      (sub_pos.2 hlamc)).le
  let x := Real.sqrt (lam * mu) / c
  let y :=
    Real.sqrt
      ((c ^ 2 - mu) * (lam - c ^ 2)) / c
  have hxrel : c ^ 2 * x ^ 2 = lam * mu := by
    dsimp [x]
    rw [div_pow, Real.sq_sqrt hq1]
    field_simp [hc.ne']
  have hyrel :
      c ^ 2 * y ^ 2 =
        (c ^ 2 - mu) * (lam - c ^ 2) := by
    dsimp [y]
    rw [div_pow, Real.sq_sqrt hq2]
    field_simp [hc.ne']
  have hsum :
      x ^ 2 + y ^ 2 + c ^ 2 = lam + mu := by
    apply (mul_left_cancel₀
      (show c ^ 2 ≠ 0 from (sq_pos_of_pos hc).ne'))
    calc
      c ^ 2 * (x ^ 2 + y ^ 2 + c ^ 2) =
          c ^ 2 * x ^ 2 + c ^ 2 * y ^ 2 +
            (c ^ 2) ^ 2 := by ring
      _ = lam * mu +
            (c ^ 2 - mu) * (lam - c ^ 2) +
            (c ^ 2) ^ 2 := by rw [hxrel, hyrel]
      _ = c ^ 2 * (lam + mu) := by ring
  have hdisc :
      discriminant c x y = (lam - mu) ^ 2 := by
    unfold discriminant
    rw [hsum]
    rw [show 4 * c ^ 2 * x ^ 2 =
      4 * (c ^ 2 * x ^ 2) by ring, hxrel]
    ring
  have hsqrt :
      Real.sqrt (discriminant c x y) =
        lam - mu := by
    rw [hdisc, Real.sqrt_sq_eq_abs,
      abs_of_pos hdiff]
  change lambdaCoord c x y = lam ∧
    muCoord c x y = mu
  constructor
  · unfold lambdaCoord
    rw [hsum, hsqrt]
    ring
  · unfold muCoord
    rw [hsum, hsqrt]
    ring

private lemma inverseCoordMap_mem_coordinateRegion
    (c : ℝ) (hc : 0 < c) (p : ℝ × ℝ)
    (hp : p ∈ coordRectangle c) :
    inverseCoordMap c p ∈ coordinateRegion c := by
  rcases coordRectangle_bounds c hc p hp with
    ⟨hmu0, hmuc, hlamc, _hdiff⟩
  have hlam0 : 0 < p.1 :=
    lt_trans (sq_pos_of_pos hc) hlamc
  have hx :
      0 < (inverseCoordMap c p).1 := by
    unfold inverseCoordMap
    dsimp
    exact div_pos
      (Real.sqrt_pos.2 (mul_pos hlam0 hmu0)) hc
  have hy :
      0 < (inverseCoordMap c p).2 := by
    unfold inverseCoordMap
    dsimp
    exact div_pos
      (Real.sqrt_pos.2
        (mul_pos (sub_pos.2 hmuc)
          (sub_pos.2 hlamc))) hc
  rcases inverseCoordMap_coordinates c hc p hp with
    ⟨hlam, hmu⟩
  rcases hp with ⟨hpLam, hpMu⟩
  unfold coordinateRegion
  exact
    ⟨hx, hy, by simpa [hlam] using hpLam.1,
      by simpa [hlam] using hpLam.2,
      by simpa [hmu] using hpMu.1,
      by simpa [hmu] using hpMu.2⟩

private lemma inverseCoordMap_of_coordinates
    (c x y : ℝ) (hc : 0 < c) (hx : 0 < x)
    (hy : 0 < y) :
    inverseCoordMap c
        (lambdaCoord c x y, muCoord c x y) =
      (x, y) := by
  rcases coordinate_algebra c x y
      (lambdaCoord c x y) (muCoord c x y)
      rfl rfl with ⟨_hdiff, hprod, hother⟩
  apply Prod.ext
  · unfold inverseCoordMap
    dsimp
    rw [hprod,
      show c ^ 2 * x ^ 2 = (c * x) ^ 2 by ring,
      Real.sqrt_sq_eq_abs,
      abs_of_pos (mul_pos hc hx)]
    field_simp [hc.ne']
  · unfold inverseCoordMap
    dsimp
    rw [hother,
      show c ^ 2 * y ^ 2 = (c * y) ^ 2 by ring,
      Real.sqrt_sq_eq_abs,
      abs_of_pos (mul_pos hc hy)]
    field_simp [hc.ne']

private lemma inverseCoordMap_image_rectangle
    (c : ℝ) (hc : 0 < c) :
    inverseCoordMap c '' coordRectangle c =
      coordinateRegion c := by
  ext z
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact inverseCoordMap_mem_coordinateRegion c hc p hp
  · intro hz
    rcases hz with
      ⟨hx, hy, hlamLo, hlamHi, hmuLo, hmuHi⟩
    let p : ℝ × ℝ :=
      (lambdaCoord c z.1 z.2,
        muCoord c z.1 z.2)
    have hp : p ∈ coordRectangle c :=
      ⟨⟨hlamLo, hlamHi⟩, ⟨hmuLo, hmuHi⟩⟩
    refine ⟨p, hp, ?_⟩
    simpa [p] using
      inverseCoordMap_of_coordinates c z.1 z.2
        hc hx hy

private lemma inverseCoordMap_injOn
    (c : ℝ) (hc : 0 < c) :
    Set.InjOn (inverseCoordMap c)
      (coordRectangle c) := by
  intro p hp q hq hpq
  have hpCoords :=
    inverseCoordMap_coordinates c hc p hp
  have hqCoords :=
    inverseCoordMap_coordinates c hc q hq
  have hLam :
      p.1 = q.1 := by
    rw [← hpCoords.1, ← hqCoords.1, hpq]
  have hMu :
      p.2 = q.2 := by
    rw [← hpCoords.2, ← hqCoords.2, hpq]
  exact Prod.ext hLam hMu

private noncomputable def inverseCoordFDeriv
    (c : ℝ) (p : ℝ × ℝ) :
    (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (Matrix.toLin (.finTwoProd ℝ) (.finTwoProd ℝ)
    !![
      p.2 /
          (2 * c * Real.sqrt (p.1 * p.2)),
        p.1 /
          (2 * c * Real.sqrt (p.1 * p.2));
      (c ^ 2 - p.2) /
          (2 * c *
            Real.sqrt
              ((c ^ 2 - p.2) * (p.1 - c ^ 2))),
        -(p.1 - c ^ 2) /
          (2 * c *
            Real.sqrt
              ((c ^ 2 - p.2) * (p.1 - c ^ 2)))
    ]).toContinuousLinearMap

private lemma hasFDerivAt_inverseCoordMap
    (c : ℝ) (hc : 0 < c) (p : ℝ × ℝ)
    (hp : p ∈ coordRectangle c) :
    HasFDerivAt (inverseCoordMap c)
      (inverseCoordFDeriv c p) p := by
  rcases coordRectangle_bounds c hc p hp with
    ⟨hmu0, hmuc, hlamc, _hdiff⟩
  have hlam0 : 0 < p.1 :=
    lt_trans (sq_pos_of_pos hc) hlamc
  have hq1 :
      p.1 * p.2 ≠ 0 :=
    (mul_pos hlam0 hmu0).ne'
  have hq2 :
      (c ^ 2 - p.2) * (p.1 - c ^ 2) ≠ 0 :=
    (mul_pos (sub_pos.2 hmuc)
      (sub_pos.2 hlamc)).ne'
  unfold inverseCoordFDeriv inverseCoordMap
  rw [Matrix.toLin_finTwoProd_toContinuousLinearMap]
  convert HasFDerivAt.prodMk (𝕜 := ℝ)
    (((hasFDerivAt_fst.mul hasFDerivAt_snd).sqrt
      hq1).mul_const c⁻¹)
    ((((hasFDerivAt_snd.const_sub (c ^ 2)).mul
      (hasFDerivAt_fst.sub_const (c ^ 2))).sqrt
        hq2).mul_const c⁻¹) using 2 <;>
    ext z <;>
    simp [smul_smul, div_eq_mul_inv] <;>
    field_simp [hc.ne', hq1, hq2] <;>
    ring

private lemma abs_det_inverseCoordFDeriv
    (c : ℝ) (hc : 0 < c) (p : ℝ × ℝ)
    (hp : p ∈ coordRectangle c) :
    |(inverseCoordFDeriv c p).det| =
      (p.1 - p.2) /
        (4 * Real.sqrt
          (p.1 * p.2 * (c ^ 2 - p.2) *
            (p.1 - c ^ 2))) := by
  rcases coordRectangle_bounds c hc p hp with
    ⟨hmu0, hmuc, hlamc, hdiff⟩
  have hlam0 : 0 < p.1 :=
    lt_trans (sq_pos_of_pos hc) hlamc
  have hq1 :
      0 < p.1 * p.2 :=
    mul_pos hlam0 hmu0
  have hq2 :
      0 < (c ^ 2 - p.2) * (p.1 - c ^ 2) :=
    mul_pos (sub_pos.2 hmuc) (sub_pos.2 hlamc)
  have hs1 :
      Real.sqrt (p.1 * p.2) ≠ 0 :=
    (Real.sqrt_pos.2 hq1).ne'
  have hs2 :
      Real.sqrt
          ((c ^ 2 - p.2) * (p.1 - c ^ 2)) ≠ 0 :=
    (Real.sqrt_pos.2 hq2).ne'
  have hdet :
      (inverseCoordFDeriv c p).det =
        -((p.1 - p.2) /
          (4 * Real.sqrt (p.1 * p.2) *
            Real.sqrt
              ((c ^ 2 - p.2) *
                (p.1 - c ^ 2)))) := by
    unfold inverseCoordFDeriv
    simp only [LinearMap.det_toContinuousLinearMap,
      LinearMap.det_toLin, Matrix.det_fin_two_of]
    field_simp [hc.ne', hs1, hs2]
    ring
  have hsqrt :
      Real.sqrt
          (p.1 * p.2 * (c ^ 2 - p.2) *
            (p.1 - c ^ 2)) =
        Real.sqrt (p.1 * p.2) *
          Real.sqrt
            ((c ^ 2 - p.2) *
              (p.1 - c ^ 2)) := by
    rw [show
        p.1 * p.2 * (c ^ 2 - p.2) *
            (p.1 - c ^ 2) =
          (p.1 * p.2) *
            ((c ^ 2 - p.2) *
              (p.1 - c ^ 2)) by ring,
      Real.sqrt_mul' (p.1 * p.2) hq2.le]
  rw [hdet, abs_neg,
    abs_of_pos (by
      exact div_pos hdiff
        (mul_pos
          (mul_pos (by norm_num)
            (Real.sqrt_pos.2 hq1))
          (Real.sqrt_pos.2 hq2))),
    hsqrt]
  ring

private noncomputable def coordinateDensity
    (c : ℝ) (p : ℝ × ℝ) : ℝ :=
  (p.1 - p.2) /
    (4 * Real.sqrt
      (p.1 * p.2 * (c ^ 2 - p.2) *
        (p.1 - c ^ 2)))

private lemma coordinateDensity_continuousOn
    (c : ℝ) (hc : 0 < c) :
    ContinuousOn (coordinateDensity c)
      (coordRectangle c) := by
  intro p hp
  rcases coordRectangle_bounds c hc p hp with
    ⟨hmu0, hmuc, hlamc, _hdiff⟩
  have hlam0 : 0 < p.1 :=
    lt_trans (sq_pos_of_pos hc) hlamc
  have hrad :
      0 <
        p.1 * p.2 * (c ^ 2 - p.2) *
          (p.1 - c ^ 2) := by
    exact mul_pos
      (mul_pos (mul_pos hlam0 hmu0)
        (sub_pos.2 hmuc))
      (sub_pos.2 hlamc)
  have hden :
      4 * Real.sqrt
        (p.1 * p.2 * (c ^ 2 - p.2) *
          (p.1 - c ^ 2)) ≠ 0 := by
    positivity
  apply ContinuousAt.continuousWithinAt
  exact
    (continuousAt_fst.sub continuousAt_snd).div
      (continuousAt_const.mul
        (Real.continuous_sqrt.comp
          (((continuous_fst.mul continuous_snd).mul
              (continuous_const.sub continuous_snd)).mul
            (continuous_fst.sub continuous_const))).continuousAt)
      hden

private lemma coordinateDensity_integrableOn
    (c : ℝ) (hc : 0 < c) :
    IntegrableOn (coordinateDensity c)
      (coordRectangle c) volume := by
  exact (coordinateDensity_continuousOn c hc).integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc)

local instance :
    Measure.IsAddHaarMeasure volume (G := ℝ × ℝ) :=
  Measure.prod.instIsAddHaarMeasure _ _

theorem gap12 (c : ℝ) (hc : 0 < c) :
    regionArea c =
      ∫ lam in 4 / 3 * c ^ 2..5 / 3 * c ^ 2,
        ∫ mu in 1 / 3 * c ^ 2..2 / 3 * c ^ 2,
          (lam - mu) /
            (4 * Real.sqrt
              (lam * mu * (c ^ 2 - mu) *
                (lam - c ^ 2))) := by
  have hs : MeasurableSet (coordRectangle c) :=
    measurableSet_Icc.prod measurableSet_Icc
  have hchange :
      (∫ z in inverseCoordMap c '' coordRectangle c,
          (1 : ℝ)) =
        ∫ p in coordRectangle c,
          coordinateDensity c p := by
    calc
      (∫ z in inverseCoordMap c '' coordRectangle c,
          (1 : ℝ)) =
          ∫ p in coordRectangle c,
            |(inverseCoordFDeriv c p).det| •
              (1 : ℝ) := by
        exact
          MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul
            volume hs
            (fun p hp =>
              (hasFDerivAt_inverseCoordMap c hc p hp).hasFDerivWithinAt)
            (inverseCoordMap_injOn c hc)
            (fun _ => (1 : ℝ))
      _ = ∫ p in coordRectangle c,
            coordinateDensity c p := by
        apply setIntegral_congr_fun hs
        intro p hp
        simpa [coordinateDensity] using
          abs_det_inverseCoordFDeriv c hc p hp
  have hprod :
      (∫ p in coordRectangle c,
          coordinateDensity c p) =
        ∫ lam in
            Set.Icc (4 / 3 * c ^ 2)
              (5 / 3 * c ^ 2),
          ∫ mu in
              Set.Icc (1 / 3 * c ^ 2)
                (2 / 3 * c ^ 2),
            coordinateDensity c (lam, mu) := by
    unfold coordRectangle
    exact MeasureTheory.setIntegral_prod
      (coordinateDensity c)
      (coordinateDensity_integrableOn c hc)
  have hlamLe :
      4 / 3 * c ^ 2 ≤ 5 / 3 * c ^ 2 := by
    have hk : 0 < c ^ 2 := sq_pos_of_pos hc
    nlinarith
  have hmuLe :
      1 / 3 * c ^ 2 ≤ 2 / 3 * c ^ 2 := by
    have hk : 0 < c ^ 2 := sq_pos_of_pos hc
    nlinarith
  have hinner :
      ∀ lam ∈
          Set.Icc (4 / 3 * c ^ 2)
            (5 / 3 * c ^ 2),
        (∫ mu in
            Set.Icc (1 / 3 * c ^ 2)
              (2 / 3 * c ^ 2),
            coordinateDensity c (lam, mu)) =
          ∫ mu in
              1 / 3 * c ^ 2..2 / 3 * c ^ 2,
            coordinateDensity c (lam, mu) := by
    intro lam _hlam
    calc
      (∫ mu in
          Set.Icc (1 / 3 * c ^ 2)
            (2 / 3 * c ^ 2),
          coordinateDensity c (lam, mu)) =
          ∫ mu in
            Set.Ioc (1 / 3 * c ^ 2)
              (2 / 3 * c ^ 2),
            coordinateDensity c (lam, mu) := by
        exact setIntegral_congr_set
          (Ioc_ae_eq_Icc (α := ℝ)
            (μ := volume)).symm
      _ = ∫ mu in
            1 / 3 * c ^ 2..2 / 3 * c ^ 2,
          coordinateDensity c (lam, mu) :=
        (intervalIntegral.integral_of_le hmuLe).symm
  unfold regionArea
  rw [← inverseCoordMap_image_rectangle c hc,
    hchange, hprod]
  calc
    (∫ lam in
        Set.Icc (4 / 3 * c ^ 2)
          (5 / 3 * c ^ 2),
        ∫ mu in
            Set.Icc (1 / 3 * c ^ 2)
              (2 / 3 * c ^ 2),
          coordinateDensity c (lam, mu)) =
        ∫ lam in
            Set.Icc (4 / 3 * c ^ 2)
              (5 / 3 * c ^ 2),
          ∫ mu in
              1 / 3 * c ^ 2..2 / 3 * c ^ 2,
            coordinateDensity c (lam, mu) := by
      apply setIntegral_congr_fun measurableSet_Icc
      exact hinner
    _ = ∫ lam in
          Set.Ioc (4 / 3 * c ^ 2)
            (5 / 3 * c ^ 2),
        ∫ mu in
            1 / 3 * c ^ 2..2 / 3 * c ^ 2,
          coordinateDensity c (lam, mu) := by
      exact setIntegral_congr_set
        (Ioc_ae_eq_Icc (α := ℝ)
          (μ := volume)).symm
    _ = ∫ lam in
          4 / 3 * c ^ 2..5 / 3 * c ^ 2,
        ∫ mu in
            1 / 3 * c ^ 2..2 / 3 * c ^ 2,
          coordinateDensity c (lam, mu) :=
      (intervalIntegral.integral_of_le hlamLe).symm
    _ = ∫ lam in
          4 / 3 * c ^ 2..5 / 3 * c ^ 2,
        ∫ mu in
            1 / 3 * c ^ 2..2 / 3 * c ^ 2,
          (lam - mu) /
            (4 * Real.sqrt
              (lam * mu * (c ^ 2 - mu) *
                (lam - c ^ 2))) := by
      rfl

theorem gap14 (c : ℝ) (hc : 0 < c) :
    regionArea c =
      c ^ 2 / 4 *
        ∫ u in (4 / 3 : ℝ)..5 / 3,
          ∫ v in (1 / 3 : ℝ)..2 / 3,
            (u - v) /
              Real.sqrt
                (u * v * (1 - v) * (u - 1)) := by
  rw [gap12 c hc, gap13 c hc]

theorem gap15 (c : ℝ) (hc : 0 < c) :
    regionArea c =
      c ^ 2 / 4 *
          (∫ u in (4 / 3 : ℝ)..5 / 3,
            Real.sqrt u / Real.sqrt (u - 1)) *
          (∫ v in (1 / 3 : ℝ)..2 / 3,
            1 / Real.sqrt (v * (1 - v))) -
        c ^ 2 / 4 *
          (∫ u in (4 / 3 : ℝ)..5 / 3,
            1 / Real.sqrt (u * (u - 1))) *
          (∫ v in (1 / 3 : ℝ)..2 / 3,
            Real.sqrt v / Real.sqrt (1 - v)) := by
  rw [gap14 c hc]
  have hinner :
      ∀ u ∈ Set.uIcc (4 / 3 : ℝ) (5 / 3),
        (∫ v in (1 / 3 : ℝ)..2 / 3,
            (u - v) /
              Real.sqrt
                (u * v * (1 - v) * (u - 1))) =
          (Real.sqrt u / Real.sqrt (u - 1)) *
              (∫ v in (1 / 3 : ℝ)..2 / 3,
                1 / Real.sqrt (v * (1 - v))) -
            (1 / Real.sqrt (u * (u - 1))) *
              (∫ v in (1 / 3 : ℝ)..2 / 3,
                Real.sqrt v / Real.sqrt (1 - v)) := by
    intro u hu
    rw [Set.uIcc_of_le (by norm_num)] at hu
    norm_num at hu
    have hcongr :
        (∫ v in (1 / 3 : ℝ)..2 / 3,
            (u - v) /
              Real.sqrt
                (u * v * (1 - v) * (u - 1))) =
          ∫ v in (1 / 3 : ℝ)..2 / 3,
            (Real.sqrt u / Real.sqrt (u - 1)) *
                (1 / Real.sqrt (v * (1 - v))) -
              (1 / Real.sqrt (u * (u - 1))) *
                (Real.sqrt v / Real.sqrt (1 - v)) := by
      apply intervalIntegral.integral_congr
      intro v hv
      rw [Set.uIcc_of_le (by norm_num)] at hv
      exact separated_integrand u v
        (by linarith [hu.1])
        (by linarith [hv.1])
        (by linarith [hv.2])
    rw [hcongr]
    rw [intervalIntegral.integral_sub
      (by
        exact intervalIntegrable_invV.const_mul
            (Real.sqrt u / Real.sqrt (u - 1)))
      (by
        exact intervalIntegrable_sqrtV.const_mul
            (1 / Real.sqrt (u * (u - 1))))]
    simp only [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_congr hinner]
  rw [intervalIntegral.integral_sub
    (by
      exact intervalIntegrable_sqrtU.mul_const
          (∫ v in (1 / 3 : ℝ)..2 / 3,
            1 / Real.sqrt (v * (1 - v))))
    (by
      exact intervalIntegrable_invU.mul_const
          (∫ v in (1 / 3 : ℝ)..2 / 3,
            Real.sqrt v / Real.sqrt (1 - v)))]
  simp only [intervalIntegral.integral_mul_const]
  ring

theorem gap20 (c : ℝ) (hc : 0 < c) :
    regionArea c =
      c ^ 2 / 6 * (Real.sqrt 10 - 2) *
        Real.arcsin (1 / 3) := by
  rw [gap15 c hc, gap16, gap17, gap18, gap19,
    arcsin_sqrt_difference]
  have ha :
      Real.arcsin (Real.sqrt (2 / 3)) =
        Real.arcsin (1 / 3) +
          Real.arcsin (Real.sqrt (1 / 3)) := by
    linarith [arcsin_sqrt_difference]
  rw [ha]
  ring

end

end ProofGap.Exercise4000
