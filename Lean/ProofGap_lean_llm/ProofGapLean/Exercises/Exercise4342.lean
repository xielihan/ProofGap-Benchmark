import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4342

noncomputable section

open scoped Interval

abbrev Point3 := ℝ × (ℝ × ℝ)

def radialParam (a r θ y : ℝ) : Point3 :=
  (a * r * Real.sin θ, (y, a + a * r * Real.cos θ))

def cylinderSurface (a : ℝ) : Set Point3 :=
  {p | p.1 ^ 2 + p.2.2 ^ 2 = 2 * a * p.2.2}

def surfaceSet (a : ℝ) : Set Point3 :=
  {p |
    p.1 ^ 2 + p.2.2 ^ 2 = 2 * a * p.2.2 ∧
      Real.sqrt (p.1 ^ 2 + p.2.1 ^ 2) ≤ p.2.2}

def halfWidth (a θ : ℝ) : ℝ :=
  Real.sqrt 2 * a *
    Real.sqrt (Real.cos θ * (1 + Real.cos θ))

def surfaceMoment (a : ℝ) : ℝ :=
  ∫ θ in (-Real.pi / 2)..Real.pi / 2,
    ∫ y in -halfWidth a θ..halfWidth a θ,
      (a + a * Real.cos θ) * a

def reducedIntegrand (a θ : ℝ) : ℝ :=
  2 * Real.sqrt 2 * a ^ 3 *
    Real.sqrt (Real.cos θ) *
    Real.sqrt ((1 + Real.cos θ) ^ 3)

def betaIntegrand (t : ℝ) : ℝ :=
  Real.rpow t (1 / 2 : ℝ) * Real.rpow (1 - t) (-1 / 2 : ℝ) +
    Real.rpow t (3 / 2 : ℝ) * Real.rpow (1 - t) (-1 / 2 : ℝ)

def betaFn (x y : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1,
    Real.rpow t (x - 1) * Real.rpow (1 - t) (y - 1)

private theorem integral_even_neg_pos
    (f : ℝ → ℝ) (A : ℝ) (hA : 0 ≤ A)
    (hint : IntervalIntegrable f MeasureTheory.volume (-A) A)
    (heven : ∀ x : ℝ, f (-x) = f x) :
    (∫ x in -A..A, f x) =
      2 * ∫ x in (0 : ℝ)..A, f x := by
  have hleft : IntervalIntegrable f MeasureTheory.volume (-A) 0 :=
    hint.mono_set (by
      rw [Set.uIcc_of_le (neg_nonpos.2 hA),
        Set.uIcc_of_le (by linarith : -A ≤ A)]
      intro x hx
      exact ⟨hx.1, hx.2.trans hA⟩)
  have hright : IntervalIntegrable f MeasureTheory.volume 0 A :=
    hint.mono_set (by
      rw [Set.uIcc_of_le hA,
        Set.uIcc_of_le (by linarith : -A ≤ A)]
      intro x hx
      exact ⟨by linarith [hx.1], hx.2⟩)
  have hsplit :=
    intervalIntegral.integral_add_adjacent_intervals hleft hright
  have hreflect :
      (∫ x in -A..(0 : ℝ), f x) =
        ∫ x in (0 : ℝ)..A, f x := by
    calc
      (∫ x in -A..(0 : ℝ), f x) =
          ∫ x in (0 : ℝ)..A, f (-x) := by
        simpa using
          (intervalIntegral.integral_comp_neg
            (f := f) (a := (0 : ℝ)) (b := A)).symm
      _ = ∫ x in (0 : ℝ)..A, f x := by
        apply intervalIntegral.integral_congr
        intro x hx
        exact heven x
  rw [← hsplit, hreflect]
  ring

private theorem betaTerm_intervalIntegrable
    (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    IntervalIntegrable
      (fun t : ℝ =>
        Real.rpow t (x - 1) * Real.rpow (1 - t) (y - 1))
      MeasureTheory.volume 0 1 := by
  have hc :=
    Complex.betaIntegral_convergent
      (u := (x : ℂ)) (v := (y : ℂ))
      (by simpa using hx) (by simpa using hy)
  have hn := hc.norm
  refine hn.congr ?_
  intro t ht
  rw [Set.uIoc_of_le zero_le_one] at ht
  have ht0 : 0 ≤ t := ht.1.le
  have ht1 : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
  change
    ‖(t : ℂ) ^ (((x : ℂ) - 1)) *
        (1 - (t : ℂ)) ^ (((y : ℂ) - 1))‖ =
      Real.rpow t (x - 1) * Real.rpow (1 - t) (y - 1)
  have hnorm1 :
      ‖(t : ℂ) ^ (((x : ℂ) - 1))‖ =
        Real.rpow t (x - 1) := by
    simpa [Complex.norm_real, abs_of_nonneg ht0] using
      (Complex.norm_cpow_real (t : ℂ) (x - 1))
  have hnorm2 :
      ‖(1 - (t : ℂ)) ^ (((y : ℂ) - 1))‖ =
        Real.rpow (1 - t) (y - 1) := by
    have hbase : ‖1 - (t : ℂ)‖ = 1 - t := by
      rw [show 1 - (t : ℂ) = ((1 - t : ℝ) : ℂ) by norm_num,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht1]
    have hbase' : ‖((1 - t : ℝ) : ℂ)‖ = 1 - t := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht1]
    have hnormraw :=
      Complex.norm_cpow_real ((1 - t : ℝ) : ℂ) (y - 1)
    rw [hbase'] at hnormraw
    convert hnormraw using 1 <;> norm_num
  rw [norm_mul, hnorm1, hnorm2]

private theorem sqrt_cube (q : ℝ) (hq : 0 ≤ q) :
    Real.sqrt (q ^ 3) = q * Real.sqrt q := by
  rw [show q ^ 3 = q ^ 2 * q by ring,
    Real.sqrt_mul (sq_nonneg q), Real.sqrt_sq_eq_abs,
    abs_of_nonneg hq]

theorem gap1 (a r θ y : ℝ) :
    (radialParam a r θ y).1 = a * r * Real.sin θ := by
  rfl

theorem gap2 (a r θ y : ℝ) :
    (radialParam a r θ y).2.1 = y := by
  rfl

theorem gap3 (a r θ y : ℝ) :
    (radialParam a r θ y).2.2 =
      a + a * r * Real.cos θ := by
  rfl

theorem gap4
    (a r θ y : ℝ) (ha : 0 < a) (hr : 0 ≤ r)
    (hp : radialParam a r θ y ∈ cylinderSurface a) :
    r = 1 := by
  change
    (a * r * Real.sin θ) ^ 2 +
        (a + a * r * Real.cos θ) ^ 2 =
      2 * a * (a + a * r * Real.cos θ) at hp
  have htrig := Real.sin_sq_add_cos_sq θ
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  have hfactor : a ^ 2 * r ^ 2 = a ^ 2 := by
    nlinarith
  have hrsq : r ^ 2 = 1 := by
    nlinarith
  nlinarith

theorem gap5
    (a r θ y : ℝ) (ha : 0 < a) (hr : 0 ≤ r)
    (hp : radialParam a r θ y ∈ surfaceSet a) :
    y ^ 2 ≤
      2 * a ^ 2 * Real.cos θ * (1 + Real.cos θ) := by
  have hr1 : r = 1 := by
    apply gap4 a r θ y ha hr
    exact hp.1
  subst r
  change
    ((a * 1 * Real.sin θ) ^ 2 +
          (a + a * 1 * Real.cos θ) ^ 2 =
        2 * a * (a + a * 1 * Real.cos θ)) ∧
      Real.sqrt
          ((a * 1 * Real.sin θ) ^ 2 + y ^ 2) ≤
        a + a * 1 * Real.cos θ at hp
  norm_num at hp
  have hroot0 :
      0 ≤ Real.sqrt ((a * Real.sin θ) ^ 2 + y ^ 2) :=
    Real.sqrt_nonneg _
  have hz0 : 0 ≤ a + a * Real.cos θ :=
    hroot0.trans hp.2
  have harg0 : 0 ≤ (a * Real.sin θ) ^ 2 + y ^ 2 := by positivity
  have hroot_sq :
      Real.sqrt ((a * Real.sin θ) ^ 2 + y ^ 2) ^ 2 =
        (a * Real.sin θ) ^ 2 + y ^ 2 :=
    Real.sq_sqrt harg0
  have hsq :
      (a * Real.sin θ) ^ 2 + y ^ 2 ≤
        (a + a * Real.cos θ) ^ 2 := by
    have hmul :=
      mul_nonneg (sub_nonneg.mpr hp.2) (add_nonneg hroot0 hz0)
    nlinarith
  nlinarith [Real.sin_sq_add_cos_sq θ]

theorem gap6 (a θ y : ℝ) :
    (radialParam a 1 θ y).1 = a * Real.sin θ := by
  simp [radialParam]

theorem gap7
    (a θ y : ℝ) (ha : 0 < a)
    (hθ : θ ∈ Set.Icc (-Real.pi / 2) (Real.pi / 2))
    (hp : radialParam a 1 θ y ∈ surfaceSet a) :
    |y| ≤ halfWidth a θ := by
  have hy :=
    gap5 a 1 θ y ha zero_le_one hp
  have hcos : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc (by
      convert hθ using 1 <;> ring)
  have hq : 0 ≤ 1 + Real.cos θ := by linarith
  have hprod : 0 ≤ Real.cos θ * (1 + Real.cos θ) :=
    mul_nonneg hcos hq
  have hsqrt2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hhalf : 0 ≤ halfWidth a θ := by
    unfold halfWidth
    positivity
  have hsqrt2sq : (Real.sqrt 2) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  have hprodsq :
      Real.sqrt (Real.cos θ * (1 + Real.cos θ)) ^ 2 =
        Real.cos θ * (1 + Real.cos θ) :=
    Real.sq_sqrt hprod
  have hhalf_sq :
      halfWidth a θ ^ 2 =
        2 * a ^ 2 * Real.cos θ * (1 + Real.cos θ) := by
    unfold halfWidth
    rw [mul_pow, mul_pow, hsqrt2sq, hprodsq]
    ring
  nlinarith [sq_abs y]

theorem gap8 (a θ y : ℝ) :
    (radialParam a 1 θ y).2.2 =
      a + a * Real.cos θ := by
  simp [radialParam]

theorem gap9 (a : ℝ) (ha : 0 < a) :
    surfaceMoment a =
      ∫ θ in (-Real.pi / 2)..Real.pi / 2,
        ∫ y in -halfWidth a θ..halfWidth a θ,
          (a + a * Real.cos θ) * a := by
  rfl

theorem gap10 (a : ℝ) (ha : 0 < a) :
    surfaceMoment a =
      ∫ θ in (-Real.pi / 2)..Real.pi / 2,
        reducedIntegrand a θ := by
  unfold surfaceMoment
  apply intervalIntegral.integral_congr
  intro θ hθ
  rw [Set.uIcc_of_le (by linarith [Real.pi_pos])] at hθ
  have hcos : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc (by
      convert hθ using 1 <;> ring)
  have hq : 0 ≤ 1 + Real.cos θ := by linarith
  have hprod : 0 ≤ Real.cos θ * (1 + Real.cos θ) :=
    mul_nonneg hcos hq
  change
    (∫ _y in -halfWidth a θ..halfWidth a θ,
      (a + a * Real.cos θ) * a) =
        reducedIntegrand a θ
  rw [intervalIntegral.integral_const]
  unfold halfWidth reducedIntegrand
  simp only [smul_eq_mul]
  rw [Real.sqrt_mul hcos, sqrt_cube (1 + Real.cos θ) hq]
  ring

theorem gap11 (a : ℝ) (ha : 0 < a) :
    surfaceMoment a =
      4 * Real.sqrt 2 * a ^ 3 *
        (∫ θ in (0 : ℝ)..Real.pi / 2,
          Real.sqrt (Real.cos θ) *
            Real.sqrt ((1 + Real.cos θ) ^ 3)) := by
  let f : ℝ → ℝ := fun θ =>
    Real.sqrt (Real.cos θ) *
      Real.sqrt ((1 + Real.cos θ) ^ 3)
  have hf : Continuous f := by
    dsimp [f]
    fun_prop
  have heven : ∀ θ : ℝ, f (-θ) = f θ := by
    intro θ
    simp [f]
  have hsym :
      (∫ θ in (-Real.pi / 2)..Real.pi / 2, f θ) =
        2 * ∫ θ in (0 : ℝ)..Real.pi / 2, f θ := by
    convert
      integral_even_neg_pos f (Real.pi / 2)
        (by positivity) (hf.intervalIntegrable _ _) heven using 1 <;>
      ring
  rw [gap10 a ha]
  calc
    (∫ θ in (-Real.pi / 2)..Real.pi / 2,
        reducedIntegrand a θ) =
        ∫ θ in (-Real.pi / 2)..Real.pi / 2,
          (2 * Real.sqrt 2 * a ^ 3) * f θ := by
      apply intervalIntegral.integral_congr
      intro θ hθ
      simp only [reducedIntegrand, f]
      ring
    _ = (2 * Real.sqrt 2 * a ^ 3) *
        (∫ θ in (-Real.pi / 2)..Real.pi / 2, f θ) := by
      rw [intervalIntegral.integral_const_mul]
    _ = 4 * Real.sqrt 2 * a ^ 3 *
        (∫ θ in (0 : ℝ)..Real.pi / 2, f θ) := by
      rw [hsym]
      ring
    _ = 4 * Real.sqrt 2 * a ^ 3 *
        (∫ θ in (0 : ℝ)..Real.pi / 2,
          Real.sqrt (Real.cos θ) *
            Real.sqrt ((1 + Real.cos θ) ^ 3)) := by
      rfl

private theorem betaIntegrand_intervalIntegrable :
    IntervalIntegrable betaIntegrand MeasureTheory.volume 0 1 := by
  have h1 := betaTerm_intervalIntegrable
    (3 / 2 : ℝ) (1 / 2 : ℝ) (by norm_num) (by norm_num)
  have h2 := betaTerm_intervalIntegrable
    (5 / 2 : ℝ) (1 / 2 : ℝ) (by norm_num) (by norm_num)
  convert h1.add h2 using 1
  ext t
  norm_num [betaIntegrand]

private theorem angular_beta_relation
    (θ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    betaIntegrand (Real.cos θ) * Real.sin θ =
      Real.sqrt (Real.cos θ) *
        Real.sqrt ((1 + Real.cos θ) ^ 3) := by
  have hθpi : θ < Real.pi := by
    nlinarith [hθ.2, Real.pi_pos]
  have hsin : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ.1 hθpi
  have hcos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo (by
      constructor <;> nlinarith [hθ.1, hθ.2, Real.pi_pos])
  have hcosle : Real.cos θ ≤ 1 := Real.cos_le_one θ
  have hcosne : Real.cos θ ≠ 1 := by
    intro hc
    have hθ0 : θ = 0 := by
      apply (Real.cos_eq_one_iff_of_lt_of_lt
        (x := θ) (by nlinarith [hθ.1, Real.pi_pos])
        (by nlinarith [hθ.2, Real.pi_pos])).1
      exact hc
    nlinarith [hθ.1]
  have hcoslt : Real.cos θ < 1 :=
    lt_of_le_of_ne hcosle hcosne
  have hsub : 0 < 1 - Real.cos θ := sub_pos.mpr hcoslt
  have hq : 0 < 1 + Real.cos θ := by linarith
  have hsubsqrt :
      Real.sqrt (1 - Real.cos θ) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr hsub
  have hsqrtprod :
      Real.sqrt (1 - Real.cos θ) *
          Real.sqrt (1 + Real.cos θ) =
        Real.sin θ := by
    calc
      Real.sqrt (1 - Real.cos θ) *
          Real.sqrt (1 + Real.cos θ) =
          Real.sqrt
            ((1 - Real.cos θ) * (1 + Real.cos θ)) := by
        rw [Real.sqrt_mul hsub.le]
      _ = Real.sqrt (Real.sin θ ^ 2) := by
        congr 1
        nlinarith [Real.sin_sq_add_cos_sq θ]
      _ = |Real.sin θ| := Real.sqrt_sq_eq_abs _
      _ = Real.sin θ := abs_of_pos hsin
  have hratio :
      Real.sin θ / Real.sqrt (1 - Real.cos θ) =
        Real.sqrt (1 + Real.cos θ) := by
    field_simp [hsubsqrt]
    nlinarith [hsqrtprod]
  have hcosHalf :
      Real.rpow (Real.cos θ) (1 / 2 : ℝ) =
        Real.sqrt (Real.cos θ) := by
    rw [Real.rpow_eq_pow, ← Real.sqrt_eq_rpow]
  have hcosThreeHalf :
      Real.rpow (Real.cos θ) (3 / 2 : ℝ) =
        Real.cos θ * Real.sqrt (Real.cos θ) := by
    calc
      Real.rpow (Real.cos θ) (3 / 2 : ℝ) =
          Real.rpow (Real.cos θ) (1 + 1 / 2) := by norm_num
      _ = Real.rpow (Real.cos θ) 1 *
          Real.rpow (Real.cos θ) (1 / 2) :=
        Real.rpow_add hcos 1 (1 / 2)
      _ = Real.cos θ * Real.sqrt (Real.cos θ) := by
        have hone : Real.rpow (Real.cos θ) 1 = Real.cos θ := by
          simp
        rw [hone]
        exact congrArg (fun z : ℝ => Real.cos θ * z) hcosHalf
  have hsubNegHalf :
      Real.rpow (1 - Real.cos θ) (-1 / 2 : ℝ) =
        (Real.sqrt (1 - Real.cos θ))⁻¹ := by
    calc
      Real.rpow (1 - Real.cos θ) (-1 / 2 : ℝ) =
          Real.rpow (1 - Real.cos θ) (-(1 / 2)) := by ring
      _ = (Real.rpow (1 - Real.cos θ) (1 / 2))⁻¹ :=
        Real.rpow_neg hsub.le (1 / 2)
      _ = (Real.sqrt (1 - Real.cos θ))⁻¹ := by
        rw [Real.rpow_eq_pow, ← Real.sqrt_eq_rpow]
  unfold betaIntegrand
  rw [hcosHalf, hcosThreeHalf, hsubNegHalf]
  rw [sqrt_cube (1 + Real.cos θ) hq.le, ← hratio]
  simp only [div_eq_mul_inv]
  ring

private theorem angular_integral_eq_beta :
    (∫ θ in (0 : ℝ)..Real.pi / 2,
      Real.sqrt (Real.cos θ) *
        Real.sqrt ((1 + Real.cos θ) ^ 3)) =
      ∫ t in (0 : ℝ)..1, betaIntegrand t := by
  let ang : ℝ → ℝ := fun θ =>
    Real.sqrt (Real.cos θ) *
      Real.sqrt ((1 + Real.cos θ) ^ 3)
  let source : ℝ → ℝ := fun θ =>
    (betaIntegrand ∘ Real.cos) θ * (-Real.sin θ)
  have hab : (0 : ℝ) < Real.pi / 2 := by positivity
  have hang : Continuous ang := by
    dsimp [ang]
    fun_prop
  have hsourceEq :
      Set.EqOn (fun θ => -ang θ) source
        (Set.uIoc (0 : ℝ) (Real.pi / 2)) := by
    intro θ hθ
    rw [Set.uIoc_of_le hab.le] at hθ
    by_cases heq : θ = Real.pi / 2
    · subst θ
      simp [ang, source, betaIntegrand]
    · have hθ' : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
        ⟨hθ.1, lt_of_le_of_ne hθ.2 heq⟩
      have hrel := angular_beta_relation θ hθ'
      dsimp [ang, source, Function.comp_def]
      nlinarith
  have hsourceInterval :
      IntervalIntegrable source MeasureTheory.volume
        (0 : ℝ) (Real.pi / 2) := by
    exact (hang.neg.intervalIntegrable _ _).congr hsourceEq
  have hcosCont : ContinuousOn Real.cos
      (Set.uIcc (0 : ℝ) (Real.pi / 2)) :=
    Real.continuous_cos.continuousOn
  have hcosDeriv :
      ∀ θ ∈ Set.Ioo
          (min (0 : ℝ) (Real.pi / 2))
          (max (0 : ℝ) (Real.pi / 2)),
        HasDerivWithinAt Real.cos (-Real.sin θ)
          (Set.Ioi θ) θ := by
    intro θ hθ
    exact (Real.hasDerivAt_cos θ).hasDerivWithinAt
  have hbetaCont :
      ContinuousOn betaIntegrand
        (Real.cos '' Set.Ioo
          (min (0 : ℝ) (Real.pi / 2))
          (max (0 : ℝ) (Real.pi / 2))) := by
    rintro t ⟨θ, hθ, rfl⟩
    rw [min_eq_left hab.le, max_eq_right hab.le] at hθ
    have hcpos : 0 < Real.cos θ :=
      Real.cos_pos_of_mem_Ioo (by
        constructor <;> nlinarith [hθ.1, hθ.2, Real.pi_pos])
    have hclt : Real.cos θ < 1 := by
      have hcle := Real.cos_le_one θ
      have hcne : Real.cos θ ≠ 1 := by
        intro hc
        have hzero :=
          (Real.cos_eq_one_iff_of_lt_of_lt
            (x := θ) (by nlinarith [hθ.1, Real.pi_pos])
            (by nlinarith [hθ.2, Real.pi_pos])).1 hc
        nlinarith [hθ.1]
      exact lt_of_le_of_ne hcle hcne
    have hpow
        (q : ℝ) (hq : 0 < q) (e : ℝ) :
        ContinuousAt (fun x : ℝ => Real.rpow x e) q := by
      simpa [Real.rpow_eq_pow] using
        Real.continuousAt_rpow_const q e (Or.inl hq.ne')
    have h1 : ContinuousAt
        (fun x : ℝ => Real.rpow x (1 / 2 : ℝ))
        (Real.cos θ) :=
      hpow (Real.cos θ) hcpos (1 / 2)
    have h3 : ContinuousAt
        (fun x : ℝ => Real.rpow x (3 / 2 : ℝ))
        (Real.cos θ) :=
      hpow (Real.cos θ) hcpos (3 / 2)
    have hmBase : ContinuousAt
        (fun x : ℝ => Real.rpow x (-1 / 2 : ℝ))
        (1 - Real.cos θ) :=
      hpow (1 - Real.cos θ) (sub_pos.mpr hclt) (-1 / 2)
    have hm : ContinuousAt
        (fun x : ℝ => Real.rpow (1 - x) (-1 / 2 : ℝ))
        (Real.cos θ) :=
      by
        simpa [Function.comp_def] using
          hmBase.comp (continuousAt_const.sub continuousAt_id)
    change ContinuousWithinAt
      (fun x : ℝ =>
        Real.rpow x (1 / 2 : ℝ) *
            Real.rpow (1 - x) (-1 / 2 : ℝ) +
          Real.rpow x (3 / 2 : ℝ) *
            Real.rpow (1 - x) (-1 / 2 : ℝ))
      (Real.cos '' Set.Ioo
        (min (0 : ℝ) (Real.pi / 2))
        (max (0 : ℝ) (Real.pi / 2)))
      (Real.cos θ)
    exact ((h1.mul hm).add (h3.mul hm)).continuousWithinAt
  have hbetaImage :
      MeasureTheory.IntegrableOn betaIntegrand
        (Real.cos '' Set.uIcc (0 : ℝ) (Real.pi / 2))
        MeasureTheory.volume := by
    have hIcc :
        MeasureTheory.IntegrableOn betaIntegrand
          (Set.Icc (0 : ℝ) 1) MeasureTheory.volume :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le
        zero_le_one).1 betaIntegrand_intervalIntegrable
    apply hIcc.mono_set
    rintro t ⟨θ, hθ, rfl⟩
    rw [Set.uIcc_of_le hab.le] at hθ
    constructor
    · apply Real.cos_nonneg_of_mem_Icc
      constructor <;> nlinarith [hθ.1, hθ.2, Real.pi_pos]
    · exact Real.cos_le_one θ
  have hsourceOn :
      MeasureTheory.IntegrableOn source
        (Set.uIcc (0 : ℝ) (Real.pi / 2))
        MeasureTheory.volume := by
    rw [Set.uIcc_of_le hab.le]
    exact
      (intervalIntegrable_iff_integrableOn_Icc_of_le hab.le).1
        hsourceInterval
  have hsub :=
    intervalIntegral.integral_comp_mul_deriv'''
      (a := (0 : ℝ)) (b := Real.pi / 2)
      (f := Real.cos) (f' := fun θ => -Real.sin θ)
      (g := betaIntegrand)
      hcosCont hcosDeriv hbetaCont hbetaImage hsourceOn
  have hleft :
      (∫ θ in (0 : ℝ)..Real.pi / 2, source θ) =
        -(∫ θ in (0 : ℝ)..Real.pi / 2, ang θ) := by
    calc
      (∫ θ in (0 : ℝ)..Real.pi / 2, source θ) =
          ∫ θ in (0 : ℝ)..Real.pi / 2, -ang θ := by
        apply intervalIntegral.integral_congr_ae
        exact Filter.Eventually.of_forall (fun θ hθ =>
          (hsourceEq hθ).symm)
      _ = -(∫ θ in (0 : ℝ)..Real.pi / 2, ang θ) := by
        rw [intervalIntegral.integral_neg]
  have hright :
      (∫ t in Real.cos 0..Real.cos (Real.pi / 2),
        betaIntegrand t) =
        -(∫ t in (0 : ℝ)..1, betaIntegrand t) := by
    rw [Real.cos_zero, Real.cos_pi_div_two,
      intervalIntegral.integral_symm]
  change
    (∫ θ in (0 : ℝ)..Real.pi / 2, ang θ) =
      ∫ t in (0 : ℝ)..1, betaIntegrand t
  change
    (∫ θ in (0 : ℝ)..Real.pi / 2, source θ) =
      ∫ t in Real.cos 0..Real.cos (Real.pi / 2),
        betaIntegrand t at hsub
  rw [hleft, hright] at hsub
  linarith

private theorem betaFn_as_complex (x y : ℝ) :
    (betaFn x y : ℂ) =
      Complex.betaIntegral (x : ℂ) (y : ℂ) := by
  rw [betaFn, ← intervalIntegral.integral_ofReal,
    Complex.betaIntegral]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le zero_le_one] at ht
  have ht0 : 0 ≤ t := ht.1
  have ht1 : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
  have hleft :
      (((Real.rpow t (x - 1)) : ℝ) : ℂ) =
        (t : ℂ) ^ ((x - 1 : ℝ) : ℂ) := by
    rw [Real.rpow_eq_pow]
    exact Complex.ofReal_cpow ht0 (x - 1)
  have hright :
      (((Real.rpow (1 - t) (y - 1)) : ℝ) : ℂ) =
        ((1 - t : ℝ) : ℂ) ^ ((y - 1 : ℝ) : ℂ) := by
    rw [Real.rpow_eq_pow]
    exact Complex.ofReal_cpow ht1 (y - 1)
  change
    (((Real.rpow t (x - 1) *
        Real.rpow (1 - t) (y - 1) : ℝ)) : ℂ) =
      (t : ℂ) ^ ((x : ℂ) - 1) *
        (1 - (t : ℂ)) ^ ((y : ℂ) - 1)
  rw [Complex.ofReal_mul, hleft, hright]
  push_cast
  rfl

private theorem betaFn_three_halves_one_half :
    betaFn (3 / 2) (1 / 2) = Real.pi / 2 := by
  apply Complex.ofReal_injective
  rw [betaFn_as_complex]
  rw [Complex.betaIntegral_eq_Gamma_mul_div
    (((3 / 2 : ℝ) : ℂ)) (((1 / 2 : ℝ) : ℂ))
    (by norm_num) (by norm_num)]
  have h32 : (3 / 2 : ℂ) = ((3 / 2 : ℝ) : ℂ) := by norm_num
  have h12 : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  have hsum :
      ((3 / 2 : ℝ) : ℂ) + ((1 / 2 : ℝ) : ℂ) =
        ((2 : ℝ) : ℂ) := by norm_num
  rw [hsum]
  rw [Complex.Gamma_ofReal, Complex.Gamma_ofReal,
    Complex.Gamma_ofReal]
  push_cast
  rw [show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num,
    Real.Gamma_add_one (by norm_num : (1 / 2 : ℝ) ≠ 0),
    Real.Gamma_one_half_eq]
  rw [show (2 : ℝ) = (1 : ℕ) + 1 by norm_num,
    Real.Gamma_nat_eq_factorial]
  norm_num
  have hsqrt :
      Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi :=
    Real.mul_self_sqrt Real.pi_pos.le
  calc
    (1 / 2 : ℂ) * (Real.sqrt Real.pi : ℂ) *
          (Real.sqrt Real.pi : ℂ) =
        (1 / 2 : ℂ) *
          ((Real.sqrt Real.pi * Real.sqrt Real.pi : ℝ) : ℂ) := by
      push_cast
      ring
    _ = (1 / 2 : ℂ) * (Real.pi : ℂ) := by rw [hsqrt]
    _ = (Real.pi : ℂ) / 2 := by ring

private theorem betaFn_five_halves_one_half :
    betaFn (5 / 2) (1 / 2) = 3 * Real.pi / 8 := by
  apply Complex.ofReal_injective
  rw [betaFn_as_complex]
  rw [Complex.betaIntegral_eq_Gamma_mul_div
    (((5 / 2 : ℝ) : ℂ)) (((1 / 2 : ℝ) : ℂ))
    (by norm_num) (by norm_num)]
  have h52 : (5 / 2 : ℂ) = ((5 / 2 : ℝ) : ℂ) := by norm_num
  have h12 : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  have hsum :
      ((5 / 2 : ℝ) : ℂ) + ((1 / 2 : ℝ) : ℂ) =
        ((3 : ℝ) : ℂ) := by norm_num
  rw [hsum]
  rw [Complex.Gamma_ofReal, Complex.Gamma_ofReal,
    Complex.Gamma_ofReal]
  push_cast
  rw [show (5 / 2 : ℝ) = 3 / 2 + 1 by norm_num,
    Real.Gamma_add_one (by norm_num : (3 / 2 : ℝ) ≠ 0),
    show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num,
    Real.Gamma_add_one (by norm_num : (1 / 2 : ℝ) ≠ 0),
    Real.Gamma_one_half_eq]
  rw [show (3 : ℝ) = (2 : ℕ) + 1 by norm_num,
    Real.Gamma_nat_eq_factorial]
  norm_num
  have hsqrt :
      Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi :=
    Real.mul_self_sqrt Real.pi_pos.le
  calc
    (3 / 2 : ℂ) *
          ((1 / 2 : ℂ) * (Real.sqrt Real.pi : ℂ)) *
          (Real.sqrt Real.pi : ℂ) / 2 =
        (3 / 8 : ℂ) *
          ((Real.sqrt Real.pi * Real.sqrt Real.pi : ℝ) : ℂ) := by
      push_cast
      ring
    _ = (3 / 8 : ℂ) * (Real.pi : ℂ) := by rw [hsqrt]
    _ = 3 * (Real.pi : ℂ) / 8 := by ring

theorem gap12 (a : ℝ) (ha : 0 < a) :
    surfaceMoment a =
      4 * Real.sqrt 2 * a ^ 3 *
        (∫ t in (0 : ℝ)..1, betaIntegrand t) := by
  rw [gap11 a ha, angular_integral_eq_beta]

theorem gap13 (a : ℝ) (ha : 0 < a) :
    4 * Real.sqrt 2 * a ^ 3 *
        (∫ t in (0 : ℝ)..1, betaIntegrand t) =
      4 * Real.sqrt 2 * a ^ 3 *
        (betaFn (3 / 2) (1 / 2) + betaFn (5 / 2) (1 / 2)) := by
  have h1 := betaTerm_intervalIntegrable
    (3 / 2 : ℝ) (1 / 2 : ℝ) (by norm_num) (by norm_num)
  have h2 := betaTerm_intervalIntegrable
    (5 / 2 : ℝ) (1 / 2 : ℝ) (by norm_num) (by norm_num)
  apply congrArg (fun z : ℝ => 4 * Real.sqrt 2 * a ^ 3 * z)
  unfold betaIntegrand betaFn
  convert intervalIntegral.integral_add h1 h2 using 1 <;>
    norm_num

theorem gap14 (a : ℝ) :
    4 * Real.sqrt 2 * a ^ 3 *
        (betaFn (3 / 2) (1 / 2) + betaFn (5 / 2) (1 / 2)) =
      (7 / 2 : ℝ) * Real.sqrt 2 * Real.pi * a ^ 3 := by
  rw [betaFn_three_halves_one_half,
    betaFn_five_halves_one_half]
  ring

theorem gap15 (a : ℝ) (ha : 0 < a) :
    surfaceMoment a =
      (7 / 2 : ℝ) * Real.sqrt 2 * Real.pi * a ^ 3 := by
  calc
    surfaceMoment a =
        4 * Real.sqrt 2 * a ^ 3 *
          (∫ t in (0 : ℝ)..1, betaIntegrand t) :=
      gap12 a ha
    _ = 4 * Real.sqrt 2 * a ^ 3 *
          (betaFn (3 / 2) (1 / 2) +
            betaFn (5 / 2) (1 / 2)) :=
      gap13 a ha
    _ = (7 / 2 : ℝ) * Real.sqrt 2 *
          Real.pi * a ^ 3 :=
      gap14 a

end

end ProofGap.Exercise4342
