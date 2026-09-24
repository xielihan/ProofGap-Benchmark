import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4149

noncomputable section

open MeasureTheory
open scoped Interval

abbrev Point3 := ℝ × ℝ × ℝ

def parameterDomain : Set Point3 :=
  {q |
    0 ≤ q.1 ∧ q.1 ≤ 2 * Real.pi ∧
      0 ≤ q.2.1 ∧ q.2.1 ≤ 1 ∧
        q.2.1 ≤ q.2.2 ∧
          q.2.2 ≤ Real.sqrt (2 - q.2.1 ^ 2)}

def solid : Set Point3 :=
  {p |
    p.1 ^ 2 + p.2.1 ^ 2 ≤ 1 ∧
      Real.sqrt (p.1 ^ 2 + p.2.1 ^ 2) ≤ p.2.2 ∧
        p.2.2 ≤ Real.sqrt (2 - (p.1 ^ 2 + p.2.1 ^ 2))}

def inertiaZ : ℝ :=
  ∫ p in solid, p.1 ^ 2 + p.2.1 ^ 2

private def solidIntegrand (p : Point3) : ℝ :=
  solid.indicator (fun q => q.1 ^ 2 + q.2.1 ^ 2) p

private def verticalIntegral (xy : ℝ × ℝ) : ℝ :=
  ∫ z : ℝ, solidIntegrand (xy.1, xy.2, z)

private def radialValue (r : ℝ) : ℝ :=
  r ^ 3 * (Real.sqrt (2 - r ^ 2) - r)

private theorem ae_ne_real (a : ℝ) :
    ∀ᵐ x : ℝ ∂volume, x ≠ a := by
  rw [ae_iff]
  simp

private theorem solid_measurable : MeasurableSet solid := by
  unfold solid
  measurability

private theorem solid_subset_box :
    solid ⊆
      Set.Icc (-1 : ℝ) 1 ×ˢ
        (Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 2) := by
  intro p hp
  rcases p with ⟨x, y, z⟩
  rcases hp with ⟨hxy, hz₀, hz₁⟩
  have hx₀ : -1 ≤ x := by nlinarith [sq_nonneg x, sq_nonneg y]
  have hx₁ : x ≤ 1 := by nlinarith [sq_nonneg x, sq_nonneg y]
  have hy₀ : -1 ≤ y := by nlinarith [sq_nonneg x, sq_nonneg y]
  have hy₁ : y ≤ 1 := by nlinarith [sq_nonneg x, sq_nonneg y]
  have hznonneg : 0 ≤ z := (Real.sqrt_nonneg _).trans hz₀
  have harg : 0 ≤ 2 - (x ^ 2 + y ^ 2) := by
    nlinarith [sq_nonneg x, sq_nonneg y]
  have hsquaresqrt :
      (Real.sqrt (2 - (x ^ 2 + y ^ 2))) ^ 2 =
        2 - (x ^ 2 + y ^ 2) := Real.sq_sqrt harg
  have hzle : z ≤ 2 := by
    have hsqrtle : Real.sqrt (2 - (x ^ 2 + y ^ 2)) ≤ 2 := by
      nlinarith [Real.sqrt_nonneg (2 - (x ^ 2 + y ^ 2)),
        hsquaresqrt]
    exact hz₁.trans hsqrtle
  exact ⟨⟨hx₀, hx₁⟩, ⟨⟨hy₀, hy₁⟩, hznonneg, hzle⟩⟩

private theorem solidIntegrand_integrable : Integrable solidIntegrand := by
  have hbox : IsCompact
      (Set.Icc (-1 : ℝ) 1 ×ˢ
        (Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 2)) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hcont : Continuous
      (fun p : Point3 => p.1 ^ 2 + p.2.1 ^ 2) := by
    fun_prop
  have hi : IntegrableOn
      (fun p : Point3 => p.1 ^ 2 + p.2.1 ^ 2)
      (Set.Icc (-1 : ℝ) 1 ×ˢ
        (Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 2)) :=
    hcont.continuousOn.integrableOn_compact hbox
  unfold solidIntegrand
  exact (integrable_indicator_iff solid_measurable).2
    (hi.mono_set solid_subset_box)

private theorem verticalIntegral_polar
    (u : ℝ × ℝ) (hu : u ∈ polarCoord.target) :
    u.1 * verticalIntegral (polarCoord.symm u) =
      if u.1 ≤ 1 then radialValue u.1 else 0 := by
  have hrpos : 0 < u.1 := hu.1
  have hsq :
      (polarCoord.symm u).1 ^ 2 + (polarCoord.symm u).2 ^ 2 =
        u.1 ^ 2 := by
    simp only [polarCoord_symm_apply]
    nlinarith [Real.sin_sq_add_cos_sq u.2]
  have hsqrt : Real.sqrt (u.1 ^ 2) = u.1 := by
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hrpos]
  have hmem_iff (z : ℝ) :
      ((polarCoord.symm u).1, (polarCoord.symm u).2, z) ∈ solid ↔
        u.1 ^ 2 ≤ 1 ∧
          u.1 ≤ z ∧ z ≤ Real.sqrt (2 - u.1 ^ 2) := by
    change
      (polarCoord.symm u).1 ^ 2 + (polarCoord.symm u).2 ^ 2 ≤ 1 ∧
          Real.sqrt
              ((polarCoord.symm u).1 ^ 2 +
                (polarCoord.symm u).2 ^ 2) ≤ z ∧
            z ≤ Real.sqrt
              (2 - ((polarCoord.symm u).1 ^ 2 +
                (polarCoord.symm u).2 ^ 2)) ↔ _
    rw [hsq, hsqrt]
  by_cases hr : u.1 ≤ 1
  · rw [if_pos hr]
    have hrsq : u.1 ^ 2 ≤ 1 := by
      nlinarith [mul_nonneg hrpos.le (sub_nonneg.mpr hr)]
    have hupper : u.1 ≤ Real.sqrt (2 - u.1 ^ 2) := by
      apply Real.le_sqrt_of_sq_le
      nlinarith [mul_nonneg hrpos.le (sub_nonneg.mpr hr)]
    have hvertical :
        verticalIntegral (polarCoord.symm u) =
          ∫ z in u.1..Real.sqrt (2 - u.1 ^ 2), u.1 ^ 2 := by
      unfold verticalIntegral
      rw [intervalIntegral.integral_of_le hupper]
      rw [← MeasureTheory.integral_indicator measurableSet_Ioc]
      apply integral_congr_ae
      filter_upwards [ae_ne_real u.1] with z hzne
      simp only [solidIntegrand]
      by_cases hz :
          z ∈ Set.Ioc u.1 (Real.sqrt (2 - u.1 ^ 2))
      · have hm : ((polarCoord.symm u).1,
            (polarCoord.symm u).2, z) ∈ solid :=
          (hmem_iff z).2 ⟨hrsq, hz.1.le, hz.2⟩
        rw [Set.indicator_of_mem hz, Set.indicator_of_mem hm]
        exact hsq
      · have hnm : ((polarCoord.symm u).1,
            (polarCoord.symm u).2, z) ∉ solid := by
          intro hm
          apply hz
          have hm' := (hmem_iff z).1 hm
          exact ⟨lt_of_le_of_ne hm'.2.1 (Ne.symm hzne), hm'.2.2⟩
        rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hnm]
    rw [hvertical, intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    unfold radialValue
    ring
  · rw [if_neg hr]
    have hvertical : verticalIntegral (polarCoord.symm u) = 0 := by
      unfold verticalIntegral
      rw [← integral_zero]
      apply integral_congr_ae
      filter_upwards with z
      simp only [solidIntegrand]
      have hnm : ((polarCoord.symm u).1,
          (polarCoord.symm u).2, z) ∉ solid := by
        intro hm
        have hrsq := ((hmem_iff z).1 hm).1
        apply hr
        nlinarith [sq_nonneg (u.1 - 1)]
      rw [Set.indicator_of_notMem hnm]
    rw [hvertical, mul_zero]

private theorem polar_integral_eq :
    (∫ u in polarCoord.target,
        u.1 * verticalIntegral (polarCoord.symm u)) =
      2 * Real.pi * ∫ r in (0 : ℝ)..1, radialValue r := by
  let rect : Set (ℝ × ℝ) :=
    Set.Ioc (0 : ℝ) 1 ×ˢ Set.Ioo (-Real.pi) Real.pi
  have hrect : MeasurableSet rect :=
    measurableSet_Ioc.prod measurableSet_Ioo
  have htarget : MeasurableSet polarCoord.target :=
    polarCoord.open_target.measurableSet
  have hrestrict :
      (∫ u in polarCoord.target,
          u.1 * verticalIntegral (polarCoord.symm u)) =
        ∫ u in rect, radialValue u.1 := by
    rw [← integral_indicator htarget, ← integral_indicator hrect]
    apply integral_congr_ae
    filter_upwards with u
    by_cases hu : u ∈ polarCoord.target
    · rw [Set.indicator_of_mem hu]
      by_cases hr : u.1 ≤ 1
      · have hur : u ∈ rect := ⟨⟨hu.1, hr⟩, hu.2⟩
        rw [Set.indicator_of_mem hur, verticalIntegral_polar u hu,
          if_pos hr]
      · have hur : u ∉ rect := by
          intro h
          exact hr h.1.2
        rw [Set.indicator_of_notMem hur, verticalIntegral_polar u hu,
          if_neg hr]
    · rw [Set.indicator_of_notMem hu]
      have hur : u ∉ rect := by
        intro h
        apply hu
        exact ⟨h.1.1, h.2⟩
      rw [Set.indicator_of_notMem hur]
  rw [hrestrict]
  have hcont : Continuous
      (fun u : ℝ × ℝ => radialValue u.1) := by
    unfold radialValue
    fun_prop
  have hcompact :
      IsCompact
        (Set.Icc (0 : ℝ) 1 ×ˢ
          Set.Icc (-Real.pi) Real.pi) :=
    isCompact_Icc.prod isCompact_Icc
  have hsubset :
      rect ⊆ Set.Icc (0 : ℝ) 1 ×ˢ
          Set.Icc (-Real.pi) Real.pi := by
    intro u hu
    exact ⟨⟨hu.1.1.le, hu.1.2⟩, ⟨hu.2.1.le, hu.2.2.le⟩⟩
  have hi : IntegrableOn
      (fun u : ℝ × ℝ => radialValue u.1) rect :=
    (hcont.continuousOn.integrableOn_compact hcompact).mono_set hsubset
  have hi' : IntegrableOn
      (fun u : ℝ × ℝ => radialValue u.1) rect
      (volume.prod volume) := by
    simpa only [Measure.volume_eq_prod] using hi
  change
    (∫ u in rect, radialValue u.1 ∂volume.prod volume) =
      2 * Real.pi * ∫ r in (0 : ℝ)..1, radialValue r
  rw [MeasureTheory.setIntegral_prod _ hi']
  have htheta : ∀ r : ℝ,
      (∫ _θ in Set.Ioo (-Real.pi) Real.pi, radialValue r) =
        (2 * Real.pi) * radialValue r := by
    intro r
    rw [setIntegral_const,
      Real.volume_real_Ioo_of_le (by linarith [Real.pi_pos])]
    simp only [smul_eq_mul]
    ring
  simp_rw [htheta]
  rw [intervalIntegral.integral_of_le
    (by norm_num : (0 : ℝ) ≤ 1)]
  rw [MeasureTheory.integral_const_mul]

private theorem iterated_integral_eq :
    (∫ φ in (0 : ℝ)..2 * Real.pi,
        ∫ r in (0 : ℝ)..1,
          ∫ z in r..Real.sqrt (2 - r ^ 2), r ^ 3) =
      2 * Real.pi * ∫ r in (0 : ℝ)..1, radialValue r := by
  have hz : ∀ r ∈ Set.uIcc (0 : ℝ) 1,
      (∫ z in r..Real.sqrt (2 - r ^ 2), r ^ 3) =
        radialValue r := by
    intro r hr
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hr
    rw [intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    unfold radialValue
    ring
  have hr :
      (∫ r in (0 : ℝ)..1,
          ∫ z in r..Real.sqrt (2 - r ^ 2), r ^ 3) =
        ∫ r in (0 : ℝ)..1, radialValue r := by
    apply intervalIntegral.integral_congr
    exact hz
  rw [show
      (fun _φ : ℝ =>
        ∫ r in (0 : ℝ)..1,
          ∫ z in r..Real.sqrt (2 - r ^ 2), r ^ 3) =
      (fun _φ : ℝ => ∫ r in (0 : ℝ)..1, radialValue r) by
        funext φ
        exact hr]
  rw [intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

private def radialAntiderivative (r : ℝ) : ℝ :=
  -(2 / 3 : ℝ) * Real.rpow (2 - r ^ 2) (3 / 2 : ℝ) +
    (1 / 5 : ℝ) * Real.rpow (2 - r ^ 2) (5 / 2 : ℝ)

private theorem integral_r3_sqrt :
    (∫ r in (0 : ℝ)..1, r ^ 3 * Real.sqrt (2 - r ^ 2)) =
      (8 * Real.sqrt 2 - 7) / 15 := by
  have hint : IntervalIntegrable
      (fun r : ℝ => r ^ 3 * Real.sqrt (2 - r ^ 2))
      volume (0 : ℝ) 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hder : ∀ r ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt radialAntiderivative
        (r ^ 3 * Real.sqrt (2 - r ^ 2)) r := by
    intro r hr
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hr
    have hu : 0 < 2 - r ^ 2 := by
      nlinarith [mul_nonneg hr.1 (sub_nonneg.mpr hr.2)]
    have hinner :
        HasDerivAt (fun x : ℝ => 2 - x ^ 2) (-2 * r) r := by
      convert (hasDerivAt_const r 2).sub
          ((hasDerivAt_id r).pow 2) using 1 <;>
        simp [id] <;> ring
    have h3 := (Real.hasDerivAt_rpow_const
      (p := (3 / 2 : ℝ)) (Or.inl hu.ne')).comp r hinner
    have h5 := (Real.hasDerivAt_rpow_const
      (p := (5 / 2 : ℝ)) (Or.inl hu.ne')).comp r hinner
    unfold radialAntiderivative
    convert (h3.const_mul (-(2 / 3 : ℝ))).add
      (h5.const_mul (1 / 5 : ℝ)) using 1
    norm_num [Real.sqrt_eq_rpow]
    have hpow3 :
        (2 - r ^ 2) ^ (3 / 2 : ℝ) =
          (2 - r ^ 2) * (2 - r ^ 2) ^ (1 / 2 : ℝ) := by
      convert Real.rpow_add hu (1 : ℝ) (1 / 2 : ℝ) using 1 <;>
        norm_num
    rw [hpow3]
    ring
  have hftc :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hder hint
  rw [hftc]
  unfold radialAntiderivative
  have h1_3 : Real.rpow 1 (3 / 2 : ℝ) = 1 := by
    rw [Real.rpow_eq_pow, Real.one_rpow]
  have h1_5 : Real.rpow 1 (5 / 2 : ℝ) = 1 := by
    rw [Real.rpow_eq_pow, Real.one_rpow]
  have h2_3 :
      Real.rpow 2 (3 / 2 : ℝ) = 2 * Real.sqrt 2 := by
    rw [Real.sqrt_eq_rpow, Real.rpow_eq_pow]
    convert Real.rpow_add (by norm_num : (0 : ℝ) < 2)
      (1 : ℝ) (1 / 2 : ℝ) using 1 <;>
      norm_num
  have h2_5 :
      Real.rpow 2 (5 / 2 : ℝ) = 4 * Real.sqrt 2 := by
    rw [Real.sqrt_eq_rpow, Real.rpow_eq_pow]
    have h := Real.rpow_add (by norm_num : (0 : ℝ) < 2)
      (2 : ℝ) (1 / 2 : ℝ)
    norm_num at h ⊢
    exact h
  rw [show (2 : ℝ) - 1 ^ 2 = 1 by norm_num,
    show (2 : ℝ) - 0 ^ 2 = 2 by norm_num,
    h1_3, h1_5, h2_3, h2_5]
  ring

theorem gap1 (φ r z : ℝ) (hmem : (φ, r, z) ∈ parameterDomain) :
    0 ≤ φ := by
  exact hmem.1

theorem gap2 (φ r z : ℝ) (hmem : (φ, r, z) ∈ parameterDomain) :
    φ ≤ 2 * Real.pi := by
  exact hmem.2.1

theorem gap3 (φ r z : ℝ) (hmem : (φ, r, z) ∈ parameterDomain) :
    0 ≤ r := by
  exact hmem.2.2.1

theorem gap4 (φ r z : ℝ) (hmem : (φ, r, z) ∈ parameterDomain) :
    r ≤ 1 := by
  exact hmem.2.2.2.1

theorem gap5 (φ r z : ℝ) (hmem : (φ, r, z) ∈ parameterDomain) :
    r ≤ z := by
  exact hmem.2.2.2.2.1

theorem gap6 (φ r z : ℝ) (hmem : (φ, r, z) ∈ parameterDomain) :
    z ≤ Real.sqrt (2 - r ^ 2) := by
  exact hmem.2.2.2.2.2

theorem gap7 :
    inertiaZ =
      ∫ φ in (0 : ℝ)..2 * Real.pi,
        ∫ r in (0 : ℝ)..1,
          ∫ z in r..Real.sqrt (2 - r ^ 2), r ^ 3 := by
  have hgassoc :
      Integrable
        (solidIntegrand ∘
          (MeasurableEquiv.prodAssoc :
            (ℝ × ℝ) × ℝ ≃ᵐ Point3)) :=
    (volume_preserving_prodAssoc.integrable_comp_emb
      MeasurableEquiv.prodAssoc.measurableEmbedding).2
        solidIntegrand_integrable
  have hfubini :
      (∫ q : (ℝ × ℝ) × ℝ,
          solidIntegrand (MeasurableEquiv.prodAssoc q)) =
        ∫ xy : ℝ × ℝ, verticalIntegral xy := by
    have hgassoc' : Integrable
        (fun q : (ℝ × ℝ) × ℝ =>
          solidIntegrand (MeasurableEquiv.prodAssoc q))
        (volume.prod volume) := by
      simpa only [Measure.volume_eq_prod] using hgassoc
    change
      (∫ q : (ℝ × ℝ) × ℝ,
          solidIntegrand (MeasurableEquiv.prodAssoc q)
            ∂volume.prod volume) =
        ∫ xy : ℝ × ℝ, verticalIntegral xy
    rw [MeasureTheory.integral_prod _ hgassoc']
    rfl
  have hassoc :
      (∫ q : (ℝ × ℝ) × ℝ,
          solidIntegrand (MeasurableEquiv.prodAssoc q)) =
        ∫ p : Point3, solidIntegrand p :=
    volume_preserving_prodAssoc.integral_comp
      MeasurableEquiv.prodAssoc.measurableEmbedding solidIntegrand
  have hpolar :
      (∫ xy : ℝ × ℝ, verticalIntegral xy) =
        ∫ u in polarCoord.target,
          u.1 * verticalIntegral (polarCoord.symm u) := by
    simpa only [smul_eq_mul] using
      (integral_comp_polarCoord_symm verticalIntegral).symm
  calc
    inertiaZ = ∫ p : Point3, solidIntegrand p := by
      unfold inertiaZ solidIntegrand
      rw [integral_indicator solid_measurable]
    _ = ∫ q : (ℝ × ℝ) × ℝ,
          solidIntegrand (MeasurableEquiv.prodAssoc q) := hassoc.symm
    _ = ∫ xy : ℝ × ℝ, verticalIntegral xy := hfubini
    _ = ∫ u in polarCoord.target,
          u.1 * verticalIntegral (polarCoord.symm u) := hpolar
    _ = 2 * Real.pi * ∫ r in (0 : ℝ)..1, radialValue r :=
      polar_integral_eq
    _ = ∫ φ in (0 : ℝ)..2 * Real.pi,
        ∫ r in (0 : ℝ)..1,
          ∫ z in r..Real.sqrt (2 - r ^ 2), r ^ 3 :=
      iterated_integral_eq.symm

theorem gap8 :
    (∫ φ in (0 : ℝ)..2 * Real.pi,
        ∫ r in (0 : ℝ)..1,
          ∫ z in r..Real.sqrt (2 - r ^ 2), r ^ 3) =
      ∫ φ in (0 : ℝ)..2 * Real.pi,
        ∫ r in (0 : ℝ)..1,
          r ^ 3 * Real.sqrt (2 - r ^ 2) - r ^ 4 := by
  apply intervalIntegral.integral_congr
  intro φ hφ
  apply intervalIntegral.integral_congr
  intro r hr
  change
    (∫ z in r..Real.sqrt (2 - r ^ 2), r ^ 3) =
      r ^ 3 * Real.sqrt (2 - r ^ 2) - r ^ 4
  rw [intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

theorem gap9 :
    (∫ φ in (0 : ℝ)..2 * Real.pi,
        ∫ r in (0 : ℝ)..1,
          r ^ 3 * Real.sqrt (2 - r ^ 2) - r ^ 4) =
      4 * Real.pi / 15 * (4 * Real.sqrt 2 - 5) := by
  have hr4 :
      (∫ r in (0 : ℝ)..1, r ^ 4) = (1 / 5 : ℝ) := by
    norm_num [integral_pow]
  have hinner :
      (∫ r in (0 : ℝ)..1,
          r ^ 3 * Real.sqrt (2 - r ^ 2) - r ^ 4) =
        (8 * Real.sqrt 2 - 10) / 15 := by
    rw [intervalIntegral.integral_sub]
    · rw [integral_r3_sqrt, hr4]
      ring
    · exact (by fun_prop : Continuous
        (fun r : ℝ => r ^ 3 * Real.sqrt (2 - r ^ 2))).intervalIntegrable
          (0 : ℝ) 1
    · exact (by fun_prop : Continuous
        (fun r : ℝ => r ^ 4)).intervalIntegrable (0 : ℝ) 1
  rw [show
      (fun _φ : ℝ =>
        ∫ r in (0 : ℝ)..1,
          r ^ 3 * Real.sqrt (2 - r ^ 2) - r ^ 4) =
      (fun _φ : ℝ => (8 * Real.sqrt 2 - 10) / 15) by
        funext φ
        exact hinner]
  rw [intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

theorem gap10 :
    inertiaZ = 4 * Real.pi / 15 * (4 * Real.sqrt 2 - 5) := by
  rw [gap7, gap8, gap9]

end

end ProofGap.Exercise4149
