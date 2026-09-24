import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

namespace ProofGap.Exercise4134

noncomputable section

open MeasureTheory
open scoped Interval

abbrev Point3 := ℝ × ℝ × ℝ

def solid (a : ℝ) : Set Point3 :=
  {p |
    0 ≤ p.1 ∧ p.1 ≤ a ∧
      0 ≤ p.2.1 ∧ p.2.1 ≤ a - p.1 ∧
        0 ≤ p.2.2 ∧ p.2.2 ≤ p.1 ^ 2 + p.2.1 ^ 2}

def mass (a : ℝ) : ℝ :=
  ∫ _p in solid a, (1 : ℝ)

def xCentroid (a : ℝ) : ℝ :=
  1 / mass a * ∫ p in solid a, p.1

def yCentroid (a : ℝ) : ℝ :=
  1 / mass a * ∫ p in solid a, p.2.1

def zCentroid (a : ℝ) : ℝ :=
  1 / mass a * ∫ p in solid a, p.2.2

private theorem solid_measurable (a : ℝ) : MeasurableSet (solid a) := by
  unfold solid
  measurability

private theorem solid_subset_box (a : ℝ) (ha : 0 < a) :
    solid a ⊆
      Set.Icc (0 : ℝ) a ×ˢ
        (Set.Icc (0 : ℝ) a ×ˢ Set.Icc (0 : ℝ) (2 * a ^ 2)) := by
  intro q hq
  rcases hq with ⟨hx₀, hx₁, hy₀, hy₁, hz₀, hz₁⟩
  have hy_a : q.2.1 ≤ a := by linarith
  have hx_sq : q.1 ^ 2 ≤ a ^ 2 := by
    nlinarith [mul_nonneg hx₀ (sub_nonneg.mpr hx₁)]
  have hy_sq : q.2.1 ^ 2 ≤ a ^ 2 := by
    nlinarith [mul_nonneg hy₀ (sub_nonneg.mpr hy_a)]
  exact
    ⟨⟨hx₀, hx₁⟩,
      ⟨⟨hy₀, hy_a⟩, hz₀, hz₁.trans (by nlinarith)⟩⟩

private theorem solid_box_compact (a : ℝ) :
    IsCompact
      (Set.Icc (0 : ℝ) a ×ˢ
        (Set.Icc (0 : ℝ) a ×ˢ Set.Icc (0 : ℝ) (2 * a ^ 2))) :=
  isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)

private theorem integral_solid_eq_iterated
    (a : ℝ) (ha : 0 < a) (f : Point3 → ℝ) (hf : Continuous f) :
    (∫ q in solid a, f q) =
      ∫ x in (0 : ℝ)..a,
        ∫ y in (0 : ℝ)..a - x,
          ∫ z in (0 : ℝ)..x ^ 2 + y ^ 2, f (x, y, z) := by
  classical
  have hbox :
      IntegrableOn f
        (Set.Icc (0 : ℝ) a ×ˢ
          (Set.Icc (0 : ℝ) a ×ˢ Set.Icc (0 : ℝ) (2 * a ^ 2)))
        volume :=
    hf.continuousOn.integrableOn_compact (solid_box_compact a)
  have hfi : IntegrableOn f (solid a) volume :=
    hbox.mono_set (solid_subset_box a ha)
  have hind : Integrable ((solid a).indicator f) volume :=
    (integrable_indicator_iff (solid_measurable a)).2 hfi
  change Integrable ((solid a).indicator f)
    (volume.prod (volume.prod volume)) at hind
  have hprod :
      (∫ q : Point3, (solid a).indicator f q
          ∂volume.prod (volume.prod volume)) =
        ∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ,
          (solid a).indicator f (x, y, z) := by
    rw [MeasureTheory.integral_prod _ hind]
    apply integral_congr_ae
    filter_upwards [hind.prod_right_ae] with x hx
    change
      (∫ yz : ℝ × ℝ, (solid a).indicator f (x, yz)
          ∂volume.prod volume) =
        ∫ y : ℝ, ∫ z : ℝ, (solid a).indicator f (x, y, z)
    rw [MeasureTheory.integral_prod _ hx]
  have hsections :
      (∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ,
        (solid a).indicator f (x, y, z)) =
        ∫ x in Set.Icc (0 : ℝ) a,
          ∫ y in Set.Icc (0 : ℝ) (a - x),
            ∫ z in Set.Icc (0 : ℝ) (x ^ 2 + y ^ 2),
              f (x, y, z) := by
    rw [← MeasureTheory.integral_indicator measurableSet_Icc]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ Set.Icc (0 : ℝ) a
    · rw [Set.indicator_of_mem hx]
      rw [← MeasureTheory.integral_indicator measurableSet_Icc]
      apply integral_congr_ae
      filter_upwards with y
      by_cases hy : y ∈ Set.Icc (0 : ℝ) (a - x)
      · rw [Set.indicator_of_mem hy]
        rw [← MeasureTheory.integral_indicator measurableSet_Icc]
        apply integral_congr_ae
        filter_upwards with z
        by_cases hz : z ∈ Set.Icc (0 : ℝ) (x ^ 2 + y ^ 2)
        · have hsolid : (x, y, z) ∈ solid a :=
            ⟨hx.1, hx.2, hy.1, hy.2, hz.1, hz.2⟩
          simp only [Set.indicator_of_mem hz,
            Set.indicator_of_mem hsolid]
        · have hnsolid : (x, y, z) ∉ solid a := by
            intro hq
            exact hz ⟨hq.2.2.2.2.1, hq.2.2.2.2.2⟩
          simp [Set.indicator, hz, hnsolid]
      · have hyr :
            (Set.Icc (0 : ℝ) (a - x)).indicator
              (fun y =>
                ∫ z in Set.Icc (0 : ℝ) (x ^ 2 + y ^ 2),
                  f (x, y, z)) y = 0 := by
          simp [Set.indicator, hy]
        rw [hyr, ← integral_zero]
        apply integral_congr_ae
        filter_upwards with z
        have hnsolid : (x, y, z) ∉ solid a := by
          intro hq
          exact hy ⟨hq.2.2.1, hq.2.2.2.1⟩
        simp [Set.indicator, hnsolid]
    · have hxr :
          (Set.Icc (0 : ℝ) a).indicator
            (fun x =>
              ∫ y in Set.Icc (0 : ℝ) (a - x),
                ∫ z in Set.Icc (0 : ℝ) (x ^ 2 + y ^ 2),
                  f (x, y, z)) x = 0 := by
        simp [Set.indicator, hx]
      rw [hxr, ← integral_zero]
      apply integral_congr_ae
      filter_upwards with y
      rw [← integral_zero]
      apply integral_congr_ae
      filter_upwards with z
      have hnsolid : (x, y, z) ∉ solid a := by
        intro hq
        exact hx ⟨hq.1, hq.2.1⟩
      simp [Set.indicator, hnsolid]
  calc
    (∫ q in solid a, f q) =
        ∫ q : Point3, (solid a).indicator f q := by
      rw [MeasureTheory.integral_indicator (solid_measurable a)]
    _ = ∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ,
          (solid a).indicator f (x, y, z) := hprod
    _ = ∫ x in Set.Icc (0 : ℝ) a,
          ∫ y in Set.Icc (0 : ℝ) (a - x),
            ∫ z in Set.Icc (0 : ℝ) (x ^ 2 + y ^ 2),
              f (x, y, z) := hsections
    _ = ∫ x in (0 : ℝ)..a,
          ∫ y in (0 : ℝ)..a - x,
            ∫ z in (0 : ℝ)..x ^ 2 + y ^ 2,
              f (x, y, z) := by
      rw [intervalIntegral.integral_of_le ha.le]
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
      intro x hx
      dsimp only
      have hyorder : 0 ≤ a - x := sub_nonneg.mpr hx.2
      rw [intervalIntegral.integral_of_le hyorder]
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
      intro y hy
      dsimp only
      have hzorder : 0 ≤ x ^ 2 + y ^ 2 :=
        add_nonneg (sq_nonneg x) (sq_nonneg y)
      rw [intervalIntegral.integral_of_le hzorder]
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc]

private theorem integral_poly5
    (c₀ c₁ c₂ c₃ c₄ c₅ a b : ℝ) :
    (∫ x in a..b,
        c₀ + c₁ * x + c₂ * x ^ 2 + c₃ * x ^ 3 +
          c₄ * x ^ 4 + c₅ * x ^ 5) =
      c₀ * (b - a) +
        c₁ / 2 * (b ^ 2 - a ^ 2) +
        c₂ / 3 * (b ^ 3 - a ^ 3) +
        c₃ / 4 * (b ^ 4 - a ^ 4) +
        c₄ / 5 * (b ^ 5 - a ^ 5) +
        c₅ / 6 * (b ^ 6 - a ^ 6) := by
  let F : ℝ → ℝ := fun x =>
    c₀ * x + c₁ / 2 * x ^ 2 + c₂ / 3 * x ^ 3 +
      c₃ / 4 * x ^ 4 + c₄ / 5 * x ^ 5 + c₅ / 6 * x ^ 6
  have hderiv (x : ℝ) :
      HasDerivAt F
        (c₀ + c₁ * x + c₂ * x ^ 2 + c₃ * x ^ 3 +
          c₄ * x ^ 4 + c₅ * x ^ 5) x := by
    dsimp [F]
    convert
      ((((((hasDerivAt_id x).const_mul c₀).add
          (((hasDerivAt_id x).pow 2).const_mul (c₁ / 2))).add
          (((hasDerivAt_id x).pow 3).const_mul (c₂ / 3))).add
          (((hasDerivAt_id x).pow 4).const_mul (c₃ / 4))).add
          (((hasDerivAt_id x).pow 5).const_mul (c₄ / 5))).add
          (((hasDerivAt_id x).pow 6).const_mul (c₅ / 6))
      using 1 <;> norm_num <;> ring
  have hcont : Continuous (fun x : ℝ =>
      c₀ + c₁ * x + c₂ * x ^ 2 + c₃ * x ^ 3 +
        c₄ * x ^ 4 + c₅ * x ^ 5) := by
    fun_prop
  calc
    (∫ x in a..b,
        c₀ + c₁ * x + c₂ * x ^ 2 + c₃ * x ^ 3 +
          c₄ * x ^ 4 + c₅ * x ^ 5) =
        F b - F a :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x _hx => hderiv x) (hcont.intervalIntegrable a b)
    _ = _ := by
      dsimp [F]
      ring

private theorem volume_inner (a x : ℝ) :
    (∫ y in (0 : ℝ)..a - x, x ^ 2 + y ^ 2) =
      a ^ 3 / 3 - a ^ 2 * x + 2 * a * x ^ 2 -
        (4 / 3 : ℝ) * x ^ 3 := by
  calc
    (∫ y in (0 : ℝ)..a - x, x ^ 2 + y ^ 2) =
        ∫ y in (0 : ℝ)..a - x,
          x ^ 2 + 0 * y + 1 * y ^ 2 + 0 * y ^ 3 +
            0 * y ^ 4 + 0 * y ^ 5 := by
      apply intervalIntegral.integral_congr
      intro y hy
      ring
    _ = _ := by
      rw [integral_poly5]
      ring

private theorem mass_iterated_value (a : ℝ) :
    (∫ x in (0 : ℝ)..a,
        ∫ y in (0 : ℝ)..a - x,
          ∫ z in (0 : ℝ)..x ^ 2 + y ^ 2, (1 : ℝ)) =
      (1 : ℝ) / 6 * a ^ 4 := by
  have hinner (x y : ℝ) :
      (∫ z in (0 : ℝ)..x ^ 2 + y ^ 2, (1 : ℝ)) =
        x ^ 2 + y ^ 2 := by
    rw [intervalIntegral.integral_const]
    simp only [smul_eq_mul, sub_zero, mul_one]
  calc
    (∫ x in (0 : ℝ)..a,
        ∫ y in (0 : ℝ)..a - x,
          ∫ z in (0 : ℝ)..x ^ 2 + y ^ 2, (1 : ℝ)) =
        ∫ x in (0 : ℝ)..a,
          ∫ y in (0 : ℝ)..a - x, x ^ 2 + y ^ 2 := by
      apply intervalIntegral.integral_congr
      intro x hx
      apply intervalIntegral.integral_congr
      intro y hy
      exact hinner x y
    _ = ∫ x in (0 : ℝ)..a,
          a ^ 3 / 3 - a ^ 2 * x + 2 * a * x ^ 2 -
            (4 / 3 : ℝ) * x ^ 3 := by
      apply intervalIntegral.integral_congr
      intro x hx
      exact volume_inner a x
    _ = (1 : ℝ) / 6 * a ^ 4 := by
      calc
        (∫ x in (0 : ℝ)..a,
          a ^ 3 / 3 - a ^ 2 * x + 2 * a * x ^ 2 -
            (4 / 3 : ℝ) * x ^ 3) =
            ∫ x in (0 : ℝ)..a,
              a ^ 3 / 3 + (-a ^ 2) * x + (2 * a) * x ^ 2 +
                (-(4 / 3 : ℝ)) * x ^ 3 + 0 * x ^ 4 + 0 * x ^ 5 := by
          apply intervalIntegral.integral_congr
          intro x hx
          ring
        _ = _ := by
          rw [integral_poly5]
          ring

theorem gap1 (a : ℝ) (ha : 0 < a) :
    mass a =
      ∫ x in (0 : ℝ)..a,
        ∫ y in (0 : ℝ)..a - x,
          ∫ z in (0 : ℝ)..x ^ 2 + y ^ 2, (1 : ℝ) := by
  unfold mass
  simpa using integral_solid_eq_iterated a ha
    (fun _p : Point3 => (1 : ℝ)) continuous_const

theorem gap2 (a : ℝ) (ha : 0 < a) :
    (∫ x in (0 : ℝ)..a,
        ∫ y in (0 : ℝ)..a - x,
          ∫ z in (0 : ℝ)..x ^ 2 + y ^ 2, (1 : ℝ)) =
      (1 : ℝ) / 6 * a ^ 4 := by
  exact mass_iterated_value a

theorem gap3 (a : ℝ) (ha : 0 < a) :
    mass a = (1 : ℝ) / 6 * a ^ 4 := by
  rw [gap1 a ha, gap2 a ha]

theorem gap4 (a : ℝ) (ha : 0 < a) :
    xCentroid a =
      1 / mass a *
        ∫ x in (0 : ℝ)..a,
          x * ∫ y in (0 : ℝ)..a - x,
            ∫ z in (0 : ℝ)..x ^ 2 + y ^ 2, (1 : ℝ) := by
  unfold xCentroid
  rw [integral_solid_eq_iterated a ha
    (fun p : Point3 => p.1) continuous_fst]
  congr 1
  apply intervalIntegral.integral_congr
  intro x hx
  calc
    (∫ y in (0 : ℝ)..a - x,
      ∫ z in (0 : ℝ)..x ^ 2 + y ^ 2, x) =
        ∫ y in (0 : ℝ)..a - x,
          x * ∫ z in (0 : ℝ)..x ^ 2 + y ^ 2, (1 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro y hy
      dsimp only
      rw [← intervalIntegral.integral_const_mul]
      simp
    _ = x * ∫ y in (0 : ℝ)..a - x,
          ∫ z in (0 : ℝ)..x ^ 2 + y ^ 2, (1 : ℝ) := by
      rw [intervalIntegral.integral_const_mul]

theorem gap5 (a : ℝ) (ha : 0 < a) :
    1 / mass a *
        (∫ x in (0 : ℝ)..a,
          x * ∫ y in (0 : ℝ)..a - x,
            ∫ z in (0 : ℝ)..x ^ 2 + y ^ 2, (1 : ℝ)) =
      6 / a ^ 4 * (a ^ 5 / 15) := by
  have ha0 : a ≠ 0 := ha.ne'
  have hmoment :
      (∫ x in (0 : ℝ)..a,
        x * ∫ y in (0 : ℝ)..a - x,
          ∫ z in (0 : ℝ)..x ^ 2 + y ^ 2, (1 : ℝ)) =
        a ^ 5 / 15 := by
    have hinner (x y : ℝ) :
        (∫ z in (0 : ℝ)..x ^ 2 + y ^ 2, (1 : ℝ)) =
          x ^ 2 + y ^ 2 := by
      rw [intervalIntegral.integral_const]
      simp only [smul_eq_mul, sub_zero, mul_one]
    calc
      (∫ x in (0 : ℝ)..a,
        x * ∫ y in (0 : ℝ)..a - x,
          ∫ z in (0 : ℝ)..x ^ 2 + y ^ 2, (1 : ℝ)) =
          ∫ x in (0 : ℝ)..a, x *
            (a ^ 3 / 3 - a ^ 2 * x + 2 * a * x ^ 2 -
              (4 / 3 : ℝ) * x ^ 3) := by
        apply intervalIntegral.integral_congr
        intro x hx
        apply congrArg (fun t : ℝ => x * t)
        calc
          (∫ y in (0 : ℝ)..a - x,
            ∫ z in (0 : ℝ)..x ^ 2 + y ^ 2, (1 : ℝ)) =
              ∫ y in (0 : ℝ)..a - x, x ^ 2 + y ^ 2 := by
            apply intervalIntegral.integral_congr
            intro y hy
            exact hinner x y
          _ = _ := volume_inner a x
      _ = ∫ x in (0 : ℝ)..a,
          0 + (a ^ 3 / 3) * x + (-a ^ 2) * x ^ 2 +
            (2 * a) * x ^ 3 + (-(4 / 3 : ℝ)) * x ^ 4 +
              0 * x ^ 5 := by
        apply intervalIntegral.integral_congr
        intro x hx
        ring
      _ = a ^ 5 / 15 := by
        rw [integral_poly5]
        ring
  rw [gap3 a ha, hmoment]
  field_simp [ha0]
  <;> ring

theorem gap6 (a : ℝ) (ha : 0 < a) :
    6 / a ^ 4 * (a ^ 5 / 15) = 2 * a / 5 := by
  field_simp [ha.ne']
  <;> ring

theorem gap7 (a : ℝ) (ha : 0 < a) :
    xCentroid a = 2 * a / 5 := by
  rw [gap4 a ha, gap5 a ha, gap6 a ha]

theorem gap8 (a : ℝ) (ha : 0 < a) :
    yCentroid a = 2 * a / 5 := by
  have ha0 : a ≠ 0 := ha.ne'
  have hyint :
      (∫ q in solid a, q.2.1) = a ^ 5 / 15 := by
    rw [integral_solid_eq_iterated a ha
      (fun q : Point3 => q.2.1)
      (continuous_fst.comp continuous_snd)]
    have hinner (x y : ℝ) :
        (∫ z in (0 : ℝ)..x ^ 2 + y ^ 2, y) =
          y * (x ^ 2 + y ^ 2) := by
      rw [intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      ring
    calc
      (∫ x in (0 : ℝ)..a,
        ∫ y in (0 : ℝ)..a - x,
          ∫ z in (0 : ℝ)..x ^ 2 + y ^ 2, y) =
          ∫ x in (0 : ℝ)..a,
            ∫ y in (0 : ℝ)..a - x, y * (x ^ 2 + y ^ 2) := by
        apply intervalIntegral.integral_congr
        intro x hx
        apply intervalIntegral.integral_congr
        intro y hy
        exact hinner x y
      _ = ∫ x in (0 : ℝ)..a,
          a ^ 4 / 4 - a ^ 3 * x + 2 * a ^ 2 * x ^ 2 -
            2 * a * x ^ 3 + (3 / 4 : ℝ) * x ^ 4 := by
        apply intervalIntegral.integral_congr
        intro x hx
        calc
          (∫ y in (0 : ℝ)..a - x, y * (x ^ 2 + y ^ 2)) =
              ∫ y in (0 : ℝ)..a - x,
                0 + x ^ 2 * y + 0 * y ^ 2 + 1 * y ^ 3 +
                  0 * y ^ 4 + 0 * y ^ 5 := by
            apply intervalIntegral.integral_congr
            intro y hy
            ring
          _ = _ := by
            rw [integral_poly5]
            ring
      _ = a ^ 5 / 15 := by
        calc
          (∫ x in (0 : ℝ)..a,
            a ^ 4 / 4 - a ^ 3 * x + 2 * a ^ 2 * x ^ 2 -
              2 * a * x ^ 3 + (3 / 4 : ℝ) * x ^ 4) =
              ∫ x in (0 : ℝ)..a,
                a ^ 4 / 4 + (-a ^ 3) * x + (2 * a ^ 2) * x ^ 2 +
                  (-2 * a) * x ^ 3 + (3 / 4) * x ^ 4 +
                    0 * x ^ 5 := by
            apply intervalIntegral.integral_congr
            intro x hx
            ring
          _ = _ := by
            rw [integral_poly5]
            ring
  unfold yCentroid
  rw [hyint, gap3 a ha]
  field_simp [ha0]
  <;> ring

theorem gap9 (a : ℝ) (ha : 0 < a) :
    zCentroid a =
      1 / mass a *
        ∫ x in (0 : ℝ)..a,
          ∫ y in (0 : ℝ)..a - x,
            ∫ z in (0 : ℝ)..x ^ 2 + y ^ 2, z := by
  unfold zCentroid
  rw [integral_solid_eq_iterated a ha
    (fun q : Point3 => q.2.2)
    (continuous_snd.comp continuous_snd)]

theorem gap10 (a : ℝ) (ha : 0 < a) :
    1 / mass a *
        (∫ x in (0 : ℝ)..a,
          ∫ y in (0 : ℝ)..a - x,
            ∫ z in (0 : ℝ)..x ^ 2 + y ^ 2, z) =
      6 / a ^ 4 * ((7 : ℝ) / 180) * a ^ 6 := by
  have ha0 : a ≠ 0 := ha.ne'
  have hinner (x y : ℝ) :
      (∫ z in (0 : ℝ)..x ^ 2 + y ^ 2, z) =
        (x ^ 2 + y ^ 2) ^ 2 / 2 := by
    convert
      integral_poly5 0 1 0 0 0 0 0 (x ^ 2 + y ^ 2)
      using 1 <;> ring
  have hmoment :
      (∫ x in (0 : ℝ)..a,
        ∫ y in (0 : ℝ)..a - x,
          ∫ z in (0 : ℝ)..x ^ 2 + y ^ 2, z) =
        (7 : ℝ) / 180 * a ^ 6 := by
    calc
      (∫ x in (0 : ℝ)..a,
        ∫ y in (0 : ℝ)..a - x,
          ∫ z in (0 : ℝ)..x ^ 2 + y ^ 2, z) =
          ∫ x in (0 : ℝ)..a,
            ∫ y in (0 : ℝ)..a - x, (x ^ 2 + y ^ 2) ^ 2 / 2 := by
        apply intervalIntegral.integral_congr
        intro x hx
        apply intervalIntegral.integral_congr
        intro y hy
        exact hinner x y
      _ = ∫ x in (0 : ℝ)..a,
          a ^ 5 / 10 - a ^ 4 / 2 * x +
            (4 * a ^ 3 / 3) * x ^ 2 - 2 * a ^ 2 * x ^ 3 +
              2 * a * x ^ 4 - (14 / 15 : ℝ) * x ^ 5 := by
        apply intervalIntegral.integral_congr
        intro x hx
        calc
          (∫ y in (0 : ℝ)..a - x, (x ^ 2 + y ^ 2) ^ 2 / 2) =
              ∫ y in (0 : ℝ)..a - x,
                x ^ 4 / 2 + 0 * y + x ^ 2 * y ^ 2 +
                  0 * y ^ 3 + (1 / 2) * y ^ 4 + 0 * y ^ 5 := by
            apply intervalIntegral.integral_congr
            intro y hy
            ring
          _ = _ := by
            rw [integral_poly5]
            ring
      _ = (7 : ℝ) / 180 * a ^ 6 := by
        calc
          (∫ x in (0 : ℝ)..a,
            a ^ 5 / 10 - a ^ 4 / 2 * x +
              (4 * a ^ 3 / 3) * x ^ 2 - 2 * a ^ 2 * x ^ 3 +
                2 * a * x ^ 4 - (14 / 15 : ℝ) * x ^ 5) =
              ∫ x in (0 : ℝ)..a,
                a ^ 5 / 10 + (-(a ^ 4 / 2)) * x +
                  (4 * a ^ 3 / 3) * x ^ 2 + (-2 * a ^ 2) * x ^ 3 +
                    (2 * a) * x ^ 4 + (-(14 / 15 : ℝ)) * x ^ 5 := by
            apply intervalIntegral.integral_congr
            intro x hx
            ring
          _ = _ := by
            rw [integral_poly5]
            ring
  rw [gap3 a ha, hmoment]
  field_simp [ha0]
  <;> ring

theorem gap11 (a : ℝ) (ha : 0 < a) :
    6 / a ^ 4 * ((7 : ℝ) / 180) * a ^ 6 =
      (7 : ℝ) / 30 * a ^ 2 := by
  field_simp [ha.ne']
  <;> ring

theorem gap12 (a : ℝ) (ha : 0 < a) :
    zCentroid a = (7 : ℝ) / 30 * a ^ 2 := by
  rw [gap9 a ha, gap10 a ha, gap11 a ha]

theorem gap13 (a : ℝ) (ha : 0 < a) :
    (xCentroid a, yCentroid a, zCentroid a) =
      (2 * a / 5, 2 * a / 5, (7 : ℝ) / 30 * a ^ 2) := by
  rw [gap7 a ha, gap8 a ha, gap12 a ha]

end

end ProofGap.Exercise4134
