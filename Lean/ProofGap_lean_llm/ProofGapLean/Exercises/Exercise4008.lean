import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4008

noncomputable section

open MeasureTheory
open scoped Interval

def baseRegion (R : ℝ) : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 ^ 2 + p.2 ^ 2 ≤ R ^ 2}

def volume (a R : ℝ) : ℝ :=
  ∫ p in baseRegion R, a - p.1 - p.2

theorem gap1 (a R : ℝ) (hR : 0 ≤ R)
    (ha : R * Real.sqrt 2 ≤ a) :
    volume a R =
      ∫ x in (0 : ℝ)..R,
        ∫ y in (0 : ℝ)..Real.sqrt (R ^ 2 - x ^ 2),
          a - x - y := by
  let g : ℝ × ℝ → ℝ := fun p => a - p.1 - p.2
  have hbase : MeasurableSet (baseRegion R) := by
    unfold baseRegion
    measurability
  have hsubset :
      baseRegion R ⊆ Set.Icc (0 : ℝ) R ×ˢ Set.Icc (0 : ℝ) R := by
    rintro ⟨x, y⟩ ⟨hx, hy, hxy⟩
    have hxR : x ≤ R := by nlinarith [sq_nonneg y]
    have hyR : y ≤ R := by nlinarith [sq_nonneg x]
    exact ⟨⟨hx, hxR⟩, ⟨hy, hyR⟩⟩
  have hgcont : Continuous g := by
    dsimp [g]
    fun_prop
  have hgint : IntegrableOn g (baseRegion R) := by
    have hbox :
        IsCompact (Set.Icc (0 : ℝ) R ×ˢ Set.Icc (0 : ℝ) R) :=
      isCompact_Icc.prod isCompact_Icc
    exact (hgcont.continuousOn.integrableOn_compact hbox).mono_set hsubset
  have hsection : ∀ x ∈ Set.Icc (0 : ℝ) R,
      (∫ y : ℝ, (baseRegion R).indicator g (x, y)) =
        ∫ y in (0 : ℝ)..Real.sqrt (R ^ 2 - x ^ 2), a - x - y := by
    intro x hx
    have hrad : 0 ≤ R ^ 2 - x ^ 2 := by
      have hfac := mul_nonneg (sub_nonneg.mpr hx.2) (add_nonneg hR hx.1)
      nlinarith
    let s : ℝ := Real.sqrt (R ^ 2 - x ^ 2)
    have hs : 0 ≤ s := Real.sqrt_nonneg _
    have hsquare : s ^ 2 = R ^ 2 - x ^ 2 := Real.sq_sqrt hrad
    have hmem : ∀ y : ℝ,
        (x, y) ∈ baseRegion R ↔ y ∈ Set.Icc (0 : ℝ) s := by
      intro y
      constructor
      · rintro ⟨_, hy, hxy⟩
        exact ⟨hy, by nlinarith [sq_nonneg (s - y)]⟩
      · rintro ⟨hy, hys⟩
        refine ⟨hx.1, hy, ?_⟩
        nlinarith [sq_nonneg (s - y)]
    have hind :
        (fun y : ℝ => (baseRegion R).indicator g (x, y)) =
          (Set.Icc (0 : ℝ) s).indicator (fun y => a - x - y) := by
      funext y
      by_cases hy : y ∈ Set.Icc (0 : ℝ) s
      · rw [Set.indicator_of_mem hy,
          Set.indicator_of_mem ((hmem y).mpr hy)]
      · rw [Set.indicator_of_notMem hy,
          Set.indicator_of_notMem (fun hxy => hy ((hmem y).mp hxy))]
    rw [hind, MeasureTheory.integral_indicator measurableSet_Icc]
    rw [← Measure.restrict_congr_set
      (Ioc_ae_eq_Icc :
        Set.Ioc (0 : ℝ) s =ᵐ[MeasureTheory.volume] Set.Icc 0 s)]
    rw [← intervalIntegral.integral_of_le hs]
  have hinner : ∀ x : ℝ,
      (∫ y : ℝ, (baseRegion R).indicator g (x, y)) =
        (Set.Icc (0 : ℝ) R).indicator
          (fun x =>
            ∫ y in (0 : ℝ)..Real.sqrt (R ^ 2 - x ^ 2),
              a - x - y) x := by
    intro x
    by_cases hx : x ∈ Set.Icc (0 : ℝ) R
    · rw [Set.indicator_of_mem hx]
      exact hsection x hx
    · rw [Set.indicator_of_notMem hx]
      have hnone : ∀ y : ℝ, (x, y) ∉ baseRegion R := by
        intro y hxy
        exact hx (hsubset hxy).1
      simp [hnone]
  calc
    volume a R =
        ∫ p : ℝ × ℝ, (baseRegion R).indicator g p := by
          rw [volume, MeasureTheory.integral_indicator hbase]
    _ = ∫ x : ℝ, ∫ y : ℝ,
          (baseRegion R).indicator g (x, y) := by
          have hi : Integrable ((baseRegion R).indicator g) :=
            (integrable_indicator_iff hbase).2 hgint
          simpa using MeasureTheory.integral_prod _ hi
    _ = ∫ x : ℝ,
          (Set.Icc (0 : ℝ) R).indicator
            (fun x =>
              ∫ y in (0 : ℝ)..Real.sqrt (R ^ 2 - x ^ 2),
                a - x - y) x := by
          apply MeasureTheory.integral_congr_ae
          exact Filter.Eventually.of_forall hinner
    _ = ∫ x in Set.Icc (0 : ℝ) R,
          ∫ y in (0 : ℝ)..Real.sqrt (R ^ 2 - x ^ 2),
            a - x - y := by
          rw [MeasureTheory.integral_indicator measurableSet_Icc]
    _ = ∫ x in Set.Ioc (0 : ℝ) R,
          ∫ y in (0 : ℝ)..Real.sqrt (R ^ 2 - x ^ 2),
            a - x - y := by
          rw [Measure.restrict_congr_set
            (Ioc_ae_eq_Icc :
              Set.Ioc (0 : ℝ) R =ᵐ[MeasureTheory.volume] Set.Icc 0 R)]
    _ = ∫ x in (0 : ℝ)..R,
          ∫ y in (0 : ℝ)..Real.sqrt (R ^ 2 - x ^ 2),
            a - x - y := by
          rw [intervalIntegral.integral_of_le hR]

theorem gap2 (a R : ℝ) (hR : 0 ≤ R)
    (ha : R * Real.sqrt 2 ≤ a) :
    volume a R =
      ∫ x in (0 : ℝ)..R,
        (a - x) * Real.sqrt (R ^ 2 - x ^ 2) -
          (R ^ 2 - x ^ 2) / 2 := by
  rw [gap1 a R hR ha]
  apply intervalIntegral.integral_congr
  intro x hx
  rw [Set.uIcc_of_le hR] at hx
  have hrad : 0 ≤ R ^ 2 - x ^ 2 := by
    have hfac := mul_nonneg (sub_nonneg.mpr hx.2) (add_nonneg hR hx.1)
    nlinarith
  let s : ℝ := Real.sqrt (R ^ 2 - x ^ 2)
  have hsquare : s ^ 2 = R ^ 2 - x ^ 2 := Real.sq_sqrt hrad
  have hderiv : ∀ y : ℝ,
      HasDerivAt (fun z : ℝ => (a - x) * z - z ^ 2 / 2)
        (a - x - y) y := by
    intro y
    convert
      ((hasDerivAt_id y).const_mul (a - x)).sub
        (((hasDerivAt_id y).pow 2).div_const 2) using 1 <;>
      simp only [id_eq] <;> ring
  have hint : IntervalIntegrable (fun y : ℝ => a - x - y)
      MeasureTheory.volume 0 s :=
    (by fun_prop : Continuous (fun y : ℝ => a - x - y)).intervalIntegrable 0 s
  change (∫ y in (0 : ℝ)..s, a - x - y) =
    (a - x) * s - (R ^ 2 - x ^ 2) / 2
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y _ => hderiv y) hint]
  rw [← hsquare]
  ring

theorem gap3 (a R : ℝ) (hR : 0 ≤ R)
    (ha : R * Real.sqrt 2 ≤ a) :
    volume a R =
      (∫ x in (0 : ℝ)..R, a * Real.sqrt (R ^ 2 - x ^ 2)) -
        ∫ x in (0 : ℝ)..R,
          x * Real.sqrt (R ^ 2 - x ^ 2) +
            (R ^ 2 - x ^ 2) / 2 := by
  rw [gap2 a R hR ha]
  let f : ℝ → ℝ := fun x => a * Real.sqrt (R ^ 2 - x ^ 2)
  let g : ℝ → ℝ := fun x =>
    x * Real.sqrt (R ^ 2 - x ^ 2) + (R ^ 2 - x ^ 2) / 2
  have hf : IntervalIntegrable f MeasureTheory.volume 0 R :=
    (by fun_prop : Continuous f).intervalIntegrable 0 R
  have hg : IntervalIntegrable g MeasureTheory.volume 0 R :=
    (by fun_prop : Continuous g).intervalIntegrable 0 R
  calc
    (∫ x in (0 : ℝ)..R,
      (a - x) * Real.sqrt (R ^ 2 - x ^ 2) -
        (R ^ 2 - x ^ 2) / 2) =
        ∫ x in (0 : ℝ)..R, f x - g x := by
          apply intervalIntegral.integral_congr
          intro x hx
          dsimp [f, g]
          ring
    _ = (∫ x in (0 : ℝ)..R, f x) -
        ∫ x in (0 : ℝ)..R, g x := by
          rw [intervalIntegral.integral_sub hf hg]
    _ = _ := rfl

private theorem quarterCircle (R : ℝ) (hR : 0 ≤ R) :
    (∫ x in (0 : ℝ)..R, Real.sqrt (R ^ 2 - x ^ 2)) =
      Real.pi * R ^ 2 / 4 := by
  rcases hR.eq_or_lt with rfl | hRpos
  · simp
  have hR0 : R ≠ 0 := ne_of_gt hRpos
  have hunit :
      (∫ u in (0 : ℝ)..1, Real.sqrt (1 - u ^ 2)) = Real.pi / 4 := by
    let f : ℝ → ℝ := fun u => Real.sqrt (1 - u ^ 2)
    have heven : ∀ u : ℝ, f (-u) = f u := by
      intro u
      simp [f]
    have hneg :
        (∫ u in (-1 : ℝ)..0, f u) = ∫ u in (0 : ℝ)..1, f u := by
      have h := intervalIntegral.integral_comp_neg
        (f := f) (a := (0 : ℝ)) (b := 1)
      calc
        (∫ u in (-1 : ℝ)..0, f u) =
            ∫ u in (0 : ℝ)..1, f (-u) := by
              simpa only [neg_zero] using h.symm
        _ = ∫ u in (0 : ℝ)..1, f u := by
              apply intervalIntegral.integral_congr
              intro u hu
              exact heven u
    have hcont : Continuous f := by
      dsimp [f]
      fun_prop
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (μ := MeasureTheory.volume)
      (hcont.intervalIntegrable (-1) 0)
      (hcont.intervalIntegrable 0 1)
    rw [hneg, integral_sqrt_one_sub_sq] at hadd
    linarith
  have hpoint : ∀ u : ℝ,
      Real.sqrt (R ^ 2 - (R * u) ^ 2) =
        R * Real.sqrt (1 - u ^ 2) := by
    intro u
    rw [show R ^ 2 - (R * u) ^ 2 = R ^ 2 * (1 - u ^ 2) by ring,
      Real.sqrt_mul (sq_nonneg R), Real.sqrt_sq hRpos.le]
  have hchange :=
    intervalIntegral.smul_integral_comp_mul_left
      (fun x : ℝ => Real.sqrt (R ^ 2 - x ^ 2))
      (a := (0 : ℝ)) (b := 1) R
  calc
    (∫ x in (0 : ℝ)..R, Real.sqrt (R ^ 2 - x ^ 2)) =
        R * ∫ u in (0 : ℝ)..1,
          Real.sqrt (R ^ 2 - (R * u) ^ 2) := by
            simpa [smul_eq_mul] using hchange.symm
    _ = R * ∫ u in (0 : ℝ)..1,
          R * Real.sqrt (1 - u ^ 2) := by
            congr 1
            apply intervalIntegral.integral_congr
            intro u hu
            exact hpoint u
    _ = R * (R * ∫ u in (0 : ℝ)..1,
          Real.sqrt (1 - u ^ 2)) := by
            rw [intervalIntegral.integral_const_mul]
    _ = Real.pi * R ^ 2 / 4 := by rw [hunit]; ring

private theorem firstMoment (R : ℝ) (hR : 0 ≤ R) :
    (∫ x in (0 : ℝ)..R,
      x * Real.sqrt (R ^ 2 - x ^ 2)) = R ^ 3 / 3 := by
  rcases hR.eq_or_lt with rfl | hRpos
  · simp
  let F : ℝ → ℝ := fun x => -(Real.sqrt (R ^ 2 - x ^ 2) ^ 3) / 3
  have hFcont : Continuous F := by
    dsimp [F]
    fun_prop
  have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) R,
      HasDerivAt F (x * Real.sqrt (R ^ 2 - x ^ 2)) x := by
    intro x hx
    have hrad : 0 < R ^ 2 - x ^ 2 := by
      have hfac := mul_pos (sub_pos.mpr hx.2) (add_pos_of_pos_of_nonneg hx.1 hR)
      nlinarith
    have hinner : HasDerivAt (fun z : ℝ => R ^ 2 - z ^ 2)
        (-2 * x) x := by
      convert (hasDerivAt_const x (R ^ 2)).sub
        ((hasDerivAt_id x).pow 2) using 1 <;>
        simp only [id_eq] <;> ring
    have hsqrt : HasDerivAt (fun z : ℝ => Real.sqrt (R ^ 2 - z ^ 2))
        (1 / (2 * Real.sqrt (R ^ 2 - x ^ 2)) * (-2 * x)) x := by
      simpa only [Function.comp_apply] using
        (Real.hasDerivAt_sqrt hrad.ne').comp x hinner
    have hsquare : Real.sqrt (R ^ 2 - x ^ 2) ^ 2 = R ^ 2 - x ^ 2 :=
      Real.sq_sqrt hrad.le
    change HasDerivAt
      (fun z : ℝ => -(Real.sqrt (R ^ 2 - z ^ 2) ^ 3) / 3)
      _ x
    convert (hsqrt.pow 3).neg.div_const 3 using 1
    field_simp [Real.sqrt_ne_zero'.mpr hrad]
    ring
  have hint : IntervalIntegrable
      (fun x : ℝ => x * Real.sqrt (R ^ 2 - x ^ 2))
      MeasureTheory.volume 0 R := by
    refine intervalIntegral.intervalIntegrable_deriv_of_nonneg
      hFcont.continuousOn ?_ ?_
    · intro x hx
      exact hderiv x (by
        simpa [min_eq_left hRpos.le, max_eq_right hRpos.le] using hx)
    · intro x hx
      have hx' : x ∈ Set.Ioo (0 : ℝ) R := by
        simpa [min_eq_left hRpos.le, max_eq_right hRpos.le] using hx
      exact mul_nonneg hx'.1.le (Real.sqrt_nonneg _)
  have hftc :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      hRpos.le hFcont.continuousOn hderiv hint
  have hsR : Real.sqrt (R ^ 2) = R := Real.sqrt_sq hRpos.le
  convert hftc using 1 <;> simp [F, hsR] <;> ring

private theorem polynomialMoment (R : ℝ) :
    (∫ x in (0 : ℝ)..R, (R ^ 2 - x ^ 2) / 2) = R ^ 3 / 3 := by
  let F : ℝ → ℝ := fun x => R ^ 2 * x / 2 - x ^ 3 / 6
  have hd : ∀ x : ℝ,
      HasDerivAt F ((R ^ 2 - x ^ 2) / 2) x := by
    intro x
    change HasDerivAt
      (fun z : ℝ => R ^ 2 * z / 2 - z ^ 3 / 6) _ x
    convert
      (((hasDerivAt_id x).const_mul (R ^ 2)).div_const 2).sub
        (((hasDerivAt_id x).pow 3).div_const 6) using 1 <;>
      simp only [id_eq] <;> ring
  have hi : IntervalIntegrable (fun x : ℝ => (R ^ 2 - x ^ 2) / 2)
      MeasureTheory.volume 0 R :=
    (by fun_prop : Continuous
      (fun x : ℝ => (R ^ 2 - x ^ 2) / 2)).intervalIntegrable 0 R
  calc
    _ = F R - F 0 := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro x hx
        exact hd x
      · exact hi
    _ = _ := by dsimp [F]; ring

theorem gap4 (a R : ℝ) (hR : 0 ≤ R)
    (ha : R * Real.sqrt 2 ≤ a) :
    (∫ x in (0 : ℝ)..R, a * Real.sqrt (R ^ 2 - x ^ 2)) -
          (∫ x in (0 : ℝ)..R,
            x * Real.sqrt (R ^ 2 - x ^ 2) +
              (R ^ 2 - x ^ 2) / 2) =
      Real.pi * a * R ^ 2 / 4 - 2 * R ^ 3 / 3 := by
  have h1 : IntervalIntegrable
      (fun x : ℝ => x * Real.sqrt (R ^ 2 - x ^ 2))
      MeasureTheory.volume 0 R :=
    (by fun_prop : Continuous
      (fun x : ℝ => x * Real.sqrt (R ^ 2 - x ^ 2))).intervalIntegrable 0 R
  have h2 : IntervalIntegrable
      (fun x : ℝ => (R ^ 2 - x ^ 2) / 2)
      MeasureTheory.volume 0 R :=
    (by fun_prop : Continuous
      (fun x : ℝ => (R ^ 2 - x ^ 2) / 2)).intervalIntegrable 0 R
  rw [intervalIntegral.integral_const_mul, quarterCircle R hR,
    intervalIntegral.integral_add h1 h2, firstMoment R hR,
    polynomialMoment R]
  ring

theorem gap5 (a R : ℝ) (hR : 0 ≤ R)
    (ha : R * Real.sqrt 2 ≤ a) :
    volume a R =
      Real.pi * a * R ^ 2 / 4 - 2 * R ^ 3 / 3 := by
  exact (gap3 a R hR ha).trans (gap4 a R hR ha)

end

end ProofGap.Exercise4008
