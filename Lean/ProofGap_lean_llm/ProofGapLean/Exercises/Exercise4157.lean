import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Measurability
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4157

noncomputable section

open MeasureTheory
open scoped Interval

abbrev Point3 := ℝ × ℝ × ℝ

def cylinder (a h : ℝ) : Set Point3 :=
  {p |
    p.1 ^ 2 + p.2.1 ^ 2 ≤ a ^ 2 ∧
      0 ≤ p.2.2 ∧ p.2.2 ≤ h}

def potential (a h ρ₀ z : ℝ) : ℝ :=
  ρ₀ * ∫ p in cylinder a h,
    1 / Real.sqrt (p.1 ^ 2 + p.2.1 ^ 2 + (p.2.2 - z) ^ 2)

private theorem radialKernelIntegrable (s d : ℝ) (hs : 0 ≤ s) :
    IntegrableOn
      (fun r : ℝ => r / Real.sqrt (r ^ 2 + d ^ 2))
      (Set.Ioc 0 s) := by
  by_cases hd : d = 0
  · subst d
    have hconst : Set.EqOn
        (fun r : ℝ => r / Real.sqrt (r ^ 2 + 0 ^ 2))
        (fun _ : ℝ => 1) (Set.Ioc 0 s) := by
      intro r hr
      dsimp
      rw [show (0 : ℝ) ^ 2 = 0 by norm_num, add_zero,
        Real.sqrt_sq_eq_abs, abs_of_pos hr.1,
        div_self (ne_of_gt hr.1)]
    exact
      (integrableOn_const (C := (1 : ℝ)) measure_Ioc_lt_top.ne).congr_fun
        hconst.symm measurableSet_Ioc
  · have hpos (r : ℝ) : 0 < r ^ 2 + d ^ 2 := by
      nlinarith [sq_nonneg r, sq_pos_of_ne_zero hd]
    have hcont : Continuous
        (fun r : ℝ => r / Real.sqrt (r ^ 2 + d ^ 2)) := by
      apply Continuous.div continuous_id
        (Real.continuous_sqrt.comp
          ((continuous_id.pow 2).add (continuous_const.pow 2)))
      intro r
      exact ne_of_gt (Real.sqrt_pos.2 (hpos r))
    exact hcont.integrableOn_Ioc

private theorem radialKernelIntegral (s d : ℝ) (hs : 0 ≤ s) :
    (∫ r in Set.Ioc 0 s, r / Real.sqrt (r ^ 2 + d ^ 2)) =
      Real.sqrt (s ^ 2 + d ^ 2) - |d| := by
  by_cases hd : d = 0
  · subst d
    calc
      (∫ r in Set.Ioc 0 s, r / Real.sqrt (r ^ 2 + 0 ^ 2)) =
          ∫ _r in Set.Ioc 0 s, (1 : ℝ) := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro r hr
        dsimp
        rw [show (0 : ℝ) ^ 2 = 0 by norm_num, add_zero,
          Real.sqrt_sq_eq_abs, abs_of_pos hr.1,
          div_self (ne_of_gt hr.1)]
      _ = s := by simp [Real.volume_Ioc, hs]
      _ = Real.sqrt (s ^ 2 + 0 ^ 2) - |(0 : ℝ)| := by
        rw [zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero,
          Real.sqrt_sq_eq_abs, abs_of_nonneg hs]
        simp
  · have hpos (r : ℝ) : 0 < r ^ 2 + d ^ 2 := by
      nlinarith [sq_nonneg r, sq_pos_of_ne_zero hd]
    have hcontF : Continuous
        (fun r : ℝ => Real.sqrt (r ^ 2 + d ^ 2)) :=
      Real.continuous_sqrt.comp
        ((continuous_id.pow 2).add (continuous_const.pow 2))
    have hcontf : Continuous
        (fun r : ℝ => r / Real.sqrt (r ^ 2 + d ^ 2)) := by
      apply Continuous.div continuous_id hcontF
      intro r
      exact ne_of_gt (Real.sqrt_pos.2 (hpos r))
    have hder : ∀ r ∈ Set.Ioo 0 s,
        HasDerivAt
          (fun x : ℝ => Real.sqrt (x ^ 2 + d ^ 2))
          (r / Real.sqrt (r ^ 2 + d ^ 2)) r := by
      intro r _
      have hinner :
          HasDerivAt (fun x : ℝ => x ^ 2 + d ^ 2) (2 * r) r := by
        convert ((hasDerivAt_id r).pow 2).add_const (d ^ 2) using 1 <;>
          simp [id] <;> ring
      have hsqrt := hinner.sqrt (ne_of_gt (hpos r))
      convert hsqrt using 1
      field_simp [ne_of_gt (Real.sqrt_pos.2 (hpos r))]
    have hFTC :
        (∫ r in 0..s, r / Real.sqrt (r ^ 2 + d ^ 2)) =
          Real.sqrt (s ^ 2 + d ^ 2) -
            Real.sqrt (0 ^ 2 + d ^ 2) := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hs
        hcontF.continuousOn hder
      exact hcontf.intervalIntegrable 0 s
    rw [← intervalIntegral.integral_of_le hs, hFTC,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      zero_add, Real.sqrt_sq_eq_abs]

private theorem radialKernelLIntegral (s d : ℝ) (hs : 0 ≤ s) :
    (∫⁻ r in Set.Ioc 0 s,
        ENNReal.ofReal (r / Real.sqrt (r ^ 2 + d ^ 2))) =
      ENNReal.ofReal (Real.sqrt (s ^ 2 + d ^ 2) - |d|) := by
  have hnonneg :
      ∀ᵐ r ∂volume.restrict (Set.Ioc 0 s),
        0 ≤ r / Real.sqrt (r ^ 2 + d ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact div_nonneg hr.1.le (Real.sqrt_nonneg _)
  rw [← ofReal_integral_eq_lintegral_ofReal
    (radialKernelIntegrable s d hs) hnonneg,
    radialKernelIntegral s d hs]

private theorem planeKernelLIntegral (s d : ℝ) (hs : 0 ≤ s) :
    (∫⁻ xy in {xy : ℝ × ℝ | xy.1 ^ 2 + xy.2 ^ 2 ≤ s ^ 2},
        ENNReal.ofReal
          (1 / Real.sqrt (xy.1 ^ 2 + xy.2 ^ 2 + d ^ 2))) =
      ENNReal.ofReal
        (2 * Real.pi * (Real.sqrt (s ^ 2 + d ^ 2) - |d|)) := by
  let D : Set (ℝ × ℝ) :=
    {xy | xy.1 ^ 2 + xy.2 ^ 2 ≤ s ^ 2}
  have hD : MeasurableSet D := by
    exact (isClosed_le
      ((continuous_fst.pow 2).add (continuous_snd.pow 2))
      continuous_const).measurableSet
  let P : Set (ℝ × ℝ) := polarCoord.symm ⁻¹' D
  have hP : MeasurableSet P :=
    hD.preimage continuous_polarCoord_symm.measurable
  let K : ℝ × ℝ → ENNReal := fun xy =>
    ENNReal.ofReal
      (1 / Real.sqrt (xy.1 ^ 2 + xy.2 ^ 2 + d ^ 2))
  change (∫⁻ xy in D, K xy) = _
  rw [← lintegral_indicator hD]
  rw [← lintegral_comp_polarCoord_symm]
  have hsq (u : ℝ × ℝ) :
      (polarCoord.symm u).1 ^ 2 +
          (polarCoord.symm u).2 ^ 2 = u.1 ^ 2 := by
    simp only [polarCoord_symm_apply]
    nlinarith [Real.sin_sq_add_cos_sq u.2]
  have hrewrite :
      (∫⁻ u in polarCoord.target,
          ENNReal.ofReal u.1 •
            D.indicator K (polarCoord.symm u)) =
        ∫⁻ u in polarCoord.target,
          P.indicator
            (fun v =>
              ENNReal.ofReal
                (v.1 / Real.sqrt (v.1 ^ 2 + d ^ 2))) u := by
    apply setLIntegral_congr_fun polarCoord.open_target.measurableSet
    intro u hu
    have hu₁ : 0 ≤ u.1 := hu.1.le
    by_cases hm : polarCoord.symm u ∈ D
    · have hmP : u ∈ P := hm
      rw [Set.indicator_of_mem hmP]
      simp only [K, Set.indicator_of_mem hm, smul_eq_mul]
      rw [hsq]
      simp only [div_eq_mul_inv]
      rw [ENNReal.ofReal_mul hu₁]
      simp
    · have hmP : u ∉ P := hm
      rw [Set.indicator_of_notMem hmP]
      change ENNReal.ofReal u.1 • D.indicator K (polarCoord.symm u) = 0
      rw [Set.indicator_of_notMem hm]
      simp
  rw [hrewrite, setLIntegral_indicator hP]
  have hset :
      P ∩ polarCoord.target =
        Set.Ioc 0 s ×ˢ Set.Ioo (-Real.pi) Real.pi := by
    ext u
    constructor
    · rintro ⟨hp, hu⟩
      have htpos : 0 < u.1 := hu.1
      have htsq : u.1 ^ 2 ≤ s ^ 2 := by
        change polarCoord.symm u ∈ D at hp
        simpa only [D, Set.mem_setOf_eq, hsq] using hp
      exact ⟨⟨htpos, (sq_le_sq₀ htpos.le hs).mp htsq⟩, hu.2⟩
    · rintro ⟨ht, hθ⟩
      refine ⟨?_, ⟨ht.1, hθ⟩⟩
      change polarCoord.symm u ∈ D
      change (polarCoord.symm u).1 ^ 2 +
          (polarCoord.symm u).2 ^ 2 ≤ s ^ 2
      rw [hsq]
      exact (sq_le_sq₀ ht.1.le hs).mpr ht.2
  rw [hset]
  have hmeas : Measurable
      (fun u : ℝ × ℝ =>
        ENNReal.ofReal
          (u.1 / Real.sqrt (u.1 ^ 2 + d ^ 2))) := by
    fun_prop
  rw [Measure.volume_eq_prod ℝ ℝ]
  rw [setLIntegral_prod _ hmeas.aemeasurable]
  simp_rw [setLIntegral_const]
  have hmeas₁ : Measurable
      (fun r : ℝ =>
        ENNReal.ofReal (r / Real.sqrt (r ^ 2 + d ^ 2))) := by
    fun_prop
  rw [lintegral_mul_const''
    (volume (Set.Ioo (-Real.pi) Real.pi))
    hmeas₁.aemeasurable]
  rw [radialKernelLIntegral s d hs]
  have hangle :
      volume (Set.Ioo (-Real.pi) Real.pi) =
        ENNReal.ofReal (2 * Real.pi) := by
    rw [Real.volume_Ioo]
    congr 1
    ring
  rw [hangle]
  calc
    ENNReal.ofReal (Real.sqrt (s ^ 2 + d ^ 2) - |d|) *
        ENNReal.ofReal (2 * Real.pi) =
      ENNReal.ofReal (2 * Real.pi) *
        ENNReal.ofReal (Real.sqrt (s ^ 2 + d ^ 2) - |d|) := by
          rw [mul_comm]
    _ = ENNReal.ofReal
        (2 * Real.pi * (Real.sqrt (s ^ 2 + d ^ 2) - |d|)) :=
      (ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * Real.pi)).symm

private theorem cylinder_measurable (a h : ℝ) :
    MeasurableSet (cylinder a h) := by
  unfold cylinder
  measurability

private theorem cylinderKernelLIntegral
    (a h z : ℝ) (ha : 0 < a) (hh : 0 < h) :
    (∫⁻ p in cylinder a h,
        ENNReal.ofReal
          (1 / Real.sqrt
            (p.1 ^ 2 + p.2.1 ^ 2 + (p.2.2 - z) ^ 2))) =
      ENNReal.ofReal
        (2 * Real.pi *
          ∫ ζ in (0 : ℝ)..h,
            Real.sqrt (a ^ 2 + (ζ - z) ^ 2) - |ζ - z|) := by
  let K : Point3 → ENNReal := fun p =>
    ENNReal.ofReal
      (1 / Real.sqrt
        (p.1 ^ 2 + p.2.1 ^ 2 + (p.2.2 - z) ^ 2))
  have hK : Measurable K := by
    dsimp [K]
    fun_prop
  have hC := cylinder_measurable a h
  rw [← lintegral_indicator hC]
  change (∫⁻ p, (cylinder a h).indicator K p) = _
  let A : ((ℝ × ℝ) × ℝ) ≃ᵐ Point3 :=
    MeasurableEquiv.prodAssoc
  have hA : MeasurePreserving A :=
    volume_preserving_prodAssoc
  have hcomp :
      (∫⁻ p, (cylinder a h).indicator K p) =
        ∫⁻ q : (ℝ × ℝ) × ℝ,
          (cylinder a h).indicator K (A q) := by
    exact (hA.lintegral_comp_emb A.measurableEmbedding _).symm
  rw [hcomp]
  have hmeas :
      Measurable
        (fun q : (ℝ × ℝ) × ℝ =>
          (cylinder a h).indicator K (A q)) :=
    (hK.indicator hC).comp A.measurable
  rw [Measure.volume_eq_prod (ℝ × ℝ) ℝ]
  rw [lintegral_prod_symm' _ hmeas]
  have hslice (ζ : ℝ) :
      (∫⁻ xy : ℝ × ℝ,
          (cylinder a h).indicator K (A (xy, ζ))) =
        if ζ ∈ Set.Icc (0 : ℝ) h then
          ENNReal.ofReal
            (2 * Real.pi *
              (Real.sqrt (a ^ 2 + (ζ - z) ^ 2) - |ζ - z|))
        else 0 := by
    by_cases hζ : ζ ∈ Set.Icc (0 : ℝ) h
    · rw [if_pos hζ]
      let D : Set (ℝ × ℝ) :=
        {xy | xy.1 ^ 2 + xy.2 ^ 2 ≤ a ^ 2}
      have hD : MeasurableSet D := by
        exact (isClosed_le
          ((continuous_fst.pow 2).add (continuous_snd.pow 2))
          continuous_const).measurableSet
      calc
        (∫⁻ xy : ℝ × ℝ,
            (cylinder a h).indicator K (A (xy, ζ))) =
            ∫⁻ xy in D,
              ENNReal.ofReal
                (1 / Real.sqrt
                  (xy.1 ^ 2 + xy.2 ^ 2 + (ζ - z) ^ 2)) := by
              rw [← lintegral_indicator hD]
              apply lintegral_congr
              intro xy
              have hmem :
                  A (xy, ζ) ∈ cylinder a h ↔ xy ∈ D := by
                change
                  (xy.1 ^ 2 + xy.2 ^ 2 ≤ a ^ 2 ∧
                    0 ≤ ζ ∧ ζ ≤ h) ↔
                      xy.1 ^ 2 + xy.2 ^ 2 ≤ a ^ 2
                simp only [hζ.1, hζ.2, and_self, and_true]
              by_cases hxy : xy ∈ D
              · rw [Set.indicator_of_mem hxy,
                  Set.indicator_of_mem (hmem.mpr hxy)]
                rfl
              · rw [Set.indicator_of_notMem hxy,
                  Set.indicator_of_notMem (mt hmem.mp hxy)]
        _ = ENNReal.ofReal
              (2 * Real.pi *
                (Real.sqrt (a ^ 2 + (ζ - z) ^ 2) - |ζ - z|)) := by
          simpa only [add_comm] using
            planeKernelLIntegral a (ζ - z) ha.le
    · rw [if_neg hζ]
      have hzero :
          (fun xy : ℝ × ℝ =>
            (cylinder a h).indicator K (A (xy, ζ))) =
              fun _ => 0 := by
        funext xy
        rw [Set.indicator_of_notMem]
        intro hm
        apply hζ
        exact ⟨hm.2.1, hm.2.2⟩
      rw [hzero]
      simp
  simp_rw [hslice]
  have hIcc : MeasurableSet (Set.Icc (0 : ℝ) h) := measurableSet_Icc
  have houter :
      (∫⁻ ζ : ℝ,
          if ζ ∈ Set.Icc (0 : ℝ) h then
            ENNReal.ofReal
              (2 * Real.pi *
                (Real.sqrt (a ^ 2 + (ζ - z) ^ 2) - |ζ - z|))
          else 0) =
        ∫⁻ ζ in Set.Icc (0 : ℝ) h,
          ENNReal.ofReal
            (2 * Real.pi *
              (Real.sqrt (a ^ 2 + (ζ - z) ^ 2) - |ζ - z|)) := by
    rw [← lintegral_indicator hIcc]
    apply lintegral_congr
    intro ζ
    by_cases hζ : ζ ∈ Set.Icc (0 : ℝ) h
    · rw [Set.indicator_of_mem hζ, if_pos hζ]
    · rw [Set.indicator_of_notMem hζ, if_neg hζ]
  rw [houter]
  let g : ℝ → ℝ := fun ζ =>
    2 * Real.pi *
      (Real.sqrt (a ^ 2 + (ζ - z) ^ 2) - |ζ - z|)
  have hgcont : Continuous g := by
    dsimp [g]
    fun_prop
  have hgint : IntegrableOn g (Set.Icc (0 : ℝ) h) :=
    hgcont.integrableOn_Icc
  have hgnonneg :
      ∀ᵐ ζ ∂volume.restrict (Set.Icc (0 : ℝ) h), 0 ≤ g ζ := by
    filter_upwards with ζ
    have hrad :
        (ζ - z) ^ 2 ≤ a ^ 2 + (ζ - z) ^ 2 := by
      nlinarith [sq_nonneg a]
    have hsqrt :
        |ζ - z| ≤ Real.sqrt (a ^ 2 + (ζ - z) ^ 2) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt hrad
    dsimp [g]
    exact mul_nonneg (by positivity) (sub_nonneg.mpr hsqrt)
  rw [← ofReal_integral_eq_lintegral_ofReal hgint hgnonneg]
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hh.le]
  dsimp [g]
  rw [intervalIntegral.integral_const_mul]

private theorem cylinderKernelIntegral
    (a h z : ℝ) (ha : 0 < a) (hh : 0 < h) :
    (∫ p in cylinder a h,
        1 / Real.sqrt
          (p.1 ^ 2 + p.2.1 ^ 2 + (p.2.2 - z) ^ 2)) =
      2 * Real.pi *
        ∫ ζ in (0 : ℝ)..h,
          Real.sqrt (a ^ 2 + (ζ - z) ^ 2) - |ζ - z| := by
  let K : Point3 → ℝ := fun p =>
    1 / Real.sqrt
      (p.1 ^ 2 + p.2.1 ^ 2 + (p.2.2 - z) ^ 2)
  have hnonneg :
      ∀ᵐ p ∂volume.restrict (cylinder a h), 0 ≤ K p :=
    Filter.Eventually.of_forall fun p =>
      div_nonneg zero_le_one (Real.sqrt_nonneg _)
  have hmeas :
      AEStronglyMeasurable K (volume.restrict (cylinder a h)) := by
    have hm : Measurable K := by
      dsimp [K]
      fun_prop
    exact hm.aestronglyMeasurable.restrict
  change (∫ p in cylinder a h, K p) = _
  rw [integral_eq_lintegral_of_nonneg_ae hnonneg hmeas,
    cylinderKernelLIntegral a h z ha hh]
  have hpoint (ζ : ℝ) :
      0 ≤ Real.sqrt (a ^ 2 + (ζ - z) ^ 2) - |ζ - z| := by
    have hrad :
        (ζ - z) ^ 2 ≤ a ^ 2 + (ζ - z) ^ 2 := by
      nlinarith [sq_nonneg a]
    have hsqrt :
        |ζ - z| ≤ Real.sqrt (a ^ 2 + (ζ - z) ^ 2) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt hrad
    exact sub_nonneg.mpr hsqrt
  have hint_nonneg :
      0 ≤ ∫ ζ in (0 : ℝ)..h,
        Real.sqrt (a ^ 2 + (ζ - z) ^ 2) - |ζ - z| :=
    intervalIntegral.integral_nonneg hh.le fun ζ _ => hpoint ζ
  rw [ENNReal.toReal_ofReal]
  exact mul_nonneg (by positivity) hint_nonneg

theorem gap1 (a h ρ₀ z : ℝ) (ha : 0 < a) (hh : 0 < h) :
    potential a h ρ₀ z =
      ρ₀ *
        ∫ φ in (0 : ℝ)..2 * Real.pi,
          ∫ ζ in (0 : ℝ)..h,
            ∫ r in (0 : ℝ)..a,
              r / Real.sqrt (r ^ 2 + (ζ - z) ^ 2) := by
  have hrad (ζ : ℝ) :
      (∫ r in (0 : ℝ)..a,
          r / Real.sqrt (r ^ 2 + (ζ - z) ^ 2)) =
        Real.sqrt (a ^ 2 + (ζ - z) ^ 2) - |ζ - z| := by
    rw [intervalIntegral.integral_of_le ha.le]
    exact radialKernelIntegral a (ζ - z) ha.le
  unfold potential
  rw [cylinderKernelIntegral a h z ha hh]
  simp_rw [hrad]
  rw [intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul]

theorem gap2 (a h ρ₀ z : ℝ) (ha : 0 < a) (hh : 0 < h) :
    potential a h ρ₀ z =
      2 * Real.pi * ρ₀ *
        ∫ ζ in (0 : ℝ)..h,
          Real.sqrt (a ^ 2 + (ζ - z) ^ 2) - |ζ - z| := by
  unfold potential
  rw [cylinderKernelIntegral a h z ha hh]
  ring

private def sqrtPrimitive (a x : ℝ) : ℝ :=
  x / 2 * Real.sqrt (x ^ 2 + a ^ 2) +
    a ^ 2 / 2 * Real.log (x + Real.sqrt (x ^ 2 + a ^ 2))

private theorem sqrtPrimitive_hasDerivAt
    (a x : ℝ) (ha : 0 < a) :
    HasDerivAt (sqrtPrimitive a)
      (Real.sqrt (a ^ 2 + x ^ 2)) x := by
  have hq : 0 < x ^ 2 + a ^ 2 := by
    nlinarith [sq_nonneg x, sq_nonneg a]
  have hspos : 0 < Real.sqrt (x ^ 2 + a ^ 2) :=
    Real.sqrt_pos.2 hq
  have hsq :
      Real.sqrt (x ^ 2 + a ^ 2) ^ 2 = x ^ 2 + a ^ 2 :=
    Real.sq_sqrt hq.le
  have hs_ge_abs : |x| ≤ Real.sqrt (x ^ 2 + a ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs x]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg a])
  have hsum_nonneg :
      0 ≤ x + Real.sqrt (x ^ 2 + a ^ 2) := by
    nlinarith [neg_abs_le x]
  have hsum_ne :
      x + Real.sqrt (x ^ 2 + a ^ 2) ≠ 0 := by
    intro hz
    nlinarith [hsq, sq_pos_of_pos ha]
  have hpoly :
      HasDerivAt (fun y : ℝ => y ^ 2 + a ^ 2) (2 * x) x := by
    convert
      (((hasDerivAt_id x).pow 2).add
        (hasDerivAt_const x (a ^ 2))) using 1 <;>
      norm_num <;> ring
  have hsqrt :
      HasDerivAt (fun y : ℝ => Real.sqrt (y ^ 2 + a ^ 2))
        (x / Real.sqrt (x ^ 2 + a ^ 2)) x := by
    convert (Real.hasDerivAt_sqrt hq.ne').comp x hpoly using 1 <;>
      field_simp [hspos.ne'] <;> ring
  have hlog :
      HasDerivAt
        (fun y : ℝ =>
          Real.log (y + Real.sqrt (y ^ 2 + a ^ 2)))
        ((1 + x / Real.sqrt (x ^ 2 + a ^ 2)) /
          (x + Real.sqrt (x ^ 2 + a ^ 2))) x := by
    convert
      (Real.hasDerivAt_log hsum_ne).comp x
        ((hasDerivAt_id x).add hsqrt) using 1 <;>
      field_simp [hspos.ne', hsum_ne] <;> ring
  have hratio :
      (1 + x / Real.sqrt (x ^ 2 + a ^ 2)) /
          (x + Real.sqrt (x ^ 2 + a ^ 2)) =
        1 / Real.sqrt (x ^ 2 + a ^ 2) := by
    field_simp [hspos.ne', hsum_ne] <;> ring
  have hderiv :
      1 / 2 * Real.sqrt (x ^ 2 + a ^ 2) +
          x / 2 * (x / Real.sqrt (x ^ 2 + a ^ 2)) +
          (0 * Real.log (x + Real.sqrt (x ^ 2 + a ^ 2)) +
            a ^ 2 / 2 *
              ((1 + x / Real.sqrt (x ^ 2 + a ^ 2)) /
                (x + Real.sqrt (x ^ 2 + a ^ 2)))) =
        Real.sqrt (a ^ 2 + x ^ 2) := by
    rw [hratio]
    rw [show a ^ 2 + x ^ 2 = x ^ 2 + a ^ 2 by ring]
    field_simp [hspos.ne']
    nlinarith [hsq]
  have htotal :=
    (((hasDerivAt_id x).div_const 2).mul hsqrt).add
      ((hasDerivAt_const x (a ^ 2 / 2)).mul hlog)
  have htotal' :
      HasDerivAt (sqrtPrimitive a)
        (1 / 2 * Real.sqrt (x ^ 2 + a ^ 2) +
          x / 2 * (x / Real.sqrt (x ^ 2 + a ^ 2)) +
          (0 * Real.log (x + Real.sqrt (x ^ 2 + a ^ 2)) +
            a ^ 2 / 2 *
              ((1 + x / Real.sqrt (x ^ 2 + a ^ 2)) /
                (x + Real.sqrt (x ^ 2 + a ^ 2))))) x := by
    simpa only [sqrtPrimitive, id_eq] using htotal
  rw [hderiv] at htotal'
  exact htotal'

private theorem shiftedSqrtIntegral
    (a h z : ℝ) (ha : 0 < a) :
    (∫ ζ in (0 : ℝ)..h,
        Real.sqrt (a ^ 2 + (ζ - z) ^ 2)) =
      sqrtPrimitive a (h - z) - sqrtPrimitive a (-z) := by
  calc
    (∫ ζ in (0 : ℝ)..h,
        Real.sqrt (a ^ 2 + (ζ - z) ^ 2)) =
        ∫ x in (0 : ℝ) - z..h - z,
          Real.sqrt (a ^ 2 + x ^ 2) := by
      simpa only [zero_sub] using
        (intervalIntegral.integral_comp_sub_right
          (fun x : ℝ => Real.sqrt (a ^ 2 + x ^ 2)) z
          (a := (0 : ℝ)) (b := h))
    _ = sqrtPrimitive a (h - z) - sqrtPrimitive a (-z) := by
      simpa only [zero_sub] using
        (intervalIntegral.integral_eq_sub_of_hasDerivAt
          (fun x _ => sqrtPrimitive_hasDerivAt a x ha)
          ((Real.continuous_sqrt.comp
            ((continuous_const.pow 2).add
              (continuous_id.pow 2))).intervalIntegrable
                ((0 : ℝ) - z) (h - z)))

private theorem shiftedAbsIntegral (h z : ℝ) (hh : 0 < h) :
    (∫ ζ in (0 : ℝ)..h, |ζ - z|) =
      ((h - z) * |h - z| + z * |z|) / 2 := by
  have habs (u v : ℝ) :
      IntervalIntegrable (fun ζ : ℝ => |ζ - z|) volume u v :=
    ((continuous_id.sub continuous_const).abs).intervalIntegrable _ _
  have evalRight (u v : ℝ) :
      (∫ ζ in u..v, ζ - z) =
        (v ^ 2 - u ^ 2) / 2 - z * (v - u) := by
    have hiId :
        IntervalIntegrable (fun ζ : ℝ => ζ) volume u v :=
      continuous_id.intervalIntegrable _ _
    have hiConst :
        IntervalIntegrable (fun _ζ : ℝ => z) volume u v :=
      continuous_const.intervalIntegrable _ _
    rw [intervalIntegral.integral_sub hiId hiConst, integral_id,
      intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  have evalLeft (u v : ℝ) :
      (∫ ζ in u..v, z - ζ) =
        z * (v - u) - (v ^ 2 - u ^ 2) / 2 := by
    have hiId :
        IntervalIntegrable (fun ζ : ℝ => ζ) volume u v :=
      continuous_id.intervalIntegrable _ _
    have hiConst :
        IntervalIntegrable (fun _ζ : ℝ => z) volume u v :=
      continuous_const.intervalIntegrable _ _
    rw [intervalIntegral.integral_sub hiConst hiId, integral_id,
      intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    ring
  by_cases hz₀ : z ≤ 0
  · calc
      (∫ ζ in (0 : ℝ)..h, |ζ - z|) =
          ∫ ζ in (0 : ℝ)..h, ζ - z := by
        apply intervalIntegral.integral_congr
        intro ζ hζ
        rw [Set.uIcc_of_le hh.le] at hζ
        change |ζ - z| = ζ - z
        rw [abs_of_nonneg
          (sub_nonneg.mpr (hz₀.trans hζ.1))]
      _ = (h ^ 2 - 0 ^ 2) / 2 - z * (h - 0) :=
        evalRight 0 h
      _ = ((h - z) * |h - z| + z * |z|) / 2 := by
        rw [abs_of_nonneg (by linarith),
          abs_of_nonpos hz₀]
        ring
  · have hzpos : 0 < z := lt_of_not_ge hz₀
    by_cases hzh : h ≤ z
    · calc
        (∫ ζ in (0 : ℝ)..h, |ζ - z|) =
            ∫ ζ in (0 : ℝ)..h, z - ζ := by
          apply intervalIntegral.integral_congr
          intro ζ hζ
          rw [Set.uIcc_of_le hh.le] at hζ
          change |ζ - z| = z - ζ
          rw [abs_of_nonpos
            (sub_nonpos.mpr (hζ.2.trans hzh))]
          ring
        _ = z * (h - 0) - (h ^ 2 - 0 ^ 2) / 2 :=
          evalLeft 0 h
        _ = ((h - z) * |h - z| + z * |z|) / 2 := by
          rw [abs_of_nonpos (by linarith),
            abs_of_pos hzpos]
          ring
    · have hzh' : z < h := lt_of_not_ge hzh
      rw [← intervalIntegral.integral_add_adjacent_intervals
        (habs 0 z) (habs z h)]
      have hleft :
          (∫ ζ in (0 : ℝ)..z, |ζ - z|) =
            ∫ ζ in (0 : ℝ)..z, z - ζ := by
        apply intervalIntegral.integral_congr
        intro ζ hζ
        rw [Set.uIcc_of_le hzpos.le] at hζ
        change |ζ - z| = z - ζ
        rw [abs_of_nonpos (sub_nonpos.mpr hζ.2)]
        ring
      have hright :
          (∫ ζ in z..h, |ζ - z|) =
            ∫ ζ in z..h, ζ - z := by
        apply intervalIntegral.integral_congr
        intro ζ hζ
        rw [Set.uIcc_of_le hzh'.le] at hζ
        change |ζ - z| = ζ - z
        rw [abs_of_nonneg (sub_nonneg.mpr hζ.1)]
      rw [hleft, hright, evalLeft, evalRight,
        abs_of_pos (by linarith : 0 < h - z),
        abs_of_pos hzpos]
      ring

theorem gap3 (a h ρ₀ z : ℝ) (ha : 0 < a) (hh : 0 < h) :
    potential a h ρ₀ z =
      Real.pi * ρ₀ *
        ((h - z) * Real.sqrt (a ^ 2 + (h - z) ^ 2) +
          z * Real.sqrt (a ^ 2 + z ^ 2) -
          ((h - z) * |h - z| + z * |z|) +
          a ^ 2 *
            Real.log
              |(h - z + Real.sqrt (a ^ 2 + (h - z) ^ 2)) /
                (-z + Real.sqrt (a ^ 2 + z ^ 2))|) := by
  rw [gap2 a h ρ₀ z ha hh]
  have hsqrtInt :
      IntervalIntegrable
        (fun ζ : ℝ => Real.sqrt (a ^ 2 + (ζ - z) ^ 2))
        volume 0 h :=
    (Real.continuous_sqrt.comp
      ((continuous_const.pow 2).add
        ((continuous_id.sub continuous_const).pow 2))).intervalIntegrable _ _
  have habsInt :
      IntervalIntegrable (fun ζ : ℝ => |ζ - z|) volume 0 h :=
    ((continuous_id.sub continuous_const).abs).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub hsqrtInt habsInt,
    shiftedSqrtIntegral a h z ha,
    shiftedAbsIntegral h z hh]
  have hpos (x : ℝ) :
      0 < x + Real.sqrt (a ^ 2 + x ^ 2) := by
    have hq : 0 < a ^ 2 + x ^ 2 := by
      nlinarith [sq_pos_of_pos ha, sq_nonneg x]
    have hs : 0 < Real.sqrt (a ^ 2 + x ^ 2) :=
      Real.sqrt_pos.2 hq
    have hsq :
        Real.sqrt (a ^ 2 + x ^ 2) ^ 2 = a ^ 2 + x ^ 2 :=
      Real.sq_sqrt hq.le
    by_contra hn
    have hle : Real.sqrt (a ^ 2 + x ^ 2) ≤ -x := by
      linarith
    have hx : x < 0 := by linarith
    nlinarith [mul_self_le_mul_self hs.le hle]
  have hnum :
      0 < h - z + Real.sqrt (a ^ 2 + (h - z) ^ 2) :=
    hpos (h - z)
  have hden :
      0 < -z + Real.sqrt (a ^ 2 + z ^ 2) := by
    simpa only [neg_sq] using hpos (-z)
  have hlog :
      Real.log
          (h - z + Real.sqrt (a ^ 2 + (h - z) ^ 2)) -
          Real.log (-z + Real.sqrt (a ^ 2 + z ^ 2)) =
        Real.log
          |(h - z + Real.sqrt (a ^ 2 + (h - z) ^ 2)) /
            (-z + Real.sqrt (a ^ 2 + z ^ 2))| := by
    rw [abs_of_pos (div_pos hnum hden),
      Real.log_div hnum.ne' hden.ne']
  unfold sqrtPrimitive
  rw [show (-z) ^ 2 = z ^ 2 by ring]
  have hs₁ :
      Real.sqrt ((h - z) ^ 2 + a ^ 2) =
        Real.sqrt (a ^ 2 + (h - z) ^ 2) := by
    congr 1
    ring
  have hs₂ :
      Real.sqrt (z ^ 2 + a ^ 2) =
        Real.sqrt (a ^ 2 + z ^ 2) := by
    congr 1
    ring
  rw [hs₁, hs₂, ← hlog]
  ring

end

end ProofGap.Exercise4157
