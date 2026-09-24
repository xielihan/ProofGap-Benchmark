import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4155

noncomputable section

open MeasureTheory
open scoped Interval

abbrev Point3 := ℝ × ℝ × ℝ

def ball (R : ℝ) : Set Point3 :=
  {p | p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 ≤ R ^ 2}

def potential (R ρ₀ r : ℝ) : ℝ :=
  ρ₀ * ∫ p in ball R,
    1 / Real.sqrt (p.1 ^ 2 + p.2.1 ^ 2 + (p.2.2 - r) ^ 2)

private theorem radialKernelIntegrable (s a : ℝ) (hs : 0 ≤ s) :
    IntegrableOn
      (fun t : ℝ => t / Real.sqrt (t ^ 2 + a ^ 2))
      (Set.Ioc 0 s) := by
  by_cases ha : a = 0
  · subst a
    have hconst : Set.EqOn
        (fun t : ℝ => t / Real.sqrt (t ^ 2 + 0 ^ 2))
        (fun _ : ℝ => 1) (Set.Ioc 0 s) := by
      intro t ht
      dsimp
      rw [show (0 : ℝ) ^ 2 = 0 by norm_num, add_zero,
        Real.sqrt_sq_eq_abs, abs_of_pos ht.1, div_self (ne_of_gt ht.1)]
    exact (integrableOn_const (C := (1 : ℝ)) measure_Ioc_lt_top.ne).congr_fun
      hconst.symm measurableSet_Ioc
  · have hpos (t : ℝ) : 0 < t ^ 2 + a ^ 2 := by
      nlinarith [sq_nonneg t, sq_pos_of_ne_zero ha]
    have hcont : Continuous
        (fun t : ℝ => t / Real.sqrt (t ^ 2 + a ^ 2)) := by
      apply Continuous.div continuous_id
        (Real.continuous_sqrt.comp
          (continuous_pow 2 |>.add (continuous_const.pow 2)))
      intro t
      exact ne_of_gt (Real.sqrt_pos.2 (hpos t))
    exact hcont.integrableOn_Ioc

private theorem radialKernelIntegral (s a : ℝ) (hs : 0 ≤ s) :
    (∫ t in Set.Ioc 0 s, t / Real.sqrt (t ^ 2 + a ^ 2)) =
      Real.sqrt (s ^ 2 + a ^ 2) - |a| := by
  by_cases ha : a = 0
  · subst a
    calc
      (∫ t in Set.Ioc 0 s, t / Real.sqrt (t ^ 2 + 0 ^ 2)) =
          ∫ _t in Set.Ioc 0 s, (1 : ℝ) := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro t ht
        dsimp
        rw [show (0 : ℝ) ^ 2 = 0 by norm_num, add_zero,
          Real.sqrt_sq_eq_abs, abs_of_pos ht.1, div_self (ne_of_gt ht.1)]
      _ = s := by simp [Real.volume_Ioc, hs]
      _ = Real.sqrt (s ^ 2 + 0 ^ 2) - |(0 : ℝ)| := by
        rw [zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero,
          Real.sqrt_sq_eq_abs, abs_of_nonneg hs]
        simp
  · have hpos (t : ℝ) : 0 < t ^ 2 + a ^ 2 := by
      nlinarith [sq_nonneg t, sq_pos_of_ne_zero ha]
    have hcontF : Continuous
        (fun t : ℝ => Real.sqrt (t ^ 2 + a ^ 2)) :=
      Real.continuous_sqrt.comp
        (continuous_pow 2 |>.add (continuous_const.pow 2))
    have hcontf : Continuous
        (fun t : ℝ => t / Real.sqrt (t ^ 2 + a ^ 2)) := by
      apply Continuous.div continuous_id hcontF
      intro t
      exact ne_of_gt (Real.sqrt_pos.2 (hpos t))
    have hder : ∀ t ∈ Set.Ioo 0 s,
        HasDerivAt
          (fun x : ℝ => Real.sqrt (x ^ 2 + a ^ 2))
          (t / Real.sqrt (t ^ 2 + a ^ 2)) t := by
      intro t ht
      have hinner :
          HasDerivAt (fun x : ℝ => x ^ 2 + a ^ 2) (2 * t) t := by
        convert ((hasDerivAt_id t).pow 2).add_const (a ^ 2) using 1 <;>
          simp [id] <;> ring
      have hsqrt := hinner.sqrt (ne_of_gt (hpos t))
      convert hsqrt using 1
      field_simp [ne_of_gt (Real.sqrt_pos.2 (hpos t))]
    have hFTC :
        (∫ t in 0..s, t / Real.sqrt (t ^ 2 + a ^ 2)) =
          Real.sqrt (s ^ 2 + a ^ 2) - Real.sqrt (0 ^ 2 + a ^ 2) := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hs
        hcontF.continuousOn hder
      exact hcontf.intervalIntegrable 0 s
    rw [← intervalIntegral.integral_of_le hs, hFTC,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      zero_add, Real.sqrt_sq_eq_abs]

private theorem radialKernelLIntegral (s a : ℝ) (hs : 0 ≤ s) :
    (∫⁻ t in Set.Ioc 0 s,
        ENNReal.ofReal (t / Real.sqrt (t ^ 2 + a ^ 2))) =
      ENNReal.ofReal (Real.sqrt (s ^ 2 + a ^ 2) - |a|) := by
  have hnonneg : ∀ᵐ t ∂MeasureTheory.volume.restrict (Set.Ioc 0 s),
      0 ≤ t / Real.sqrt (t ^ 2 + a ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact div_nonneg ht.1.le (Real.sqrt_nonneg _)
  rw [← ofReal_integral_eq_lintegral_ofReal
    (radialKernelIntegrable s a hs) hnonneg, radialKernelIntegral s a hs]

private theorem planeKernelLIntegral (s a : ℝ) (hs : 0 ≤ s) :
    (∫⁻ xy in {xy : ℝ × ℝ | xy.1 ^ 2 + xy.2 ^ 2 ≤ s ^ 2},
        ENNReal.ofReal
          (1 / Real.sqrt (xy.1 ^ 2 + xy.2 ^ 2 + a ^ 2))) =
      ENNReal.ofReal
        (2 * Real.pi * (Real.sqrt (s ^ 2 + a ^ 2) - |a|)) := by
  let D : Set (ℝ × ℝ) :=
    {xy | xy.1 ^ 2 + xy.2 ^ 2 ≤ s ^ 2}
  have hD : MeasurableSet D := by
    exact (isClosed_le
      ((continuous_fst.pow 2).add (continuous_snd.pow 2))
      continuous_const).measurableSet
  let P : Set (ℝ × ℝ) := polarCoord.symm ⁻¹' D
  have hP : MeasurableSet P :=
    hD.preimage continuous_polarCoord_symm.measurable
  let k : ℝ × ℝ → ENNReal := fun xy =>
    ENNReal.ofReal
      (1 / Real.sqrt (xy.1 ^ 2 + xy.2 ^ 2 + a ^ 2))
  change (∫⁻ xy in D, k xy) = _
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
            D.indicator k (polarCoord.symm u)) =
        ∫⁻ u in polarCoord.target,
          P.indicator
            (fun v =>
              ENNReal.ofReal
                (v.1 / Real.sqrt (v.1 ^ 2 + a ^ 2))) u := by
    apply setLIntegral_congr_fun polarCoord.open_target.measurableSet
    intro u hu
    have hu₁ : 0 ≤ u.1 := hu.1.le
    by_cases hm : polarCoord.symm u ∈ D
    · have hmP : u ∈ P := hm
      rw [Set.indicator_of_mem hmP]
      simp only [k, Set.indicator_of_mem hm, smul_eq_mul]
      rw [hsq]
      simp only [div_eq_mul_inv]
      rw [ENNReal.ofReal_mul hu₁]
      simp
    · have hmP : u ∉ P := hm
      rw [Set.indicator_of_notMem hmP]
      change ENNReal.ofReal u.1 • D.indicator k (polarCoord.symm u) = 0
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
          (u.1 / Real.sqrt (u.1 ^ 2 + a ^ 2))) := by
    fun_prop
  rw [Measure.volume_eq_prod ℝ ℝ]
  rw [setLIntegral_prod _ hmeas.aemeasurable]
  simp_rw [setLIntegral_const]
  have hmeas₁ : Measurable
      (fun t : ℝ =>
        ENNReal.ofReal (t / Real.sqrt (t ^ 2 + a ^ 2))) := by
    fun_prop
  rw [lintegral_mul_const''
    (MeasureTheory.volume (Set.Ioo (-Real.pi) Real.pi))
    hmeas₁.aemeasurable]
  rw [radialKernelLIntegral s a hs]
  have hpi : 0 ≤ 2 * Real.pi := by positivity
  have hangle :
      MeasureTheory.volume (Set.Ioo (-Real.pi) Real.pi) =
        ENNReal.ofReal (2 * Real.pi) := by
    rw [Real.volume_Ioo]
    congr 1
    ring
  rw [hangle]
  calc
    ENNReal.ofReal (Real.sqrt (s ^ 2 + a ^ 2) - |a|) *
        ENNReal.ofReal (2 * Real.pi) =
      ENNReal.ofReal (2 * Real.pi) *
        ENNReal.ofReal (Real.sqrt (s ^ 2 + a ^ 2) - |a|) := by
          rw [mul_comm]
    _ = ENNReal.ofReal
        (2 * Real.pi * (Real.sqrt (s ^ 2 + a ^ 2) - |a|)) :=
      (ENNReal.ofReal_mul hpi).symm

private theorem rpow_sq_three_halves (x : ℝ) :
    (x ^ 2) ^ (3 / 2 : ℝ) = |x| ^ (3 : ℕ) := by
  have hx : x ^ 2 = |x| ^ 2 := by
    nlinarith [sq_abs x]
  rw [hx]
  calc
    (|x| ^ (2 : ℕ)) ^ (3 / 2 : ℝ) =
        (|x| ^ (2 : ℝ)) ^ (3 / 2 : ℝ) := by
      congr 1
      exact (Real.rpow_natCast |x| 2).symm
    _ = |x| ^ ((2 : ℝ) * (3 / 2 : ℝ)) := by
      rw [← Real.rpow_mul (abs_nonneg x)]
    _ = |x| ^ (3 : ℝ) := by
      norm_num
    _ = |x| ^ (3 : ℕ) := by
      exact Real.rpow_natCast |x| 3

theorem gap1 (R ρ₀ r : ℝ) (hR : 0 < R) (hr : 0 ≤ r) :
    potential R ρ₀ r =
      ρ₀ * ∫ p in ball R,
        1 / Real.sqrt (p.1 ^ 2 + p.2.1 ^ 2 + (p.2.2 - r) ^ 2) := by
  rfl

theorem gap3 (R r : ℝ) (hR : 0 < R) (hr : 0 ≤ r) :
    (∫ ζ in -R..R,
        Real.sqrt (R ^ 2 - 2 * r * ζ + r ^ 2)) =
      if R < r then
        (2 : ℝ) / 3 * R ^ 3 * (1 / r) + 2 * r * R
      else
        (2 : ℝ) / 3 * r ^ 2 + 2 * R ^ 2 := by
  by_cases hrz : r = 0
  · subst r
    have hsqrt : Real.sqrt (R ^ 2) = R := by
      rw [Real.sqrt_sq_eq_abs, abs_of_pos hR]
    simp [hsqrt, not_lt_of_ge hR.le]
    ring
  · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hrz)
    let F : ℝ → ℝ := fun ζ =>
      -(1 / (3 * r)) * (R ^ 2 - 2 * r * ζ + r ^ 2) ^ (3 / 2 : ℝ)
    have hpoly : Continuous
        (fun ζ : ℝ => R ^ 2 - 2 * r * ζ + r ^ 2) := by
      exact ((continuous_const.sub (continuous_const.mul continuous_id)).add
        continuous_const)
    have hint : IntervalIntegrable
        (fun ζ : ℝ => Real.sqrt (R ^ 2 - 2 * r * ζ + r ^ 2))
        volume (-R) R := by
      exact (Real.continuous_sqrt.comp hpoly).intervalIntegrable
        (μ := volume) (-R) R
    have hder : ∀ ζ ∈ Set.uIcc (-R) R,
        HasDerivAt F (Real.sqrt (R ^ 2 - 2 * r * ζ + r ^ 2)) ζ := by
      intro ζ hζ
      have hbounds : ζ ∈ Set.Icc (-R) R := by
        rw [Set.uIcc_of_le (by linarith : -R ≤ R)] at hζ
        exact hζ
      have hprod : 0 ≤ r * (R - ζ) :=
        mul_nonneg hr (sub_nonneg.mpr hbounds.2)
      have hq : 0 ≤ R ^ 2 - 2 * r * ζ + r ^ 2 := by
        nlinarith [sq_nonneg (R - r), hprod]
      have hlin : HasDerivAt
          (fun x : ℝ => R ^ 2 - 2 * r * x + r ^ 2) (-2 * r) ζ := by
        convert ((hasDerivAt_const ζ (R ^ 2 + r ^ 2)).sub
          ((hasDerivAt_id ζ).const_mul (2 * r))) using 1
        · funext x
          dsimp
          ring
        · ring
      have hp :=
        (Real.hasDerivAt_rpow_const (p := (3 / 2 : ℝ))
          (Or.inr (by norm_num))).comp ζ hlin
      dsimp [F]
      convert hp.const_mul (-(1 / (3 * r))) using 1 <;>
        norm_num [Real.sqrt_eq_rpow, hq] <;>
        field_simp [hrz] <;> ring
    have hFTC :
        (∫ ζ in -R..R, Real.sqrt (R ^ 2 - 2 * r * ζ + r ^ 2)) =
          F R - F (-R) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt hder hint
    rw [hFTC]
    dsimp [F]
    have hplus : R ^ 2 - 2 * r * (-R) + r ^ 2 = (R + r) ^ 2 := by ring
    have hminus : R ^ 2 - 2 * r * R + r ^ 2 = (R - r) ^ 2 := by ring
    rw [hplus, hminus, rpow_sq_three_halves, rpow_sq_three_halves]
    split_ifs with h
    · have hsum : 0 ≤ R + r := by linarith
      have hdiff : R - r ≤ 0 := by linarith
      rw [abs_of_nonneg hsum, abs_of_nonpos hdiff]
      field_simp [hrz]
      ring
    · have hRr : r ≤ R := le_of_not_gt h
      have hsum : 0 ≤ R + r := by linarith
      have hdiff : 0 ≤ R - r := sub_nonneg.mpr hRr
      rw [abs_of_nonneg hsum, abs_of_nonneg hdiff]
      field_simp [hrz]
      ring

theorem gap4 (R r : ℝ) (hR : 0 < R) (hr : 0 ≤ r) :
    (∫ ζ in -R..R, |ζ - r|) =
      if R < r then 2 * R * r else r ^ 2 + R ^ 2 := by
  have eval_left : ∀ a b : ℝ,
      (∫ ζ in a..b, (r - ζ)) =
        (r * b - b ^ 2 / 2) - (r * a - a ^ 2 / 2) := by
    intro a b
    have hc : Continuous (fun ζ : ℝ => r - ζ) :=
      continuous_const.sub continuous_id
    have hi : IntervalIntegrable (fun ζ : ℝ => r - ζ) volume a b := by
      exact hc.intervalIntegrable (μ := volume) a b
    have hd : ∀ ζ ∈ Set.uIcc a b,
        HasDerivAt (fun x : ℝ => r * x - x ^ 2 / 2) (r - ζ) ζ := by
      intro ζ hζ
      have hquad : HasDerivAt (fun x : ℝ => x ^ 2 / 2) ζ ζ := by
        convert (((hasDerivAt_id ζ).pow 2).div_const 2) using 1 <;>
          norm_num <;> ring
      convert ((hasDerivAt_id ζ).const_mul r).sub hquad using 1 <;> ring
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  have eval_right : ∀ a b : ℝ,
      (∫ ζ in a..b, (ζ - r)) =
        (b ^ 2 / 2 - r * b) - (a ^ 2 / 2 - r * a) := by
    intro a b
    have hc : Continuous (fun ζ : ℝ => ζ - r) :=
      continuous_id.sub continuous_const
    have hi : IntervalIntegrable (fun ζ : ℝ => ζ - r) volume a b := by
      exact hc.intervalIntegrable (μ := volume) a b
    have hd : ∀ ζ ∈ Set.uIcc a b,
        HasDerivAt (fun x : ℝ => x ^ 2 / 2 - r * x) (ζ - r) ζ := by
      intro ζ hζ
      have hquad : HasDerivAt (fun x : ℝ => x ^ 2 / 2) ζ ζ := by
        convert (((hasDerivAt_id ζ).pow 2).div_const 2) using 1 <;>
          norm_num <;> ring
      convert hquad.sub ((hasDerivAt_id ζ).const_mul r) using 1 <;> ring
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  split_ifs with h
  · have hbounds : -R ≤ R := by linarith
    calc
      (∫ ζ in -R..R, |ζ - r|) = ∫ ζ in -R..R, (r - ζ) := by
        apply intervalIntegral.integral_congr
        intro ζ hζ
        rw [Set.uIcc_of_le hbounds] at hζ
        change |ζ - r| = r - ζ
        rw [abs_of_nonpos (sub_nonpos.mpr (le_trans hζ.2 h.le))]
        ring
      _ = 2 * R * r := by
        rw [eval_left]
        ring
  · have hrR : r ≤ R := le_of_not_gt h
    have hnegRr : -R ≤ r :=
      le_trans (le_of_lt (neg_lt_zero.mpr hR)) hr
    have habs : ∀ a b : ℝ,
        IntervalIntegrable (fun ζ : ℝ => |ζ - r|) volume a b := by
      intro a b
      have hc : Continuous (fun ζ : ℝ => |ζ - r|) := by
        exact (continuous_id.sub continuous_const).abs
      exact hc.intervalIntegrable (μ := volume) a b
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (habs (-R) r) (habs r R)]
    have hleft : (∫ ζ in -R..r, |ζ - r|) =
        ∫ ζ in -R..r, (r - ζ) := by
      apply intervalIntegral.integral_congr
      intro ζ hζ
      rw [Set.uIcc_of_le hnegRr] at hζ
      change |ζ - r| = r - ζ
      rw [abs_of_nonpos (sub_nonpos.mpr hζ.2)]
      ring
    have hright : (∫ ζ in r..R, |ζ - r|) =
        ∫ ζ in r..R, (ζ - r) := by
      apply intervalIntegral.integral_congr
      intro ζ hζ
      rw [Set.uIcc_of_le hrR] at hζ
      change |ζ - r| = ζ - r
      rw [abs_of_nonneg (sub_nonneg.mpr hζ.1)]
    rw [hleft, hright, eval_left, eval_right]
    ring

private theorem axialKernelLIntegral (R r : ℝ) (hR : 0 < R) :
    (∫⁻ q in ball R,
        ENNReal.ofReal
          (1 / Real.sqrt
            (q.1 ^ 2 + q.2.1 ^ 2 + (q.2.2 - r) ^ 2))) =
      ENNReal.ofReal
        (2 * Real.pi *
          ∫ ζ in -R..R,
            Real.sqrt (R ^ 2 - 2 * r * ζ + r ^ 2) - |ζ - r|) := by
  let f : Point3 → ENNReal := fun q =>
    ENNReal.ofReal
      (1 / Real.sqrt
        (q.1 ^ 2 + q.2.1 ^ 2 + (q.2.2 - r) ^ 2))
  have hf : Measurable f := by
    dsimp [f]
    fun_prop
  have hball : MeasurableSet (ball R) := by
    exact (isClosed_le
      (((continuous_fst.pow 2).add
        ((continuous_fst.comp continuous_snd).pow 2)).add
        ((continuous_snd.comp continuous_snd).pow 2))
      continuous_const).measurableSet
  rw [← lintegral_indicator hball]
  change (∫⁻ q, (ball R).indicator f q) = _
  let A : ((ℝ × ℝ) × ℝ) ≃ᵐ Point3 :=
    MeasurableEquiv.prodAssoc
  have hA : MeasurePreserving A :=
    MeasureTheory.volume_preserving_prodAssoc
  have hcomp :
      (∫⁻ q, (ball R).indicator f q) =
        ∫⁻ u : (ℝ × ℝ) × ℝ, (ball R).indicator f (A u) := by
    exact (hA.lintegral_comp_emb A.measurableEmbedding _).symm
  rw [hcomp]
  have hmeas :
      Measurable
        (fun u : (ℝ × ℝ) × ℝ =>
          (ball R).indicator f (A u)) :=
    (hf.indicator hball).comp A.measurable
  rw [Measure.volume_eq_prod (ℝ × ℝ) ℝ]
  rw [lintegral_prod_symm' _ hmeas]
  have hslice (z : ℝ) :
      (∫⁻ xy : ℝ × ℝ,
          (ball R).indicator f (A (xy, z))) =
        if z ∈ Set.Icc (-R) R then
          ENNReal.ofReal
            (2 * Real.pi *
              (Real.sqrt (R ^ 2 - 2 * r * z + r ^ 2) - |z - r|))
        else 0 := by
    by_cases hz : z ∈ Set.Icc (-R) R
    · rw [if_pos hz]
      have hzsq : 0 ≤ R ^ 2 - z ^ 2 := by
        nlinarith [sq_nonneg (R - z), sq_nonneg (R + z), hz.1, hz.2]
      let s : ℝ := Real.sqrt (R ^ 2 - z ^ 2)
      have hs : 0 ≤ s := Real.sqrt_nonneg _
      have hs2 : s ^ 2 = R ^ 2 - z ^ 2 := by
        exact Real.sq_sqrt hzsq
      let D : Set (ℝ × ℝ) :=
        {xy | xy.1 ^ 2 + xy.2 ^ 2 ≤ s ^ 2}
      have hD : MeasurableSet D := by
        exact (isClosed_le
          ((continuous_fst.pow 2).add (continuous_snd.pow 2))
          continuous_const).measurableSet
      calc
        (∫⁻ xy : ℝ × ℝ,
            (ball R).indicator f (A (xy, z))) =
            ∫⁻ xy in D,
              ENNReal.ofReal
                (1 / Real.sqrt
                  (xy.1 ^ 2 + xy.2 ^ 2 + (z - r) ^ 2)) := by
              rw [← lintegral_indicator hD]
              apply lintegral_congr
              intro xy
              have hmem :
                  A (xy, z) ∈ ball R ↔ xy ∈ D := by
                change
                  xy.1 ^ 2 + xy.2 ^ 2 + z ^ 2 ≤ R ^ 2 ↔
                    xy.1 ^ 2 + xy.2 ^ 2 ≤ s ^ 2
                rw [hs2]
                constructor <;> intro h <;> linarith
              by_cases hxy : xy ∈ D
              · rw [Set.indicator_of_mem hxy,
                  Set.indicator_of_mem (hmem.mpr hxy)]
                have hAapply : A (xy, z) = (xy.1, xy.2, z) := rfl
                rw [hAapply]
              · rw [Set.indicator_of_notMem hxy,
                  Set.indicator_of_notMem (mt hmem.mp hxy)]
        _ = ENNReal.ofReal
              (2 * Real.pi *
                (Real.sqrt (s ^ 2 + (z - r) ^ 2) - |z - r|)) :=
          planeKernelLIntegral s (z - r) hs
        _ = ENNReal.ofReal
              (2 * Real.pi *
                (Real.sqrt (R ^ 2 - 2 * r * z + r ^ 2) - |z - r|)) := by
          have harg :
              s ^ 2 + (z - r) ^ 2 =
                R ^ 2 - 2 * r * z + r ^ 2 := by
            rw [hs2]
            ring
          rw [harg]
    · rw [if_neg hz]
      have hzout : z < -R ∨ R < z := by
        simpa only [Set.mem_Icc, not_and_or, not_le] using hz
      have hzsq : R ^ 2 < z ^ 2 := by
        rcases hzout with hzleft | hzright
        · nlinarith [sq_nonneg (z - R)]
        · nlinarith [sq_nonneg (z + R)]
      have hzero :
          (fun xy : ℝ × ℝ => (ball R).indicator f (A (xy, z))) =
            fun _ => 0 := by
        funext xy
        rw [Set.indicator_of_notMem]
        change ¬(xy.1 ^ 2 + xy.2 ^ 2 + z ^ 2 ≤ R ^ 2)
        nlinarith [sq_nonneg xy.1, sq_nonneg xy.2]
      rw [hzero]
      simp
  simp_rw [hslice]
  have hIcc : MeasurableSet (Set.Icc (-R) R) := measurableSet_Icc
  have houter :
      (∫⁻ z : ℝ,
          if z ∈ Set.Icc (-R) R then
            ENNReal.ofReal
              (2 * Real.pi *
                (Real.sqrt (R ^ 2 - 2 * r * z + r ^ 2) - |z - r|))
          else 0) =
        ∫⁻ z in Set.Icc (-R) R,
          ENNReal.ofReal
            (2 * Real.pi *
              (Real.sqrt (R ^ 2 - 2 * r * z + r ^ 2) - |z - r|)) := by
    rw [← lintegral_indicator hIcc]
    apply lintegral_congr
    intro z
    by_cases hz : z ∈ Set.Icc (-R) R
    · rw [Set.indicator_of_mem hz, if_pos hz]
    · rw [Set.indicator_of_notMem hz, if_neg hz]
  rw [houter]
  let g : ℝ → ℝ := fun z =>
    2 * Real.pi *
      (Real.sqrt (R ^ 2 - 2 * r * z + r ^ 2) - |z - r|)
  have hgcont : Continuous g := by
    dsimp [g]
    fun_prop
  have hgint : IntegrableOn g (Set.Icc (-R) R) :=
    hgcont.integrableOn_Icc
  have hgnonneg : ∀ᵐ z ∂volume.restrict (Set.Icc (-R) R), 0 ≤ g z := by
    filter_upwards [ae_restrict_mem hIcc] with z hz
    have hbase : 0 ≤ R ^ 2 - z ^ 2 := by
      nlinarith [sq_nonneg (R - z), sq_nonneg (R + z), hz.1, hz.2]
    have hrad :
        (z - r) ^ 2 ≤ R ^ 2 - 2 * r * z + r ^ 2 := by
      nlinarith
    have hsqrt :
        |z - r| ≤ Real.sqrt (R ^ 2 - 2 * r * z + r ^ 2) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt hrad
    dsimp [g]
    exact mul_nonneg (by positivity) (sub_nonneg.mpr hsqrt)
  rw [← ofReal_integral_eq_lintegral_ofReal hgint hgnonneg]
  have hbounds : -R ≤ R := by linarith
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hbounds]
  dsimp [g]
  rw [intervalIntegral.integral_const_mul]

private theorem axialKernelIntegral (R r : ℝ) (hR : 0 < R) :
    (∫ q in ball R,
        1 / Real.sqrt
          (q.1 ^ 2 + q.2.1 ^ 2 + (q.2.2 - r) ^ 2)) =
      2 * Real.pi *
        ∫ ζ in -R..R,
          Real.sqrt (R ^ 2 - 2 * r * ζ + r ^ 2) - |ζ - r| := by
  let k : Point3 → ℝ := fun q =>
    1 / Real.sqrt
      (q.1 ^ 2 + q.2.1 ^ 2 + (q.2.2 - r) ^ 2)
  have hnonneg :
      ∀ᵐ q ∂volume.restrict (ball R), 0 ≤ k q := by
    exact Filter.Eventually.of_forall fun q =>
      div_nonneg zero_le_one (Real.sqrt_nonneg _)
  have hmeas :
      AEStronglyMeasurable k (volume.restrict (ball R)) := by
    have hm : Measurable k := by
      dsimp [k]
      fun_prop
    exact hm.aestronglyMeasurable.restrict
  change (∫ q in ball R, k q) = _
  rw [integral_eq_lintegral_of_nonneg_ae hnonneg hmeas,
    axialKernelLIntegral R r hR]
  have hbounds : -R ≤ R := by linarith
  have hpoint : ∀ z ∈ Set.Icc (-R) R,
      0 ≤ Real.sqrt (R ^ 2 - 2 * r * z + r ^ 2) - |z - r| := by
    intro z hz
    have hbase : 0 ≤ R ^ 2 - z ^ 2 := by
      nlinarith [sq_nonneg (R - z), sq_nonneg (R + z), hz.1, hz.2]
    have hrad :
        (z - r) ^ 2 ≤ R ^ 2 - 2 * r * z + r ^ 2 := by
      nlinarith
    have hsqrt :
        |z - r| ≤ Real.sqrt (R ^ 2 - 2 * r * z + r ^ 2) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt hrad
    exact sub_nonneg.mpr hsqrt
  have hint_nonneg :
      0 ≤ ∫ ζ in -R..R,
        Real.sqrt (R ^ 2 - 2 * r * ζ + r ^ 2) - |ζ - r| :=
    intervalIntegral.integral_nonneg hbounds hpoint
  rw [ENNReal.toReal_ofReal]
  exact mul_nonneg (by positivity) hint_nonneg

theorem gap2 (R ρ₀ r : ℝ) (hR : 0 < R) (hr : 0 ≤ r) :
    potential R ρ₀ r =
      2 * Real.pi * ρ₀ *
        ∫ ζ in -R..R,
          Real.sqrt (R ^ 2 - 2 * r * ζ + r ^ 2) - |ζ - r| := by
  unfold potential
  rw [axialKernelIntegral R r hR]
  ring

theorem gap5 (R ρ₀ r : ℝ) (hR : 0 < R) (hr : 0 ≤ r) :
    potential R ρ₀ r =
      if R < r then
        4 / (3 * r) * Real.pi * R ^ 3 * ρ₀
      else
        2 * Real.pi * ρ₀ * (R ^ 2 - (1 : ℝ) / 3 * r ^ 2) := by
  rw [gap2 R ρ₀ r hR hr]
  have hpoly : Continuous
      (fun ζ : ℝ => R ^ 2 - 2 * r * ζ + r ^ 2) := by
    exact ((continuous_const.sub (continuous_const.mul continuous_id)).add
      continuous_const)
  have hsqrt : IntervalIntegrable
      (fun ζ : ℝ => Real.sqrt (R ^ 2 - 2 * r * ζ + r ^ 2))
      volume (-R) R := by
    exact (Real.continuous_sqrt.comp hpoly).intervalIntegrable
      (μ := volume) (-R) R
  have habs : IntervalIntegrable (fun ζ : ℝ => |ζ - r|)
      volume (-R) R := by
    have hc : Continuous (fun ζ : ℝ => |ζ - r|) := by
      exact (continuous_id.sub continuous_const).abs
    exact hc.intervalIntegrable (μ := volume) (-R) R
  rw [intervalIntegral.integral_sub hsqrt habs,
    gap3 R r hR hr, gap4 R r hR hr]
  split_ifs with h
  · have hrpos : 0 < r := lt_trans hR h
    have hrne : r ≠ 0 := ne_of_gt hrpos
    field_simp [hrne]
    ring
  · ring

theorem gap6 (R₁ R₂ ρ₀ r : ℝ)
    (hR₁ : 0 < R₁) (hR₁₂ : R₁ ≤ R₂)
    (hr₀ : 0 ≤ r) (hr₁ : r ≤ R₁) :
    potential R₂ ρ₀ r - potential R₁ ρ₀ r =
      2 * Real.pi * (R₂ ^ 2 - R₁ ^ 2) * ρ₀ := by
  have hR₂ : 0 < R₂ := lt_of_lt_of_le hR₁ hR₁₂
  have hn₁ : ¬R₁ < r := not_lt_of_ge hr₁
  have hn₂ : ¬R₂ < r := not_lt_of_ge (le_trans hr₁ hR₁₂)
  rw [gap5 R₂ ρ₀ r hR₂ hr₀, gap5 R₁ ρ₀ r hR₁ hr₀]
  simp only [if_neg hn₁, if_neg hn₂]
  ring

end

end ProofGap.Exercise4155
