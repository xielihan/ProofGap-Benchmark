import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Measurability
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4156

noncomputable section

open MeasureTheory Set intervalIntegral

abbrev Point3 := ℝ × ℝ × ℝ

private abbrev squaredRadius (p : Point3) : ℝ :=
  p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2

private def radius (p : Point3) : ℝ := Real.sqrt (squaredRadius p)

def shell (R₁ R₂ : ℝ) : Set Point3 :=
  {p |
    R₁ ^ 2 ≤ p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 ∧
      p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 ≤ R₂ ^ 2}

private def distance (p q : Point3) : ℝ :=
  Real.sqrt
    ((p.1 - q.1) ^ 2 + (p.2.1 - q.2.1) ^ 2 + (p.2.2 - q.2.2) ^ 2)

private def potential (f : ℝ → ℝ) (R₁ R₂ : ℝ) (p : Point3) : ℝ :=
  ∫ q in shell R₁ R₂, f (radius q) / distance q p ∂MeasureTheory.volume

def shellPotential (f : ℝ → ℝ) (R₁ R₂ r : ℝ) : ℝ :=
  ∫ p in shell R₁ R₂,
    f (Real.sqrt (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2)) /
      Real.sqrt (p.1 ^ 2 + p.2.1 ^ 2 + (p.2.2 - r) ^ 2)

private def radialKernel (ρ r : ℝ) : ℝ :=
  if r = 0 then ρ else min (ρ ^ 2 / r) ρ

private def radialFormula (f : ℝ → ℝ) (R₁ R₂ r : ℝ) : ℝ :=
  4 * Real.pi * ∫ ρ in R₁..R₂, f ρ * radialKernel ρ r

/-! Source: `results/stage1_gpt55/09_重积分与含参积分/exercise_4156_autoformalization_result/exercise_4156.md`. -/

private def ball (R : ℝ) : Set Point3 :=
  {q | squaredRadius q ≤ R ^ 2}

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

private theorem rpowSqThreeHalves (x : ℝ) :
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
    _ = |x| ^ (3 : ℝ) := by norm_num
    _ = |x| ^ (3 : ℕ) := Real.rpow_natCast |x| 3

private theorem axialSqrtIntegral (R r : ℝ) (hR : 0 < R) (hr : 0 ≤ r) :
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
        volume (-R) R :=
      (Real.continuous_sqrt.comp hpoly).intervalIntegrable (-R) R
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
    rw [hplus, hminus, rpowSqThreeHalves, rpowSqThreeHalves]
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

private theorem axialAbsIntegral (R r : ℝ) (hR : 0 < R) (hr : 0 ≤ r) :
    (∫ ζ in -R..R, |ζ - r|) =
      if R < r then 2 * R * r else r ^ 2 + R ^ 2 := by
  have eval_left : ∀ a b : ℝ,
      (∫ ζ in a..b, (r - ζ)) =
        (r * b - b ^ 2 / 2) - (r * a - a ^ 2 / 2) := by
    intro a b
    have hc : Continuous (fun ζ : ℝ => r - ζ) :=
      continuous_const.sub continuous_id
    have hi : IntervalIntegrable (fun ζ : ℝ => r - ζ) volume a b :=
      hc.intervalIntegrable a b
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
    have hi : IntervalIntegrable (fun ζ : ℝ => ζ - r) volume a b :=
      hc.intervalIntegrable a b
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
      exact (continuous_id.sub continuous_const).abs.intervalIntegrable a b
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

private theorem axialKernelLIntegral (R r : ℝ) (hR : 0 < R) (hr : 0 ≤ r) :
    (∫⁻ q in ball R,
        ENNReal.ofReal (1 / distance q (0, 0, r))) =
      ENNReal.ofReal
        (if R < r then
          4 * Real.pi * R ^ 3 / (3 * r)
        else
          2 * Real.pi * (R ^ 2 - r ^ 2 / 3)) := by
  let f : Point3 → ENNReal := fun q =>
    ENNReal.ofReal (1 / distance q (0, 0, r))
  have hf : Measurable f := by
    dsimp [f, distance]
    fun_prop
  have hball : MeasurableSet (ball R) := by
    exact (isClosed_le
      (((continuous_fst.pow 2).add
        ((continuous_fst.comp continuous_snd).pow 2)).add
        ((continuous_snd.comp continuous_snd).pow 2))
      continuous_const).measurableSet
  rw [← lintegral_indicator hball]
  change (∫⁻ q, (ball R).indicator f q) = _
  let A :
      ((ℝ × ℝ) × ℝ) ≃ᵐ Point3 :=
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
                simp only [f, distance]
                congr 2
                ring
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
  have hsqrtint :
      IntervalIntegrable
        (fun z : ℝ => Real.sqrt (R ^ 2 - 2 * r * z + r ^ 2))
        volume (-R) R := by
    exact (Real.continuous_sqrt.comp
      (((continuous_const.sub (continuous_const.mul continuous_id)).add
        continuous_const))).intervalIntegrable (-R) R
  have habsint :
      IntervalIntegrable (fun z : ℝ => |z - r|) volume (-R) R := by
    exact (continuous_id.sub continuous_const).abs.intervalIntegrable (-R) R
  dsimp [g]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub hsqrtint habsint,
    axialSqrtIntegral R r hR hr, axialAbsIntegral R r hR hr]
  split_ifs with h
  · have hrpos : 0 < r := lt_trans hR h
    congr 1
    field_simp [ne_of_gt hrpos]
    ring
  · congr 1
    ring

private def coordinateEquiv :
    Point3 ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 3) :=
  { toFun := fun p => !₂[p.1, p.2.1, p.2.2]
    invFun := fun x => (x 0, x 1, x 2)
    left_inv := by
      intro p
      ext <;> simp
    right_inv := by
      intro x
      ext i
      fin_cases i <;> simp
    map_add' := by
      intro p q
      ext i
      fin_cases i <;> simp
    map_smul' := by
      intro c p
      ext i
      fin_cases i <;> simp }

private theorem coordinateNormSq (p : Point3) :
    ‖coordinateEquiv p‖ ^ 2 = squaredRadius p := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [coordinateEquiv, squaredRadius, Fin.sum_univ_succ]
  ring

private theorem coordinateDistance (p q : Point3) :
    distance p q = ‖coordinateEquiv p - coordinateEquiv q‖ := by
  rw [EuclideanSpace.norm_eq]
  simp [coordinateEquiv, distance, Fin.sum_univ_succ, Real.norm_eq_abs,
    sq_abs]
  ring

private theorem kernelLIntegral (R : ℝ) (p : Point3) (hR : 0 < R) :
    (∫⁻ q in ball R, ENNReal.ofReal (1 / distance q p)) =
      ENNReal.ofReal
        (if R < radius p then
          4 * Real.pi * R ^ 3 / (3 * radius p)
        else
          2 * Real.pi * (R ^ 2 - radius p ^ 2 / 3)) := by
  classical
  have hsq : 0 ≤ squaredRadius p := by
    dsimp [squaredRadius]
    positivity
  have hr : 0 ≤ radius p := Real.sqrt_nonneg _
  have hr2 : radius p ^ 2 = squaredRadius p :=
    Real.sq_sqrt hsq
  let p₀ : Point3 := (0, 0, radius p)
  have hnorm :
      ‖coordinateEquiv p‖ = ‖coordinateEquiv p₀‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [coordinateNormSq, coordinateNormSq]
    dsimp [p₀, squaredRadius]
    simpa using hr2.symm
  let K : Submodule ℝ (EuclideanSpace ℝ (Fin 3)) :=
    (ℝ ∙ (coordinateEquiv p - coordinateEquiv p₀))ᗮ
  let O : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin 3) :=
    K.reflection
  have hOp : O (coordinateEquiv p) = coordinateEquiv p₀ := by
    dsimp [O, K]
    exact Submodule.reflection_sub hnorm
  let T : Point3 ≃ₗ[ℝ] Point3 :=
    coordinateEquiv.trans
      (O.toLinearEquiv.trans coordinateEquiv.symm)
  have hTp : T p = p₀ := by
    change coordinateEquiv.symm (O (coordinateEquiv p)) = p₀
    rw [hOp]
    exact coordinateEquiv.symm_apply_apply p₀
  have hTcoord (q : Point3) :
      coordinateEquiv (T q) = O (coordinateEquiv q) := by
    simp [T]
  have hTnorm (q : Point3) :
      ‖coordinateEquiv (T q)‖ = ‖coordinateEquiv q‖ := by
    rw [hTcoord]
    exact O.norm_map _
  have hTsq (q : Point3) :
      squaredRadius (T q) = squaredRadius q := by
    calc
      squaredRadius (T q) = ‖coordinateEquiv (T q)‖ ^ 2 :=
        (coordinateNormSq _).symm
      _ = ‖coordinateEquiv q‖ ^ 2 := by rw [hTnorm]
      _ = squaredRadius q := coordinateNormSq q
  have hTdist (q u : Point3) :
      distance (T q) (T u) = distance q u := by
    rw [coordinateDistance, coordinateDistance, hTcoord, hTcoord,
      ← map_sub, O.norm_map]
  have hTball : T ⁻¹' ball R = ball R := by
    ext q
    simp only [Set.mem_preimage, ball, Set.mem_setOf_eq, hTsq]
  have hTdet :
      LinearMap.det (T : Point3 →ₗ[ℝ] Point3) =
        LinearMap.det O.toLinearMap := by
    change
      LinearMap.det
          ((coordinateEquiv.symm :
              EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] Point3) ∘ₗ
            O.toLinearMap ∘ₗ
              (coordinateEquiv :
                Point3 →ₗ[ℝ] EuclideanSpace ℝ (Fin 3))) =
        LinearMap.det O.toLinearMap
    simpa only [LinearEquiv.symm_symm] using
      (LinearMap.det_conj O.toLinearMap coordinateEquiv.symm)
  have hTdetabs :
      |LinearMap.det (T : Point3 →ₗ[ℝ] Point3)| = 1 := by
    rw [hTdet]
    dsimp [O]
    rw [K.det_reflection]
    simp
  have hTdetne :
      LinearMap.det (T : Point3 →ₗ[ℝ] Point3) ≠ 0 := by
    intro hzero
    have := congrArg abs hzero
    rw [hTdetabs, abs_zero] at this
    norm_num at this
  letI : Measure.IsAddHaarMeasure
      (MeasureTheory.volume : Measure (ℝ × ℝ)) := by
    change Measure.IsAddHaarMeasure
      ((MeasureTheory.volume : Measure ℝ).prod
        (MeasureTheory.volume : Measure ℝ))
    exact Measure.prod.instIsAddHaarMeasure _ _
  letI : Measure.IsAddHaarMeasure
      (MeasureTheory.volume : Measure Point3) := by
    change Measure.IsAddHaarMeasure
      ((MeasureTheory.volume : Measure ℝ).prod
        (MeasureTheory.volume : Measure (ℝ × ℝ)))
    exact Measure.prod.instIsAddHaarMeasure _ _
  have hmap :
      Measure.map (T : Point3 →ₗ[ℝ] Point3) volume = volume := by
    rw [MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar
      volume hTdetne]
    have habsinv :
        |(LinearMap.det (T : Point3 →ₗ[ℝ] Point3))⁻¹| = 1 := by
      rw [abs_inv, hTdetabs, inv_one]
    rw [habsinv]
    simp
  have hTmeas : Measurable (T : Point3 → Point3) :=
    (LinearMap.continuous_of_finiteDimensional
      (T : Point3 →ₗ[ℝ] Point3)).measurable
  have hmp : MeasurePreserving (T : Point3 → Point3) volume volume :=
    ⟨hTmeas, hmap⟩
  have hTemb : MeasurableEmbedding (T : Point3 → Point3) := by
    exact
      T.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv.measurableEmbedding
  let kp : Point3 → ENNReal := fun q =>
    ENNReal.ofReal (1 / distance q p)
  let k₀ : Point3 → ENNReal := fun q =>
    ENNReal.ofReal (1 / distance q p₀)
  have hkcomp (q : Point3) : k₀ (T q) = kp q := by
    dsimp [k₀, kp]
    rw [← hTp, hTdist]
  calc
    (∫⁻ q in ball R, ENNReal.ofReal (1 / distance q p)) =
        ∫⁻ q in T ⁻¹' ball R, k₀ (T q) := by
      change (∫⁻ q in ball R, kp q) = _
      rw [hTball]
      apply setLIntegral_congr_fun
        (by
          exact (isClosed_le
            (((continuous_fst.pow 2).add
              ((continuous_fst.comp continuous_snd).pow 2)).add
              ((continuous_snd.comp continuous_snd).pow 2))
            continuous_const).measurableSet)
      intro q hq
      exact (hkcomp q).symm
    _ = ∫⁻ q in ball R, k₀ q :=
      hmp.setLIntegral_comp_preimage_emb hTemb k₀ (ball R)
    _ = ENNReal.ofReal
          (if R < radius p then
            4 * Real.pi * R ^ 3 / (3 * radius p)
          else
            2 * Real.pi * (R ^ 2 - radius p ^ 2 / 3)) := by
      simpa [k₀, p₀] using
        axialKernelLIntegral R (radius p) hR hr

private theorem radialKernel_continuous (r : ℝ) :
    Continuous (fun ρ : ℝ => radialKernel ρ r) := by
  by_cases hr : r = 0
  · simpa [radialKernel, hr] using (continuous_id : Continuous fun ρ : ℝ => ρ)
  · simp only [radialKernel, hr, if_false]
    exact (continuous_id.pow 2 |>.div_const r).min continuous_id

private theorem radialKernel_nonneg
    (ρ r : ℝ) (hρ : 0 ≤ ρ) (hr : 0 ≤ r) :
    0 ≤ radialKernel ρ r := by
  by_cases hr0 : r = 0
  · simp [radialKernel, hr0, hρ]
  · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
    simp only [radialKernel, hr0, if_false]
    exact le_min
      (div_nonneg (sq_nonneg ρ) hrpos.le) hρ

private theorem integral_id_interval (a b : ℝ) :
    (∫ x in a..b, x) = (b ^ 2 - a ^ 2) / 2 := by
  have hderiv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun y : ℝ => y ^ 2 / 2) x x := by
    intro x _
    convert ((hasDerivAt_id x).pow 2).div_const 2 using 1 <;>
      simp only [id_eq] <;> ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (continuous_id.intervalIntegrable a b)]
  ring

private theorem integral_sq_div_interval
    (a b r : ℝ) (hr : r ≠ 0) :
    (∫ x in a..b, x ^ 2 / r) =
      (b ^ 3 - a ^ 3) / (3 * r) := by
  have hcont : Continuous (fun x : ℝ => x ^ 2 / r) :=
    (continuous_id.pow 2).div_const r
  have hderiv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun y : ℝ => y ^ 3 / (3 * r)) (x ^ 2 / r) x := by
    intro x _
    convert ((hasDerivAt_id x).pow 3).div_const (3 * r) using 1 <;>
      simp only [id_eq] <;> field_simp [hr] <;> ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (hcont.intervalIntegrable a b)]
  field_simp [hr]

private theorem radialKernel_intervalIntegral
    (x r : ℝ) (hx : 0 ≤ x) (hr : 0 ≤ r) :
    (∫ ρ in (0 : ℝ)..x, radialKernel ρ r) =
      if x < r then x ^ 3 / (3 * r)
      else x ^ 2 / 2 - r ^ 2 / 6 := by
  by_cases hr0 : r = 0
  · subst r
    rw [if_neg (not_lt_of_ge hx)]
    simp only [radialKernel, if_pos rfl, if_true, zero_pow, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, div_zero, sub_zero]
    rw [integral_id_interval]
    ring
  · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
    by_cases hxr : x < r
    · rw [if_pos hxr]
      have hpoint : ∀ ρ ∈ Set.uIcc (0 : ℝ) x,
          radialKernel ρ r = ρ ^ 2 / r := by
        intro ρ hρ
        rw [Set.uIcc_of_le hx] at hρ
        simp only [radialKernel, hr0, if_false]
        rw [min_eq_left]
        rw [div_le_iff₀ hrpos]
        nlinarith [mul_nonneg hρ.1 (sub_nonneg.mpr
          (le_trans hρ.2 hxr.le))]
      rw [intervalIntegral.integral_congr hpoint,
        integral_sq_div_interval 0 x r hr0]
      ring
    · rw [if_neg hxr]
      have hrx : r ≤ x := le_of_not_gt hxr
      have hcont := radialKernel_continuous r
      rw [← intervalIntegral.integral_add_adjacent_intervals
        (hcont.intervalIntegrable 0 r)
        (hcont.intervalIntegrable r x)]
      have hleft :
          (∫ ρ in (0 : ℝ)..r, radialKernel ρ r) =
            ∫ ρ in (0 : ℝ)..r, ρ ^ 2 / r := by
        apply intervalIntegral.integral_congr
        intro ρ hρ
        rw [Set.uIcc_of_le hrpos.le] at hρ
        simp only [radialKernel, hr0, if_false]
        rw [min_eq_left]
        rw [div_le_iff₀ hrpos]
        nlinarith [mul_nonneg hρ.1 (sub_nonneg.mpr hρ.2)]
      have hright :
          (∫ ρ in r..x, radialKernel ρ r) =
            ∫ ρ in r..x, ρ := by
        apply intervalIntegral.integral_congr
        intro ρ hρ
        rw [Set.uIcc_of_le hrx] at hρ
        simp only [radialKernel, hr0, if_false]
        rw [min_eq_right]
        rw [le_div_iff₀ hrpos]
        have hρ0 : 0 ≤ ρ := hrpos.le.trans hρ.1
        nlinarith [mul_nonneg hρ0 (sub_nonneg.mpr hρ.1)]
      rw [hleft, hright,
        integral_sq_div_interval 0 r r hr0,
        integral_id_interval]
      field_simp [hr0]
      ring

private def kernelProfile (x r : ℝ) : ℝ :=
  if x < r then
    4 * Real.pi * x ^ 3 / (3 * r)
  else
    2 * Real.pi * (x ^ 2 - r ^ 2 / 3)

private theorem radialKernel_weighted_integral
    (x r : ℝ) (hx : 0 ≤ x) (hr : 0 ≤ r) :
    (∫ ρ in (0 : ℝ)..x, 4 * Real.pi * radialKernel ρ r) =
      kernelProfile x r := by
  rw [intervalIntegral.integral_const_mul,
    radialKernel_intervalIntegral x r hx hr]
  unfold kernelProfile
  split_ifs <;> ring

private theorem radius_measurable : Measurable radius := by
  unfold radius squaredRadius
  fun_prop

private def kernelWeight (p : Point3) (q : Point3) : ENNReal :=
  ENNReal.ofReal (1 / distance q p)

private theorem kernelWeight_measurable (p : Point3) :
    Measurable (kernelWeight p) := by
  unfold kernelWeight distance
  fun_prop

private def kernelBallMeasure (R : ℝ) (p : Point3) : Measure Point3 :=
  (MeasureTheory.volume.withDensity (kernelWeight p)).restrict (ball R)

private def pushedKernelMeasure (R : ℝ) (p : Point3) : Measure ℝ :=
  Measure.map radius (kernelBallMeasure R p)

private def radialDensity (r ρ : ℝ) : ENNReal :=
  ENNReal.ofReal (4 * Real.pi * radialKernel ρ r)

private theorem radialDensity_measurable (r : ℝ) :
    Measurable (radialDensity r) := by
  unfold radialDensity
  exact ((radialKernel_continuous r).const_mul
    (4 * Real.pi)).measurable.ennreal_ofReal

private def modelRadialMeasure (R r : ℝ) : Measure ℝ :=
  (MeasureTheory.volume.withDensity (radialDensity r)).restrict
    (Set.Ioc 0 R)

private theorem radialDensityLIntegral
    (x r : ℝ) (hx : 0 ≤ x) (hr : 0 ≤ r) :
    (∫⁻ ρ in Set.Ioc 0 x, radialDensity r ρ) =
      ENNReal.ofReal (kernelProfile x r) := by
  have hcont : Continuous
      (fun ρ : ℝ => 4 * Real.pi * radialKernel ρ r) :=
    (radialKernel_continuous r).const_mul (4 * Real.pi)
  have hint : IntegrableOn
      (fun ρ : ℝ => 4 * Real.pi * radialKernel ρ r)
      (Set.Ioc 0 x) :=
    hcont.integrableOn_Ioc
  have hnonneg :
      ∀ᵐ ρ ∂MeasureTheory.volume.restrict (Set.Ioc 0 x),
        0 ≤ 4 * Real.pi * radialKernel ρ r := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with ρ hρ
    exact mul_nonneg (by positivity)
      (radialKernel_nonneg ρ r hρ.1.le hr)
  unfold radialDensity
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnonneg,
    ← intervalIntegral.integral_of_le hx,
    radialKernel_weighted_integral x r hx hr]

private theorem ball_measurable (R : ℝ) :
    MeasurableSet (ball R) := by
  exact (isClosed_le
    (((continuous_fst.pow 2).add
      ((continuous_fst.comp continuous_snd).pow 2)).add
      ((continuous_snd.comp continuous_snd).pow 2))
    continuous_const).measurableSet

private theorem mem_ball_iff_radius_le
    (R : ℝ) (hR : 0 ≤ R) (q : Point3) :
    q ∈ ball R ↔ radius q ≤ R := by
  unfold ball radius
  simp only [Set.mem_setOf_eq, Real.sqrt_le_iff]
  exact ⟨fun h => ⟨hR, h⟩, fun h => h.2⟩

private theorem radius_preimage_Iic_zero :
    radius ⁻¹' Set.Iic (0 : ℝ) = ({(0, 0, 0)} : Set Point3) := by
  ext q
  constructor
  · intro hq
    have hr0 : radius q = 0 :=
      le_antisymm hq (Real.sqrt_nonneg _)
    have hsq : squaredRadius q = 0 := by
      calc
        squaredRadius q = radius q ^ 2 := by
          rw [radius, Real.sq_sqrt]
          unfold squaredRadius
          positivity
        _ = 0 := by rw [hr0]; norm_num
    have hx : q.1 = 0 := by
      unfold squaredRadius at hsq
      nlinarith [sq_nonneg q.2.1, sq_nonneg q.2.2]
    have hy : q.2.1 = 0 := by
      unfold squaredRadius at hsq
      nlinarith [sq_nonneg q.1, sq_nonneg q.2.2]
    have hz : q.2.2 = 0 := by
      unfold squaredRadius at hsq
      nlinarith [sq_nonneg q.1, sq_nonneg q.2.1]
    rcases q with ⟨x, y, z⟩
    simpa only [Set.mem_singleton_iff, Prod.mk.injEq] using
      And.intro hx (And.intro hy hz)
  · intro hq
    rw [Set.mem_singleton_iff] at hq
    subst q
    simp [radius, squaredRadius]

private theorem pushedKernelMeasure_Iic
    (R : ℝ) (p : Point3) (hR : 0 < R) (x : ℝ) :
    pushedKernelMeasure R p (Set.Iic x) =
      if x ≤ 0 then 0
      else ENNReal.ofReal
        (kernelProfile (min x R) (radius p)) := by
  rw [pushedKernelMeasure,
    Measure.map_apply radius_measurable measurableSet_Iic]
  by_cases hx : x ≤ 0
  · rw [if_pos hx]
    have hsubset :
        radius ⁻¹' Set.Iic x ⊆ radius ⁻¹' Set.Iic (0 : ℝ) := by
      intro q hq
      exact le_trans hq hx
    have hnull :
        (MeasureTheory.volume.withDensity (kernelWeight p))
          (radius ⁻¹' Set.Iic (0 : ℝ)) = 0 := by
      rw [radius_preimage_Iic_zero,
        withDensity_apply _ (measurableSet_singleton (0, 0, 0))]
      apply setLIntegral_measure_zero
      rw [Measure.volume_eq_prod]
      simp
    unfold kernelBallMeasure
    rw [Measure.restrict_apply
      ((measurableSet_Iic.preimage radius_measurable))]
    exact measure_mono_null
      (fun q hq => hsubset hq.1) hnull
  · rw [if_neg hx]
    have hxpos : 0 < x := lt_of_not_ge hx
    let y : ℝ := min x R
    have hypos : 0 < y := lt_min hxpos hR
    have hy0 : 0 ≤ y := hypos.le
    have hset :
        radius ⁻¹' Set.Iic x ∩ ball R = ball y := by
      ext q
      rw [Set.mem_inter_iff,
        mem_ball_iff_radius_le R hR.le,
        mem_ball_iff_radius_le y hy0]
      change (radius q ≤ x ∧ radius q ≤ R) ↔ radius q ≤ min x R
      exact (le_min_iff).symm
    unfold kernelBallMeasure
    rw [Measure.restrict_apply
      ((measurableSet_Iic.preimage radius_measurable)),
      withDensity_apply _
        ((measurableSet_Iic.preimage radius_measurable).inter
          (ball_measurable R)),
      hset]
    change
      (∫⁻ q in ball y, ENNReal.ofReal (1 / distance q p)) =
        ENNReal.ofReal (kernelProfile y (radius p))
    rw [kernelLIntegral y p hypos]
    rfl

private theorem modelRadialMeasure_Iic
    (R r : ℝ) (hR : 0 < R) (hr : 0 ≤ r) (x : ℝ) :
    modelRadialMeasure R r (Set.Iic x) =
      if x ≤ 0 then 0
      else ENNReal.ofReal (kernelProfile (min x R) r) := by
  unfold modelRadialMeasure
  rw [Measure.restrict_apply measurableSet_Iic,
    withDensity_apply _ (measurableSet_Iic.inter measurableSet_Ioc)]
  by_cases hx : x ≤ 0
  · rw [if_pos hx]
    have hempty :
        Set.Iic x ∩ Set.Ioc (0 : ℝ) R = ∅ := by
      ext ρ
      simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ioc,
        Set.mem_empty_iff_false, iff_false]
      exact fun h => by linarith
    rw [hempty]
    simp
  · rw [if_neg hx]
    have hxpos : 0 < x := lt_of_not_ge hx
    let y : ℝ := min x R
    have hypos : 0 < y := lt_min hxpos hR
    have hset :
        Set.Iic x ∩ Set.Ioc (0 : ℝ) R = Set.Ioc 0 y := by
      ext ρ
      change
        (ρ ≤ x ∧ 0 < ρ ∧ ρ ≤ R) ↔ 0 < ρ ∧ ρ ≤ min x R
      constructor
      · rintro ⟨hρx, hρ0, hρR⟩
        exact ⟨hρ0, le_min hρx hρR⟩
      · rintro ⟨hρ0, hρ⟩
        exact ⟨hρ.trans (min_le_left x R), hρ0,
          hρ.trans (min_le_right x R)⟩
    rw [hset, radialDensityLIntegral y r hypos.le hr]

private theorem pushedKernelMeasure_eq_model
    (R : ℝ) (p : Point3) (hR : 0 < R) :
    pushedKernelMeasure R p = modelRadialMeasure R (radius p) := by
  have hfinite :
      pushedKernelMeasure R p Set.univ < ⊤ := by
    rw [pushedKernelMeasure,
      Measure.map_apply radius_measurable MeasurableSet.univ]
    simp only [Set.preimage_univ]
    unfold kernelBallMeasure
    rw [Measure.restrict_apply MeasurableSet.univ,
      Set.univ_inter,
      withDensity_apply _ (ball_measurable R)]
    change
      (∫⁻ q in ball R, ENNReal.ofReal (1 / distance q p)) < ⊤
    rw [kernelLIntegral R p hR]
    exact ENNReal.ofReal_lt_top
  letI : IsFiniteMeasure (pushedKernelMeasure R p) := ⟨hfinite⟩
  apply Measure.ext_of_Iic
  intro x
  rw [pushedKernelMeasure_Iic R p hR x,
    modelRadialMeasure_Iic R (radius p) hR (Real.sqrt_nonneg _) x]

private theorem shell_eq_radius_preimage
    (R₁ R₂ : ℝ) (hR₁ : 0 ≤ R₁) (hR₂ : 0 ≤ R₂) :
    shell R₁ R₂ = radius ⁻¹' Set.Icc R₁ R₂ := by
  ext q
  have hr : 0 ≤ radius q := Real.sqrt_nonneg _
  have hsq : radius q ^ 2 = squaredRadius q := by
    rw [radius, Real.sq_sqrt]
    unfold squaredRadius
    positivity
  unfold shell
  simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Icc]
  constructor
  · rintro ⟨h₁, h₂⟩
    constructor <;> nlinarith
  · rintro ⟨h₁, h₂⟩
    constructor <;> nlinarith

private theorem shell_measurable
    (R₁ R₂ : ℝ) (hR₁ : 0 ≤ R₁) (hR₂ : 0 ≤ R₂) :
    MeasurableSet (shell R₁ R₂) := by
  rw [shell_eq_radius_preimage R₁ R₂ hR₁ hR₂]
  exact measurableSet_Icc.preimage radius_measurable

private theorem shell_subset_ball (R₁ R₂ : ℝ) :
    shell R₁ R₂ ⊆ ball R₂ := by
  intro q hq
  exact hq.2

private theorem kernelWeight_toReal (p q : Point3) :
    (kernelWeight p q).toReal = 1 / distance q p := by
  unfold kernelWeight
  rw [ENNReal.toReal_ofReal]
  unfold distance
  positivity

private theorem potential_eq_kernel_integral
    (f : ℝ → ℝ) (R₁ R₂ : ℝ)
    (hR₁ : 0 ≤ R₁) (hR₂ : 0 ≤ R₂) (p : Point3) :
    potential f R₁ R₂ p =
      ∫ q in shell R₁ R₂, f (radius q)
        ∂MeasureTheory.volume.withDensity (kernelWeight p) := by
  unfold potential
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul
    (kernelWeight_measurable p)
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))
    (fun q => f (radius q))
    (shell_measurable R₁ R₂ hR₁ hR₂)]
  apply setIntegral_congr_fun
    (shell_measurable R₁ R₂ hR₁ hR₂)
  intro q _
  dsimp
  rw [kernelWeight_toReal]
  simp only [smul_eq_mul, one_div]
  ring

private theorem kernel_integral_eq_pushed
    (f : ℝ → ℝ) (R₁ R₂ : ℝ)
    (hR₁ : 0 ≤ R₁) (hR₂ : 0 ≤ R₂)
    (hf : ContinuousOn f (Set.Icc R₁ R₂)) (p : Point3) :
    (∫ q in shell R₁ R₂, f (radius q)
        ∂MeasureTheory.volume.withDensity (kernelWeight p)) =
      ∫ ρ, Set.indicator (Set.Icc R₁ R₂) f ρ
        ∂pushedKernelMeasure R₂ p := by
  let g : ℝ → ℝ := Set.indicator (Set.Icc R₁ R₂) f
  have hg : Measurable g := by
    dsimp [g]
    rw [← Set.piecewise_eq_indicator]
    exact hf.measurable_piecewise
      continuous_zero.continuousOn measurableSet_Icc
  have hcomp :
      (fun q : Point3 => g (radius q)) =
        Set.indicator (shell R₁ R₂) (fun q => f (radius q)) := by
    funext q
    classical
    rw [shell_eq_radius_preimage R₁ R₂ hR₁ hR₂]
    simp only [g, Set.indicator_apply, Set.mem_preimage]
  calc
    (∫ q in shell R₁ R₂, f (radius q)
        ∂MeasureTheory.volume.withDensity (kernelWeight p)) =
        ∫ q in ball R₂, g (radius q)
          ∂MeasureTheory.volume.withDensity (kernelWeight p) := by
      rw [hcomp, setIntegral_indicator
        (shell_measurable R₁ R₂ hR₁ hR₂)]
      rw [Set.inter_eq_right.mpr (shell_subset_ball R₁ R₂)]
    _ = ∫ q, g (radius q) ∂kernelBallMeasure R₂ p := by
      rfl
    _ = ∫ ρ, g ρ ∂pushedKernelMeasure R₂ p := by
      unfold pushedKernelMeasure
      exact (integral_map_of_stronglyMeasurable
        radius_measurable hg.stronglyMeasurable).symm
    _ = ∫ ρ, Set.indicator (Set.Icc R₁ R₂) f ρ
        ∂pushedKernelMeasure R₂ p := by
      rfl

private theorem radialDensity_toReal
    (r ρ : ℝ) (hr : 0 ≤ r) (hρ : 0 ≤ ρ) :
    (radialDensity r ρ).toReal =
      4 * Real.pi * radialKernel ρ r := by
  unfold radialDensity
  rw [ENNReal.toReal_ofReal]
  exact mul_nonneg (by positivity)
    (radialKernel_nonneg ρ r hρ hr)

private theorem model_integral_eq_radialFormula
    (f : ℝ → ℝ) (R₁ R₂ r : ℝ)
    (hR₁ : 0 ≤ R₁) (hR : R₁ < R₂) (hr : 0 ≤ r) :
    (∫ ρ, Set.indicator (Set.Icc R₁ R₂) f ρ
        ∂modelRadialMeasure R₂ r) =
      radialFormula f R₁ R₂ r := by
  have hR₂ : 0 ≤ R₂ := hR₁.trans hR.le
  have hsetae :
      ((Set.Ioc (0 : ℝ) R₂ ∩ Set.Icc R₁ R₂ : Set ℝ)
          =ᵐ[(MeasureTheory.volume : Measure ℝ)]
        Set.Ioc R₁ R₂) := by
    have hfirst :
        ((Set.Ioc (0 : ℝ) R₂ ∩ Set.Icc R₁ R₂ : Set ℝ)
            =ᵐ[(MeasureTheory.volume : Measure ℝ)]
          (Set.Ioc (0 : ℝ) R₂ ∩ Set.Ioc R₁ R₂ : Set ℝ)) :=
      Filter.EventuallyEq.rfl.inter
        (Ioc_ae_eq_Icc
          (μ := (MeasureTheory.volume : Measure ℝ))
          (a := R₁) (b := R₂)).symm
    have hsecond :
        ((Set.Ioc (0 : ℝ) R₂ ∩ Set.Ioc R₁ R₂ : Set ℝ)
            =ᵐ[(MeasureTheory.volume : Measure ℝ)]
          (Set.Ioc R₁ R₂ : Set ℝ)) := by
      apply Filter.Eventually.of_forall
      intro ρ
      apply propext
      change
        ((0 < ρ ∧ ρ ≤ R₂) ∧ (R₁ < ρ ∧ ρ ≤ R₂)) ↔
          (R₁ < ρ ∧ ρ ≤ R₂)
      constructor
      · rintro ⟨_, hρ⟩
        exact hρ
      · intro hρ
        exact ⟨⟨hR₁.trans_lt hρ.1, hρ.2⟩, hρ⟩
    exact hfirst.trans hsecond
  unfold modelRadialMeasure
  change
    (∫ ρ in Set.Ioc (0 : ℝ) R₂,
      Set.indicator (Set.Icc R₁ R₂) f ρ
        ∂MeasureTheory.volume.withDensity (radialDensity r)) =
      radialFormula f R₁ R₂ r
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul
    (radialDensity_measurable r)
    (Filter.Eventually.of_forall
      (fun _ => ENNReal.ofReal_lt_top))
    (Set.indicator (Set.Icc R₁ R₂) f)
    measurableSet_Ioc]
  calc
    (∫ ρ in Set.Ioc (0 : ℝ) R₂,
        (radialDensity r ρ).toReal •
          Set.indicator (Set.Icc R₁ R₂) f ρ) =
        ∫ ρ in Set.Ioc (0 : ℝ) R₂,
          Set.indicator (Set.Icc R₁ R₂)
            (fun ρ => 4 * Real.pi *
              (f ρ * radialKernel ρ r)) ρ := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro ρ hρ
      dsimp
      rw [radialDensity_toReal r ρ hr hρ.1.le]
      by_cases hmem : ρ ∈ Set.Icc R₁ R₂
      · simp only [Set.indicator_of_mem hmem, smul_eq_mul]
        ring
      · simp only [Set.indicator_of_notMem hmem, smul_zero, mul_zero]
    _ = ∫ ρ in
          Set.Ioc (0 : ℝ) R₂ ∩ Set.Icc R₁ R₂,
          4 * Real.pi * (f ρ * radialKernel ρ r) := by
      rw [setIntegral_indicator measurableSet_Icc]
    _ = ∫ ρ in Set.Ioc R₁ R₂,
          4 * Real.pi * (f ρ * radialKernel ρ r) := by
      exact setIntegral_congr_set hsetae
    _ = radialFormula f R₁ R₂ r := by
      unfold radialFormula
      rw [intervalIntegral.integral_of_le hR.le,
        MeasureTheory.integral_const_mul]

private theorem potential_radial_formula
    (f : ℝ → ℝ) (R₁ R₂ : ℝ)
    (hR₁ : 0 ≤ R₁) (hR : R₁ < R₂)
    (hf : ContinuousOn f (Icc R₁ R₂))
    (p : Point3) :
    potential f R₁ R₂ p = radialFormula f R₁ R₂ (radius p) := by
  have hR₂pos : 0 < R₂ := hR₁.trans_lt hR
  calc
    potential f R₁ R₂ p =
        ∫ q in shell R₁ R₂, f (radius q)
          ∂MeasureTheory.volume.withDensity (kernelWeight p) :=
      potential_eq_kernel_integral f R₁ R₂ hR₁ hR₂pos.le p
    _ = ∫ ρ, Set.indicator (Set.Icc R₁ R₂) f ρ
          ∂pushedKernelMeasure R₂ p :=
      kernel_integral_eq_pushed f R₁ R₂ hR₁ hR₂pos.le hf p
    _ = ∫ ρ, Set.indicator (Set.Icc R₁ R₂) f ρ
          ∂modelRadialMeasure R₂ (radius p) := by
      rw [pushedKernelMeasure_eq_model R₂ p hR₂pos]
    _ = radialFormula f R₁ R₂ (radius p) :=
      model_integral_eq_radialFormula f R₁ R₂ (radius p)
        hR₁ hR (Real.sqrt_nonneg _)

private theorem shellPotential_eq_potential
    (f : ℝ → ℝ) (R₁ R₂ r : ℝ)
    (hR₁ : 0 ≤ R₁) (hR₂ : 0 ≤ R₂) :
    shellPotential f R₁ R₂ r =
      potential f R₁ R₂ (0, 0, r) := by
  unfold shellPotential potential radius squaredRadius distance
  apply setIntegral_congr_fun
    (shell_measurable R₁ R₂ hR₁ hR₂)
  intro p _
  simp only [sub_zero]

private theorem shellPotential_radial_formula
    (f : ℝ → ℝ) (R₁ R₂ r : ℝ)
    (hR₁ : 0 ≤ R₁) (hR : R₁ < R₂)
    (hf : ContinuousOn f (Set.Icc R₁ R₂)) :
    shellPotential f R₁ R₂ r =
      radialFormula f R₁ R₂ |r| := by
  have hR₂ : 0 ≤ R₂ := hR₁.trans hR.le
  rw [shellPotential_eq_potential f R₁ R₂ r hR₁ hR₂,
    potential_radial_formula f R₁ R₂ hR₁ hR hf]
  unfold radius squaredRadius
  simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    zero_add, Real.sqrt_sq_eq_abs]

theorem gap1 (f : ℝ → ℝ) (R₁ R₂ r : ℝ)
    (hR₁ : 0 < R₁) (hR₁₂ : R₁ < R₂) (hr : 0 ≤ r) :
    shellPotential f R₁ R₂ r =
      ∫ p in shell R₁ R₂,
        f (Real.sqrt (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2)) /
          Real.sqrt (p.1 ^ 2 + p.2.1 ^ 2 + (p.2.2 - r) ^ 2) := by
  rfl

private theorem axial_abs_eq_two_radialKernel
    (ρ r : ℝ) (hρ : 0 < ρ) (hr : 0 < r) :
    ρ ^ 2 * (-(1 / (ρ * r))) *
        (|ρ - r| - (ρ + r)) =
      2 * radialKernel ρ r := by
  simp only [radialKernel, hr.ne', if_false]
  by_cases hρr : ρ ≤ r
  · have hmin : min (ρ ^ 2 / r) ρ = ρ ^ 2 / r := by
      rw [min_eq_left]
      rw [div_le_iff₀ hr]
      nlinarith [mul_nonneg hρ.le (sub_nonneg.mpr hρr)]
    rw [hmin, abs_of_nonpos (sub_nonpos.mpr hρr)]
    field_simp [hρ.ne', hr.ne']
    ring
  · have hrρ : r < ρ := lt_of_not_ge hρr
    have hmin : min (ρ ^ 2 / r) ρ = ρ := by
      rw [min_eq_right]
      rw [le_div_iff₀ hr]
      nlinarith [mul_nonneg hρ.le (sub_nonneg.mpr hrρ.le)]
    rw [hmin, abs_of_pos (sub_pos.mpr hrρ)]
    field_simp [hρ.ne', hr.ne']
    ring

private def angularQ (ρ r ψ : ℝ) : ℝ :=
  ρ ^ 2 + r ^ 2 - 2 * ρ * r * Real.sin ψ

private theorem angularQ_eq_sq (ρ r ψ : ℝ) :
    angularQ ρ r ψ =
      (ρ * Real.cos ψ) ^ 2 +
        (ρ * Real.sin ψ - r) ^ 2 := by
  calc
    angularQ ρ r ψ =
        ρ ^ 2 *
            (Real.cos ψ ^ 2 + Real.sin ψ ^ 2) +
          r ^ 2 - 2 * ρ * r * Real.sin ψ := by
      rw [Real.cos_sq_add_sin_sq]
      unfold angularQ
      ring
    _ = _ := by ring

private theorem angularKernel_intervalIntegrable
    (ρ r : ℝ) (hρ : 0 < ρ) :
    IntervalIntegrable
      (fun ψ : ℝ =>
        Real.cos ψ / Real.sqrt (angularQ ρ r ψ))
      volume (-Real.pi / 2) (Real.pi / 2) := by
  rw [intervalIntegrable_iff]
  apply Measure.integrableOn_of_bounded (M := 1 / ρ)
  · rw [Real.volume_uIoc]
    exact ENNReal.ofReal_ne_top
  · have hm : Measurable
        (fun ψ : ℝ =>
          Real.cos ψ / Real.sqrt (angularQ ρ r ψ)) := by
      unfold angularQ
      fun_prop
    exact hm.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with ψ hψ
    rw [Set.uIoc_of_le (by linarith [Real.pi_pos] :
      -Real.pi / 2 ≤ Real.pi / 2)] at hψ
    have hcos : 0 ≤ Real.cos ψ :=
      Real.cos_nonneg_of_mem_Icc
        ⟨by linarith [hψ.1], hψ.2⟩
    have hQ : 0 ≤ angularQ ρ r ψ := by
      rw [angularQ_eq_sq]
      positivity
    have hsqrt_ge :
        ρ * Real.cos ψ ≤ Real.sqrt (angularQ ρ r ψ) := by
      apply (sq_le_sq₀
        (mul_nonneg hρ.le hcos) (Real.sqrt_nonneg _)).mp
      rw [Real.sq_sqrt hQ, angularQ_eq_sq]
      nlinarith [sq_nonneg (ρ * Real.sin ψ - r)]
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg hcos,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    by_cases hs : Real.sqrt (angularQ ρ r ψ) = 0
    · have hp0 : ρ * Real.cos ψ = 0 :=
        le_antisymm (by simpa [hs] using hsqrt_ge)
          (mul_nonneg hρ.le hcos)
      have hc0 : Real.cos ψ = 0 :=
        (mul_eq_zero.mp hp0).resolve_left hρ.ne'
      simp [hs, hc0, hρ.le]
    · have hspos : 0 < Real.sqrt (angularQ ρ r ψ) :=
        lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hs)
      rw [div_le_iff₀ hspos]
      calc
        Real.cos ψ ≤ Real.sqrt (angularQ ρ r ψ) / ρ :=
          (le_div_iff₀ hρ).2 (by
            simpa [mul_comm] using hsqrt_ge)
        _ = (1 / ρ) * Real.sqrt (angularQ ρ r ψ) := by
          ring

private theorem angularKernel_integral
    (ρ r : ℝ) (hρ : 0 < ρ) (hr : 0 < r) :
    (∫ ψ in -Real.pi / 2..Real.pi / 2,
        Real.cos ψ / Real.sqrt (angularQ ρ r ψ)) =
      -(1 / (ρ * r)) * (|ρ - r| - (ρ + r)) := by
  let F : ℝ → ℝ := fun ψ =>
    -(1 / (ρ * r)) * Real.sqrt (angularQ ρ r ψ)
  have hQpos (ψ : ℝ)
      (hψ : ψ ∈ Set.Ioo (-Real.pi / 2) (Real.pi / 2)) :
      0 < angularQ ρ r ψ := by
    have hcos : 0 < Real.cos ψ :=
      Real.cos_pos_of_mem_Ioo
        ⟨by linarith [hψ.1], hψ.2⟩
    rw [angularQ_eq_sq]
    nlinarith [sq_pos_of_pos (mul_pos hρ hcos),
      sq_nonneg (ρ * Real.sin ψ - r)]
  have hder : ∀ ψ ∈ Set.Ioo (-Real.pi / 2) (Real.pi / 2),
      HasDerivAt F
        (Real.cos ψ / Real.sqrt (angularQ ρ r ψ)) ψ := by
    intro ψ hψ
    have hq := hQpos ψ hψ
    have hinner :
        HasDerivAt (angularQ ρ r)
          (-2 * ρ * r * Real.cos ψ) ψ := by
      unfold angularQ
      convert
        (((hasDerivAt_const ψ (ρ ^ 2)).add_const (r ^ 2)).sub
          ((hasDerivAt_const ψ (2 * ρ * r)).mul
            (Real.hasDerivAt_sin ψ))) using 1 <;> ring
    have hsqrt :
        HasDerivAt
          (fun x : ℝ => Real.sqrt (angularQ ρ r x))
          (1 / (2 * Real.sqrt (angularQ ρ r ψ)) *
            (-2 * ρ * r * Real.cos ψ)) ψ := by
      simpa only [Function.comp_apply] using
        (Real.hasDerivAt_sqrt hq.ne').comp ψ hinner
    dsimp [F]
    convert
      (hasDerivAt_const ψ (-(1 / (ρ * r)))).mul hsqrt using 1
    field_simp [hρ.ne', hr.ne',
      Real.sqrt_ne_zero'.mpr hq]
    ring
  have hcontF :
      ContinuousOn F
        (Set.Icc (-Real.pi / 2) (Real.pi / 2)) := by
    dsimp [F]
    unfold angularQ
    fun_prop
  have hFTC :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      (by linarith [Real.pi_pos] :
        -Real.pi / 2 ≤ Real.pi / 2)
      hcontF hder
      (angularKernel_intervalIntegrable ρ r hρ)
  rw [hFTC]
  dsimp [F]
  have htop :
      angularQ ρ r (Real.pi / 2) = (ρ - r) ^ 2 := by
    unfold angularQ
    rw [Real.sin_pi_div_two]
    ring
  have hbottom :
      angularQ ρ r (-Real.pi / 2) = (ρ + r) ^ 2 := by
    unfold angularQ
    rw [show -Real.pi / 2 = -(Real.pi / 2) by ring,
      Real.sin_neg, Real.sin_pi_div_two]
    ring
  rw [htop, hbottom, Real.sqrt_sq_eq_abs,
    Real.sqrt_sq_eq_abs, abs_of_pos (add_pos hρ hr)]
  ring

private def angularRadialKernel
    (f : ℝ → ℝ) (r : ℝ) (p : ℝ × ℝ) : ℝ :=
  p.2 ^ 2 * f p.2 * Real.cos p.1 /
    Real.sqrt (angularQ p.2 r p.1)

private theorem angularRadialKernel_integrableOn
    (f : ℝ → ℝ) (R₁ R₂ r : ℝ)
    (hR₁ : 0 < R₁) (hR₁₂ : R₁ < R₂)
    (hf : ContinuousOn f (Set.Icc R₁ R₂)) :
    IntegrableOn (angularRadialKernel f r)
      (Set.Icc (-Real.pi / 2) (Real.pi / 2) ×ˢ
        Set.Icc R₁ R₂) := by
  let rect :=
    Set.Icc (-Real.pi / 2) (Real.pi / 2) ×ˢ
      Set.Icc R₁ R₂
  have hrectMeas : MeasurableSet rect :=
    measurableSet_Icc.prod measurableSet_Icc
  have hrectCompact : IsCompact rect :=
    isCompact_Icc.prod isCompact_Icc
  have hbound :
      BddAbove ((fun ρ : ℝ => |f ρ|) '' Set.Icc R₁ R₂) :=
    isCompact_Icc.bddAbove_image hf.abs
  rcases hbound with ⟨C, hC⟩
  have hfC (ρ : ℝ) (hρ : ρ ∈ Set.Icc R₁ R₂) :
      |f ρ| ≤ C :=
    hC ⟨ρ, hρ, rfl⟩
  have hC0 : 0 ≤ C := by
    exact (abs_nonneg (f R₁)).trans
      (hfC R₁ ⟨le_rfl, hR₁₂.le⟩)
  let g : ℝ → ℝ := Set.indicator (Set.Icc R₁ R₂) f
  have hg : Measurable g := by
    dsimp [g]
    rw [← Set.piecewise_eq_indicator]
    exact hf.measurable_piecewise
      continuous_zero.continuousOn measurableSet_Icc
  let KG : ℝ × ℝ → ℝ := fun p =>
    p.2 ^ 2 * g p.2 * Real.cos p.1 /
      Real.sqrt (angularQ p.2 r p.1)
  have hKGmeas : Measurable KG := by
    dsimp [KG]
    unfold angularQ
    fun_prop
  have hiG : IntegrableOn KG rect := by
    apply Measure.integrableOn_of_bounded (M := R₂ * C)
    · exact hrectCompact.measure_lt_top.ne
    · exact hKGmeas.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem hrectMeas] with p hp
      have hψ := hp.1
      have hρ := hp.2
      have hρpos : 0 < p.2 := hR₁.trans_le hρ.1
      have hR₂pos : 0 < R₂ := hR₁.trans hR₁₂
      have hcos : 0 ≤ Real.cos p.1 :=
        Real.cos_nonneg_of_mem_Icc
          ⟨by linarith [hψ.1], hψ.2⟩
      have hQ : 0 ≤ angularQ p.2 r p.1 := by
        rw [angularQ_eq_sq]
        positivity
      have hsqrt_ge :
          p.2 * Real.cos p.1 ≤
            Real.sqrt (angularQ p.2 r p.1) := by
        apply (sq_le_sq₀
          (mul_nonneg hρpos.le hcos)
          (Real.sqrt_nonneg _)).mp
        rw [Real.sq_sqrt hQ, angularQ_eq_sq]
        nlinarith [sq_nonneg (p.2 * Real.sin p.1 - r)]
      have hratio :
          Real.cos p.1 / Real.sqrt (angularQ p.2 r p.1) ≤
            1 / p.2 := by
        by_cases hs : Real.sqrt (angularQ p.2 r p.1) = 0
        · have hp0 : p.2 * Real.cos p.1 = 0 :=
            le_antisymm (by simpa [hs] using hsqrt_ge)
              (mul_nonneg hρpos.le hcos)
          have hc0 : Real.cos p.1 = 0 :=
            (mul_eq_zero.mp hp0).resolve_left hρpos.ne'
          simp [hs, hc0, hρpos.le]
        · have hspos : 0 < Real.sqrt (angularQ p.2 r p.1) :=
            lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hs)
          rw [div_le_iff₀ hspos]
          calc
            Real.cos p.1 ≤
                Real.sqrt (angularQ p.2 r p.1) / p.2 :=
              (le_div_iff₀ hρpos).2 (by
                simpa [mul_comm] using hsqrt_ge)
            _ = (1 / p.2) *
                Real.sqrt (angularQ p.2 r p.1) := by ring
      have hratio0 :
          0 ≤ Real.cos p.1 /
            Real.sqrt (angularQ p.2 r p.1) :=
        div_nonneg hcos (Real.sqrt_nonneg _)
      have hFC : |g p.2| ≤ C := by
        dsimp [g]
        rw [Set.indicator_of_mem hρ]
        exact hfC p.2 hρ
      have hA :
          p.2 ^ 2 * |g p.2| ≤ p.2 ^ 2 * C :=
        mul_le_mul_of_nonneg_left hFC (sq_nonneg p.2)
      have hA0 : 0 ≤ p.2 ^ 2 * |g p.2| := by positivity
      have hB0 : 0 ≤ 1 / p.2 := by positivity
      have hprod :
          (p.2 ^ 2 * |g p.2|) *
              (Real.cos p.1 /
                Real.sqrt (angularQ p.2 r p.1)) ≤
            (p.2 ^ 2 * C) * (1 / p.2) :=
        mul_le_mul hA hratio hratio0
          (mul_nonneg (sq_nonneg p.2) hC0)
      have hsimpl :
          (p.2 ^ 2 * C) * (1 / p.2) = p.2 * C := by
        field_simp [hρpos.ne']
      have hlast : p.2 * C ≤ R₂ * C :=
        mul_le_mul_of_nonneg_right hρ.2 hC0
      dsimp [KG]
      rw [abs_div, abs_mul, abs_mul,
        abs_of_nonneg hcos,
        abs_of_nonneg (Real.sqrt_nonneg _),
        abs_of_nonneg (sq_nonneg p.2)]
      calc
        (p.2 ^ 2 * |g p.2| * Real.cos p.1) /
            Real.sqrt (angularQ p.2 r p.1) =
            (p.2 ^ 2 * |g p.2|) *
              (Real.cos p.1 /
                Real.sqrt (angularQ p.2 r p.1)) := by ring
        _ ≤ (p.2 ^ 2 * C) * (1 / p.2) := hprod
        _ = p.2 * C := hsimpl
        _ ≤ R₂ * C := hlast
  apply hiG.congr_fun
  · intro p hp
    dsimp [KG, angularRadialKernel, g]
    rw [Set.indicator_of_mem hp.2]
  · exact hrectMeas

private theorem angularRadial_swap
    (f : ℝ → ℝ) (R₁ R₂ r : ℝ)
    (hR₁ : 0 < R₁) (hR₁₂ : R₁ < R₂)
    (hf : ContinuousOn f (Set.Icc R₁ R₂)) :
    (∫ ψ in -Real.pi / 2..Real.pi / 2,
        ∫ ρ in R₁..R₂,
          angularRadialKernel f r (ψ, ρ)) =
      ∫ ρ in R₁..R₂,
        ∫ ψ in -Real.pi / 2..Real.pi / 2,
          angularRadialKernel f r (ψ, ρ) := by
  let K := angularRadialKernel f r
  have hiIcc := angularRadialKernel_integrableOn
    f R₁ R₂ r hR₁ hR₁₂ hf
  have hiIoc : IntegrableOn K
      (Set.Ioc (-Real.pi / 2) (Real.pi / 2) ×ˢ
        Set.Ioc R₁ R₂) (volume.prod volume) := by
    have hsubψ :
        Set.Ioc (-Real.pi / 2) (Real.pi / 2) ⊆
          Set.Icc (-Real.pi / 2) (Real.pi / 2) := by
      intro x hx
      exact ⟨hx.1.le, hx.2⟩
    have hsubρ :
        Set.Ioc R₁ R₂ ⊆ Set.Icc R₁ R₂ := by
      intro x hx
      exact ⟨hx.1.le, hx.2⟩
    have hi' := hiIcc.mono_set
      (Set.prod_mono hsubψ hsubρ)
    simpa only [Measure.volume_eq_prod] using hi'
  have hp :=
    MeasureTheory.setIntegral_prod
      (μ := (volume : Measure ℝ))
      (ν := (volume : Measure ℝ)) K hiIoc
  have hps :=
    MeasureTheory.setIntegral_prod
      (μ := (volume : Measure ℝ))
      (ν := (volume : Measure ℝ))
      (K ∘ Prod.swap) hiIoc.swap
  have hswap :=
    MeasureTheory.setIntegral_prod_swap
      (μ := (volume : Measure ℝ))
      (ν := (volume : Measure ℝ))
      (Set.Ioc (-Real.pi / 2) (Real.pi / 2))
      (Set.Ioc R₁ R₂) K
  simp_rw [intervalIntegral.integral_of_le
      (by linarith [Real.pi_pos] :
        -Real.pi / 2 ≤ Real.pi / 2),
    intervalIntegral.integral_of_le hR₁₂.le]
  change
    (∫ ψ in Set.Ioc (-Real.pi / 2) (Real.pi / 2),
        ∫ ρ in Set.Ioc R₁ R₂, K (ψ, ρ)) =
      ∫ ρ in Set.Ioc R₁ R₂,
        ∫ ψ in Set.Ioc (-Real.pi / 2) (Real.pi / 2),
          (K ∘ Prod.swap) (ρ, ψ)
  rw [← hp, ← hps]
  exact hswap.symm

private theorem angularRadial_inner_integral
    (f : ℝ → ℝ) (ρ r : ℝ) (hρ : 0 < ρ) (hr : 0 ≤ r) :
    (∫ ψ in -Real.pi / 2..Real.pi / 2,
        angularRadialKernel f r (ψ, ρ)) =
      2 * (f ρ * radialKernel ρ r) := by
  by_cases hr0 : r = 0
  · subst r
    have hsqrt : Real.sqrt (ρ ^ 2) = ρ := by
      rw [Real.sqrt_sq_eq_abs, abs_of_pos hρ]
    have hfun :
        (fun ψ : ℝ =>
            ρ ^ 2 * f ρ * Real.cos ψ /
              Real.sqrt (angularQ ρ 0 ψ)) =
          fun ψ : ℝ => (ρ * f ρ) * Real.cos ψ := by
      funext ψ
      unfold angularQ
      rw [show
          ρ ^ 2 + 0 ^ 2 - 2 * ρ * 0 * Real.sin ψ = ρ ^ 2 by
            ring,
        hsqrt]
      field_simp [hρ.ne']
    unfold angularRadialKernel
    rw [hfun, intervalIntegral.integral_const_mul,
      integral_cos]
    rw [show radialKernel ρ 0 = ρ by simp [radialKernel]]
    simp only [Real.sin_pi_div_two,
      show -Real.pi / 2 = -(Real.pi / 2) by ring,
      Real.sin_neg]
    ring
  · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
    have hfun :
        (fun ψ : ℝ =>
            ρ ^ 2 * f ρ * Real.cos ψ /
              Real.sqrt (angularQ ρ r ψ)) =
          fun ψ : ℝ =>
            (ρ ^ 2 * f ρ) *
              (Real.cos ψ / Real.sqrt (angularQ ρ r ψ)) := by
      funext ψ
      ring
    unfold angularRadialKernel
    rw [hfun, intervalIntegral.integral_const_mul,
      angularKernel_integral ρ r hρ hrpos]
    calc
      ρ ^ 2 * f ρ *
          (-(1 / (ρ * r)) * (|ρ - r| - (ρ + r))) =
          f ρ *
            (ρ ^ 2 * (-(1 / (ρ * r))) *
              (|ρ - r| - (ρ + r))) := by ring
      _ = f ρ * (2 * radialKernel ρ r) := by
        rw [axial_abs_eq_two_radialKernel ρ r hρ hrpos]
      _ = 2 * (f ρ * radialKernel ρ r) := by ring

theorem gap2 (f : ℝ → ℝ) (R₁ R₂ r : ℝ)
    (hR₁ : 0 < R₁) (hR₁₂ : R₁ < R₂) (hr : 0 ≤ r)
    (hf : ContinuousOn f (Set.Icc R₁ R₂)) :
    shellPotential f R₁ R₂ r =
      ∫ φ in (0 : ℝ)..2 * Real.pi,
        ∫ ψ in -Real.pi / 2..Real.pi / 2,
          ∫ ρ in R₁..R₂,
            ρ ^ 2 * f ρ * Real.cos ψ *
              (1 / Real.sqrt (ρ ^ 2 + r ^ 2 - 2 * ρ * r * Real.sin ψ)) := by
  rw [shellPotential_radial_formula f R₁ R₂ r
      hR₁.le hR₁₂ hf,
    abs_of_nonneg hr]
  unfold radialFormula
  have hraw :
      (∫ ψ in -Real.pi / 2..Real.pi / 2,
          ∫ ρ in R₁..R₂,
            ρ ^ 2 * f ρ * Real.cos ψ *
              (1 / Real.sqrt
                (ρ ^ 2 + r ^ 2 - 2 * ρ * r * Real.sin ψ))) =
        ∫ ψ in -Real.pi / 2..Real.pi / 2,
          ∫ ρ in R₁..R₂,
            angularRadialKernel f r (ψ, ρ) := by
    apply intervalIntegral.integral_congr
    intro ψ _
    apply intervalIntegral.integral_congr
    intro ρ _
    unfold angularRadialKernel angularQ
    ring
  have hinner :
      (∫ ρ in R₁..R₂,
          ∫ ψ in -Real.pi / 2..Real.pi / 2,
            angularRadialKernel f r (ψ, ρ)) =
        ∫ ρ in R₁..R₂,
          2 * (f ρ * radialKernel ρ r) := by
    apply intervalIntegral.integral_congr
    intro ρ hρ
    rw [Set.uIcc_of_le hR₁₂.le] at hρ
    exact angularRadial_inner_integral
      f ρ r (hR₁.trans_le hρ.1) hr
  rw [intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul]
  rw [hraw, angularRadial_swap f R₁ R₂ r hR₁ hR₁₂ hf,
    hinner, intervalIntegral.integral_const_mul]
  ring

theorem gap3 (f : ℝ → ℝ) (R₁ R₂ r : ℝ)
    (hR₁ : 0 < R₁) (hR₁₂ : R₁ < R₂) (hr : 0 < r)
    (hf : ContinuousOn f (Set.Icc R₁ R₂)) :
    shellPotential f R₁ R₂ r =
      2 * Real.pi *
        ∫ ρ in R₁..R₂,
          ρ ^ 2 * f ρ * (-(1 / (ρ * r))) *
            (|ρ - r| - (ρ + r)) := by
  rw [shellPotential_radial_formula f R₁ R₂ r hR₁.le hR₁₂ hf,
    abs_of_pos hr]
  unfold radialFormula
  have hpoint :
      (∫ ρ in R₁..R₂,
          ρ ^ 2 * f ρ * (-(1 / (ρ * r))) *
            (|ρ - r| - (ρ + r))) =
        ∫ ρ in R₁..R₂, 2 * (f ρ * radialKernel ρ r) := by
    apply intervalIntegral.integral_congr
    intro ρ hρ
    rw [Set.uIcc_of_le hR₁₂.le] at hρ
    have hρpos : 0 < ρ := hR₁.trans_le hρ.1
    change
      ρ ^ 2 * f ρ * (-(1 / (ρ * r))) *
          (|ρ - r| - (ρ + r)) =
        2 * (f ρ * radialKernel ρ r)
    calc
      _ = f ρ *
          (ρ ^ 2 * (-(1 / (ρ * r))) *
            (|ρ - r| - (ρ + r))) := by ring
      _ = f ρ * (2 * radialKernel ρ r) := by
        rw [axial_abs_eq_two_radialKernel ρ r hρpos hr]
      _ = _ := by ring
  rw [hpoint, intervalIntegral.integral_const_mul]
  ring

theorem gap4 (f : ℝ → ℝ) (R₁ R₂ r : ℝ)
    (hR₁ : 0 < R₁) (hR₁₂ : R₁ < R₂) (hr : 0 ≤ r)
    (hf : ContinuousOn f (Set.Icc R₁ R₂)) :
    (r < R₁ →
      shellPotential f R₁ R₂ r =
        4 * Real.pi * ∫ ρ in R₁..R₂, ρ * f ρ) ∧
    (R₂ < r →
      shellPotential f R₁ R₂ r =
        4 * Real.pi * ∫ ρ in R₁..R₂, ρ ^ 2 / r * f ρ) := by
  constructor
  · intro hrR₁
    rw [shellPotential_radial_formula
      f R₁ R₂ r hR₁.le hR₁₂ hf, abs_of_nonneg hr]
    unfold radialFormula
    congr 1
    apply intervalIntegral.integral_congr
    intro ρ hρ
    rw [Set.uIcc_of_le hR₁₂.le] at hρ
    have hρpos : 0 < ρ := hR₁.trans_le hρ.1
    by_cases hr0 : r = 0
    · subst r
      simp [radialKernel]
      ring
    · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
      have hrρ : r < ρ := hrR₁.trans_le hρ.1
      simp only [radialKernel, hr0, if_false]
      rw [min_eq_right]
      · ring
      · rw [le_div_iff₀ hrpos]
        nlinarith [mul_nonneg hρpos.le (sub_nonneg.mpr hrρ.le)]
  · intro hR₂r
    rw [shellPotential_radial_formula
      f R₁ R₂ r hR₁.le hR₁₂ hf, abs_of_nonneg hr]
    unfold radialFormula
    have hrpos : 0 < r := hR₁₂.trans hR₂r |>.trans' hR₁
    congr 1
    apply intervalIntegral.integral_congr
    intro ρ hρ
    rw [Set.uIcc_of_le hR₁₂.le] at hρ
    have hρpos : 0 < ρ := hR₁.trans_le hρ.1
    have hρr : ρ < r := hρ.2.trans_lt hR₂r
    simp only [radialKernel, hrpos.ne', if_false]
    rw [min_eq_left]
    · ring
    · rw [div_le_iff₀ hrpos]
      nlinarith [mul_nonneg hρpos.le (sub_nonneg.mpr hρr.le)]

theorem gap5 (f : ℝ → ℝ) (R₁ R₂ r : ℝ)
    (hR₁ : 0 < R₁) (hR₁₂ : R₁ < R₂) (hr : 0 < r)
    (hf : ContinuousOn f (Set.Icc R₁ R₂)) :
    shellPotential f R₁ R₂ r =
      4 * Real.pi *
        ∫ ρ in R₁..R₂, f ρ * min (ρ ^ 2 / r) ρ := by
  rw [shellPotential_radial_formula
    f R₁ R₂ r hR₁.le hR₁₂ hf, abs_of_pos hr]
  simp only [radialFormula, radialKernel, hr.ne', if_false]

end

end ProofGap.Exercise4156
