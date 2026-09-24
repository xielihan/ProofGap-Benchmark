import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

namespace ProofGap.Exercise3860

noncomputable section

open Filter MeasureTheory
open scoped Interval

def HasImproperIntegral (a : ℝ) (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Tendsto (fun b : ℝ => ∫ x in a..b, f x) atTop (nhds L)

def improperIntegral (a : ℝ) (f : ℝ → ℝ) : ℝ :=
  sInf {L : ℝ | HasImproperIntegral a f L}

def HasReverseImproperIntegral (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Tendsto (fun A : ℝ => ∫ t in A..0, f t) atTop (nhds L)

def reverseImproperIntegral (f : ℝ → ℝ) : ℝ :=
  sInf {L : ℝ | HasReverseImproperIntegral f L}

def gammaIntegrand (q t : ℝ) : ℝ :=
  Real.rpow t (q - 1) * Real.exp (-t)

def integrand (m n x : ℝ) : ℝ :=
  Real.rpow x m * Real.exp (-Real.rpow x n)

private theorem improperIntegral_eq_integral_Ioi {f : ℝ → ℝ}
    (hf : IntegrableOn f (Set.Ioi 0)) :
    improperIntegral 0 f = ∫ x in Set.Ioi 0, f x := by
  have hlim : HasImproperIntegral 0 f (∫ x in Set.Ioi 0, f x) :=
    intervalIntegral_tendsto_integral_Ioi 0 hf tendsto_id
  have hset :
      {L : ℝ | HasImproperIntegral 0 f L} =
        {(∫ x in Set.Ioi 0, f x)} := by
    ext L
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro hL
      exact tendsto_nhds_unique hL hlim
    · rintro rfl
      exact hlim
  rw [improperIntegral, hset, csInf_singleton]

private theorem reverseImproperIntegral_eq_neg_integral_Ioi {f : ℝ → ℝ}
    (hf : IntegrableOn f (Set.Ioi 0)) :
    reverseImproperIntegral f = -(∫ x in Set.Ioi 0, f x) := by
  have hfwd :
      Tendsto (fun A : ℝ => ∫ t in 0..A, f t) atTop
        (nhds (∫ x in Set.Ioi 0, f x)) :=
    intervalIntegral_tendsto_integral_Ioi 0 hf tendsto_id
  have hlim :
      HasReverseImproperIntegral f (-(∫ x in Set.Ioi 0, f x)) := by
    refine hfwd.neg.congr' ?_
    filter_upwards with A
    rw [intervalIntegral.integral_symm]
    simp
  have hset :
      {L : ℝ | HasReverseImproperIntegral f L} =
        {(-(∫ x in Set.Ioi 0, f x))} := by
    ext L
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro hL
      exact tendsto_nhds_unique hL hlim
    · rintro rfl
      exact hlim
  rw [reverseImproperIntegral, hset, csInf_singleton]

private theorem gamma_integrable {q : ℝ} (hq : 0 < q) :
    IntegrableOn (gammaIntegrand q) (Set.Ioi 0) := by
  refine (Real.GammaIntegral_convergent hq).congr_fun ?_ measurableSet_Ioi
  intro x hx
  simp [gammaIntegrand, mul_comm]

private theorem integrand_eq_signed_change (m n x : ℝ) (hn : n ≠ 0)
    (hx : x ∈ Set.Ioi (0 : ℝ)) :
    integrand m n x =
      (1 / n) *
        ((n * x ^ (n - 1)) *
          gammaIntegrand ((m + 1) / n) (x ^ n)) := by
  have hx0 : 0 ≤ x := le_of_lt hx
  rw [integrand, gammaIntegrand]
  field_simp [hn]
  have hrpow :
      Real.rpow (Real.rpow x n) ((m + 1 - n) / n) =
        Real.rpow x (n * ((m + 1 - n) / n)) :=
    (Real.rpow_mul hx0 n ((m + 1 - n) / n)).symm
  change Real.rpow x m * Real.exp (-Real.rpow x n) =
    Real.rpow x (n - 1) *
      Real.rpow (Real.rpow x n) ((m + 1 - n) / n) *
        Real.exp (-Real.rpow x n)
  rw [hrpow]
  have hrpow_add :
      Real.rpow x (n - 1) *
          Real.rpow x (n * ((m + 1 - n) / n)) =
        Real.rpow x ((n - 1) + n * ((m + 1 - n) / n)) :=
    (Real.rpow_add hx (n - 1) (n * ((m + 1 - n) / n))).symm
  rw [hrpow_add]
  congr 2
  field_simp
  ring

private theorem integrand_integrable (m n : ℝ) (hn : n ≠ 0)
    (hq : 0 < (m + 1) / n) :
    IntegrableOn (integrand m n) (Set.Ioi 0) := by
  let q := (m + 1) / n
  have hgamma : IntegrableOn (gammaIntegrand q) (Set.Ioi 0) :=
    gamma_integrable hq
  have habs :
      IntegrableOn
        (fun x : ℝ =>
          (|n| * x ^ (n - 1)) * gammaIntegrand q (x ^ n))
        (Set.Ioi 0) := by
    simpa [smul_eq_mul] using
      (integrableOn_Ioi_comp_rpow_iff (gammaIntegrand q) hn).mpr hgamma
  rcases lt_or_gt_of_ne hn with hnneg | hnpos
  · refine IntegrableOn.congr_fun
      (habs.const_mul (-(1 / n))) ?_ measurableSet_Ioi
    intro x hx
    rw [integrand_eq_signed_change m n x hn hx, abs_of_neg hnneg]
    ring
  · refine IntegrableOn.congr_fun
      (habs.const_mul (1 / n)) ?_ measurableSet_Ioi
    intro x hx
    rw [integrand_eq_signed_change m n x hn hx, abs_of_pos hnpos]

theorem gap1 (m n : ℝ) (hn : 0 < n) (hq : 0 < (m + 1) / n) :
    improperIntegral 0 (integrand m n) =
      1 / n *
        improperIntegral 0 (gammaIntegrand ((m + 1) / n)) := by
  let q := (m + 1) / n
  have hgamma : IntegrableOn (gammaIntegrand q) (Set.Ioi 0) :=
    gamma_integrable hq
  have hint : IntegrableOn (integrand m n) (Set.Ioi 0) :=
    integrand_integrable m n hn.ne' hq
  rw [improperIntegral_eq_integral_Ioi hint,
    improperIntegral_eq_integral_Ioi hgamma]
  rw [setIntegral_congr_fun measurableSet_Ioi
    (fun x hx => integrand_eq_signed_change m n x hn.ne' hx)]
  rw [MeasureTheory.integral_const_mul]
  congr 1
  simpa [smul_eq_mul] using
    (MeasureTheory.integral_comp_rpow_Ioi_of_pos
      (g := gammaIntegrand q) hn)

theorem gap2 (m n : ℝ) (hn : 0 < n) (hq : 0 < (m + 1) / n) :
    1 / n *
        improperIntegral 0 (gammaIntegrand ((m + 1) / n)) =
      1 / n * Real.Gamma ((m + 1) / n) := by
  have hgamma :
      IntegrableOn (gammaIntegrand ((m + 1) / n)) (Set.Ioi 0) :=
    gamma_integrable hq
  rw [improperIntegral_eq_integral_Ioi hgamma]
  rw [Real.Gamma_eq_integral hq]
  apply congrArg (fun z : ℝ => (1 / n) * z)
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  simp [gammaIntegrand, mul_comm]

theorem gap3 (m n : ℝ) (hn : 0 < n) (hq : 0 < (m + 1) / n) :
    improperIntegral 0 (integrand m n) =
      1 / n * Real.Gamma ((m + 1) / n) := by
  rw [gap1 m n hn hq]
  exact gap2 m n hn hq

theorem gap4 (m n : ℝ) (hn : n < 0) (hq : 0 < (m + 1) / n) :
    improperIntegral 0 (integrand m n) =
      1 / n *
        reverseImproperIntegral (gammaIntegrand ((m + 1) / n)) := by
  let q := (m + 1) / n
  have hgamma : IntegrableOn (gammaIntegrand q) (Set.Ioi 0) :=
    gamma_integrable hq
  have hint : IntegrableOn (integrand m n) (Set.Ioi 0) :=
    integrand_integrable m n hn.ne hq
  rw [improperIntegral_eq_integral_Ioi hint,
    reverseImproperIntegral_eq_neg_integral_Ioi hgamma]
  rw [setIntegral_congr_fun measurableSet_Ioi
    (fun x hx => integrand_eq_signed_change m n x hn.ne hx)]
  rw [MeasureTheory.integral_const_mul]
  have hcomp :=
    MeasureTheory.integral_comp_rpow_Ioi (gammaIntegrand q) hn.ne
  have hcomp' :
      (∫ x in Set.Ioi 0,
          -(n * x ^ (n - 1) * gammaIntegrand q (x ^ n))) =
        ∫ y in Set.Ioi 0, gammaIntegrand q y := by
    simpa [abs_of_neg hn, smul_eq_mul] using hcomp
  have hsigned :
      (∫ x in Set.Ioi 0,
          n * x ^ (n - 1) * gammaIntegrand q (x ^ n)) =
        -(∫ y in Set.Ioi 0, gammaIntegrand q y) := by
    calc
      (∫ x in Set.Ioi 0,
          n * x ^ (n - 1) * gammaIntegrand q (x ^ n)) =
          -(∫ x in Set.Ioi 0,
            -(n * x ^ (n - 1) * gammaIntegrand q (x ^ n))) := by
              rw [← MeasureTheory.integral_neg]
              simp
      _ = -(∫ y in Set.Ioi 0, gammaIntegrand q y) := by rw [hcomp']
  rw [hsigned]

theorem gap5 (m n : ℝ) (hn : n < 0) (hq : 0 < (m + 1) / n) :
    1 / n *
        reverseImproperIntegral (gammaIntegrand ((m + 1) / n)) =
      -(1 / n) *
        improperIntegral 0 (gammaIntegrand ((m + 1) / n)) := by
  have hgamma :
      IntegrableOn (gammaIntegrand ((m + 1) / n)) (Set.Ioi 0) :=
    gamma_integrable hq
  rw [reverseImproperIntegral_eq_neg_integral_Ioi hgamma,
    improperIntegral_eq_integral_Ioi hgamma]
  ring

theorem gap6 (m n : ℝ) (hn : n < 0) (hq : 0 < (m + 1) / n) :
    -(1 / n) *
        improperIntegral 0 (gammaIntegrand ((m + 1) / n)) =
      -(1 / n) * Real.Gamma ((m + 1) / n) := by
  have hgamma :
      IntegrableOn (gammaIntegrand ((m + 1) / n)) (Set.Ioi 0) :=
    gamma_integrable hq
  rw [improperIntegral_eq_integral_Ioi hgamma,
    Real.Gamma_eq_integral hq]
  apply congrArg (fun z : ℝ => -(1 / n) * z)
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  simp [gammaIntegrand, mul_comm]

theorem gap7 (m n : ℝ) (hn : n < 0) (hq : 0 < (m + 1) / n) :
    improperIntegral 0 (integrand m n) =
      -(1 / n) * Real.Gamma ((m + 1) / n) := by
  rw [gap4 m n hn hq, gap5 m n hn hq]
  exact gap6 m n hn hq

theorem gap8 (m n : ℝ) (hn : n ≠ 0) (hq : 0 < (m + 1) / n) :
    improperIntegral 0 (integrand m n) =
      1 / |n| * Real.Gamma ((m + 1) / n) := by
  rcases lt_or_gt_of_ne hn with hnneg | hnpos
  · rw [gap7 m n hnneg hq, abs_of_neg hnneg]
    ring
  · rw [gap3 m n hnpos hq, abs_of_pos hnpos]

private theorem tendsto_symmetric_rpow_atTop {r : ℝ} (hr : 0 < r) :
    Tendsto (fun A : ℝ => (A ^ r - A ^ (-r)) / r) atTop atTop := by
  have hdiff :
      Tendsto (fun A : ℝ => A ^ r + -(A ^ (-r))) atTop atTop :=
    (tendsto_rpow_atTop hr).atTop_add
      (tendsto_rpow_neg_atTop hr).neg
  simpa only [sub_eq_add_neg] using hdiff.atTop_div_const hr

private theorem tendsto_interval_rpow_recip_atTop (m : ℝ) :
    Tendsto (fun A : ℝ => ∫ x in (1 / A)..A, Real.rpow x m)
      atTop atTop := by
  by_cases hm : m = -1
  · subst m
    have hlog :
        Tendsto (fun A : ℝ => 2 * Real.log A) atTop atTop :=
      Tendsto.const_mul_atTop (by norm_num) Real.tendsto_log_atTop
    refine hlog.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with A hA
    have hA0 : 0 < A := zero_lt_one.trans hA
    have heq :
        (∫ x in (1 / A)..A, Real.rpow x (-1)) =
          ∫ x in (1 / A)..A, x⁻¹ := by
      apply intervalIntegral.integral_congr
      intro x hx
      change Real.rpow x (-1) = x⁻¹
      exact Real.rpow_neg_one x
    rw [heq, integral_inv_of_pos (one_div_pos.mpr hA0) hA0]
    have hquot : A / (1 / A) = A ^ 2 := by
      field_simp [hA0.ne']
    rw [hquot, Real.log_pow]
    norm_num
  · rcases lt_or_gt_of_ne (sub_ne_zero.mpr hm) with hrneg | hrpos
    · have hs : 0 < -(m + 1) := by linarith
      refine (tendsto_symmetric_rpow_atTop hs).congr' ?_
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with A hA
      have hA0 : 0 < A := zero_lt_one.trans hA
      have horder : 1 / A ≤ A := by
        apply (div_le_iff₀ hA0).2
        nlinarith [sq_nonneg (A - 1)]
      have hz : (0 : ℝ) ∉ [[1 / A, A]] := by
        rw [Set.uIcc_of_le horder]
        intro hmem
        exact (not_lt_of_ge hmem.1) (one_div_pos.mpr hA0)
      simp_rw [Real.rpow_eq_pow]
      rw [integral_rpow (Or.inr ⟨hm, hz⟩)]
      simp only [one_div]
      rw [show m + 1 = -(-(m + 1)) by ring,
        Real.rpow_neg_eq_inv_rpow, Real.rpow_neg_eq_inv_rpow]
      simp only [inv_inv]
      field_simp [show m + 1 ≠ 0 by linarith]
      ring
    · have hr : 0 < m + 1 := by linarith
      refine (tendsto_symmetric_rpow_atTop hr).congr' ?_
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with A hA
      simp_rw [Real.rpow_eq_pow]
      rw [integral_rpow (Or.inl (by linarith))]
      simp only [one_div]
      rw [← Real.rpow_neg_eq_inv_rpow]

theorem gap9 (m n : ℝ) (hn : n = 0) :
    Tendsto
      (fun A : ℝ =>
        ∫ x in (1 / A)..A,
          Real.rpow x m * Real.exp (-1))
      atTop atTop := by
  have hbase := tendsto_interval_rpow_recip_atTop m
  have hscaled :
      Tendsto
        (fun A : ℝ =>
          (∫ x in (1 / A)..A, Real.rpow x m) * Real.exp (-1))
        atTop atTop :=
    hbase.atTop_mul_const (Real.exp_pos (-1))
  simpa only [intervalIntegral.integral_mul_const] using hscaled

theorem gap10 (m n : ℝ) (hn : n ≠ 0)
    (hq : 0 < (m + 1) / n) :
    0 < (m + 1) / n := by
  exact hq

end

end ProofGap.Exercise3860
