import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise1335

noncomputable section
open Filter
open scoped Topology

def punctured (x₀ : ℝ) := nhdsWithin x₀ ({x₀} : Set ℝ)ᶜ
def original (x : ℝ) :=
  (Real.arsinh (Real.sinh x) - Real.arsinh (Real.sin x)) /
    (Real.sinh x - Real.sin x)
def logarithmicStage (x : ℝ) :=
  (Real.log (Real.sinh x + Real.cosh x) -
    Real.log (Real.sin x + Real.sqrt (1 + Real.sin x ^ 2))) /
      (Real.sinh x - Real.sin x)
def firstDerivativeStage (x : ℝ) :=
  (1 - Real.cos x / Real.sqrt (1 + Real.sin x ^ 2)) /
    (Real.cosh x - Real.cos x)
def secondDerivativeStage (x : ℝ) :=
  (2 * Real.sin x / Real.rpow (1 + Real.sin x ^ 2) (3 / 2 : ℝ)) /
    (Real.sinh x + Real.sin x)
def finalStage (x : ℝ) :=
  2 * ((Real.cos x / Real.rpow (1 + Real.sin x ^ 2) (3 / 2 : ℝ) -
    3 * Real.sin x ^ 2 * Real.cos x /
      Real.rpow (1 + Real.sin x ^ 2) (5 / 2 : ℝ)) /
        (Real.cosh x + Real.cos x))

private theorem eventually_ne_zero_punctured :
    ∀ᶠ x : ℝ in punctured 0, x ≠ 0 := by
  filter_upwards [self_mem_nhdsWithin] with x hx
  simpa [punctured] using hx

private theorem sinQuotientLimit :
    Tendsto (fun x : ℝ => Real.sin x / x) (punctured 0) (nhds 1) := by
  have heq : Asymptotics.IsEquivalent (punctured 0) Real.sin (fun x : ℝ => x) :=
    Real.isEquivalent_sin.mono
      (show punctured (0 : ℝ) ≤ nhds 0 from inf_le_left)
  simpa [punctured, Function.support] using
    (Asymptotics.isEquivalent_iff_tendsto_one eventually_ne_zero_punctured).mp heq

private theorem sinhQuotientLimit :
    Tendsto (fun x : ℝ => Real.sinh x / x) (punctured 0) (nhds 1) := by
  have heq : Asymptotics.IsEquivalent (punctured 0) Real.sinh (fun x : ℝ => x) :=
    Real.isEquivalent_sinh.mono
      (show punctured (0 : ℝ) ≤ nhds 0 from inf_le_left)
  simpa [punctured, Function.support] using
    (Asymptotics.isEquivalent_iff_tendsto_one eventually_ne_zero_punctured).mp heq

private theorem rpowStageLimit (p : ℝ) :
    Tendsto (fun x : ℝ => Real.rpow (1 + Real.sin x ^ 2) p)
      (punctured 0) (nhds 1) := by
  have hsin : Tendsto Real.sin (punctured 0) (nhds 0) := by
    simpa using (Real.continuous_sin.tendsto 0).mono_left inf_le_left
  have hbase : Tendsto (fun x : ℝ => 1 + Real.sin x ^ 2)
      (punctured 0) (nhds 1) := by
    convert tendsto_const_nhds.add (hsin.pow 2) using 1 <;> norm_num
  have hlog : Tendsto (fun x : ℝ => Real.log (1 + Real.sin x ^ 2))
      (punctured 0) (nhds 0) := by
    convert ((Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto).comp
      hbase using 1 <;> norm_num
  have hp : Tendsto (fun _ : ℝ => p) (punctured 0) (nhds p) :=
    tendsto_const_nhds
  have hprod : Tendsto
      (fun x : ℝ => Real.log (1 + Real.sin x ^ 2) * p)
      (punctured 0) (nhds 0) := by
    convert hlog.mul hp using 1 <;> norm_num
  have hexp : Tendsto
      (fun x : ℝ => Real.exp (Real.log (1 + Real.sin x ^ 2) * p))
      (punctured 0) (nhds 1) := by
    simpa using (Real.continuous_exp.tendsto 0).comp hprod
  apply hexp.congr'
  filter_upwards [] with x
  have hb : 0 < 1 + Real.sin x ^ 2 := by
    nlinarith [sq_nonneg (Real.sin x)]
  symm
  exact Real.rpow_def_of_pos hb p

private theorem derivativeStageLimit :
    Tendsto firstDerivativeStage (punctured 0) (nhds 1) := by
  have hsin0 : Tendsto Real.sin (punctured 0) (nhds 0) := by
    simpa using (Real.continuous_sin.tendsto 0).mono_left inf_le_left
  have hbase : Tendsto (fun x : ℝ => 1 + Real.sin x ^ 2)
      (punctured 0) (nhds 1) := by
    convert tendsto_const_nhds.add (hsin0.pow 2) using 1 <;> norm_num
  have hsqrt : Tendsto
      (fun x : ℝ => Real.sqrt (1 + Real.sin x ^ 2))
      (punctured 0) (nhds 1) := by
    convert (Real.continuous_sqrt.tendsto 1).comp hbase using 1 <;> norm_num
  have hcos : Tendsto Real.cos (punctured 0) (nhds 1) := by
    simpa using (Real.continuous_cos.tendsto 0).mono_left inf_le_left
  have hcosh : Tendsto Real.cosh (punctured 0) (nhds 1) := by
    simpa using (Real.continuous_cosh.tendsto 0).mono_left inf_le_left
  have hnum : Tendsto
      (fun x : ℝ => 2 * (Real.sin x / x) ^ 2 * (Real.cosh x + Real.cos x))
      (punctured 0) (nhds 4) := by
    convert (tendsto_const_nhds.mul (sinQuotientLimit.pow 2)).mul
      (hcosh.add hcos) using 1 <;> norm_num
  have hden : Tendsto
      (fun x : ℝ =>
        Real.sqrt (1 + Real.sin x ^ 2) *
          (Real.sqrt (1 + Real.sin x ^ 2) + Real.cos x) *
          ((Real.sinh x / x) ^ 2 + (Real.sin x / x) ^ 2))
      (punctured 0) (nhds 4) := by
    convert (hsqrt.mul (hsqrt.add hcos)).mul
      ((sinhQuotientLimit.pow 2).add (sinQuotientLimit.pow 2)) using 1 <;>
      norm_num
  have ht : Tendsto
      (fun x : ℝ =>
        (2 * (Real.sin x / x) ^ 2 * (Real.cosh x + Real.cos x)) /
          (Real.sqrt (1 + Real.sin x ^ 2) *
            (Real.sqrt (1 + Real.sin x ^ 2) + Real.cos x) *
            ((Real.sinh x / x) ^ 2 + (Real.sin x / x) ^ 2)))
      (punctured 0) (nhds 1) := by
    convert hnum.div hden (by norm_num) using 1 <;> norm_num
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin,
    hcos.eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))]
      with x hx hcx
  have hx0 : x ≠ 0 := by
    simpa [punctured] using hx
  have hs0 : 0 < Real.sqrt (1 + Real.sin x ^ 2) :=
    Real.sqrt_pos.2 (by nlinarith [sq_nonneg (Real.sin x)])
  have hsp : 0 < Real.sqrt (1 + Real.sin x ^ 2) + Real.cos x := by
    exact add_pos hs0 hcx
  have hcosh : 1 < Real.cosh x := (Real.one_lt_cosh).2 hx0
  have hc_le : Real.cos x ≤ 1 := Real.cos_le_one x
  have hdif : 0 < Real.cosh x - Real.cos x := by nlinarith
  have hcp : 0 < Real.cosh x + Real.cos x := by nlinarith
  have hsq := Real.sq_sqrt (show 0 ≤ 1 + Real.sin x ^ 2 by positivity)
  have htrig := Real.sin_sq_add_cos_sq x
  have hhyper := Real.cosh_sq_sub_sinh_sq x
  have hnumid :
      (Real.sqrt (1 + Real.sin x ^ 2) - Real.cos x) *
        (Real.sqrt (1 + Real.sin x ^ 2) + Real.cos x) =
          2 * Real.sin x ^ 2 := by
    nlinarith
  have hdenid :
      (Real.cosh x - Real.cos x) * (Real.cosh x + Real.cos x) =
        Real.sinh x ^ 2 + Real.sin x ^ 2 := by
    nlinarith
  have hsum : 0 < Real.sinh x ^ 2 + Real.sin x ^ 2 := by
    rw [← hdenid]
    exact mul_pos hdif hcp
  have hnumrw :
      1 - Real.cos x / Real.sqrt (1 + Real.sin x ^ 2) =
        2 * Real.sin x ^ 2 /
          (Real.sqrt (1 + Real.sin x ^ 2) *
            (Real.sqrt (1 + Real.sin x ^ 2) + Real.cos x)) := by
    field_simp [ne_of_gt hs0, ne_of_gt hsp] <;> nlinarith [hnumid]
  have hdenrw :
      Real.cosh x - Real.cos x =
        (Real.sinh x ^ 2 + Real.sin x ^ 2) /
          (Real.cosh x + Real.cos x) := by
    field_simp [ne_of_gt hcp] <;> nlinarith [hdenid]
  unfold firstDerivativeStage
  rw [hnumrw, hdenrw]
  field_simp [hx0, ne_of_gt hs0, ne_of_gt hsp, ne_of_gt hcp,
    ne_of_gt hsum] <;> ring

theorem gap1 : Tendsto logarithmicStage (punctured 0) (nhds 1) := by
  have hf0 : Tendsto (fun x : ℝ => x - Real.arsinh (Real.sin x)) (nhds 0) (nhds 0) := by
    have h := (hasDerivAt_id 0).sub
      ((Real.hasDerivAt_arsinh (Real.sin 0)).comp 0 (Real.hasDerivAt_sin 0))
    simpa using h.continuousAt.tendsto
  have hg0 : Tendsto (fun x : ℝ => Real.sinh x - Real.sin x) (nhds 0) (nhds 0) := by
    have h := (Real.hasDerivAt_sinh 0).sub (Real.hasDerivAt_sin 0)
    simpa using h.continuousAt.tendsto
  have hf' : ∀ᶠ x : ℝ in nhds 0,
      HasDerivAt (fun y : ℝ => y - Real.arsinh (Real.sin y))
        (1 - Real.cos x / Real.sqrt (1 + Real.sin x ^ 2)) x := by
    filter_upwards [] with x
    simpa [div_eq_mul_inv, pow_two, mul_comm] using
      (hasDerivAt_id x).sub
        ((Real.hasDerivAt_arsinh (Real.sin x)).comp x (Real.hasDerivAt_sin x))
  have hg' : ∀ᶠ x : ℝ in nhds 0,
      HasDerivAt (fun y : ℝ => Real.sinh y - Real.sin y)
        (Real.cosh x - Real.cos x) x := by
    filter_upwards [] with x
    exact (Real.hasDerivAt_sinh x).sub (Real.hasDerivAt_sin x)
  have hgne : ∀ᶠ x : ℝ in punctured 0, Real.cosh x - Real.cos x ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := by
      simpa [punctured] using hx
    have hcosh : 1 < Real.cosh x := (Real.one_lt_cosh).2 hx0
    have hcos : Real.cos x ≤ 1 := Real.cos_le_one x
    nlinarith
  have hratio : Tendsto
      (fun x : ℝ =>
        (1 - Real.cos x / Real.sqrt (1 + Real.sin x ^ 2)) /
          (Real.cosh x - Real.cos x))
      (punctured 0) (nhds 1) := by
    simpa [firstDerivativeStage] using derivativeStageLimit
  have hGTle : nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ punctured 0 := by
    unfold punctured
    apply nhdsWithin_mono
    intro x hx
    simp only [Set.mem_Ioi] at hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    linarith
  have hLTle : nhdsWithin (0 : ℝ) (Set.Iio 0) ≤ punctured 0 := by
    unfold punctured
    apply nhdsWithin_mono
    intro x hx
    simp only [Set.mem_Iio] at hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    linarith
  have hGTnhds : nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhds 0 := inf_le_left
  have hLTnhds : nhdsWithin (0 : ℝ) (Set.Iio 0) ≤ nhds 0 := inf_le_left
  have hf0GT := hf0.mono_left hGTnhds
  have hg0GT := hg0.mono_left hGTnhds
  have hf'GT := hf'.filter_mono hGTnhds
  have hg'GT := hg'.filter_mono hGTnhds
  have hgneGT := hgne.filter_mono hGTle
  have hratioGT := hratio.mono_left hGTle
  have hsGT : Tendsto
      (fun x : ℝ =>
        (x - Real.arsinh (Real.sin x)) / (Real.sinh x - Real.sin x))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    apply HasDerivAt.lhopital_zero_nhdsGT
      (f' := fun x : ℝ => 1 - Real.cos x / Real.sqrt (1 + Real.sin x ^ 2))
      (g' := fun x : ℝ => Real.cosh x - Real.cos x)
    all_goals assumption
  have hf0LT := hf0.mono_left hLTnhds
  have hg0LT := hg0.mono_left hLTnhds
  have hf'LT := hf'.filter_mono hLTnhds
  have hg'LT := hg'.filter_mono hLTnhds
  have hgneLT := hgne.filter_mono hLTle
  have hratioLT := hratio.mono_left hLTle
  have hsLT : Tendsto
      (fun x : ℝ =>
        (x - Real.arsinh (Real.sin x)) / (Real.sinh x - Real.sin x))
      (nhdsWithin 0 (Set.Iio 0)) (nhds 1) := by
    apply HasDerivAt.lhopital_zero_nhdsLT
      (f' := fun x : ℝ => 1 - Real.cos x / Real.sqrt (1 + Real.sin x ^ 2))
      (g' := fun x : ℝ => Real.cosh x - Real.cos x)
    all_goals assumption
  have hsets : ({0} : Set ℝ)ᶜ = Set.Iio 0 ∪ Set.Ioi 0 := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_union,
      Set.mem_Iio, Set.mem_Ioi]
    constructor
    · intro hx
      exact lt_or_gt_of_ne hx
    · intro hx
      rcases hx with hx | hx <;> linarith
  have hs : Tendsto
      (fun x : ℝ =>
        (x - Real.arsinh (Real.sin x)) / (Real.sinh x - Real.sin x))
      (punctured 0) (nhds 1) := by
    rw [punctured, hsets, nhdsWithin_union]
    exact hsLT.sup hsGT
  apply hs.congr'
  filter_upwards [] with x
  have hsqrt : Real.sqrt (1 + Real.sinh x ^ 2) = Real.cosh x := by
    have hsq : 1 + Real.sinh x ^ 2 = Real.cosh x ^ 2 := by
      nlinarith [Real.cosh_sq_sub_sinh_sq x]
    rw [hsq, Real.sqrt_sq_eq_abs, abs_of_pos (Real.cosh_pos x)]
  have hlog : Real.log (Real.sinh x + Real.cosh x) = x := by
    calc
      Real.log (Real.sinh x + Real.cosh x) = Real.arsinh (Real.sinh x) := by
        simp [Real.arsinh, hsqrt]
      _ = x := Real.arsinh_sinh x
  unfold logarithmicStage
  rw [hlog]
  rfl
theorem gap2 : Tendsto firstDerivativeStage (punctured 0) (nhds 1) := by
  exact derivativeStageLimit
theorem gap3 : Tendsto firstDerivativeStage (punctured 0) (nhds 1) := by
  exact gap2
theorem gap4 : Tendsto secondDerivativeStage (punctured 0) (nhds 1) := by
  have hrpow := rpowStageLimit (3 / 2 : ℝ)
  have ht : Tendsto
      (fun x : ℝ =>
        (2 * (Real.sin x / x) /
          Real.rpow (1 + Real.sin x ^ 2) (3 / 2 : ℝ)) /
          (Real.sinh x / x + Real.sin x / x))
      (punctured 0) (nhds 1) := by
    have hn : Tendsto
        (fun x : ℝ => 2 * (Real.sin x / x) /
          Real.rpow (1 + Real.sin x ^ 2) (3 / 2 : ℝ))
        (punctured 0) (nhds 2) := by
      convert (tendsto_const_nhds.mul sinQuotientLimit).div hrpow (by norm_num) using 1 <;>
        norm_num
    convert hn.div (sinhQuotientLimit.add sinQuotientLimit) (by norm_num) using 1 <;>
      norm_num
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := by
    simpa [punctured] using hx
  have hb : 0 < 1 + Real.sin x ^ 2 := by
    nlinarith [sq_nonneg (Real.sin x)]
  have hr : Real.rpow (1 + Real.sin x ^ 2) (3 / 2 : ℝ) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hb _)
  unfold secondDerivativeStage
  field_simp [hx0, hr]
theorem gap5 : Tendsto finalStage (punctured 0) (nhds 1) := by
  have hsin : Tendsto Real.sin (punctured 0) (nhds 0) := by
    simpa using (Real.continuous_sin.tendsto 0).mono_left inf_le_left
  have hcos : Tendsto Real.cos (punctured 0) (nhds 1) := by
    simpa using (Real.continuous_cos.tendsto 0).mono_left inf_le_left
  have hcosh : Tendsto Real.cosh (punctured 0) (nhds 1) := by
    simpa using (Real.continuous_cosh.tendsto 0).mono_left inf_le_left
  have hr3 := rpowStageLimit (3 / 2 : ℝ)
  have hr5 := rpowStageLimit (5 / 2 : ℝ)
  have ha : Tendsto
      (fun x : ℝ => Real.cos x /
        Real.rpow (1 + Real.sin x ^ 2) (3 / 2 : ℝ))
      (punctured 0) (nhds 1) := by
    convert hcos.div hr3 (by norm_num) using 1 <;> norm_num
  have hb : Tendsto
      (fun x : ℝ => 3 * Real.sin x ^ 2 * Real.cos x /
        Real.rpow (1 + Real.sin x ^ 2) (5 / 2 : ℝ))
      (punctured 0) (nhds 0) := by
    convert (((tendsto_const_nhds.mul (hsin.pow 2)).mul hcos).div hr5
      (by norm_num)) using 1 <;> norm_num
  unfold finalStage
  convert tendsto_const_nhds.mul
    ((ha.sub hb).div (hcosh.add hcos) (by norm_num)) using 1 <;> norm_num
theorem gap6 : Tendsto finalStage (punctured 0) (nhds 1) := by
  exact gap5
theorem gap7 : Tendsto original (punctured 0) (nhds 1) := by
  apply gap1.congr'
  filter_upwards [] with x
  have hsqrt : Real.sqrt (1 + Real.sinh x ^ 2) = Real.cosh x := by
    have hsq : 1 + Real.sinh x ^ 2 = Real.cosh x ^ 2 := by
      nlinarith [Real.cosh_sq_sub_sinh_sq x]
    rw [hsq, Real.sqrt_sq_eq_abs, abs_of_pos (Real.cosh_pos x)]
  have hlog : Real.log (Real.sinh x + Real.cosh x) = x := by
    calc
      Real.log (Real.sinh x + Real.cosh x) = Real.arsinh (Real.sinh x) := by
        simp [Real.arsinh, hsqrt]
      _ = x := Real.arsinh_sinh x
  unfold original logarithmicStage
  rw [Real.arsinh_sinh, hlog]
  rfl

end
end ProofGap.Exercise1335
