import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace ProofGap.Exercise3859

noncomputable section

open Filter MeasureTheory
open scoped Interval

def HasImproperIntegral (a : ℝ) (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Tendsto (fun b : ℝ => ∫ x in a..b, f x) atTop (nhds L)

def improperIntegral (a : ℝ) (f : ℝ → ℝ) : ℝ :=
  sInf {L : ℝ | HasImproperIntegral a f L}

def gammaIntegrand (q t : ℝ) : ℝ :=
  Real.rpow t (q - 1) * Real.exp (-t)

private theorem improperIntegral_eq_of_has
    {a L : ℝ} {f : ℝ → ℝ} (h : HasImproperIntegral a f L) :
    improperIntegral a f = L := by
  have hset : {K : ℝ | HasImproperIntegral a f K} = {L} := by
    ext K
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro hK
      exact tendsto_nhds_unique hK h
    · rintro rfl
      exact h
  unfold improperIntegral
  rw [hset]
  simp

private theorem exp_set_integral (n : ℝ) (hn : 0 < n) :
    (∫ x in Set.Ioi (0 : ℝ), Real.exp (-Real.rpow x n)) =
      1 / n * Real.Gamma (1 / n) := by
  simpa only [Real.rpow_zero, one_mul, zero_add] using
    (integral_rpow_mul_exp_neg_rpow
      (p := n) (q := 0) hn neg_one_lt_zero)

private theorem exp_integrable (n : ℝ) (hn : 0 < n) :
    IntegrableOn (fun x => Real.exp (-Real.rpow x n)) (Set.Ioi 0) := by
  by_contra h
  have hzero :
      (∫ x in Set.Ioi (0 : ℝ), Real.exp (-Real.rpow x n)) = 0 :=
    integral_undef h
  have hq : 0 < 1 / n := one_div_pos.mpr hn
  have hpos : 0 < 1 / n * Real.Gamma (1 / n) :=
    mul_pos hq (Real.Gamma_pos_of_pos hq)
  exact (ne_of_gt hpos) ((exp_set_integral n hn).symm.trans hzero)

private theorem exp_has_improper_integral (n : ℝ) (hn : 0 < n) :
    HasImproperIntegral 0 (fun x => Real.exp (-Real.rpow x n))
      (1 / n * Real.Gamma (1 / n)) := by
  unfold HasImproperIntegral
  rw [← exp_set_integral n hn]
  exact intervalIntegral_tendsto_integral_Ioi 0
    (exp_integrable n hn) tendsto_id

private theorem gamma_set_integral (q : ℝ) (hq : 0 < q) :
    (∫ t in Set.Ioi (0 : ℝ), gammaIntegrand q t) = Real.Gamma q := by
  symm
  simpa [gammaIntegrand, mul_comm] using Real.Gamma_eq_integral hq

private theorem gamma_integrable (q : ℝ) (hq : 0 < q) :
    IntegrableOn (gammaIntegrand q) (Set.Ioi 0) := by
  refine (Real.GammaIntegral_convergent hq).congr_fun ?_ measurableSet_Ioi
  intro x hx
  simp [gammaIntegrand, mul_comm]

private theorem gamma_has_improper_integral (q : ℝ) (hq : 0 < q) :
    HasImproperIntegral 0 (gammaIntegrand q) (Real.Gamma q) := by
  unfold HasImproperIntegral
  rw [← gamma_set_integral q hq]
  exact intervalIntegral_tendsto_integral_Ioi 0
    (gamma_integrable q hq) tendsto_id

theorem gap1 (n : ℝ) (hn : 0 < n) :
    improperIntegral 0 (fun x => Real.exp (-Real.rpow x n)) =
      1 / n * improperIntegral 0 (gammaIntegrand (1 / n)) := by
  have hq : 0 < 1 / n := one_div_pos.mpr hn
  rw [improperIntegral_eq_of_has (exp_has_improper_integral n hn)]
  rw [improperIntegral_eq_of_has (gamma_has_improper_integral (1 / n) hq)]

theorem gap2 (n : ℝ) (hn : 0 < n) :
    1 / n * improperIntegral 0 (gammaIntegrand (1 / n)) =
      1 / n * Real.Gamma (1 / n) := by
  have hq : 0 < 1 / n := one_div_pos.mpr hn
  rw [improperIntegral_eq_of_has (gamma_has_improper_integral (1 / n) hq)]

theorem gap3 (n : ℝ) (hn : 0 < n) :
    improperIntegral 0 (fun x => Real.exp (-Real.rpow x n)) =
      1 / n * Real.Gamma (1 / n) := by
  calc
    improperIntegral 0 (fun x => Real.exp (-Real.rpow x n)) =
        1 / n * improperIntegral 0 (gammaIntegrand (1 / n)) :=
      gap1 n hn
    _ = 1 / n * Real.Gamma (1 / n) := gap2 n hn

theorem gap4 (n : ℝ) :
    0 < 1 / n ↔ 0 < n := by
  exact one_div_pos

end

end ProofGap.Exercise3859
