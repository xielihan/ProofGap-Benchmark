import ProofGapLean.Prelude.Analysis
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise2588

noncomputable section

def nthRoot (n : ℕ) (x : ℝ) : ℝ :=
  Real.rpow x (1 / (n : ℝ))

def comparisonTerm (n : ℕ) : ℝ := 1 / nthRoot n n
def targetTerm (n : ℕ) : ℝ := 1 / nthRoot n (Real.log n)

private theorem tail_ge_cofinite_nat (a : ℕ) :
    ∀ᶠ b : ℕ in Filter.cofinite, a ≤ b := by
  apply Filter.eventually_cofinite.2
  simpa only [not_le] using (Set.finite_Iio a)

theorem gap1 :
    ∀ n : ℕ, n ≥ 2 → Real.log n < (n : ℝ) := by
  intro n hn
  have hnreal : (2 : ℝ) ≤ (n : ℝ) := Nat.cast_le.2 hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hnne : (n : ℝ) ≠ 1 := by linarith
  have hbound := Real.log_lt_sub_one_of_pos hnpos hnne
  linarith

theorem gap2
    (hlog : ∀ n : ℕ, n ≥ 2 → Real.log n < (n : ℝ)) :
    ∀ n : ℕ, n ≥ 2 → targetTerm n > comparisonTerm n := by
  intro n hn
  have hnreal : (2 : ℝ) ≤ (n : ℝ) := Nat.cast_le.2 hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hone : (1 : ℝ) < (n : ℝ) := by linarith
  have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos hone
  have hexponent : 0 < (1 / (n : ℝ)) := one_div_pos.mpr hnpos
  have hrootlt :
      Real.rpow (Real.log (n : ℝ)) (1 / (n : ℝ)) <
        Real.rpow (n : ℝ) (1 / (n : ℝ)) :=
    Real.rpow_lt_rpow (le_of_lt hlogpos) (hlog n hn) hexponent
  have hrootpos :
      0 < Real.rpow (Real.log (n : ℝ)) (1 / (n : ℝ)) :=
    Real.rpow_pos_of_pos hlogpos _
  unfold targetTerm comparisonTerm nthRoot
  exact one_div_lt_one_div_of_lt hrootpos hrootlt

theorem gap3 :
    ∀ n : ℕ, n ≥ 2 → comparisonTerm n > 0 := by
  intro n hn
  have hnreal : (2 : ℝ) ≤ (n : ℝ) := Nat.cast_le.2 hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  unfold comparisonTerm nthRoot
  exact one_div_pos.mpr (Real.rpow_pos_of_pos hnpos _)

theorem gap4
    (hcompare : ∀ n : ℕ, n ≥ 2 →
      targetTerm n > comparisonTerm n)
    (hpositive : ∀ n : ℕ, n ≥ 2 → comparisonTerm n > 0) :
    ∀ n : ℕ, n ≥ 2 → targetTerm n > 0 := by
  intro n hn
  exact lt_trans (hpositive n hn) (hcompare n hn)

theorem gap5 :
    Tendsto comparisonTerm atTop (nhds 1) := by
  have hreal :
      Tendsto (fun x : ℝ => Real.log x / x) atTop (nhds 0) := by
    simpa using Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hquot :
      Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ)) atTop (nhds 0) :=
    Filter.Tendsto.comp hreal tendsto_natCast_atTop_atTop
  have hneg :
      Tendsto (fun n : ℕ => -(Real.log (n : ℝ) / (n : ℝ))) atTop (nhds 0) := by
    simpa using hquot.neg
  have hexp :
      Tendsto
        (fun n : ℕ => Real.exp (-(Real.log (n : ℝ) / (n : ℝ))))
        atTop (nhds (Real.exp 0)) :=
    (Real.continuous_exp.continuousAt.tendsto).comp hneg
  have htail : ∀ᶠ n : ℕ in atTop, 1 ≤ n := by
    exact Filter.eventually_atTop.2 ⟨1, fun n hn => hn⟩
  have hformula :
      comparisonTerm =ᶠ[atTop]
        (fun n : ℕ => Real.exp (-(Real.log (n : ℝ) / (n : ℝ)))) := by
    filter_upwards [htail] with n hn
    have hnpos : (0 : ℝ) < (n : ℝ) :=
      Nat.cast_pos.2 (lt_of_lt_of_le Nat.zero_lt_one hn)
    have hrpow :
        Real.rpow (n : ℝ) (1 / (n : ℝ)) =
          Real.exp (Real.log (n : ℝ) * (1 / (n : ℝ))) := by
      exact Real.rpow_def_of_pos hnpos (1 / (n : ℝ))
    unfold comparisonTerm nthRoot
    calc
      1 / Real.rpow (n : ℝ) (1 / (n : ℝ)) =
          1 / Real.exp (Real.log (n : ℝ) * (1 / (n : ℝ))) := by rw [hrpow]
      _ = Real.exp (-(Real.log (n : ℝ) * (1 / (n : ℝ)))) := by
        simpa only [one_div] using
          (Real.exp_neg (Real.log (n : ℝ) * (1 / (n : ℝ)))).symm
      _ = Real.exp (-(Real.log (n : ℝ) / (n : ℝ))) := by
        simp only [div_eq_mul_inv, one_mul]
  have hrhs :
      Tendsto
        (fun n : ℕ => Real.exp (-(Real.log (n : ℝ) / (n : ℝ))))
        atTop (nhds 1) := by
    simpa using hexp
  exact hrhs.congr' hformula.symm

theorem gap6 :
    (1 : ℝ) ≠ 0 := by
  exact one_ne_zero

theorem gap7
    (hlim : Tendsto comparisonTerm atTop (nhds 1))
    (hne : (1 : ℝ) ≠ 0) :
    ¬ Tendsto comparisonTerm atTop (nhds 0) := by
  intro hzero
  exact hne (tendsto_nhds_unique hlim hzero)

theorem gap8
    (hnotzero : ¬ Tendsto comparisonTerm atTop (nhds 0)) :
    ¬ Summable comparisonTerm := by
  intro hsum
  exact hnotzero hsum.tendsto_atTop_zero

theorem gap9
    (hcompare : ∀ n : ℕ, n ≥ 2 →
      targetTerm n > comparisonTerm n)
    (hcomparisonPos : ∀ n : ℕ, n ≥ 2 → comparisonTerm n > 0)
    (htargetPos : ∀ n : ℕ, n ≥ 2 → targetTerm n > 0)
    (hdiv : ¬ Summable comparisonTerm) :
    ¬ Summable targetTerm := by
  intro hsum
  apply hdiv
  refine Summable.of_norm_bounded_eventually hsum ?_
  filter_upwards [tail_ge_cofinite_nat (2 : ℕ)] with n hn
  simpa [Real.norm_eq_abs, abs_of_pos (hcomparisonPos n hn),
    abs_of_pos (htargetPos n hn)] using
      (le_of_lt (hcompare n hn))

theorem gap10
    (hdiv : ¬ Summable targetTerm) :
    ¬ Summable targetTerm := by
  exact hdiv

end

end ProofGap.Exercise2588
