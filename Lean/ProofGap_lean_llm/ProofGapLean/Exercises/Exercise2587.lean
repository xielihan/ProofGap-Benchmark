import ProofGapLean.Prelude.Analysis
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Defs.Filter
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise2587

noncomputable section

def targetTerm (n : ℕ) : ℝ :=
  Real.rpow (n : ℝ) ((n : ℝ) + 1 / (n : ℝ)) /
    Real.rpow ((n : ℝ) + 1 / (n : ℝ)) n

def intermediateTerm (n : ℕ) : ℝ :=
  (n : ℝ) ^ n * Real.rpow n (1 / (n : ℝ)) /
    ((n : ℝ) + 1) ^ n

def lowerTerm (n : ℕ) : ℝ :=
  Real.rpow (1 + 1 / (n : ℝ)) (-(n : ℝ)) *
    Real.rpow n (1 / (n : ℝ))

private theorem rpow_neg_nat_eq_inv_pow
    (x : ℝ) (n : ℕ) (hx : 0 < x) :
    Real.rpow x (-(n : ℝ)) = (x ^ n)⁻¹ := by
  have hrpowPos :
      Real.rpow x (n : ℝ) =
        Real.exp (Real.log x * (n : ℝ)) := by
    exact Real.rpow_def_of_pos hx (n : ℝ)
  calc
    Real.rpow x (-(n : ℝ)) =
        Real.exp (Real.log x * (-(n : ℝ))) := by
      exact Real.rpow_def_of_pos hx (-(n : ℝ))
    _ = Real.exp (-(Real.log x * (n : ℝ))) := by
      congr 1
      ring
    _ = (Real.exp (Real.log x * (n : ℝ)))⁻¹ := by
      rw [Real.exp_neg]
    _ = (Real.rpow x (n : ℝ))⁻¹ := by
      exact (congrArg (fun t : ℝ => t⁻¹) hrpowPos).symm
    _ = (x ^ n)⁻¹ := by
      simpa [abs_of_pos hx] using
        congrArg (fun t : ℝ => t⁻¹) (Real.rpow_natCast x n)

theorem gap1 :
    ∀ n : ℕ, 1 ≤ n → targetTerm n ≥ intermediateTerm n := by
  intro n hn
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hnreal : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn
  have hfrac : 1 / (n : ℝ) ≤ 1 := by
    exact (div_le_one hnpos).2 hnreal
  have hbasele : (n : ℝ) + 1 / (n : ℝ) ≤ (n : ℝ) + 1 := by
    simpa [add_comm] using add_le_add_left hfrac (n : ℝ)
  have hbasepos : 0 < (n : ℝ) + 1 / (n : ℝ) := by
    positivity
  have hpowle :
      ((n : ℝ) + 1 / (n : ℝ)) ^ n ≤ ((n : ℝ) + 1) ^ n := by
    exact pow_le_pow_left₀ hbasepos.le hbasele n
  have hrpowNat :
      Real.rpow (n : ℝ) (n : ℝ) = (n : ℝ) ^ n := by
    simpa [abs_of_pos hnpos] using
      (Real.rpow_natCast (n : ℝ) n)
  have hnum :
      Real.rpow (n : ℝ) ((n : ℝ) + 1 / (n : ℝ)) =
        (n : ℝ) ^ n * Real.rpow (n : ℝ) (1 / (n : ℝ)) := by
    calc
      Real.rpow (n : ℝ) ((n : ℝ) + 1 / (n : ℝ)) =
          Real.rpow (n : ℝ) (n : ℝ) *
            Real.rpow (n : ℝ) (1 / (n : ℝ)) := by
        simpa only using
          (Real.rpow_add hnpos (n : ℝ) (1 / (n : ℝ)))
      _ = (n : ℝ) ^ n * Real.rpow (n : ℝ) (1 / (n : ℝ)) := by
        rw [hrpowNat]
  have hden :
      Real.rpow ((n : ℝ) + 1 / (n : ℝ)) (n : ℝ) =
        ((n : ℝ) + 1 / (n : ℝ)) ^ n := by
    simpa [abs_of_pos hbasepos] using
      (Real.rpow_natCast ((n : ℝ) + 1 / (n : ℝ)) n)
  have hnumNonneg :
      0 ≤ (n : ℝ) ^ n * Real.rpow (n : ℝ) (1 / (n : ℝ)) := by
    exact
      (mul_pos (pow_pos hnpos n)
        (Real.rpow_pos_of_pos hnpos _)).le
  unfold targetTerm intermediateTerm
  rw [hnum, hden]
  apply
    (div_le_div_iff₀ (pow_pos (by positivity) n)
      (pow_pos hbasepos n)).2
  exact mul_le_mul_of_nonneg_left hpowle hnumNonneg

theorem gap2
    (hcompare : ∀ n : ℕ, 1 ≤ n →
      targetTerm n ≥ intermediateTerm n) :
    ∀ n : ℕ, 1 ≤ n → intermediateTerm n = lowerTerm n := by
  intro n hn
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hbasepos : 0 < 1 + 1 / (n : ℝ) := by
    positivity
  have hb : 1 + 1 / (n : ℝ) = ((n : ℝ) + 1) / (n : ℝ) := by
    field_simp [ne_of_gt hnpos]
  unfold intermediateTerm lowerTerm
  rw [rpow_neg_nat_eq_inv_pow _ n hbasepos, hb, div_pow, inv_div]
  ring

theorem gap3
    (hidentity : ∀ n : ℕ, 1 ≤ n →
      intermediateTerm n = lowerTerm n) :
    ∀ n : ℕ, 1 ≤ n → lowerTerm n > 0 := by
  intro n hn
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hbasepos : 0 < 1 + 1 / (n : ℝ) := by
    positivity
  unfold lowerTerm
  exact mul_pos (Real.rpow_pos_of_pos hbasepos _) (Real.rpow_pos_of_pos hnpos _)

theorem gap4
    (hcompare : ∀ n : ℕ, 1 ≤ n →
      targetTerm n ≥ intermediateTerm n)
    (hidentity : ∀ n : ℕ, 1 ≤ n →
      intermediateTerm n = lowerTerm n)
    (hlowerPos : ∀ n : ℕ, 1 ≤ n → lowerTerm n > 0) :
    ∀ n : ℕ, 1 ≤ n → targetTerm n > 0 := by
  intro n hn
  have hc := hcompare n hn
  rw [hidentity n hn] at hc
  exact lt_of_lt_of_le (hlowerPos n hn) hc

theorem gap5 :
    Tendsto lowerTerm atTop (nhds (1 / Real.exp 1)) := by
  have hcast :
      Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hinvReal :
      Tendsto (fun x : ℝ => x⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  have hinvNat :
      Tendsto (fun n : ℕ => (1 / (n : ℝ) : ℝ)) atTop (nhds 0) := by
    simpa only [one_div] using hinvReal.comp hcast
  have hone :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have hlowerLim :
      Tendsto (fun n : ℕ => 1 - 1 / (n : ℝ)) atTop (nhds 1) := by
    simpa using hone.sub hinvNat
  have hscaledLogAux :
      Tendsto
        (fun n : ℕ =>
          if n = 0 then (1 : ℝ)
          else (n : ℝ) * Real.log (1 + 1 / (n : ℝ)))
        atTop (nhds 1) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      hlowerLim hone ?_ ?_
    · intro n
      by_cases hnzero : n = 0
      · subst n
        norm_num
      · simp only [hnzero, if_false]
        have hn : 1 ≤ n := by omega
        have hnpos : 0 < (n : ℝ) := by
          exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
        have hbasepos : 0 < 1 + 1 / (n : ℝ) := by
          positivity
        have hinvlog :
            Real.log ((1 + 1 / (n : ℝ))⁻¹) ≤
              (1 + 1 / (n : ℝ))⁻¹ - 1 :=
          Real.log_le_sub_one_of_pos (inv_pos.mpr hbasepos)
        have hloglower :
            1 - (1 + 1 / (n : ℝ))⁻¹ ≤
              Real.log (1 + 1 / (n : ℝ)) := by
          rw [Real.log_inv] at hinvlog
          linarith
        have hmul :
            (n : ℝ) * (1 - (1 + 1 / (n : ℝ))⁻¹) ≤
              (n : ℝ) * Real.log (1 + 1 / (n : ℝ)) :=
          mul_le_mul_of_nonneg_left hloglower hnpos.le
        have hdenpos : 0 < (n : ℝ) + 1 := by
          positivity
        have hb :
            1 + 1 / (n : ℝ) = ((n : ℝ) + 1) / (n : ℝ) := by
          field_simp [ne_of_gt hnpos]
        have hrewrite :
            (n : ℝ) * (1 - (1 + 1 / (n : ℝ))⁻¹) =
              1 - 1 / ((n : ℝ) + 1) := by
          rw [hb, inv_div]
          field_simp [ne_of_gt hnpos, ne_of_gt hdenpos] <;> ring
        have hrecip :
            1 / ((n : ℝ) + 1) ≤ 1 / (n : ℝ) := by
          apply (div_le_div_iff₀ hdenpos hnpos).2
          linarith
        calc
          1 - 1 / (n : ℝ) ≤ 1 - 1 / ((n : ℝ) + 1) := by
            linarith
          _ = (n : ℝ) * (1 - (1 + 1 / (n : ℝ))⁻¹) :=
            hrewrite.symm
          _ ≤ (n : ℝ) * Real.log (1 + 1 / (n : ℝ)) := hmul
    · intro n
      by_cases hnzero : n = 0
      · subst n
        norm_num
      · simp only [hnzero, if_false]
        have hn : 1 ≤ n := by omega
        have hnpos : 0 < (n : ℝ) := by
          exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
        have hbasepos : 0 < 1 + 1 / (n : ℝ) := by
          positivity
        have hlogupper :
            Real.log (1 + 1 / (n : ℝ)) ≤
              (1 + 1 / (n : ℝ)) - 1 :=
          Real.log_le_sub_one_of_pos hbasepos
        calc
          (n : ℝ) * Real.log (1 + 1 / (n : ℝ)) ≤
              (n : ℝ) * ((1 + 1 / (n : ℝ)) - 1) :=
            mul_le_mul_of_nonneg_left hlogupper hnpos.le
          _ = 1 := by
            field_simp [ne_of_gt hnpos] <;> ring
  have hscaledLog :
      Tendsto
        (fun n : ℕ =>
          (n : ℝ) * Real.log (1 + 1 / (n : ℝ)))
        atTop (nhds 1) := by
    refine hscaledLogAux.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
    have hnzero : n ≠ 0 := by omega
    simp [hnzero]
  have hscaledLogComm :
      Tendsto
        (fun n : ℕ =>
          Real.log (1 + 1 / (n : ℝ)) * (n : ℝ))
        atTop (nhds 1) := by
    have heq :
        (fun n : ℕ =>
          Real.log (1 + 1 / (n : ℝ)) * (n : ℝ)) =
          (fun n : ℕ =>
            (n : ℝ) * Real.log (1 + 1 / (n : ℝ))) := by
      funext n
      ring
    rw [heq]
    exact hscaledLog
  have hpowExp :
      Tendsto
        (fun n : ℕ =>
          Real.exp (Real.log (1 + 1 / (n : ℝ)) * (n : ℝ)))
        atTop (nhds (Real.exp 1)) := by
    simpa using (Real.continuous_exp.tendsto 1).comp hscaledLogComm
  have hrpowExpEq :
      (fun n : ℕ =>
        Real.rpow (1 + 1 / (n : ℝ)) (n : ℝ)) =
        (fun n : ℕ =>
          Real.exp (Real.log (1 + 1 / (n : ℝ)) * (n : ℝ))) := by
    funext n
    have hbasepos : 0 < 1 + 1 / (n : ℝ) := by
      positivity
    exact Real.rpow_def_of_pos hbasepos (n : ℝ)
  have hpowR :
      Tendsto
        (fun n : ℕ =>
          Real.rpow (1 + 1 / (n : ℝ)) (n : ℝ))
        atTop (nhds (Real.exp 1)) := by
    rw [hrpowExpEq]
    exact hpowExp
  have hpowEq :
      (fun n : ℕ =>
        Real.rpow (1 + 1 / (n : ℝ)) (n : ℝ)) =
        (fun n : ℕ => (1 + 1 / (n : ℝ)) ^ n) := by
    funext n
    have hbasepos : 0 < 1 + 1 / (n : ℝ) := by
      positivity
    simpa [abs_of_pos hbasepos] using
      (Real.rpow_natCast (1 + 1 / (n : ℝ)) n)
  have hpow :
      Tendsto (fun n : ℕ => (1 + 1 / (n : ℝ)) ^ n) atTop
        (nhds (Real.exp 1)) := by
    rw [← hpowEq]
    exact hpowR
  have hinv :
      Tendsto (fun n : ℕ => ((1 + 1 / (n : ℝ)) ^ n)⁻¹) atTop
        (nhds ((Real.exp 1)⁻¹)) :=
    hpow.inv₀ (ne_of_gt (Real.exp_pos 1))
  have hfirstEq :
      (fun n : ℕ => Real.rpow (1 + 1 / (n : ℝ)) (-(n : ℝ))) =
        (fun n : ℕ => ((1 + 1 / (n : ℝ)) ^ n)⁻¹) := by
    funext n
    have hbasepos : 0 < 1 + 1 / (n : ℝ) := by
      positivity
    exact rpow_neg_nat_eq_inv_pow _ n hbasepos
  have hfirst :
      Tendsto
        (fun n : ℕ => Real.rpow (1 + 1 / (n : ℝ)) (-(n : ℝ)))
        atTop (nhds ((Real.exp 1)⁻¹)) := by
    rw [hfirstEq]
    exact hinv
  have hlogReal :
      Tendsto (fun x : ℝ => Real.log x / x) atTop (nhds 0) := by
    simpa only [id_eq] using
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hlog :
      Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ)) atTop
        (nhds 0) := by
    simpa only [Function.comp_apply] using
      hlogReal.comp tendsto_natCast_atTop_atTop
  have hrootExp :
      Tendsto
        (fun n : ℕ => Real.exp (Real.log (n : ℝ) / (n : ℝ)))
        atTop (nhds 1) := by
    simpa using (Real.continuous_exp.tendsto 0).comp hlog
  have hrootEq :
      (fun n : ℕ => Real.rpow (n : ℝ) (1 / (n : ℝ))) =
        (fun n : ℕ => Real.exp (Real.log (n : ℝ) / (n : ℝ))) := by
    funext n
    by_cases hn : n = 0
    · subst n
      norm_num
    · have hnpos : 0 < (n : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hn
      calc
        Real.rpow (n : ℝ) (1 / (n : ℝ)) =
            Real.exp (Real.log (n : ℝ) * (1 / (n : ℝ))) := by
          exact Real.rpow_def_of_pos hnpos (1 / (n : ℝ))
        _ = Real.exp (Real.log (n : ℝ) / (n : ℝ)) := by
          congr 1
          ring
  have hroot :
      Tendsto (fun n : ℕ => Real.rpow (n : ℝ) (1 / (n : ℝ)))
        atTop (nhds 1) := by
    rw [hrootEq]
    exact hrootExp
  unfold lowerTerm
  simpa [one_div] using hfirst.mul hroot

theorem gap6 :
    (1 / Real.exp 1 : ℝ) ≠ 0 := by
  exact div_ne_zero one_ne_zero (ne_of_gt (Real.exp_pos 1))

theorem gap7
    (hlim : Tendsto lowerTerm atTop (nhds (1 / Real.exp 1)))
    (hne : (1 / Real.exp 1 : ℝ) ≠ 0) :
    ¬ Tendsto lowerTerm atTop (nhds 0) := by
  intro hzero
  apply hne
  exact tendsto_nhds_unique hlim hzero

theorem gap8
    (hnotzero : ¬ Tendsto lowerTerm atTop (nhds 0)) :
    ¬ Summable lowerTerm := by
  intro hs
  exact hnotzero hs.tendsto_atTop_zero

theorem gap9
    (hcompare : ∀ n : ℕ, 1 ≤ n → targetTerm n ≥ intermediateTerm n)
    (hidentity : ∀ n : ℕ, 1 ≤ n →
      intermediateTerm n = lowerTerm n)
    (hlowerPos : ∀ n : ℕ, 1 ≤ n → lowerTerm n > 0)
    (htargetPos : ∀ n : ℕ, 1 ≤ n → targetTerm n > 0)
    (hlowerDiv : ¬ Summable lowerTerm) :
    ¬ Summable targetTerm := by
  intro htarget
  apply hlowerDiv
  rw [← summable_nat_add_iff 1]
  have htargetShift : Summable (fun n : ℕ => targetTerm (n + 1)) := by
    rw [summable_nat_add_iff]
    exact htarget
  refine Summable.of_nonneg_of_le ?_ ?_ htargetShift
  · intro n
    have hn : 1 ≤ n + 1 := by omega
    exact (hlowerPos (n + 1) hn).le
  · intro n
    have hn : 1 ≤ n + 1 := by omega
    have hc := hcompare (n + 1) hn
    rw [hidentity (n + 1) hn] at hc
    exact hc

theorem gap10
    (hdiv : ¬ Summable targetTerm) :
    ¬ Summable targetTerm := by
  exact hdiv

end

end ProofGap.Exercise2587
