import ProofGapLean.Prelude.Analysis
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace ProofGap.Exercise2596

noncomputable section

def nthRoot (n : ℕ) (x : ℝ) : ℝ :=
  Real.rpow x (1 / (n : ℝ))

def targetTerm (n : ℕ) : ℝ :=
  (n : ℝ) * Real.cos ((n : ℝ) * Real.pi / 3) ^ 2 / (2 : ℝ) ^ n

def comparisonTerm (n : ℕ) : ℝ := (n : ℝ) / (2 : ℝ) ^ n
def comparisonRoot (n : ℕ) : ℝ := nthRoot n n / 2

private theorem cos_nat_mul_pi_div_three_ne_zero (n : ℕ) :
    Real.cos ((n : ℝ) * Real.pi / 3) ≠ 0 := by
  apply Real.cos_ne_zero_iff.mpr
  intro k hk
  have hmul : ((n : ℝ) * Real.pi) * 2 =
      ((2 * (k : ℝ) + 1) * Real.pi) * 3 :=
    (div_eq_div_iff (by norm_num : (3 : ℝ) ≠ 0)
      (by norm_num : (2 : ℝ) ≠ 0)).mp hk
  have hzero :
      ((2 * (n : ℝ) - 3 * (2 * (k : ℝ) + 1)) * Real.pi) = 0 := by
    linear_combination hmul
  have hc : 2 * (n : ℝ) - 3 * (2 * (k : ℝ) + 1) = 0 :=
    (mul_eq_zero.mp hzero).resolve_right Real.pi_ne_zero
  have hcoeff : 2 * (n : ℝ) = 3 * (2 * (k : ℝ) + 1) := sub_eq_zero.mp hc
  have hint : (2 * (n : ℤ) : ℤ) = 3 * (2 * k + 1) := by
    exact_mod_cast hcoeff
  omega

theorem gap1 :
    ∀ n : ℕ, 1 ≤ n → 0 < targetTerm n := by
  intro n hn
  unfold targetTerm
  apply div_pos
  · exact mul_pos (by exact_mod_cast hn)
      (sq_pos_of_ne_zero (cos_nat_mul_pi_div_three_ne_zero n))
  · positivity

theorem gap2
    (hpositive : ∀ n : ℕ, 1 ≤ n → 0 < targetTerm n) :
    ∀ n : ℕ, 1 ≤ n → targetTerm n ≤ comparisonTerm n := by
  intro n hn
  unfold targetTerm comparisonTerm
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hcos := Real.abs_cos_le_one ((n : ℝ) * Real.pi / 3)
  have hcosSq : Real.cos ((n : ℝ) * Real.pi / 3) ^ 2 ≤ (1 : ℝ) := by
    have hsquare := (sq_le_sq
      (a := Real.cos ((n : ℝ) * Real.pi / 3)) (b := (1 : ℝ))).2
      (by simpa using hcos)
    norm_num at hsquare ⊢
    exact hsquare
  calc
    (n : ℝ) * Real.cos ((n : ℝ) * Real.pi / 3) ^ 2 ≤ (n : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left hcosSq (by positivity)
    _ = n := by ring

theorem gap3 :
    ∀ n : ℕ, 1 ≤ n → 0 < comparisonTerm n := by
  intro n hn
  unfold comparisonTerm
  positivity

theorem gap4
    (a : ℕ → ℝ) (ha : ∀ n, a n = comparisonTerm n) :
    ∀ L : ℝ, Tendsto (fun n => nthRoot n (a n)) atTop (nhds L) ↔
      Tendsto comparisonRoot atTop (nhds L) := by
  intro L
  have heq : (fun n ↦ nthRoot n (a n)) =ᶠ[atTop] comparisonRoot := by
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hn0 : n ≠ 0 := by omega
    rw [ha n]
    unfold nthRoot comparisonTerm comparisonRoot
    unfold nthRoot
    rw [one_div]
    have hdiv := Real.div_rpow (show (0 : ℝ) ≤ n by positivity)
      (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) n) ((n : ℝ)⁻¹)
    have hden := Real.pow_rpow_inv_natCast
      (show (0 : ℝ) ≤ 2 by norm_num) hn0
    change Real.rpow ((n : ℝ) / (2 : ℝ) ^ n) ((n : ℝ)⁻¹) =
      Real.rpow (n : ℝ) ((n : ℝ)⁻¹) / 2
    calc
      Real.rpow ((n : ℝ) / (2 : ℝ) ^ n) ((n : ℝ)⁻¹) =
          Real.rpow (n : ℝ) ((n : ℝ)⁻¹) /
            Real.rpow ((2 : ℝ) ^ n) ((n : ℝ)⁻¹) := hdiv
      _ = Real.rpow (n : ℝ) ((n : ℝ)⁻¹) / 2 :=
        congrArg (fun z : ℝ ↦ Real.rpow (n : ℝ) ((n : ℝ)⁻¹) / z) hden
  constructor
  · exact fun h ↦ h.congr' heq
  · exact fun h ↦ h.congr' heq.symm

theorem gap5 :
    Tendsto comparisonRoot atTop (nhds (1 / 2 : ℝ)) := by
  have hlogReal : Tendsto (fun x : ℝ ↦ Real.log x / x) atTop (nhds 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hlogNat : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ) / (n : ℝ))
      atTop (nhds 0) := hlogReal.comp tendsto_natCast_atTop_atTop
  have hexp : Tendsto (fun n : ℕ ↦ Real.exp (Real.log (n : ℝ) / (n : ℝ)))
      atTop (nhds 1) := by
    simpa using Real.continuous_exp.continuousAt.tendsto.comp hlogNat
  have heq : (fun n : ℕ ↦ nthRoot n n) =ᶠ[atTop]
      (fun n : ℕ ↦ Real.exp (Real.log (n : ℝ) / (n : ℝ))) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    unfold nthRoot
    have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
    calc
      Real.rpow (n : ℝ) (1 / (n : ℝ)) =
          Real.exp (Real.log (n : ℝ) * (1 / (n : ℝ))) :=
        Real.rpow_def_of_pos hnreal _
      _ = Real.exp (Real.log (n : ℝ) / (n : ℝ)) := by
        congr 1
        ring
  have hroot : Tendsto (fun n : ℕ ↦ nthRoot n n) atTop (nhds 1) :=
    hexp.congr' heq.symm
  simpa [comparisonRoot] using hroot.div_const 2

theorem gap6 :
    (1 / 2 : ℝ) < 1 := by norm_num

theorem gap7
    (a : ℕ → ℝ) (ha : ∀ n, a n = comparisonTerm n)
    (hroot : ∀ L : ℝ,
      Tendsto (fun n => nthRoot n (a n)) atTop (nhds L) ↔
        Tendsto comparisonRoot atTop (nhds L))
    (hcomparison : Tendsto comparisonRoot atTop (nhds (1 / 2 : ℝ)))
    (hlt : (1 / 2 : ℝ) < 1) :
    Tendsto (fun n => nthRoot n (a n)) atTop (nhds (1 / 2 : ℝ)) ∧
      (1 / 2 : ℝ) < 1 := ⟨(hroot (1 / 2 : ℝ)).mpr hcomparison, hlt⟩

theorem gap8
    (hroot : Tendsto (fun n => nthRoot n (comparisonTerm n)) atTop
      (nhds (1 / 2 : ℝ)))
    (hlt : (1 / 2 : ℝ) < 1) :
    Summable comparisonTerm := by
  have hsum := summable_pow_mul_geometric_of_norm_lt_one
    (R := ℝ) 1 (r := (1 / 2 : ℝ)) (by norm_num)
  simpa [comparisonTerm, one_div_pow, div_eq_mul_inv] using hsum

theorem gap9
    (hpositive : ∀ n : ℕ, 1 ≤ n → 0 < targetTerm n)
    (hcompare : ∀ n : ℕ, 1 ≤ n →
      targetTerm n ≤ comparisonTerm n)
    (hsum : Summable comparisonTerm) :
    Summable targetTerm := by
  apply Summable.of_nonneg_of_le (f := comparisonTerm)
  · intro n
    by_cases hn : 1 ≤ n
    · exact (hpositive n hn).le
    · have : n = 0 := by omega
      subst n
      norm_num [targetTerm]
  · intro n
    by_cases hn : 1 ≤ n
    · exact hcompare n hn
    · have : n = 0 := by omega
      subst n
      norm_num [targetTerm, comparisonTerm]
  · exact hsum

theorem gap10
    (hsum : Summable targetTerm) :
    Summable targetTerm := hsum

end

end ProofGap.Exercise2596
