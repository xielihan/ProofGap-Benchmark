import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

namespace ProofGap.Exercise2932_12

noncomputable section

open scoped BigOperators Interval

def selfPower (x : ℝ) : ℝ :=
  Real.rpow x x

def exponentialTerm (x : ℝ) (n : ℕ) : ℝ :=
  (x * Real.log x) ^ n / (Nat.factorial n : ℝ)

def integratedTerm (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n / ((n + 1 : ℕ) : ℝ) ^ (n + 1)

def targetIntegral : ℝ :=
  ∫ x in (0 : ℝ)..1, selfPower x

def partialIntegral : ℝ :=
  ∑ n ∈ Finset.range 4, integratedTerm n

def remainder : ℝ :=
  targetIntegral - partialIntegral

def Approx (u v ε : ℝ) : Prop :=
  |u - v| < ε

private theorem hasSum_exponentialTerm (x : ℝ) :
    HasSum (exponentialTerm x) (Real.exp (x * Real.log x)) := by
  have h := NormedSpace.expSeries_div_hasSum_exp (x * Real.log x)
  simpa only [exponentialTerm, Real.exp_eq_exp_ℝ] using h

private def momentIntegrand (n : ℕ) (x : ℝ) : ℝ :=
  x ^ n * Real.log x ^ n

private def gammaIntegrand (n : ℕ) (t : ℝ) : ℝ :=
  t ^ n * Real.exp (-(((n + 1 : ℕ) : ℝ) * t))

private theorem continuous_momentIntegrand (n : ℕ) :
    Continuous (momentIntegrand n) := by
  simpa only [momentIntegrand, mul_pow] using Real.continuous_mul_log.pow n

private theorem integral_gammaIntegrand (n : ℕ) :
    (∫ t : ℝ in Set.Ioi 0, gammaIntegrand n t) =
      (Nat.factorial n : ℝ) / ((n + 1 : ℕ) : ℝ) ^ (n + 1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := ((n + 1 : ℕ) : ℝ)) (r := ((n + 1 : ℕ) : ℝ))
    (by positivity) (by positivity)
  convert h using 1
  · apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    simp only [gammaIntegrand]
    have ht0 : 0 ≤ t := ht.le
    rw [show ((n + 1 : ℕ) : ℝ) - 1 = (n : ℝ) by push_cast; ring,
      Real.rpow_natCast]
  · rw [show ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 by push_cast; ring,
      Real.Gamma_nat_eq_factorial]
    push_cast
    rw [show (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast]
    rw [one_div_pow]
    ring

private theorem finite_moment_substitution (n : ℕ) (T : ℝ) :
    (∫ x in Real.exp (-T)..1, momentIntegrand n x) =
      (-1 : ℝ) ^ n * ∫ t in (0 : ℝ)..T, gammaIntegrand n t := by
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) T,
      HasDerivAt (fun u : ℝ => Real.exp (-u)) (-Real.exp (-t)) t := by
    intro t ht
    simpa only [Function.comp_apply, mul_neg, mul_one] using
      (Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_id t).neg
  have hsub := intervalIntegral.integral_comp_mul_deriv
    (a := (0 : ℝ)) (b := T) (f := fun t : ℝ => Real.exp (-t))
    (f' := fun t : ℝ => -Real.exp (-t)) (g := momentIntegrand n)
    hderiv (by fun_prop) (continuous_momentIntegrand n)
  have htrans : (∫ t in (0 : ℝ)..T,
      (momentIntegrand n ∘ fun u : ℝ => Real.exp (-u)) t * (-Real.exp (-t))) =
      -((-1 : ℝ) ^ n * ∫ t in (0 : ℝ)..T, gammaIntegrand n t) := by
    calc
      (∫ t in (0 : ℝ)..T,
          (momentIntegrand n ∘ fun u : ℝ => Real.exp (-u)) t * (-Real.exp (-t))) =
          ∫ t in (0 : ℝ)..T, -((-1 : ℝ) ^ n * gammaIntegrand n t) := by
        apply intervalIntegral.integral_congr
        intro t ht
        simp only [Function.comp_apply, momentIntegrand, gammaIntegrand, Real.log_exp]
        rw [neg_pow, ← Real.exp_nat_mul]
        have hexp : Real.exp ((n : ℝ) * -t) * Real.exp (-t) =
            Real.exp (-(((n + 1 : ℕ) : ℝ) * t)) := by
          rw [← Real.exp_add]
          congr 1
          push_cast
          ring
        calc
          Real.exp ((n : ℝ) * -t) * ((-1 : ℝ) ^ n * t ^ n) *
              -Real.exp (-t) =
              -((-1 : ℝ) ^ n * t ^ n *
                (Real.exp ((n : ℝ) * -t) * Real.exp (-t))) := by ring
          _ = -((-1 : ℝ) ^ n * (t ^ n *
                Real.exp (-(((n + 1 : ℕ) : ℝ) * t)))) := by
            rw [hexp]
            ring
      _ = -(∫ t in (0 : ℝ)..T, (-1 : ℝ) ^ n * gammaIntegrand n t) := by
        rw [intervalIntegral.integral_neg]
      _ = -((-1 : ℝ) ^ n * ∫ t in (0 : ℝ)..T, gammaIntegrand n t) := by
        rw [intervalIntegral.integral_const_mul]
  rw [htrans] at hsub
  simp only [neg_zero, Real.exp_zero] at hsub
  rw [intervalIntegral.integral_symm (f := momentIntegrand n) (Real.exp (-T)) 1] at hsub
  linarith

private theorem integrableOn_gammaIntegrand (n : ℕ) :
    MeasureTheory.IntegrableOn (gammaIntegrand n) (Set.Ioi (0 : ℝ)) := by
  have hbase := Real.GammaIntegral_convergent
    (s := ((n + 1 : ℕ) : ℝ)) (by positivity)
  have hbase' : MeasureTheory.IntegrableOn
      (fun t : ℝ => Real.exp (-t) * t ^ n) (Set.Ioi (0 : ℝ)) := by
    refine hbase.congr_fun ?_ measurableSet_Ioi
    intro t ht
    rw [show ((n + 1 : ℕ) : ℝ) - 1 = (n : ℝ) by push_cast; ring]
    change Real.exp (-t) * t ^ (n : ℝ) = Real.exp (-t) * t ^ n
    rw [Real.rpow_natCast]
  have hmeas : MeasureTheory.AEStronglyMeasurable (gammaIntegrand n)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    exact (by
      unfold gammaIntegrand
      fun_prop : Continuous (gammaIntegrand n)).aestronglyMeasurable
  refine hbase'.mono' hmeas ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 < t := ht
  have hr : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    push_cast
    have hn : (0 : ℝ) ≤ n := by positivity
    linarith
  simp only [gammaIntegrand, Real.norm_eq_abs]
  rw [abs_of_pos (mul_pos (pow_pos ht0 n) (Real.exp_pos _))]
  rw [mul_comm (Real.exp (-t)) (t ^ n)]
  apply mul_le_mul_of_nonneg_left
  · exact Real.exp_le_exp.mpr (by nlinarith)
  · positivity

private theorem integral_momentIntegrand (n : ℕ) :
    (∫ x in (0 : ℝ)..1, momentIntegrand n x) =
      (-1 : ℝ) ^ n * (Nat.factorial n : ℝ) /
        ((n + 1 : ℕ) : ℝ) ^ (n + 1) := by
  have hgamma : Tendsto (fun T : ℝ =>
      ∫ t in (0 : ℝ)..T, gammaIntegrand n t) atTop
      (nhds (∫ t : ℝ in Set.Ioi 0, gammaIntegrand n t)) :=
    MeasureTheory.intervalIntegral_tendsto_integral_Ioi 0
      (integrableOn_gammaIntegrand n) Filter.tendsto_id
  have hleft := hgamma.const_mul ((-1 : ℝ) ^ n)
  have hprimitive : Continuous (fun a : ℝ =>
      ∫ x in a..1, momentIntegrand n x) := by
    have hright : Continuous (fun b : ℝ =>
        ∫ x in (1 : ℝ)..b, momentIntegrand n x) := by
      rw [continuous_iff_continuousAt]
      intro b
      exact ((continuous_momentIntegrand n).integral_hasStrictDerivAt 1 b).hasDerivAt.continuousAt
    have heqfun : (fun a : ℝ => ∫ x in a..1, momentIntegrand n x) =
        fun a : ℝ => -(∫ x in (1 : ℝ)..a, momentIntegrand n x) := by
      funext a
      exact intervalIntegral.integral_symm 1 a
    rw [heqfun]
    exact hright.neg
  have hright : Tendsto (fun T : ℝ =>
      ∫ x in Real.exp (-T)..1, momentIntegrand n x) atTop
      (nhds (∫ x in (0 : ℝ)..1, momentIntegrand n x)) :=
    hprimitive.continuousAt.tendsto.comp Real.tendsto_exp_neg_atTop_nhds_zero
  have heq : (fun T : ℝ =>
      ∫ x in Real.exp (-T)..1, momentIntegrand n x) =ᶠ[atTop]
      (fun T : ℝ => (-1 : ℝ) ^ n *
        ∫ t in (0 : ℝ)..T, gammaIntegrand n t) :=
    Filter.Eventually.of_forall (finite_moment_substitution n)
  have hlimit := tendsto_nhds_unique hright (hleft.congr' heq.symm)
  rw [integral_gammaIntegrand] at hlimit
  calc
    (∫ x in (0 : ℝ)..1, momentIntegrand n x) =
        (-1 : ℝ) ^ n *
          ((Nat.factorial n : ℝ) / ((n + 1 : ℕ) : ℝ) ^ (n + 1)) := hlimit
    _ = (-1 : ℝ) ^ n * (Nat.factorial n : ℝ) /
        ((n + 1 : ℕ) : ℝ) ^ (n + 1) := by ring

private theorem abs_mul_log_le_one {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |x * Real.log x| ≤ 1 := by
  by_cases hx : x = 0
  · simp [hx]
  · have hxpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hx)
    have hlog : Real.log x ≤ 0 := Real.log_nonpos hxpos.le hx1
    have hnonpos : x * Real.log x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hx0 hlog
    rw [abs_of_nonpos hnonpos]
    have h := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos hxpos) hx0
    rw [mul_sub, mul_one, mul_inv_cancel₀ hx] at h
    linarith

private theorem integral_exponentialTerm (n : ℕ) :
    (∫ x in (0 : ℝ)..1, exponentialTerm x n) = integratedTerm n := by
  rw [show (fun x : ℝ => exponentialTerm x n) =
      fun x : ℝ => (1 / (Nat.factorial n : ℝ)) * momentIntegrand n x by
    funext x
    simp only [exponentialTerm, momentIntegrand]
    ring]
  rw [intervalIntegral.integral_const_mul, integral_momentIntegrand]
  simp only [integratedTerm]
  have hf : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  field_simp [hf]

private theorem hasSum_integratedTerm_targetIntegral :
    HasSum integratedTerm targetIntegral := by
  have hmeas : ∀ n : ℕ, MeasureTheory.AEStronglyMeasurable
      (fun x : ℝ => exponentialTerm x n)
      (MeasureTheory.volume.restrict (Ι (0 : ℝ) 1)) := by
    intro n
    have hc : Continuous (fun x : ℝ => exponentialTerm x n) := by
      unfold exponentialTerm
      exact (Real.continuous_mul_log.pow n).div_const _
    exact hc.aestronglyMeasurable
  have hbound : ∀ n : ℕ, ∀ᵐ x ∂MeasureTheory.volume,
      x ∈ Ι (0 : ℝ) 1 →
        ‖exponentialTerm x n‖ ≤ (1 : ℝ) / (Nat.factorial n : ℝ) := by
    intro n
    filter_upwards with x hx
    have hx' : x ∈ Set.Ioc (0 : ℝ) 1 := by
      simpa [Set.uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hx
    have habs := abs_mul_log_le_one hx'.1.le hx'.2
    simp only [exponentialTerm, norm_div, norm_pow, Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (Nat.factorial n : ℝ))]
    apply div_le_div_of_nonneg_right _ (by positivity)
    simpa only [one_pow] using pow_le_pow_left₀ (abs_nonneg _) habs n
  have hsum : Summable (fun n : ℕ => (1 : ℝ) / (Nat.factorial n : ℝ)) := by
    simpa using (NormedSpace.expSeries_div_summable (1 : ℝ))
  have hbound_summable : ∀ᵐ x ∂MeasureTheory.volume,
      x ∈ Ι (0 : ℝ) 1 →
        Summable (fun n : ℕ => (1 : ℝ) / (Nat.factorial n : ℝ)) :=
    MeasureTheory.ae_of_all _ (fun _ _ => hsum)
  have hbound_integrable : IntervalIntegrable
      (fun _ : ℝ => ∑' n : ℕ, (1 : ℝ) / (Nat.factorial n : ℝ))
      MeasureTheory.volume 0 1 := intervalIntegrable_const
  have hlim : ∀ᵐ x ∂MeasureTheory.volume, x ∈ Ι (0 : ℝ) 1 →
      HasSum (fun n : ℕ => exponentialTerm x n) (Real.exp (x * Real.log x)) :=
    MeasureTheory.ae_of_all _ (fun x _ => hasSum_exponentialTerm x)
  have h := intervalIntegral.hasSum_integral_of_dominated_convergence
    (a := (0 : ℝ)) (b := 1) (f := fun x : ℝ => Real.exp (x * Real.log x))
    (F := fun n x => exponentialTerm x n)
    (fun n (_ : ℝ) => (1 : ℝ) / (Nat.factorial n : ℝ))
    hmeas hbound hbound_summable hbound_integrable hlim
  have htarget : (∫ x in (0 : ℝ)..1, Real.exp (x * Real.log x)) =
      targetIntegral := by
    rw [targetIntegral]
    apply intervalIntegral.integral_congr
    intro x hx
    simp only [Set.uIcc_of_le zero_le_one, Set.mem_Icc] at hx
    by_cases hx0 : x = 0
    · simp [hx0, selfPower]
    · rw [selfPower]
      calc
        Real.exp (x * Real.log x) = Real.exp (Real.log x * x) := by ring_nf
        _ = Real.rpow x x :=
          (Real.rpow_def_of_pos (lt_of_le_of_ne hx.1 (Ne.symm hx0)) x).symm
  rw [htarget] at h
  convert h using 1
  ext n
  exact (integral_exponentialTerm n).symm

private def coefficient (n : ℕ) : ℝ :=
  1 / ((n + 1 : ℕ) : ℝ) ^ (n + 1)

private theorem integratedTerm_eq (n : ℕ) :
    integratedTerm n = (-1 : ℝ) ^ n * coefficient n := by
  simp only [integratedTerm, coefficient]
  ring

private theorem strictAnti_coefficient : StrictAnti coefficient := by
  apply strictAnti_nat_of_succ_lt
  intro n
  simp only [coefficient]
  apply one_div_lt_one_div_of_lt
  · positivity
  · calc
      ((n + 1 : ℕ) : ℝ) ^ (n + 1) <
          ((n + 2 : ℕ) : ℝ) ^ (n + 1) := by
        apply pow_lt_pow_left₀
        · push_cast
          linarith
        · positivity
        · omega
      _ ≤ ((n + 2 : ℕ) : ℝ) ^ (n + 2) := by
        apply pow_le_pow_right₀
        · push_cast
          linarith
        · omega

private theorem tendsto_integratedPartial :
    Tendsto (fun m => ∑ n ∈ Finset.range m,
      (-1 : ℝ) ^ n * coefficient n) atTop (nhds targetIntegral) := by
  convert hasSum_integratedTerm_targetIntegral.tendsto_sum_nat using 1
  ext m
  apply Finset.sum_congr rfl
  intro n hn
  exact (integratedTerm_eq n).symm

private theorem remainder_pos : 0 < remainder := by
  have hlo := strictAnti_coefficient.antitone.alternating_series_le_tendsto
    tendsto_integratedPartial 3
  rw [remainder]
  norm_num [coefficient, partialIntegral, integratedTerm,
    Finset.sum_range_succ] at hlo ⊢
  linarith

private theorem remainder_lt_next : remainder < (1 / 5 ^ 5 : ℝ) := by
  have hhi := strictAnti_coefficient.antitone.tendsto_le_alternating_series
    tendsto_integratedPartial 3
  rw [remainder]
  norm_num [coefficient, partialIntegral, integratedTerm,
    Finset.sum_range_succ] at hhi ⊢
  linarith

private theorem approx_targetIntegral :
    Approx targetIntegral (783 / 1000 : ℝ) (1 / 1000 : ℝ) := by
  have hpos := remainder_pos
  have hlt := remainder_lt_next
  rw [Approx, abs_lt]
  norm_num [remainder, partialIntegral, integratedTerm,
    Finset.sum_range_succ] at hpos hlt ⊢
  constructor <;> linarith

theorem gap1 :
    ∀ x : ℝ, 0 < x →
      selfPower x = Real.exp (x * Real.log x) := by
  intro x hx
  rw [selfPower]
  calc
    Real.rpow x x = Real.exp (Real.log x * x) := Real.rpow_def_of_pos hx x
    _ = Real.exp (x * Real.log x) := by ring_nf

theorem gap2 :
    ∀ x : ℝ,
      Real.exp (x * Real.log x) =
        ∑' n : ℕ, exponentialTerm x n := by
  intro x
  exact (hasSum_exponentialTerm x).tsum_eq.symm

theorem gap3 :
    ∀ x : ℝ, 0 < x →
      selfPower x = ∑' n : ℕ, exponentialTerm x n := by
  intro x hx
  rw [(hasSum_exponentialTerm x).tsum_eq]
  rw [selfPower]
  calc
    Real.rpow x x = Real.exp (Real.log x * x) := Real.rpow_def_of_pos hx x
    _ = Real.exp (x * Real.log x) := by ring_nf

theorem gap4 :
    ∀ n : ℕ,
      (∫ x in (0 : ℝ)..1, x ^ n * Real.log x ^ n) =
        (-1 : ℝ) ^ n * (Nat.factorial n : ℝ) /
          ((n + 1 : ℕ) : ℝ) ^ (n + 1) := by
  intro n
  exact integral_momentIntegrand n

theorem gap5 :
    targetIntegral = ∑' n : ℕ, integratedTerm n := by
  exact hasSum_integratedTerm_targetIntegral.tsum_eq.symm

theorem gap6 :
    0 < remainder := by
  exact remainder_pos

theorem gap7 :
    remainder < (1 / 5 ^ 5 : ℝ) := by
  exact remainder_lt_next

theorem gap8 :
    ((Nat.factorial 4 : ℝ) /
        ((Nat.factorial 4 : ℝ) * 5 ^ 5)) =
      1 / 5 ^ 5 := by
  norm_num

theorem gap9 :
    (1 / 5 ^ 5 : ℝ) < (1 / 10 ^ 3 : ℝ) := by
  norm_num

theorem gap10 :
    (0 : ℝ) < 1 / 10 ^ 3 := by
  norm_num

theorem gap11 :
    Approx targetIntegral (783 / 1000 : ℝ)
      (1 / 1000 : ℝ) := by
  exact approx_targetIntegral

end

end ProofGap.Exercise2932_12
