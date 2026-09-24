import ProofGapLean.Prelude.Analysis
import ProofGapLean.Prelude.Discrete
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

open Filter Topology
open scoped Interval

namespace ProofGap.Exercise2225

noncomputable section

def euler : ℝ := Real.exp 1

def rootRatio (n : ℕ) : ℝ :=
  Real.rpow (Nat.factorial n : ℝ) (1 / (n : ℝ)) / n

def normalizedLog (n : ℕ) : ℝ :=
  (1 / (n : ℝ)) *
    ((∑ i ∈ Finset.Icc 1 n, Real.log (i : ℝ)) -
      (n : ℝ) * Real.log (n : ℝ))

def logRiemannSum (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 n,
    Real.log ((i : ℝ) / n) * (1 / (n : ℝ))

def antiderivative (x : ℝ) : ℝ := x * (Real.log x - 1)

private theorem sum_log_Icc_eq_log_factorial (n : ℕ) :
    (∑ i ∈ Finset.Icc 1 n, Real.log (i : ℝ)) =
      Real.log (Nat.factorial n : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih, Nat.factorial_succ,
        Nat.cast_mul]
      rw [Real.log_mul (by positivity) (by positivity)]
      ring

private theorem log_rootRatio_eq_normalizedLog (n : ℕ) (hn : 1 ≤ n) :
    Real.log (rootRatio n) = normalizedLog n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hfac : (0 : ℝ) < Nat.factorial n := by positivity
  have hroot : 0 < Real.rpow (Nat.factorial n : ℝ) (1 / (n : ℝ)) :=
    Real.rpow_pos_of_pos hfac _
  have hrpow :
      Real.rpow (Nat.factorial n : ℝ) (1 / (n : ℝ)) =
        Real.exp (Real.log (Nat.factorial n : ℝ) * (1 / (n : ℝ))) :=
    Real.rpow_def_of_pos hfac _
  unfold rootRatio normalizedLog
  rw [Real.log_div hroot.ne' hnR.ne', hrpow, Real.log_exp,
    sum_log_Icc_eq_log_factorial]
  field_simp [hnR.ne']

private theorem normalizedLog_eq_logRiemannSum (n : ℕ) (hn : 1 ≤ n) :
    normalizedLog n = logRiemannSum n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hcard : (Finset.Icc 1 n).card = n := by
    rw [Nat.card_Icc]
    omega
  unfold normalizedLog logRiemannSum
  calc
    (1 / (n : ℝ)) *
        ((∑ i ∈ Finset.Icc 1 n, Real.log (i : ℝ)) -
          (n : ℝ) * Real.log (n : ℝ)) =
        (1 / (n : ℝ)) *
          ((∑ i ∈ Finset.Icc 1 n, Real.log (i : ℝ)) -
            ∑ _i ∈ Finset.Icc 1 n, Real.log (n : ℝ)) := by
      rw [Finset.sum_const, hcard]
      simp
    _ = (1 / (n : ℝ)) *
          ∑ i ∈ Finset.Icc 1 n,
            (Real.log (i : ℝ) - Real.log (n : ℝ)) := by
      rw [Finset.sum_sub_distrib]
    _ = ∑ i ∈ Finset.Icc 1 n,
          (1 / (n : ℝ)) *
            (Real.log (i : ℝ) - Real.log (n : ℝ)) := by
      rw [Finset.mul_sum]
    _ = ∑ i ∈ Finset.Icc 1 n,
          Real.log ((i : ℝ) / n) * (1 / (n : ℝ)) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hiPos : (0 : ℝ) < i := by
        exact_mod_cast (Finset.mem_Icc.mp hi).1
      rw [Real.log_div hiPos.ne' hnR.ne']
      ring

private theorem log_interval_integral (a b : ℝ) :
    (∫ x in a..b, Real.log x) = antiderivative b - antiderivative a := by
  rw [integral_log]
  unfold antiderivative
  ring

private theorem antiderivative_tendsto_zero :
    Tendsto antiderivative (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
  have hmul :
      Tendsto (fun x : ℝ => Real.log x * x)
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
    simpa using tendsto_log_mul_rpow_nhdsGT_zero zero_lt_one
  have hid :
      Tendsto (fun x : ℝ => x) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have heq : antiderivative = fun x : ℝ => Real.log x * x - x := by
    funext x
    unfold antiderivative
    ring
  rw [heq]
  simpa using hmul.sub hid

theorem gap1 :
    ∀ L : ℝ,
      Tendsto (fun n => Real.log (rootRatio n)) atTop (𝓝 L) ↔
        Tendsto normalizedLog atTop (𝓝 L) := by
  intro L
  have heq : (fun n => Real.log (rootRatio n)) =ᶠ[atTop] normalizedLog := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact log_rootRatio_eq_normalizedLog n hn
  constructor
  · intro h
    exact h.congr' heq
  · intro h
    exact h.congr' heq.symm

theorem gap2 :
    ∀ L : ℝ, Tendsto normalizedLog atTop (𝓝 L) ↔
      Tendsto logRiemannSum atTop (𝓝 L) := by
  intro L
  have heq : normalizedLog =ᶠ[atTop] logRiemannSum := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact normalizedLog_eq_logRiemannSum n hn
  constructor
  · intro h
    exact h.congr' heq
  · intro h
    exact h.congr' heq.symm

theorem gap3 :
    Tendsto logRiemannSum atTop
      (𝓝 (∫ x in (0 : ℝ)..1, Real.log x)) := by
  have hzero :
      Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hlogdiv :
      Tendsto (fun n : ℕ => Real.log (n : ℝ) / (n : ℝ))
        atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
      (tendsto_natCast_atTop_atTop :
        Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  have herr :
      Tendsto (fun n : ℕ => (1 + Real.log (n : ℝ)) / (n : ℝ))
        atTop (𝓝 0) := by
    have h := hzero.add hlogdiv
    convert h using 1
    · funext n
      ring
    · norm_num
  have hbnds : ∀ n : ℕ, 0 < n →
      (∫ x in (0 : ℝ)..1, Real.log x) ≤ logRiemannSum n ∧
        logRiemannSum n ≤
          (∫ x in (0 : ℝ)..1, Real.log x) +
            (1 + Real.log (n : ℝ)) / (n : ℝ) := by
    intro n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hn0 : (n : ℝ) ≠ 0 := hnR.ne'
    let F : ℝ → ℝ := antiderivative
    have hcellUpper (i : ℕ) :
        F (((i + 1 : ℕ) : ℝ) / n) - F ((i : ℝ) / n) ≤
          Real.log (((i + 1 : ℕ) : ℝ) / n) * (1 / (n : ℝ)) := by
      have hcell : (i : ℝ) / n ≤ ((i + 1 : ℕ) : ℝ) / n := by
        exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_succ i) hnR.le
      have hwidth :
          ((i + 1 : ℕ) : ℝ) / n - (i : ℝ) / n = 1 / (n : ℝ) := by
        push_cast
        field_simp [hn0]
        ring
      calc
        F (((i + 1 : ℕ) : ℝ) / n) - F ((i : ℝ) / n) =
            ∫ x in ((i : ℝ) / n)..(((i + 1 : ℕ) : ℝ) / n),
              Real.log x := by
          simpa [F] using
            (log_interval_integral ((i : ℝ) / n)
              (((i + 1 : ℕ) : ℝ) / n)).symm
        _ ≤ ∫ _ in ((i : ℝ) / n)..(((i + 1 : ℕ) : ℝ) / n),
              Real.log (((i + 1 : ℕ) : ℝ) / n) := by
          apply intervalIntegral.integral_mono_on_of_le_Ioo hcell
            intervalIntegral.intervalIntegrable_log'
            continuous_const.continuousOn.intervalIntegrable
          intro y hy
          have hyPos : 0 < y := by
            have hlo : 0 ≤ (i : ℝ) / n := div_nonneg (by positivity) hnR.le
            exact lt_of_le_of_lt hlo hy.1
          have hrightPos : 0 < ((i + 1 : ℕ) : ℝ) / n := by positivity
          exact Real.strictMonoOn_log.monotoneOn hyPos hrightPos hy.2.le
        _ = ((((i + 1 : ℕ) : ℝ) / n - (i : ℝ) / n) *
              Real.log (((i + 1 : ℕ) : ℝ) / n)) := by simp
        _ = Real.log (((i + 1 : ℕ) : ℝ) / n) *
              (1 / (n : ℝ)) := by rw [hwidth]; ring
    have htel : ∀ m : ℕ,
        (∑ i ∈ Finset.range m,
          (F (((i + 1 : ℕ) : ℝ) / n) - F ((i : ℝ) / n))) =
            F ((m : ℝ) / n) - F 0 := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
          rw [Finset.sum_range_succ, ih]
          push_cast
          ring
    have hsumIntegral :
        (∑ i ∈ Finset.range n,
          (F (((i + 1 : ℕ) : ℝ) / n) - F ((i : ℝ) / n))) =
            ∫ x in (0 : ℝ)..1, Real.log x := by
      calc
        _ = F ((n : ℝ) / n) - F 0 := htel n
        _ = F 1 - F 0 := by rw [div_self hn0]
        _ = ∫ x in (0 : ℝ)..1, Real.log x := by
          simpa [F] using (log_interval_integral 0 1).symm
    have hrepr :
        logRiemannSum n =
          ∑ i ∈ Finset.range n,
            Real.log (((i + 1 : ℕ) : ℝ) / n) * (1 / (n : ℝ)) := by
      have hIcc : Finset.Icc 1 n = Finset.Ico 1 (n + 1) := by
        ext i
        simp only [Finset.mem_Icc, Finset.mem_Ico]
        omega
      unfold logRiemannSum
      rw [hIcc, Finset.sum_Ico_eq_sum_range]
      simp only [Nat.add_sub_cancel_right]
      apply Finset.sum_congr rfl
      intro i hi
      simp [Nat.add_comm]
    have hlower :
        (∫ x in (0 : ℝ)..1, Real.log x) ≤ logRiemannSum n := by
      rw [hrepr, ← hsumIntegral]
      exact Finset.sum_le_sum fun i _ => hcellUpper i
    have hcellLower (i : ℕ) :
        Real.log (((i + 1 : ℕ) : ℝ) / n) * (1 / (n : ℝ)) ≤
          F (((i + 2 : ℕ) : ℝ) / n) - F (((i + 1 : ℕ) : ℝ) / n) := by
      have hcell : ((i + 1 : ℕ) : ℝ) / n ≤ ((i + 2 : ℕ) : ℝ) / n := by
        exact div_le_div_of_nonneg_right (by norm_num) hnR.le
      have hwidth :
          ((i + 2 : ℕ) : ℝ) / n - ((i + 1 : ℕ) : ℝ) / n =
            1 / (n : ℝ) := by
        push_cast
        field_simp [hn0]
        ring
      calc
        Real.log (((i + 1 : ℕ) : ℝ) / n) * (1 / (n : ℝ)) =
            (((i + 2 : ℕ) : ℝ) / n - ((i + 1 : ℕ) : ℝ) / n) *
              Real.log (((i + 1 : ℕ) : ℝ) / n) := by rw [hwidth]; ring
        _ = ∫ _ in (((i + 1 : ℕ) : ℝ) / n)..(((i + 2 : ℕ) : ℝ) / n),
              Real.log (((i + 1 : ℕ) : ℝ) / n) := by simp
        _ ≤ ∫ x in (((i + 1 : ℕ) : ℝ) / n)..(((i + 2 : ℕ) : ℝ) / n),
              Real.log x := by
          apply intervalIntegral.integral_mono_on hcell
            continuous_const.continuousOn.intervalIntegrable
            intervalIntegral.intervalIntegrable_log'
          intro y hy
          have hleftPos : 0 < ((i + 1 : ℕ) : ℝ) / n := by positivity
          have hyPos : 0 < y := hleftPos.trans_le hy.1
          exact Real.strictMonoOn_log.monotoneOn hleftPos hyPos hy.1
        _ = F (((i + 2 : ℕ) : ℝ) / n) -
              F (((i + 1 : ℕ) : ℝ) / n) := by
          simpa [F] using log_interval_integral
            (((i + 1 : ℕ) : ℝ) / n) (((i + 2 : ℕ) : ℝ) / n)
    have htelShift : ∀ m : ℕ,
        (∑ i ∈ Finset.range m,
          (F (((i + 2 : ℕ) : ℝ) / n) -
            F (((i + 1 : ℕ) : ℝ) / n))) =
          F (((m + 1 : ℕ) : ℝ) / n) - F (1 / (n : ℝ)) := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
          rw [Finset.sum_range_succ, ih]
          simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
          ring_nf
    have hshiftIntegral :
        (∑ i ∈ Finset.range (n - 1),
          (F (((i + 2 : ℕ) : ℝ) / n) -
            F (((i + 1 : ℕ) : ℝ) / n))) =
          ∫ x in (1 / (n : ℝ))..1, Real.log x := by
      calc
        _ = F ((((n - 1) + 1 : ℕ) : ℝ) / n) - F (1 / (n : ℝ)) :=
          htelShift (n - 1)
        _ = F 1 - F (1 / (n : ℝ)) := by
          rw [Nat.sub_add_cancel hn, div_self hn0]
        _ = ∫ x in (1 / (n : ℝ))..1, Real.log x := by
          simpa [F] using (log_interval_integral (1 / (n : ℝ)) 1).symm
    have hdropLast :
        (∑ i ∈ Finset.range n,
          Real.log (((i + 1 : ℕ) : ℝ) / n) * (1 / (n : ℝ))) =
        ∑ i ∈ Finset.range (n - 1),
          Real.log (((i + 1 : ℕ) : ℝ) / n) * (1 / (n : ℝ)) := by
      let g : ℕ → ℝ := fun i =>
        Real.log (((i + 1 : ℕ) : ℝ) / n) * (1 / (n : ℝ))
      calc
        (∑ i ∈ Finset.range n,
          Real.log (((i + 1 : ℕ) : ℝ) / n) * (1 / (n : ℝ))) =
            ∑ i ∈ Finset.range n, g i := by rfl
        _ = ∑ i ∈ Finset.range ((n - 1) + 1), g i := by
          rw [Nat.sub_add_cancel hn]
        _ = (∑ i ∈ Finset.range (n - 1), g i) + g (n - 1) := by
          rw [Finset.sum_range_succ]
        _ = ∑ i ∈ Finset.range (n - 1), g i := by
          have hlast : g (n - 1) = 0 := by
            unfold g
            rw [show n - 1 + 1 = n by omega, div_self hn0]
            simp
          rw [hlast, add_zero]
        _ = ∑ i ∈ Finset.range (n - 1),
            Real.log (((i + 1 : ℕ) : ℝ) / n) * (1 / (n : ℝ)) := by rfl
    have hupperRaw :
        logRiemannSum n ≤ ∫ x in (1 / (n : ℝ))..1, Real.log x := by
      rw [hrepr, hdropLast, ← hshiftIntegral]
      exact Finset.sum_le_sum fun i _ => hcellLower i
    have hIntegralError :
        (∫ x in (1 / (n : ℝ))..1, Real.log x) =
          (∫ x in (0 : ℝ)..1, Real.log x) +
            (1 + Real.log (n : ℝ)) / (n : ℝ) := by
      simp only [integral_log]
      rw [Real.log_div one_ne_zero hn0]
      norm_num
      field_simp [hn0]
      ring
    constructor
    · exact hlower
    · rw [hIntegralError] at hupperRaw
      exact hupperRaw
  have hupperlim :
      Tendsto
        (fun n : ℕ => (∫ x in (0 : ℝ)..1, Real.log x) +
          (1 + Real.log (n : ℝ)) / (n : ℝ))
        atTop (𝓝 (∫ x in (0 : ℝ)..1, Real.log x)) := by
    simpa using tendsto_const_nhds.add herr
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupperlim ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact (hbnds n hn).1
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact (hbnds n hn).2

theorem gap4 :
    Tendsto (fun n => Real.log (rootRatio n)) atTop
      (𝓝 (∫ x in (0 : ℝ)..1, Real.log x)) := by
  exact (gap1 _).mpr ((gap2 _).mpr gap3)

theorem gap5 :
    Tendsto
      (fun ε : ℝ => ∫ x in ε..1, Real.log x)
      (nhdsWithin 0 (Set.Ioi 0))
      (𝓝 (∫ x in (0 : ℝ)..1, Real.log x)) := by
  have heq :
      (fun ε : ℝ => ∫ x in ε..1, Real.log x) =
        fun ε => antiderivative 1 - antiderivative ε := by
    funext ε
    exact log_interval_integral ε 1
  rw [heq]
  have hconst :
      Tendsto (fun _ : ℝ => antiderivative 1)
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (antiderivative 1)) :=
    tendsto_const_nhds
  have hlim := hconst.sub antiderivative_tendsto_zero
  simpa [antiderivative, integral_log] using hlim

theorem gap6 :
    ∀ L : ℝ,
      Tendsto (fun ε : ℝ => ∫ x in ε..1, Real.log x)
          (nhdsWithin 0 (Set.Ioi 0)) (𝓝 L) ↔
        Tendsto (fun ε : ℝ => antiderivative 1 - antiderivative ε)
          (nhdsWithin 0 (Set.Ioi 0)) (𝓝 L) := by
  intro L
  have heq :
      (fun ε : ℝ => ∫ x in ε..1, Real.log x) =
        fun ε => antiderivative 1 - antiderivative ε := by
    funext ε
    exact log_interval_integral ε 1
  rw [heq]

theorem gap7 :
    Tendsto (fun ε : ℝ => antiderivative 1 - antiderivative ε)
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (-1)) := by
  have hconst :
      Tendsto (fun _ : ℝ => antiderivative 1)
        (nhdsWithin 0 (Set.Ioi 0)) (𝓝 (antiderivative 1)) :=
    tendsto_const_nhds
  have hlim := hconst.sub antiderivative_tendsto_zero
  simpa [antiderivative] using hlim

theorem gap8 :
    (∫ x in (0 : ℝ)..1, Real.log x) = -1 := by
  norm_num [integral_log]

theorem gap9 :
    Tendsto rootRatio atTop (𝓝 (Real.exp (-1))) := by
  have hlog :
      Tendsto (fun n => Real.log (rootRatio n)) atTop (𝓝 (-1)) := by
    simpa [gap8] using gap4
  have hexp := Real.continuous_exp.continuousAt.tendsto.comp hlog
  apply hexp.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hroot : 0 < rootRatio n := by
    unfold rootRatio
    exact div_pos
      (Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < Nat.factorial n) _)
      hnR
  exact Real.exp_log hroot

theorem gap10 :
    Real.exp (-1) = 1 / euler := by
  simp [euler, Real.exp_neg]

theorem gap11 :
    Tendsto rootRatio atTop (𝓝 (1 / euler)) := by
  rw [← gap10]
  exact gap9

end

end ProofGap.Exercise2225
