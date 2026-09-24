import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.Order.Floor.Semiring

namespace ProofGap.Exercise2384_2
noncomputable section

open Filter MeasureTheory
open scoped BigOperators Interval

def width (k : ℕ) : ℝ := Real.sqrt (k + 1) - Real.sqrt k
def alternatingTerm (k : ℕ) : ℝ := (-1 : ℝ) ^ k * width k
def partialSum (n : ℕ) : ℝ := ∑ k ∈ Finset.range n, alternatingTerm k
def stepIntegrand (x : ℝ) : ℝ := (-1 : ℝ) ^ Nat.floor (x ^ 2)

private theorem sqrt_nat_succ_lt (k : ℕ) :
    Real.sqrt k < Real.sqrt (k + 1) := by
  apply Real.sqrt_lt_sqrt (by positivity)
  norm_num

private theorem width_pos (k : ℕ) : 0 < width k := by
  unfold width
  exact sub_pos.mpr (sqrt_nat_succ_lt k)

private theorem width_eq_recip (n : ℕ) :
    width n = 1 / (Real.sqrt (n + 1) + Real.sqrt n) := by
  have hden : 0 < Real.sqrt (n + 1) + Real.sqrt n :=
    add_pos_of_pos_of_nonneg (Real.sqrt_pos.2 (by positivity)) (Real.sqrt_nonneg _)
  apply (eq_div_iff hden.ne').2
  unfold width
  have hsq1 : (Real.sqrt ((n : ℝ) + 1)) ^ 2 = (n : ℝ) + 1 :=
    Real.sq_sqrt (by positivity)
  have hsq0 : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) :=
    Real.sq_sqrt (by positivity)
  nlinarith

private theorem width_antitone : Antitone width := by
  intro m n hmn
  rw [width_eq_recip n, width_eq_recip m]
  apply one_div_le_one_div_of_le
  · exact add_pos_of_pos_of_nonneg (Real.sqrt_pos.2 (by positivity)) (Real.sqrt_nonneg _)
  · gcongr <;> exact_mod_cast hmn

theorem gap1 (A : ℝ) (hA : 0 ≤ A) :
    ∃! n : ℕ, Real.sqrt n ≤ A ∧ A < Real.sqrt (n + 1) := by
  let n := Nat.floor (A ^ 2)
  have hfloor : (n : ℝ) ≤ A ^ 2 ∧ A ^ 2 < (n : ℝ) + 1 := by
    exact (Nat.floor_eq_iff (sq_nonneg A)).1 rfl
  refine ⟨n, ?_, ?_⟩
  · constructor
    · exact Real.sqrt_le_iff.mpr ⟨hA, hfloor.1⟩
    · apply (Real.lt_sqrt hA).2
      simpa only [Nat.cast_add, Nat.cast_one] using hfloor.2
  · intro m hm
    have hmLower : (m : ℝ) ≤ A ^ 2 :=
      (Real.sqrt_le_iff.mp hm.1).2
    have hmUpper : A ^ 2 < (m : ℝ) + 1 := by
      simpa only [Nat.cast_add, Nat.cast_one] using (Real.lt_sqrt hA).1 hm.2
    have heq : Nat.floor (A ^ 2) = m :=
      (Nat.floor_eq_iff (sq_nonneg A)).2 ⟨hmLower, hmUpper⟩
    exact heq.symm

theorem gap2 :
    Tendsto (fun A : ℝ => Nat.floor (A ^ 2)) atTop atTop := by
  apply tendsto_nat_floor_atTop.comp
  simpa [pow_two] using (tendsto_mul_self_atTop (α := ℝ))

theorem gap3 (k : ℕ) (x : ℝ)
    (h₀ : 0 ≤ x) (h₁ : Real.sqrt k ≤ x) (h₂ : x < Real.sqrt (k + 1)) :
    Nat.floor (x ^ 2) = k := by
  apply (Nat.floor_eq_iff (sq_nonneg x)).2
  constructor
  · exact (Real.sqrt_le_iff.mp h₁).2
  · simpa only [Nat.cast_add, Nat.cast_one] using (Real.lt_sqrt h₀).1 h₂

private theorem step_interval_ae (k : ℕ) :
    (fun _ : ℝ => (-1 : ℝ) ^ k) =ᵐ[
      volume.restrict (Set.uIoc (Real.sqrt k) (Real.sqrt (k + 1)))] stepIntegrand := by
  have hle : Real.sqrt k ≤ Real.sqrt (k + 1) := (sqrt_nat_succ_lt k).le
  filter_upwards [ae_restrict_mem measurableSet_uIoc,
    ae_restrict_of_ae ((volume : Measure ℝ).ae_ne (Real.sqrt (k + 1)))] with x hx hne
  rw [Set.uIoc_of_le hle] at hx
  have hxlt : x < Real.sqrt (k + 1) := lt_of_le_of_ne hx.2 hne
  unfold stepIntegrand
  rw [gap3 k x (Real.sqrt_nonneg _ |>.trans_lt hx.1).le hx.1.le hxlt]

private theorem step_intervalIntegrable (k : ℕ) :
    IntervalIntegrable stepIntegrand volume (Real.sqrt k) (Real.sqrt (k + 1)) := by
  exact (intervalIntegrable_const (c := (-1 : ℝ) ^ k)).congr_ae (step_interval_ae k)

private theorem integral_step_interval (k : ℕ) :
    (∫ x in Real.sqrt k..Real.sqrt (k + 1), stepIntegrand x) = alternatingTerm k := by
  calc
    (∫ x in Real.sqrt k..Real.sqrt (k + 1), stepIntegrand x) =
        ∫ _x in Real.sqrt k..Real.sqrt (k + 1), (-1 : ℝ) ^ k := by
      exact intervalIntegral.integral_congr_ae_restrict (step_interval_ae k).symm
    _ = alternatingTerm k := by
      simp [alternatingTerm, width, mul_comm]

private theorem step_zero_sqrt_integrable (n : ℕ) :
    IntervalIntegrable stepIntegrand volume 0 (Real.sqrt n) := by
  have h : IntervalIntegrable stepIntegrand volume (Real.sqrt (0 : ℕ))
      (Real.sqrt n) := IntervalIntegrable.trans_iterate
    (a := fun k : ℕ => Real.sqrt k) (n := n)
    (fun k _ => by
      simpa only [Nat.cast_add, Nat.cast_one] using step_intervalIntegrable k)
  simpa using h

private theorem integral_step_zero_sqrt (n : ℕ) :
    (∫ x in (0 : ℝ)..Real.sqrt n, stepIntegrand x) = partialSum n := by
  induction n with
  | zero => simp [partialSum]
  | succ n ih =>
      have hadd := intervalIntegral.integral_add_adjacent_intervals
        (step_zero_sqrt_integrable n) (step_intervalIntegrable n)
      rw [show Real.sqrt ((n + 1 : ℕ) : ℝ) = Real.sqrt ((n : ℝ) + 1) by norm_num]
      rw [← hadd, ih, integral_step_interval]
      simp [partialSum, Finset.sum_range_succ]

private theorem step_partial_integrable (n : ℕ) (A : ℝ)
    (hnA : Real.sqrt n ≤ A) (hA : A < Real.sqrt (n + 1)) :
    IntervalIntegrable stepIntegrand volume (Real.sqrt n) A := by
  have hconst : IntervalIntegrable (fun _ : ℝ => (-1 : ℝ) ^ n)
      volume (Real.sqrt n) A := intervalIntegrable_const
  apply hconst.congr
  intro x hx
  rw [Set.uIoc_of_le hnA] at hx
  unfold stepIntegrand
  rw [gap3 n x ((Real.sqrt_nonneg _).trans hx.1.le)
    hx.1.le (hx.2.trans_lt hA)]

private theorem integral_step_partial (n : ℕ) (A : ℝ)
    (hnA : Real.sqrt n ≤ A) (hA : A < Real.sqrt (n + 1)) :
    (∫ x in Real.sqrt n..A, stepIntegrand x) =
      (-1 : ℝ) ^ n * (A - Real.sqrt n) := by
  calc
    (∫ x in Real.sqrt n..A, stepIntegrand x) =
        ∫ _x in Real.sqrt n..A, (-1 : ℝ) ^ n := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le hnA] at hx
      unfold stepIntegrand
      rw [gap3 n x ((Real.sqrt_nonneg _).trans hx.1)
        hx.1 (hx.2.trans_lt hA)]
    _ = (-1 : ℝ) ^ n * (A - Real.sqrt n) := by
      simp [mul_comm]

theorem gap4 (A : ℝ) (hA : 0 ≤ A) :
    ∃ n : ℕ,
      Real.sqrt n ≤ A ∧ A < Real.sqrt (n + 1) ∧
      (∫ x in (0 : ℝ)..A, stepIntegrand x) =
        partialSum n + (-1 : ℝ) ^ n * (A - Real.sqrt n) := by
  obtain ⟨n, hn, _⟩ := gap1 A hA
  refine ⟨n, hn.1, hn.2, ?_⟩
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (step_zero_sqrt_integrable n) (step_partial_integrable n A hn.1 hn.2)
  rw [← hadd, integral_step_zero_sqrt, integral_step_partial n A hn.1 hn.2]

theorem gap5 :
    Tendsto width atTop (nhds 0) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hn
  have hden : Tendsto
      (fun n : ℕ => Real.sqrt (n + 1) + Real.sqrt n) atTop atTop := by
    apply tendsto_atTop_mono' atTop _ hsqrt
    exact Filter.Eventually.of_forall (fun n => le_add_of_nonneg_left (Real.sqrt_nonneg _))
  have hinv := tendsto_inv_atTop_zero.comp hden
  apply hinv.congr'
  exact Filter.Eventually.of_forall (fun n => by
    simpa only [Function.comp_apply, one_div] using (width_eq_recip n).symm)

theorem gap6 :
    ∃ S : ℝ, Tendsto partialSum atTop (nhds S) := by
  simpa only [partialSum, alternatingTerm] using
    width_antitone.tendsto_alternating_series_of_tendsto_zero gap5

theorem gap7 (A : ℝ) (hA : 0 ≤ A) :
    ∃ n : ℕ,
      Real.sqrt n ≤ A ∧ A < Real.sqrt (n + 1) ∧
      |(-1 : ℝ) ^ n * (A - Real.sqrt n)| < width n := by
  obtain ⟨n, hn, _⟩ := gap1 A hA
  refine ⟨n, hn.1, hn.2, ?_⟩
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg (sub_nonneg.mpr hn.1)]
  unfold width
  linarith

theorem gap8 (n : ℕ) :
    width n = 1 / (Real.sqrt (n + 1) + Real.sqrt n) := by
  exact width_eq_recip n

theorem gap9 (A : ℝ) (hA : 0 ≤ A) :
    ∃ n : ℕ,
      Real.sqrt n ≤ A ∧ A < Real.sqrt (n + 1) ∧
      |(-1 : ℝ) ^ n * (A - Real.sqrt n)| <
        1 / (Real.sqrt (n + 1) + Real.sqrt n) := by
  obtain ⟨n, hn1, hn2, hbound⟩ := gap7 A hA
  refine ⟨n, hn1, hn2, ?_⟩
  rwa [gap8 n] at hbound

theorem gap10 :
    ∃ S : ℝ,
      Tendsto (fun A => ∫ x in (0 : ℝ)..A, stepIntegrand x)
        atTop (nhds S) := by
  obtain ⟨S, hS⟩ := gap6
  refine ⟨S, ?_⟩
  let N : ℝ → ℕ := fun A => Nat.floor (A ^ 2)
  let err : ℝ → ℝ := fun A => (-1 : ℝ) ^ (N A) * (A - Real.sqrt (N A))
  have hN : Tendsto N atTop atTop := by simpa only [N] using gap2
  have hsum : Tendsto (fun A => partialSum (N A)) atTop (nhds S) := hS.comp hN
  have hwidth : Tendsto (fun A => width (N A)) atTop (nhds 0) := gap5.comp hN
  have herrAbs : Tendsto (fun A => |err A|) atTop (nhds 0) := by
    apply squeeze_zero' (Filter.Eventually.of_forall (fun A => abs_nonneg (err A))) _ hwidth
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with A hA
    obtain ⟨n, hn1, hn2, hbound⟩ := gap7 A hA
    have hn : N A = n := by
      unfold N
      exact gap3 n A hA hn1 hn2
    simpa [err, hn] using hbound.le
  have herr : Tendsto err atTop (nhds 0) :=
    (tendsto_zero_iff_abs_tendsto_zero _).2 herrAbs
  have hformula : (fun A => ∫ x in (0 : ℝ)..A, stepIntegrand x) =ᶠ[atTop]
      (fun A => partialSum (N A) + err A) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with A hA
    obtain ⟨n, hn1, hn2, hInt⟩ := gap4 A hA
    have hn : N A = n := by
      unfold N
      exact gap3 n A hA hn1 hn2
    simpa [err, hn] using hInt
  have hlim : Tendsto (fun A => partialSum (N A) + err A) atTop (nhds S) := by
    simpa using hsum.add herr
  exact hlim.congr' hformula.symm

private def evenPhaseSeq (n : ℕ) : ℝ := Real.sqrt (2 * (n : ℝ))

private def oddPhaseSeq (n : ℕ) : ℝ := Real.sqrt (2 * (n : ℝ) + 1)

private theorem evenPhaseSeq_tendsto : Tendsto evenPhaseSeq atTop atTop := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hmul : Tendsto (fun n : ℕ => (n : ℝ) * 2) atTop atTop :=
    hn.atTop_mul_const (by norm_num)
  have hmul' : Tendsto (fun n : ℕ => 2 * (n : ℝ)) atTop atTop := by
    simpa [mul_comm] using hmul
  exact Real.tendsto_sqrt_atTop.comp (by simpa [evenPhaseSeq] using hmul')

private theorem oddPhaseSeq_tendsto : Tendsto oddPhaseSeq atTop atTop := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hmul : Tendsto (fun n : ℕ => (n : ℝ) * 2) atTop atTop :=
    hn.atTop_mul_const (by norm_num)
  have hmul' : Tendsto (fun n : ℕ => 2 * (n : ℝ)) atTop atTop := by
    simpa [mul_comm] using hmul
  have hadd : Tendsto (fun n : ℕ => 2 * (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 hmul'
  exact Real.tendsto_sqrt_atTop.comp (by simpa [oddPhaseSeq] using hadd)

private theorem step_evenPhaseSeq (n : ℕ) : stepIntegrand (evenPhaseSeq n) = 1 := by
  have hnonneg : 0 ≤ 2 * (n : ℝ) := by positivity
  unfold stepIntegrand evenPhaseSeq
  rw [Real.sq_sqrt hnonneg,
    show 2 * (n : ℝ) = ((2 * n : ℕ) : ℝ) by norm_num,
    Nat.floor_natCast]
  simp [pow_mul]

private theorem step_oddPhaseSeq (n : ℕ) : stepIntegrand (oddPhaseSeq n) = -1 := by
  have hnonneg : 0 ≤ 2 * (n : ℝ) + 1 := by positivity
  unfold stepIntegrand oddPhaseSeq
  rw [Real.sq_sqrt hnonneg,
    show 2 * (n : ℝ) + 1 = ((2 * n + 1 : ℕ) : ℝ) by norm_num,
    Nat.floor_natCast]
  simp [pow_add, pow_mul]

theorem gap11 :
    ¬ ∃ L : ℝ, Tendsto stepIntegrand atTop (nhds L) := by
  rintro ⟨L, hL⟩
  have he := hL.comp evenPhaseSeq_tendsto
  have ho := hL.comp oddPhaseSeq_tendsto
  have he' : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds L) := by
    apply he.congr'
    exact Filter.Eventually.of_forall step_evenPhaseSeq
  have ho' : Tendsto (fun _ : ℕ => (-1 : ℝ)) atTop (nhds L) := by
    apply ho.congr'
    exact Filter.Eventually.of_forall step_oddPhaseSeq
  have hL1 : L = 1 := tendsto_nhds_unique he' tendsto_const_nhds
  have hLn : L = -1 := tendsto_nhds_unique ho' tendsto_const_nhds
  linarith

theorem gap12 :
    ¬ ∀ (f : ℝ → ℝ) (a : ℝ),
      (∃ L : ℝ, Tendsto (fun A => ∫ x in a..A, f x) atTop (nhds L)) →
      Tendsto f atTop (nhds 0) := by
  intro h
  exact gap11 ⟨0, h stepIntegrand 0 gap10⟩

end
end ProofGap.Exercise2384_2
