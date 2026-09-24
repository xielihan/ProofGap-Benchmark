import ProofGapLean.Prelude.Analysis
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Filter Topology
open scoped Interval

namespace ProofGap.Exercise2229

noncomputable section

def localRoot (x : ℝ) (k n : ℕ) : ℝ :=
  Real.sqrt ((x + (k : ℝ) / n) * (x + ((k : ℝ) + 1) / n))

def originalSeq (x : ℝ) (n : ℕ) : ℝ :=
  (1 / (n : ℝ) ^ 2) *
    ∑ k ∈ Finset.Icc 1 n,
      Real.sqrt (((n : ℝ) * x + k) * ((n : ℝ) * x + k + 1))

def riemannSum (x : ℝ) (n : ℕ) : ℝ :=
  (1 / (n : ℝ)) *
    ∑ k ∈ Finset.Icc 1 n, (x + (k : ℝ) / n)

def errorBound (x : ℝ) (n : ℕ) : ℝ :=
  (1 / (2 * x * (n : ℝ) ^ 2)) *
    ∑ k ∈ Finset.Icc 1 n, (x + (k : ℝ) / n)

def closedBound (x : ℝ) (n : ℕ) : ℝ :=
  1 / (2 * (n : ℝ)) +
    (1 / (4 * x)) * (1 + 1 / (n : ℝ)) * (1 / (n : ℝ))

private theorem scaledRoot_eq (x : ℝ) (k n : ℕ) (hn : 1 ≤ n) :
    Real.sqrt (((n : ℝ) * x + k) * ((n : ℝ) * x + k + 1)) =
      (n : ℝ) * localRoot x k n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hfactor :
      ((n : ℝ) * x + k) * ((n : ℝ) * x + k + 1) =
        (n : ℝ) ^ 2 *
          ((x + (k : ℝ) / n) * (x + ((k : ℝ) + 1) / n)) := by
    field_simp [hn0]
    ring
  rw [hfactor, Real.sqrt_mul (sq_nonneg (n : ℝ)), Real.sqrt_sq hnR.le]
  rfl

private theorem sum_cast_Icc (n : ℕ) :
    (∑ k ∈ Finset.Icc 1 n, (k : ℝ)) =
      (n : ℝ) * ((n : ℝ) + 1) / 2 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega) (fun k => (k : ℝ)), ih]
      simp only [Nat.cast_succ]
      ring

private theorem sum_affine_Icc (x : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    (∑ k ∈ Finset.Icc 1 n, (x + (k : ℝ) / n)) =
      (n : ℝ) * x + ((n : ℝ) + 1) / 2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hcard : (Finset.Icc 1 n).card = n := by
    simp
  rw [Finset.sum_add_distrib, Finset.sum_const, ← Finset.sum_div, sum_cast_Icc,
    hcard]
  simp only [nsmul_eq_mul]
  field_simp [hn0]

private theorem originalSeq_eq_localRoot (x : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    originalSeq x n =
      (1 / (n : ℝ)) * ∑ k ∈ Finset.Icc 1 n, localRoot x k n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  unfold originalSeq
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [scaledRoot_eq x k n hn]
  field_simp [hn0]

private theorem seq_sub_eq_sum (x : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    originalSeq x n - riemannSum x n =
      (1 / (n : ℝ)) *
        ∑ k ∈ Finset.Icc 1 n,
          (localRoot x k n - (x + (k : ℝ) / n)) := by
  rw [originalSeq_eq_localRoot x n hn]
  unfold riemannSum
  rw [Finset.sum_sub_distrib]
  ring

theorem gap1 (x : ℝ) (hx : 0 < x) (k n : ℕ)
    (hn : 1 ≤ n) (hk : k ∈ Finset.Icc 1 n) :
    0 ≤ localRoot x k n - (x + (k : ℝ) / n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have ha : 0 < x + (k : ℝ) / n := by positivity
  have hab : x + (k : ℝ) / n ≤ x + ((k : ℝ) + 1) / n := by
    have hfrac : (k : ℝ) / n ≤ ((k : ℝ) + 1) / n := by
      apply (div_le_div_iff₀ hnR hnR).2
      nlinarith
    simpa [add_comm] using add_le_add_left hfrac x
  rw [sub_nonneg]
  unfold localRoot
  apply (Real.le_sqrt' ha).2
  calc
    (x + (k : ℝ) / n) ^ 2 =
        (x + (k : ℝ) / n) * (x + (k : ℝ) / n) := by ring
    _ ≤ (x + (k : ℝ) / n) * (x + ((k : ℝ) + 1) / n) :=
      mul_le_mul_of_nonneg_left hab ha.le

theorem gap2 (x : ℝ) (hx : 0 < x) (k n : ℕ)
    (hn : 1 ≤ n) (hk : k ∈ Finset.Icc 1 n) :
    localRoot x k n - (x + (k : ℝ) / n) =
      (((x + (k : ℝ) / n) * (x + ((k : ℝ) + 1) / n) -
          (x + (k : ℝ) / n) ^ 2) /
        (localRoot x k n + x + (k : ℝ) / n)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have ha : 0 < x + (k : ℝ) / n := by positivity
  have hb : 0 < x + ((k : ℝ) + 1) / n := by positivity
  have hsq : (localRoot x k n) ^ 2 =
      (x + (k : ℝ) / n) * (x + ((k : ℝ) + 1) / n) := by
    unfold localRoot
    exact Real.sq_sqrt (mul_nonneg ha.le hb.le)
  have hden : localRoot x k n + x + (k : ℝ) / n ≠ 0 := by
    have hr0 : 0 ≤ localRoot x k n := by
      exact Real.sqrt_nonneg _
    nlinarith
  apply (eq_div_iff hden).2
  nlinarith [hsq]

theorem gap3 (x : ℝ) (hx : 0 < x) (k n : ℕ)
    (hn : 1 ≤ n) (hk : k ∈ Finset.Icc 1 n) :
    (((x + (k : ℝ) / n) * (x + ((k : ℝ) + 1) / n) -
          (x + (k : ℝ) / n) ^ 2) /
        (localRoot x k n + x + (k : ℝ) / n)) ≤
      (1 / (2 * x)) * (x + (k : ℝ) / n) * (1 / (n : ℝ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have ha : 0 < x + (k : ℝ) / n := by positivity
  have hnum :
      (x + (k : ℝ) / n) * (x + ((k : ℝ) + 1) / n) -
          (x + (k : ℝ) / n) ^ 2 =
        (x + (k : ℝ) / n) * (1 / (n : ℝ)) := by
    field_simp [hn0]
    ring
  have hrge : x + (k : ℝ) / n ≤ localRoot x k n := by
    exact sub_nonneg.mp (gap1 x hx k n hn hk)
  have hk0 : (0 : ℝ) ≤ (k : ℝ) / n := by positivity
  have hden : 2 * x ≤ localRoot x k n + x + (k : ℝ) / n := by
    nlinarith
  have hden0 : 0 < localRoot x k n + x + (k : ℝ) / n := by
    nlinarith
  have hnum0 : 0 ≤ (x + (k : ℝ) / n) * (1 / (n : ℝ)) := by positivity
  rw [hnum]
  calc
    ((x + (k : ℝ) / n) * (1 / (n : ℝ))) /
          (localRoot x k n + x + (k : ℝ) / n) ≤
        ((x + (k : ℝ) / n) * (1 / (n : ℝ))) / (2 * x) := by
      exact div_le_div_of_nonneg_left hnum0 (by positivity) hden
    _ = (1 / (2 * x)) * (x + (k : ℝ) / n) * (1 / (n : ℝ)) := by
      ring

theorem gap4 (x : ℝ) (hx : 0 < x) (k n : ℕ)
    (hn : 1 ≤ n) (hk : k ∈ Finset.Icc 1 n) :
    0 ≤ (1 / (2 * x)) * (x + (k : ℝ) / n) * (1 / (n : ℝ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  positivity

theorem gap5 (x : ℝ) (hx : 0 < x) (n : ℕ) (hn : 1 ≤ n) :
    0 ≤ originalSeq x n - riemannSum x n := by
  rw [seq_sub_eq_sum x n hn]
  apply mul_nonneg (by positivity)
  exact Finset.sum_nonneg fun k hk => gap1 x hx k n hn hk

theorem gap6 (x : ℝ) (hx : 0 < x) (n : ℕ) (hn : 1 ≤ n) :
    originalSeq x n - riemannSum x n ≤ errorBound x n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hsum :
      (∑ k ∈ Finset.Icc 1 n,
          (localRoot x k n - (x + (k : ℝ) / n))) ≤
        ∑ k ∈ Finset.Icc 1 n,
          (1 / (2 * x)) * (x + (k : ℝ) / n) * (1 / (n : ℝ)) := by
    apply Finset.sum_le_sum
    intro k hk
    rw [gap2 x hx k n hn hk]
    exact gap3 x hx k n hn hk
  have hsum_bound :
      (∑ k ∈ Finset.Icc 1 n,
          (1 / (2 * x)) * (x + (k : ℝ) / n) * (1 / (n : ℝ))) =
        ((1 / (2 * x)) * (1 / (n : ℝ))) *
          ∑ k ∈ Finset.Icc 1 n, (x + (k : ℝ) / n) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [seq_sub_eq_sum x n hn]
  unfold errorBound
  calc
    (1 / (n : ℝ)) *
          (∑ k ∈ Finset.Icc 1 n,
            (localRoot x k n - (x + (k : ℝ) / n))) ≤
        (1 / (n : ℝ)) *
          (∑ k ∈ Finset.Icc 1 n,
            (1 / (2 * x)) * (x + (k : ℝ) / n) * (1 / (n : ℝ))) := by
      exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (1 / (2 * x * (n : ℝ) ^ 2)) *
          ∑ k ∈ Finset.Icc 1 n, (x + (k : ℝ) / n) := by
      rw [hsum_bound]
      field_simp [hn0, ne_of_gt hx]

theorem gap7 (x : ℝ) (hx : 0 < x) (n : ℕ) (hn : 1 ≤ n) :
    errorBound x n = closedBound x n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  unfold errorBound closedBound
  rw [sum_affine_Icc x n hn]
  field_simp [hn0, ne_of_gt hx]
  ring

theorem gap8 (x : ℝ) (hx : 0 < x) :
    Tendsto (closedBound x) atTop (𝓝 0) := by
  have hone :
      Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hhalf :
      Tendsto (fun n : ℕ => 1 / (2 * (n : ℝ))) atTop (𝓝 0) := by
    have hscaled :=
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (1 / 2 : ℝ)) atTop (𝓝 (1 / 2 : ℝ))).mul hone
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hscaled
  have hproduct :
      Tendsto
        (fun n : ℕ =>
          (1 / (4 * x)) * (1 + 1 / (n : ℝ)) * (1 / (n : ℝ)))
        atTop (𝓝 0) := by
    have hmiddle :=
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 (1 : ℝ))).add hone
    have hzero := hmiddle.mul hone
    have hscaled :=
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (1 / (4 * x) : ℝ)) atTop
          (𝓝 (1 / (4 * x) : ℝ))).mul hzero
    simpa [mul_assoc] using hscaled
  unfold closedBound
  simpa using hhalf.add hproduct

theorem gap9 : (0 : ℝ) ≤ 0 := by norm_num

theorem gap10 (x : ℝ) (hx : 0 < x) :
    ∀ L : ℝ, Tendsto (originalSeq x) atTop (𝓝 L) ↔
      Tendsto (riemannSum x) atTop (𝓝 L) := by
  have hdiff :
      Tendsto (fun n : ℕ => originalSeq x n - riemannSum x n)
        atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
      (gap8 x hx) ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with n hn
      exact gap5 x hx n hn
    · filter_upwards [eventually_ge_atTop 1] with n hn
      rw [← gap7 x hx n hn]
      exact gap6 x hx n hn
  intro L
  constructor
  · intro horiginal
    have h := horiginal.sub hdiff
    convert h using 1
    · funext n
      ring
    · ring
  · intro hriemann
    have h := hriemann.add hdiff
    convert h using 1
    · funext n
      ring
    · ring

private theorem riemannSum_formula (x : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    riemannSum x n = x + 1 / 2 + 1 / (2 * (n : ℝ)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  unfold riemannSum
  rw [sum_affine_Icc x n hn]
  field_simp [hn0]
  ring

private theorem integral_affine (x : ℝ) :
    (∫ t in (0 : ℝ)..1, x + t) = x + 1 / 2 := by
  have hderiv (t : ℝ) :
      HasDerivAt (fun y : ℝ => x * y + y ^ 2 / 2) (x + t) t := by
    have hlinear := (hasDerivAt_const t x).mul (hasDerivAt_id t)
    have hquadratic := ((hasDerivAt_id t).pow 2).div_const 2
    convert hlinear.add hquadratic using 1 <;> simp [id_eq] <;> ring
  calc
    (∫ t in (0 : ℝ)..1, x + t) =
        (x * 1 + (1 : ℝ) ^ 2 / 2) -
          (x * 0 + (0 : ℝ) ^ 2 / 2) := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t _ => hderiv t)
      exact (continuous_const.add continuous_id).intervalIntegrable 0 1
    _ = x + 1 / 2 := by ring

theorem gap11 (x : ℝ) :
    Tendsto (riemannSum x) atTop
      (𝓝 (∫ t in (0 : ℝ)..1, x + t)) := by
  have heq : ∀ᶠ n : ℕ in atTop,
      riemannSum x n = x + 1 / 2 + 1 / (2 * (n : ℝ)) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact riemannSum_formula x n hn
  have hone :
      Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hhalf :
      Tendsto (fun n : ℕ => 1 / (2 * (n : ℝ))) atTop (𝓝 0) := by
    have hscaled :=
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (1 / 2 : ℝ)) atTop (𝓝 (1 / 2 : ℝ))).mul hone
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hscaled
  have hlimit :
      Tendsto (fun n : ℕ => x + 1 / 2 + 1 / (2 * (n : ℝ)))
        atTop (𝓝 (x + 1 / 2)) := by
    simpa using
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => x + 1 / 2) atTop (𝓝 (x + 1 / 2))).add hhalf
  rw [integral_affine x, tendsto_congr' heq]
  exact hlimit

theorem gap12 (x : ℝ) :
    (∫ t in (0 : ℝ)..1, x + t) = x + 1 / 2 := by
  exact integral_affine x

theorem gap13 (x : ℝ) (hx : 0 < x) :
    Tendsto (originalSeq x) atTop (𝓝 (x + 1 / 2)) := by
  apply (gap10 x hx (x + 1 / 2)).2
  simpa only [gap12 x] using gap11 x

end

end ProofGap.Exercise2229
