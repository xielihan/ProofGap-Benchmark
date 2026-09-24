import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods
import Mathlib.Analysis.Normed.Group.InfiniteSum

namespace ProofGap.Exercise2967

noncomputable section

open Filter
open scoped BigOperators

def denominator (q x : ℝ) : ℝ :=
  1 - 2 * q * Real.cos x + q ^ 2

def target (q x : ℝ) : ℝ :=
  (1 - q ^ 2) / denominator q x

def epos (x : ℝ) : ℂ :=
  Complex.exp (Complex.I * x)

def eneg (x : ℝ) : ℂ :=
  Complex.exp (-Complex.I * x)

def cosineSeries (q x : ℝ) : ℝ :=
  ∑' k : ℕ, q ^ (k + 1) * Real.cos ((k + 1 : ℝ) * x)

def poissonPartial (q : ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  1 + 2 *
    ∑ k ∈ Finset.range N,
      q ^ (k + 1) * Real.cos ((k + 1 : ℝ) * x)

theorem gap1 (q : ℝ) (hq : |q| < 1) :
    ∀ x,
      (target q x : ℂ) =
        (1 - (q : ℂ) ^ 2) /
          (1 - (q : ℂ) * (epos x + eneg x) + (q : ℂ) ^ 2) := by
  intro x
  have hexp : epos x + eneg x = (2 * Complex.cos (x : ℂ) : ℂ) := by
    unfold epos eneg
    rw [show Complex.I * (x : ℂ) = (x : ℂ) * Complex.I by ring]
    rw [show -Complex.I * (x : ℂ) = ((-x : ℝ) : ℂ) * Complex.I by
      push_cast
      ring_nf]
    rw [Complex.exp_mul_I, Complex.exp_mul_I]
    simp
    ring
  unfold target denominator
  push_cast
  rw [hexp]
  ring

theorem gap2 (q : ℝ) (hq : |q| < 1) :
    ∀ x,
      (target q x : ℂ) =
        (1 - (q : ℂ) ^ 2) *
          (1 / ((1 - (q : ℂ) * epos x) *
            (1 - (q : ℂ) * eneg x))) := by
  intro x
  have hprod : epos x * eneg x = 1 := by
    unfold epos eneg
    rw [← Complex.exp_add]
    have hz : Complex.I * (x : ℂ) + -Complex.I * (x : ℂ) = 0 := by ring
    rw [hz]
    simp
  rw [gap1 q hq x]
  have hfactor :
      (1 - (q : ℂ) * epos x) * (1 - (q : ℂ) * eneg x) =
        1 - (q : ℂ) * (epos x + eneg x) + (q : ℂ) ^ 2 := by
    calc
      (1 - (q : ℂ) * epos x) * (1 - (q : ℂ) * eneg x) =
          1 - (q : ℂ) * (epos x + eneg x) +
            (q : ℂ) ^ 2 * (epos x * eneg x) := by ring
      _ = 1 - (q : ℂ) * (epos x + eneg x) + (q : ℂ) ^ 2 := by
        rw [hprod]
        ring
  rw [← hfactor]
  simp [div_eq_mul_inv]

theorem gap3 (q : ℝ) (hq : |q| < 1) :
    ∀ x,
      (target q x : ℂ) =
        -1 +
          1 / (1 - (q : ℂ) * epos x) +
          1 / (1 - (q : ℂ) * eneg x) := by
  intro x
  have hqnorm : ‖(q : ℂ)‖ < 1 := by
    simpa using hq
  have hpnorm : ‖epos x‖ = 1 := by
    simp [epos, Complex.norm_exp]
  have hmnorm : ‖eneg x‖ = 1 := by
    simp [eneg, Complex.norm_exp]
  have hpne : 1 - (q : ℂ) * epos x ≠ 0 := by
    intro h
    have heq : (q : ℂ) * epos x = 1 := (sub_eq_zero.mp h).symm
    have hn := congrArg norm heq
    rw [norm_mul, hpnorm, norm_one, mul_one] at hn
    exact (ne_of_lt hqnorm) hn
  have hmne : 1 - (q : ℂ) * eneg x ≠ 0 := by
    intro h
    have heq : (q : ℂ) * eneg x = 1 := (sub_eq_zero.mp h).symm
    have hn := congrArg norm heq
    rw [norm_mul, hmnorm, norm_one, mul_one] at hn
    exact (ne_of_lt hqnorm) hn
  have hprod : epos x * eneg x = 1 := by
    unfold epos eneg
    rw [← Complex.exp_add]
    have hz : Complex.I * (x : ℂ) + -Complex.I * (x : ℂ) = 0 := by ring
    rw [hz]
    simp
  have hmul :
      ((q : ℂ) * epos x) * ((q : ℂ) * eneg x) = (q : ℂ) ^ 2 := by
    calc
      ((q : ℂ) * epos x) * ((q : ℂ) * eneg x) =
          (q : ℂ) ^ 2 * (epos x * eneg x) := by ring
      _ = (q : ℂ) ^ 2 := by
        rw [hprod]
        ring
  rw [gap2 q hq x, ← hmul]
  field_simp [hpne, hmne]
  ring

theorem gap4 (q : ℝ) (hq : |q| < 1) :
    ∀ x,
      (target q x : ℂ) =
        -1 +
          (∑' n : ℕ, (q : ℂ) ^ n * epos x ^ n) +
          ∑' n : ℕ, (q : ℂ) ^ n * eneg x ^ n := by
  intro x
  have hqnorm : ‖(q : ℂ)‖ < 1 := by
    simpa using hq
  have hpnorm : ‖epos x‖ = 1 := by
    simp [epos, Complex.norm_exp]
  have hmnorm : ‖eneg x‖ = 1 := by
    simp [eneg, Complex.norm_exp]
  have hp_lt : ‖(q : ℂ) * epos x‖ < 1 := by
    rw [norm_mul, hpnorm, mul_one]
    exact hqnorm
  have hm_lt : ‖(q : ℂ) * eneg x‖ < 1 := by
    rw [norm_mul, hmnorm, mul_one]
    exact hqnorm
  have hp :
      (∑' n : ℕ, (q : ℂ) ^ n * epos x ^ n) =
        1 / (1 - (q : ℂ) * epos x) := by
    simpa [mul_pow, one_div] using
      (hasSum_geometric_of_norm_lt_one hp_lt).tsum_eq
  have hm :
      (∑' n : ℕ, (q : ℂ) ^ n * eneg x ^ n) =
        1 / (1 - (q : ℂ) * eneg x) := by
    simpa [mul_pow, one_div] using
      (hasSum_geometric_of_norm_lt_one hm_lt).tsum_eq
  simpa [hp, hm] using gap3 q hq x

theorem gap5 (q : ℝ) (hq : |q| < 1) :
    ∀ x, target q x = 1 + 2 * cosineSeries q x := by
  intro x
  have hqnorm : ‖(q : ℂ)‖ < 1 := by
    simpa using hq
  have hpnorm : ‖epos x‖ = 1 := by
    simp [epos, Complex.norm_exp]
  have hmnorm : ‖eneg x‖ = 1 := by
    simp [eneg, Complex.norm_exp]
  have hp_lt : ‖(q : ℂ) * epos x‖ < 1 := by
    rw [norm_mul, hpnorm, mul_one]
    exact hqnorm
  have hm_lt : ‖(q : ℂ) * eneg x‖ < 1 := by
    rw [norm_mul, hmnorm, mul_one]
    exact hqnorm
  have hspos : Summable (fun n : ℕ => (q : ℂ) ^ n * epos x ^ n) := by
    simpa [mul_pow] using summable_geometric_of_norm_lt_one hp_lt
  have hsneg : Summable (fun n : ℕ => (q : ℂ) ^ n * eneg x ^ n) := by
    simpa [mul_pow] using summable_geometric_of_norm_lt_one hm_lt
  have hepos_pow (n : ℕ) :
      epos x ^ n = Complex.exp (Complex.I * (((n : ℝ) * x : ℝ) : ℂ)) := by
    unfold epos
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have heneg_pow (n : ℕ) :
      eneg x ^ n = Complex.exp (-Complex.I * (((n : ℝ) * x : ℝ) : ℂ)) := by
    unfold eneg
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hqpow_re (n : ℕ) : ((q : ℂ) ^ n).re = q ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
        simp [pow_succ, ih]
  have hqpow_im (n : ℕ) : ((q : ℂ) ^ n).im = 0 := by
    induction n with
    | zero => simp
    | succ n ih =>
        simp [pow_succ, ih]
  have hposre (n : ℕ) :
      ((q : ℂ) ^ n * epos x ^ n).re =
        q ^ n * Real.cos ((n : ℝ) * x) := by
    rw [hepos_pow]
    simp [hqpow_re, hqpow_im, Complex.exp_re]
  have hnegre (n : ℕ) :
      ((q : ℂ) ^ n * eneg x ^ n).re =
        q ^ n * Real.cos ((n : ℝ) * x) := by
    rw [heneg_pow]
    simp [hqpow_re, hqpow_im, Complex.exp_re]
  have hrpos :
      (∑' n : ℕ, (q : ℂ) ^ n * epos x ^ n).re =
        ∑' n : ℕ, ((q : ℂ) ^ n * epos x ^ n).re :=
    Complex.reCLM.map_tsum hspos
  have hrneg :
      (∑' n : ℕ, (q : ℂ) ^ n * eneg x ^ n).re =
        ∑' n : ℕ, ((q : ℂ) ^ n * eneg x ^ n).re :=
    Complex.reCLM.map_tsum hsneg
  let f : ℕ → ℝ := fun n => q ^ n * Real.cos ((n : ℝ) * x)
  have hf : Summable f := by
    have hrf :
        Summable (fun n : ℕ => ((q : ℂ) ^ n * epos x ^ n).re) := by
      simpa [Function.comp_def] using
        (hspos.map Complex.reCLM Complex.reCLM.continuous)
    simpa [f, hposre] using hrf
  have hsplit : (∑' n : ℕ, f n) = 1 + cosineSeries q x := by
    have hs := (hf.sum_add_tsum_nat_add 1).symm
    simpa [f, cosineSeries, add_comm, add_left_comm, add_assoc] using hs
  have h := congrArg Complex.re (gap4 q hq x)
  change target q x =
      -1 + (∑' n : ℕ, (q : ℂ) ^ n * epos x ^ n).re +
        (∑' n : ℕ, (q : ℂ) ^ n * eneg x ^ n).re at h
  rw [hrpos, hrneg] at h
  simp_rw [hposre, hnegre] at h
  change target q x = -1 + (∑' n : ℕ, f n) + ∑' n : ℕ, f n at h
  rw [hsplit] at h
  rw [h]
  ring

theorem gap6 (q : ℝ) (hq : |q| < 1) :
    TendstoUniformlyOn
      (poissonPartial q) (target q) atTop Set.univ := by
  let a : ℝ := |q|
  let f : ℝ → ℕ → ℝ := fun x k =>
    q ^ (k + 1) * Real.cos ((k + 1 : ℝ) * x)
  have ha0 : 0 ≤ a := by
    exact abs_nonneg q
  have ha1 : a < 1 := by
    exact hq
  have hg : Summable (fun k : ℕ => a ^ k) := by
    apply summable_geometric_of_norm_lt_one
    simpa [Real.norm_eq_abs, abs_of_nonneg ha0] using ha1
  have hfnorm (x : ℝ) (k : ℕ) : ‖f x k‖ ≤ a ^ (k + 1) := by
    change ‖q ^ (k + 1) * Real.cos ((k + 1 : ℝ) * x)‖ ≤ a ^ (k + 1)
    calc
      ‖q ^ (k + 1) * Real.cos ((k + 1 : ℝ) * x)‖ =
          a ^ (k + 1) * |Real.cos ((k + 1 : ℝ) * x)| := by
            simp [a, Real.norm_eq_abs]
      _ ≤ a ^ (k + 1) * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _)
          (pow_nonneg ha0 (k + 1))
      _ = a ^ (k + 1) := by ring
  have hf (x : ℝ) : Summable (f x) := by
    apply Summable.of_norm_bounded (hg.mul_left a)
    intro k
    calc
      ‖f x k‖ ≤ a ^ (k + 1) := hfnorm x k
      _ = a * a ^ k := by
        rw [pow_succ]
        ring
  have hsplit (x : ℝ) (N : ℕ) :
      cosineSeries q x =
        (∑ k ∈ Finset.range N, f x k) + ∑' k : ℕ, f x (N + k) := by
    unfold cosineSeries
    simpa [f, add_comm, add_left_comm, add_assoc] using
      ((hf x).sum_add_tsum_nat_add N).symm
  have htail (x : ℝ) (N : ℕ) :
      |∑' k : ℕ, f x (N + k)| ≤ a ^ (N + 1) / (1 - a) := by
    have hmajor : Summable (fun k : ℕ => a ^ (N + 1) * a ^ k) :=
      hg.mul_left (a ^ (N + 1))
    have hterm (k : ℕ) :
        ‖f x (N + k)‖ ≤ a ^ (N + 1) * a ^ k := by
      calc
        ‖f x (N + k)‖ ≤ a ^ ((N + k) + 1) := hfnorm x (N + k)
        _ = a ^ (N + 1) * a ^ k := by
          rw [Nat.add_right_comm N k 1, pow_add]
    have hnorm : Summable (fun k : ℕ => ‖f x (N + k)‖) := by
      apply Summable.of_norm_bounded hmajor
      intro k
      simpa [Real.norm_eq_abs] using hterm k
    have hb :
        ‖∑' k : ℕ, f x (N + k)‖ ≤
          ∑' k : ℕ, a ^ (N + 1) * a ^ k := by
      calc
        ‖∑' k : ℕ, f x (N + k)‖ ≤
            ∑' k : ℕ, ‖f x (N + k)‖ :=
          norm_tsum_le_tsum_norm hnorm
        _ ≤ ∑' k : ℕ, a ^ (N + 1) * a ^ k :=
          hnorm.tsum_le_tsum hterm hmajor
    calc
      |∑' k : ℕ, f x (N + k)| = ‖∑' k : ℕ, f x (N + k)‖ := by
        simp [Real.norm_eq_abs]
      _ ≤ ∑' k : ℕ, a ^ (N + 1) * a ^ k := hb
      _ = a ^ (N + 1) * (1 - a)⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_norm_lt_one]
        simpa [Real.norm_eq_abs, abs_of_nonneg ha0] using ha1
      _ = a ^ (N + 1) / (1 - a) := by rw [div_eq_mul_inv]
  have hpow : Tendsto (fun N : ℕ => a ^ N) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one ha0 ha1
  have hbound :
      Tendsto (fun N : ℕ => 2 * (a ^ N / (1 - a))) atTop (nhds 0) := by
    have hd := hpow.div_const (1 - a)
    have htwo :
        Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (nhds 2) :=
      tendsto_const_nhds
    have hm := htwo.mul hd
    simpa using hm
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hev : ∀ᶠ N : ℕ in atTop, 2 * (a ^ N / (1 - a)) < ε :=
    (tendsto_order.1 hbound).2 ε hε
  filter_upwards [hev] with N hN
  intro x hx
  have hpowle : a ^ (N + 1) ≤ a ^ N := by
    rw [pow_succ]
    exact mul_le_of_le_one_right (pow_nonneg ha0 N) (le_of_lt ha1)
  have hdivle : a ^ (N + 1) / (1 - a) ≤ a ^ N / (1 - a) :=
    div_le_div_of_nonneg_right hpowle (le_of_lt (sub_pos.mpr ha1))
  have htgt :
      target q x =
        1 + 2 * ((∑ k ∈ Finset.range N, f x k) +
          ∑' k : ℕ, f x (N + k)) := by
    rw [gap5 q hq x, hsplit x N]
  have hpart :
      poissonPartial q N x =
        1 + 2 * ∑ k ∈ Finset.range N, f x k := by
    rfl
  have herr :
      dist (target q x) (poissonPartial q N x) =
        2 * |∑' k : ℕ, f x (N + k)| := by
    rw [Real.dist_eq, htgt, hpart]
    ring_nf
    simp [abs_mul]
  rw [herr]
  calc
    2 * |∑' k : ℕ, f x (N + k)| ≤
        2 * (a ^ (N + 1) / (1 - a)) :=
      mul_le_mul_of_nonneg_left (htail x N) (by norm_num)
    _ ≤ 2 * (a ^ N / (1 - a)) :=
      mul_le_mul_of_nonneg_left hdivle (by norm_num)
    _ < ε := hN

end

end ProofGap.Exercise2967
