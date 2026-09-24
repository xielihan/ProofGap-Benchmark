import ProofGapLean.Prelude.Elementary
import ProofGapLean.Prelude.Finite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise1109

noncomputable section

def lg (x : ℝ) : ℝ := Real.log x / Real.log 10

private lemma log_lower_bound (t : ℝ) (ht : 0 ≤ t) :
    t / (1 + t) ≤ Real.log (1 + t) := by
  have hpos : 0 < 1 + t := by linarith
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
  rw [Real.log_inv] at h
  have hid :
      (1 + t)⁻¹ - 1 = -(t / (1 + t)) := by
    field_simp [hpos.ne'] <;> ring
  rw [hid] at h
  linarith

private lemma log_succ_estimate (n : ℕ) (hn : 0 < n) :
    (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ≤
        Real.log (((n + 1 : ℕ) : ℝ)) - Real.log (n : ℝ) ∧
      Real.log (((n + 1 : ℕ) : ℝ)) - Real.log (n : ℝ) ≤
        (1 : ℝ) / (n : ℝ) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hratio_eq :
      (((n + 1 : ℕ) : ℝ) / (n : ℝ)) = 1 + (1 : ℝ) / (n : ℝ) := by
    rw [Nat.cast_add, Nat.cast_one]
    field_simp [hnR.ne']
  have hlogeq :
      Real.log (((n + 1 : ℕ) : ℝ)) - Real.log (n : ℝ) =
        Real.log (1 + (1 : ℝ) / (n : ℝ)) := by
    calc
      Real.log (((n + 1 : ℕ) : ℝ)) - Real.log (n : ℝ) =
          Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ)) := by
            rw [Real.log_div (by positivity) (by positivity)]
      _ = Real.log (1 + (1 : ℝ) / (n : ℝ)) := by rw [hratio_eq]
  have hlo := log_lower_bound ((1 : ℝ) / (n : ℝ)) (by positivity)
  have hup := Real.log_le_sub_one_of_pos
    (show 0 < 1 + (1 : ℝ) / (n : ℝ) by positivity)
  constructor
  · calc
      (1 : ℝ) / ((n + 1 : ℕ) : ℝ) =
          ((1 : ℝ) / (n : ℝ)) / (1 + (1 : ℝ) / (n : ℝ)) := by
            rw [Nat.cast_add, Nat.cast_one]
            field_simp [hnR.ne']
      _ ≤ Real.log (1 + (1 : ℝ) / (n : ℝ)) := hlo
      _ = Real.log (((n + 1 : ℕ) : ℝ)) - Real.log (n : ℝ) := hlogeq.symm
  · calc
      Real.log (((n + 1 : ℕ) : ℝ)) - Real.log (n : ℝ) =
          Real.log (1 + (1 : ℝ) / (n : ℝ)) := hlogeq
      _ ≤ (1 + (1 : ℝ) / (n : ℝ)) - 1 := hup
      _ = (1 : ℝ) / (n : ℝ) := by ring

private lemma log_interval_estimate (m r : ℕ) (hm : 0 < m) :
    (Finset.range r).sum
        (fun k => (1 : ℝ) / ((m + k + 1 : ℕ) : ℝ)) ≤
        Real.log ((m + r : ℕ) : ℝ) - Real.log (m : ℝ) ∧
      Real.log ((m + r : ℕ) : ℝ) - Real.log (m : ℝ) ≤
        (Finset.range r).sum
          (fun k => (1 : ℝ) / ((m + k : ℕ) : ℝ)) := by
  induction r with
  | zero => simp
  | succ r ihr =>
      have hmr : 0 < m + r := Nat.add_pos_left hm r
      have hs := log_succ_estimate (m + r) hmr
      have heq : m + r + 1 = m + Nat.succ r := by omega
      simp only [Finset.sum_range_succ]
      constructor
      · calc
          (Finset.range r).sum
                (fun k => (1 : ℝ) / ((m + k + 1 : ℕ) : ℝ)) +
              (1 : ℝ) / ((m + r + 1 : ℕ) : ℝ) ≤
              (Real.log ((m + r : ℕ) : ℝ) - Real.log (m : ℝ)) +
                (Real.log ((m + r + 1 : ℕ) : ℝ) -
                  Real.log ((m + r : ℕ) : ℝ)) :=
            add_le_add ihr.1 hs.1
          _ = Real.log ((m + Nat.succ r : ℕ) : ℝ) - Real.log (m : ℝ) := by
            rw [← heq]
            ring
      · calc
          Real.log ((m + Nat.succ r : ℕ) : ℝ) - Real.log (m : ℝ) =
              (Real.log ((m + r : ℕ) : ℝ) - Real.log (m : ℝ)) +
                (Real.log ((m + r + 1 : ℕ) : ℝ) -
                  Real.log ((m + r : ℕ) : ℝ)) := by
            rw [← heq]
            ring
          _ ≤ (Finset.range r).sum
                (fun k => (1 : ℝ) / ((m + k : ℕ) : ℝ)) +
                (1 : ℝ) / ((m + r : ℕ) : ℝ) :=
            add_le_add ihr.2 hs.2

private lemma log_ten_bounds :
    (23021 / 10000 : ℝ) < Real.log 10 ∧
      Real.log 10 < (2303 / 1000 : ℝ) := by
  set_option maxHeartbeats 2000000 in
    have hq := log_interval_estimate 4000 40 (by norm_num)
    have hdiv :
        Real.log ((4040 : ℝ) / 4000) =
          Real.log (4040 : ℝ) - Real.log (4000 : ℝ) := by
      rw [Real.log_div (by norm_num) (by norm_num)]
    norm_num [Finset.sum_range_succ] at hq
    rw [← hdiv] at hq
    norm_num at hq
    let q : ℝ := 101 / 100
    have hprodlo : q ^ 231 * (251 / 250 : ℝ) < 10 := by
      norm_num [q, div_pow]
    have hprodhi : 10 < q ^ 231 * (10041 / 10000 : ℝ) := by
      norm_num [q, div_pow]
    have harglo : 0 < q ^ 231 * (251 / 250 : ℝ) := by
      exact mul_pos (pow_pos (by norm_num [q]) 231) (by norm_num)
    have harghi : 0 < q ^ 231 * (10041 / 10000 : ℝ) := by
      exact mul_pos (pow_pos (by norm_num [q]) 231) (by norm_num)
    have hloglo :
        Real.log (q ^ 231 * (251 / 250 : ℝ)) < Real.log 10 :=
      Real.strictMonoOn_log harglo (by norm_num) hprodlo
    have hloghi :
        Real.log 10 < Real.log (q ^ 231 * (10041 / 10000 : ℝ)) :=
      Real.strictMonoOn_log (by norm_num) harghi hprodhi
    have hqne : q ≠ 0 := by norm_num [q]
    have hpowne : q ^ 231 ≠ 0 := pow_ne_zero 231 hqne
    have hlofactorne : (251 / 250 : ℝ) ≠ 0 := by norm_num
    have hhifactorne : (10041 / 10000 : ℝ) ≠ 0 := by norm_num
    rw [Real.log_mul hpowne hlofactorne, Real.log_pow] at hloglo
    rw [Real.log_mul hpowne hhifactorne, Real.log_pow] at hloghi
    norm_num at hloglo hloghi
    have hlo := log_lower_bound (1 / 250 : ℝ) (by norm_num)
    have hhi := Real.log_le_sub_one_of_pos
      (by norm_num : (0 : ℝ) < (10041 / 10000 : ℝ))
    norm_num at hlo hhi
    constructor <;> nlinarith [hq.1, hq.2, hlo, hhi, hloglo, hloghi]

theorem gap1 (x dx : ℝ) (hx : 0 < x) (hdx : 0 ≤ dx) :
    |lg (x + dx) - lg x| = |lg (1 + dx / x)| := by
  have hxsum : 0 < x + dx := by linarith
  unfold lg
  apply congrArg abs
  calc
    Real.log (x + dx) / Real.log 10 - Real.log x / Real.log 10 =
        (Real.log (x + dx) - Real.log x) / Real.log 10 := by ring
    _ = Real.log ((x + dx) / x) / Real.log 10 := by
      rw [Real.log_div hxsum.ne' hx.ne']
    _ = Real.log (1 + dx / x) / Real.log 10 := by
      have hquot : (x + dx) / x = 1 + dx / x := by
        field_simp [hx.ne']
      rw [hquot]

theorem gap2 (x dx δ : ℝ) (hx : 0 < x) (hdx : 0 ≤ dx)
    (hδ : δ = |dx / x|) :
    |lg (1 + dx / x)| = |lg (1 + δ)| := by
  have hquot : 0 ≤ dx / x := div_nonneg hdx (le_of_lt hx)
  have hδ' : δ = dx / x := by
    rw [hδ, abs_of_nonneg hquot]
  rw [hδ']

theorem gap3 (δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 0.01) :
    abs (|lg (1 + δ)| - (1 / Real.log 10) * δ) ≤ 0.003 * δ := by
  have hL := log_ten_bounds
  have hLpos : 0 < Real.log 10 := by nlinarith [hL.1]
  have h1 : 0 < 1 + δ := by linarith
  have h3δ : 0 < 3 + δ := by linarith
  have h32δ : 0 < 3 + 2 * δ := by nlinarith
  have h33δ : 0 < 3 + 3 * δ := by nlinarith
  have ha := log_lower_bound (δ / 3) (div_nonneg hδ0 (by norm_num))
  have hb := log_lower_bound (δ / (3 + δ))
    (div_nonneg hδ0 (le_of_lt h3δ))
  have hc := log_lower_bound (δ / (3 + 2 * δ))
    (div_nonneg hδ0 (le_of_lt h32δ))
  have hA : 0 < 1 + δ / 3 := by positivity
  have hB : 0 < 1 + δ / (3 + δ) := by positivity
  have hC : 0 < 1 + δ / (3 + 2 * δ) := by positivity
  have hfactor :
      1 + δ =
        ((1 + δ / 3) * (1 + δ / (3 + δ))) *
          (1 + δ / (3 + 2 * δ)) := by
    field_simp [ne_of_gt h3δ, ne_of_gt h32δ] <;> ring
  have hlogfactor :
      Real.log (1 + δ) =
        Real.log (1 + δ / 3) +
          Real.log (1 + δ / (3 + δ)) +
            Real.log (1 + δ / (3 + 2 * δ)) := by
    calc
      Real.log (1 + δ) =
          Real.log (((1 + δ / 3) * (1 + δ / (3 + δ))) *
            (1 + δ / (3 + 2 * δ))) := by rw [hfactor]
      _ = Real.log ((1 + δ / 3) * (1 + δ / (3 + δ))) +
            Real.log (1 + δ / (3 + 2 * δ)) := by
          rw [Real.log_mul (mul_ne_zero hA.ne' hB.ne') hC.ne']
      _ = Real.log (1 + δ / 3) + Real.log (1 + δ / (3 + δ)) +
            Real.log (1 + δ / (3 + 2 * δ)) := by
          rw [Real.log_mul hA.ne' hB.ne']
  have ha' :
      δ / (3 + δ) ≤ Real.log (1 + δ / 3) := by
    calc
      δ / (3 + δ) = (δ / 3) / (1 + δ / 3) := by
        field_simp [ne_of_gt h3δ] <;> ring
      _ ≤ Real.log (1 + δ / 3) := ha
  have hb' :
      δ / (3 + 2 * δ) ≤ Real.log (1 + δ / (3 + δ)) := by
    calc
      δ / (3 + 2 * δ) =
          (δ / (3 + δ)) / (1 + δ / (3 + δ)) := by
        field_simp [ne_of_gt h3δ, ne_of_gt h32δ] <;> ring
      _ ≤ Real.log (1 + δ / (3 + δ)) := hb
  have hc' :
      δ / (3 + 3 * δ) ≤ Real.log (1 + δ / (3 + 2 * δ)) := by
    calc
      δ / (3 + 3 * δ) =
          (δ / (3 + 2 * δ)) / (1 + δ / (3 + 2 * δ)) := by
        field_simp [ne_of_gt h32δ, ne_of_gt h33δ] <;> ring
      _ ≤ Real.log (1 + δ / (3 + 2 * δ)) := hc
  have ht1 : δ / 3 - δ ^ 2 / 9 ≤ δ / (3 + δ) := by
    have hn : 0 ≤ δ ^ 3 / (9 * (3 + δ)) := by positivity
    have hid :
        δ / (3 + δ) - (δ / 3 - δ ^ 2 / 9) =
          δ ^ 3 / (9 * (3 + δ)) := by
      field_simp [ne_of_gt h3δ] <;> ring
    nlinarith
  have ht2 : δ / 3 - 2 * δ ^ 2 / 9 ≤ δ / (3 + 2 * δ) := by
    have hn : 0 ≤ 4 * δ ^ 3 / (9 * (3 + 2 * δ)) := by positivity
    have hid :
        δ / (3 + 2 * δ) - (δ / 3 - 2 * δ ^ 2 / 9) =
          4 * δ ^ 3 / (9 * (3 + 2 * δ)) := by
      field_simp [ne_of_gt h32δ] <;> ring
    nlinarith
  have ht3 : δ / 3 - 3 * δ ^ 2 / 9 ≤ δ / (3 + 3 * δ) := by
    have hn : 0 ≤ 9 * δ ^ 3 / (9 * (3 + 3 * δ)) := by positivity
    have hid :
        δ / (3 + 3 * δ) - (δ / 3 - 3 * δ ^ 2 / 9) =
          9 * δ ^ 3 / (9 * (3 + 3 * δ)) := by
      field_simp [ne_of_gt h33δ] <;> ring
    nlinarith
  have hlog_lower :
      δ - (2 / 3 : ℝ) * δ ^ 2 ≤ Real.log (1 + δ) := by
    rw [hlogfactor]
    nlinarith [ha', hb', hc', ht1, ht2, ht3]
  have hlog_upper : Real.log (1 + δ) ≤ δ := by
    simpa using Real.log_le_sub_one_of_pos h1
  have hlog_nonneg : 0 ≤ Real.log (1 + δ) :=
    Real.log_nonneg (by linarith)
  have herr :
      δ - Real.log (1 + δ) ≤ (2 / 3 : ℝ) * δ ^ 2 := by
    linarith
  have hsquare : δ ^ 2 ≤ (1 / 100 : ℝ) * δ := by
    nlinarith [mul_nonneg hδ0 (sub_nonneg.mpr hδ1)]
  have hbase : 0 ≤ Real.log 10 - 23021 / 10000 := by
    linarith [hL.1]
  have hm : 0 ≤ δ * (Real.log 10 - 23021 / 10000) :=
    mul_nonneg hδ0 hbase
  have hscale :
      (2 / 3 : ℝ) * δ ^ 2 ≤ 0.003 * δ * Real.log 10 := by
    nlinarith [hsquare, hm]
  unfold lg
  rw [abs_of_nonneg (div_nonneg hlog_nonneg (le_of_lt hLpos))]
  have hd :
      Real.log (1 + δ) / Real.log 10 ≤ δ / Real.log 10 :=
    div_le_div_of_nonneg_right hlog_upper (le_of_lt hLpos)
  have hcoefeq :
      (1 / Real.log 10) * δ = δ / Real.log 10 := by ring
  have hdiff :
      Real.log (1 + δ) / Real.log 10 -
          (1 / Real.log 10) * δ ≤ 0 := by
    rw [hcoefeq]
    exact sub_nonpos.mpr hd
  rw [abs_of_nonpos hdiff]
  have hfinal :
      (δ - Real.log (1 + δ)) / Real.log 10 ≤ 0.003 * δ := by
    apply (div_le_iff₀ hLpos).2
    exact le_trans herr hscale
  calc
    -(Real.log (1 + δ) / Real.log 10 -
        (1 / Real.log 10) * δ) =
        (δ - Real.log (1 + δ)) / Real.log 10 := by ring
    _ ≤ 0.003 * δ := hfinal

theorem gap4 :
    |(1 / Real.log 10 : ℝ) - 0.4343| < 0.0001 := by
  have hL := log_ten_bounds
  have hLpos : 0 < Real.log 10 := by nlinarith [hL.1]
  rw [abs_lt]
  constructor
  · have hc : (0.4342 : ℝ) < 1 / Real.log 10 := by
      apply (lt_div_iff₀ hLpos).2
      nlinarith [hL.2]
    nlinarith
  · have hc : 1 / Real.log 10 < (0.4344 : ℝ) := by
      apply (div_lt_iff₀ hLpos).2
      nlinarith [hL.1]
    nlinarith

theorem gap5 (x dx δ : ℝ) (hx : 0 < x) (hdx : 0 ≤ dx)
    (hδ : δ = |dx / x|) (hsmall : δ ≤ 0.01) :
    abs (|lg (x + dx) - lg x| - 0.4343 * δ) ≤ 0.0031 * δ := by
  have hδ0 : 0 ≤ δ := by
    rw [hδ]
    exact abs_nonneg _
  rw [gap1 x dx hx hdx, gap2 x dx δ hx hdx hδ]
  have hmain := gap3 δ hδ0 hsmall
  have hcoef := gap4
  have hcoef_mul :
      abs (((1 / Real.log 10) - 0.4343) * δ) ≤ 0.0001 * δ := by
    rw [abs_mul, abs_of_nonneg hδ0]
    exact mul_le_mul_of_nonneg_right (le_of_lt hcoef) hδ0
  calc
    abs (|lg (1 + δ)| - 0.4343 * δ) =
        abs ((|lg (1 + δ)| - (1 / Real.log 10) * δ) +
          (((1 / Real.log 10) - 0.4343) * δ)) := by ring
    _ ≤ abs (|lg (1 + δ)| - (1 / Real.log 10) * δ) +
          abs (((1 / Real.log 10) - 0.4343) * δ) := abs_add_le _ _
    _ ≤ 0.003 * δ + 0.0001 * δ := add_le_add hmain hcoef_mul
    _ = 0.0031 * δ := by ring

theorem gap6 (x dx δ : ℝ) (hx : 0 < x) (hdx : 0 ≤ dx)
    (hδ : δ = |dx / x|) (hsmall : δ ≤ 0.01) :
    abs (|lg (x + dx) - lg x| - 0.4343 * δ) ≤ 0.0031 * δ := by
  exact gap5 x dx δ hx hdx hδ hsmall

end

end ProofGap.Exercise1109
