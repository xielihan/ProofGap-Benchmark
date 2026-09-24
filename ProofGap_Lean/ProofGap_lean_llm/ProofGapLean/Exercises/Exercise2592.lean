import ProofGapLean.Prelude.Analysis
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise2592

noncomputable section

def ratio (a : ℕ → ℝ) (n : ℕ) : ℝ := a (n + 1) / a n

def TailSummable (u : ℕ → ℝ) (n₀ : ℕ) : Prop :=
  Summable (fun k : ℕ => u (k + n₀))

def counterexample (n : ℕ) : ℝ :=
  if n % 2 = 1 then 1 / (2 : ℝ) ^ (n / 2 + 1)
  else if n = 0 then 0 else 1 / (3 : ℝ) ^ (n / 2)

private theorem counterexample_norm_le (n : ℕ) :
    ‖counterexample n‖ ≤ (3 / 4 : ℝ) ^ n := by
  have hc : 0 ≤ counterexample n := by
    unfold counterexample
    split_ifs <;> positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hc]
  by_cases hodd : n % 2 = 1
  · have hn : n = 2 * (n / 2) + 1 := by omega
    simp only [counterexample, hodd, if_pos]
    have hpow :
        (1 / 2 : ℝ) ^ (n / 2) ≤ (9 / 16 : ℝ) ^ (n / 2) := by
      generalize n / 2 = m
      induction m with
      | zero => norm_num
      | succ k ih =>
          rw [pow_succ, pow_succ]
          have hk : 0 ≤ (9 / 16 : ℝ) ^ k := by positivity
          nlinarith
    calc
      1 / (2 : ℝ) ^ (n / 2 + 1) =
          (1 / 2 : ℝ) ^ (n / 2 + 1) := by rw [one_div_pow]
      _ = (1 / 2 : ℝ) ^ (n / 2) * (1 / 2 : ℝ) := by
          rw [pow_succ]
      _ ≤ (9 / 16 : ℝ) ^ (n / 2) * (3 / 4 : ℝ) := by
          have hk : 0 ≤ (9 / 16 : ℝ) ^ (n / 2) := by positivity
          nlinarith
      _ = (3 / 4 : ℝ) ^ (2 * (n / 2) + 1) := by
          rw [pow_succ, pow_mul]
          norm_num
      _ = (3 / 4 : ℝ) ^ n := by
          congr 1
          omega
  · have hmod : n % 2 = 0 := by omega
    by_cases hn0 : n = 0
    · subst n
      norm_num [counterexample]
    · have hn : n = 2 * (n / 2) := by omega
      simp only [counterexample, hodd, if_false, hn0]
      have hpow :
          (1 / 3 : ℝ) ^ (n / 2) ≤ (9 / 16 : ℝ) ^ (n / 2) := by
        generalize n / 2 = m
        induction m with
        | zero => norm_num
        | succ k ih =>
            rw [pow_succ, pow_succ]
            have hk : 0 ≤ (9 / 16 : ℝ) ^ k := by positivity
            nlinarith
      calc
        1 / (3 : ℝ) ^ (n / 2) = (1 / 3 : ℝ) ^ (n / 2) := by
          rw [one_div_pow]
        _ ≤ (9 / 16 : ℝ) ^ (n / 2) := hpow
        _ = (3 / 4 : ℝ) ^ (2 * (n / 2)) := by
          rw [pow_mul]
          norm_num
        _ = (3 / 4 : ℝ) ^ n := by
          congr 1
          omega

theorem gap1
    (a : ℕ → ℝ) (q : ℝ)
    (hratio : Tendsto (ratio a) atTop (nhds q))
    (hq : q < 1)
    (hpos : ∀ n, 0 < a n) :
    ∀ ε : ℝ, 0 < ε → ε < 1 - q →
      ∃ l : ℝ, ∃ n₀ : ℕ, 1 ≤ n₀ ∧ l = q + ε ∧ l < 1 ∧
        ∀ n ≥ n₀, ratio a n < l := by
  intro ε hε hεq
  have hevent : ∀ᶠ n in atTop, ratio a n < q + ε :=
    (tendsto_order.1 hratio).2 (q + ε) (by linarith)
  rcases Filter.eventually_atTop.1 hevent with ⟨N, hN⟩
  refine ⟨q + ε, max 1 N, le_max_left _ _, rfl, by linarith, ?_⟩
  intro n hn
  exact hN n (le_trans (le_max_right 1 N) hn)

theorem gap2
    (a : ℕ → ℝ) (q : ℝ)
    (hpos : ∀ n, 0 < a n)
    (hratioBound : ∀ ε : ℝ, 0 < ε → ε < 1 - q →
      ∃ l : ℝ, ∃ n₀ : ℕ, 1 ≤ n₀ ∧ l = q + ε ∧ l < 1 ∧
        ∀ n ≥ n₀, ratio a n < l) :
    ∀ ε : ℝ, 0 < ε → ε < 1 - q →
      ∃ l : ℝ, ∃ n₀ : ℕ, 1 ≤ n₀ ∧ 0 ≤ l ∧ l < 1 ∧
        ∀ n ≥ n₀, 0 < a n ∧
          a n ≤ a n₀ * l ^ (n - n₀) := by
  intro ε hε hεq
  rcases hratioBound ε hε hεq with
    ⟨l, n₀, hn₀, rfl, hl, hratio⟩
  have hratioPos : 0 < ratio a n₀ := by
    simpa [ratio] using div_pos (hpos (n₀ + 1)) (hpos n₀)
  have hl0 : 0 ≤ q + ε :=
    le_of_lt (lt_trans hratioPos (hratio n₀ le_rfl))
  refine ⟨q + ε, n₀, hn₀, hl0, hl, ?_⟩
  intro n hn
  refine ⟨hpos n, ?_⟩
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
      have hratio_n := hratio n hn
      have hstep : a (n + 1) ≤ a n * (q + ε) := by
        apply le_of_lt
        have hdiv := (div_lt_iff₀ (hpos n)).mp (by simpa [ratio] using hratio_n)
        simpa [mul_comm] using hdiv
      calc
        a (n + 1) ≤ a n * (q + ε) := hstep
        _ ≤ (a n₀ * (q + ε) ^ (n - n₀)) * (q + ε) :=
          mul_le_mul_of_nonneg_right ih hl0
        _ = a n₀ * (q + ε) ^ ((n + 1) - n₀) := by
          simp [Nat.succ_sub hn, pow_succ, mul_assoc]

theorem gap3
    (a : ℕ → ℝ) (q : ℝ)
    (hq : q < 1)
    (hgeometricBound : ∀ ε : ℝ, 0 < ε → ε < 1 - q →
      ∃ l : ℝ, ∃ n₀ : ℕ, 1 ≤ n₀ ∧ 0 ≤ l ∧ l < 1 ∧
        ∀ n ≥ n₀, 0 < a n ∧ a n ≤ a n₀ * l ^ (n - n₀)) :
    ∃ l : ℝ, ∃ n₀ : ℕ, 1 ≤ n₀ ∧ 0 ≤ l ∧ l < 1 ∧
      TailSummable (fun n => l ^ n) n₀ := by
  have hε : 0 < (1 - q) / 2 := by linarith
  have hεlt : (1 - q) / 2 < 1 - q := by linarith
  rcases hgeometricBound ((1 - q) / 2) hε hεlt with
    ⟨l, n₀, hn₀, hl0, hl1, hbound⟩
  have hnorm : ‖l‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hl0]
    exact hl1
  have hs : Summable (fun n : ℕ => l ^ n) :=
    summable_geometric_of_norm_lt_one hnorm
  have hinj : Function.Injective (fun k : ℕ => k + n₀) := by
    intro x y hxy
    exact Nat.add_right_cancel hxy
  refine ⟨l, n₀, hn₀, hl0, hl1, ?_⟩
  simpa [TailSummable] using hs.comp_injective hinj

theorem gap4
    (a : ℕ → ℝ)
    (hbound : ∃ l : ℝ, ∃ n₀ : ℕ, 1 ≤ n₀ ∧ 0 ≤ l ∧ l < 1 ∧
      (∀ n ≥ n₀, 0 < a n ∧ a n ≤ a n₀ * l ^ (n - n₀)) ∧
      TailSummable (fun n => l ^ n) n₀) :
    ∃ n₀ : ℕ, TailSummable a n₀ := by
  rcases hbound with
    ⟨l, n₀, hn₀, hl0, hl1, hbound, htail⟩
  have hnorm : ‖l‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hl0]
    exact hl1
  have hgeom : Summable (fun k : ℕ => l ^ k) :=
    summable_geometric_of_norm_lt_one hnorm
  have hmajor : Summable (fun k : ℕ => a n₀ * l ^ k) :=
    hgeom.mul_left (a n₀)
  refine ⟨n₀, ?_⟩
  change Summable (fun k : ℕ => a (k + n₀))
  refine Summable.of_norm_bounded hmajor ?_
  intro k
  have hk := hbound (k + n₀) (by omega)
  rw [Real.norm_eq_abs, abs_of_pos hk.1]
  simpa using hk.2

theorem gap5
    (a : ℕ → ℝ)
    (htail : ∃ n₀ : ℕ, TailSummable a n₀) :
    Summable a := by
  rcases htail with ⟨n₀, htail⟩
  exact (summable_nat_add_iff n₀).mp htail

theorem gap6 :
    Summable counterexample := by
  have hnorm : ‖(3 / 4 : ℝ)‖ < 1 := by
    norm_num [Real.norm_eq_abs]
  have hgeom : Summable (fun n : ℕ => (3 / 4 : ℝ) ^ n) :=
    summable_geometric_of_norm_lt_one hnorm
  exact Summable.of_norm_bounded hgeom counterexample_norm_le

theorem gap7 :
    (∀ m : ℕ, ratio counterexample (2 * m + 1) =
      (2 / 3 : ℝ) ^ (m + 1)) ∧
    (∀ m : ℕ, 1 ≤ m → ratio counterexample (2 * m) =
      (1 / 2 : ℝ) * (3 / 2 : ℝ) ^ m) := by
  constructor
  · intro m
    have hoddmod : (2 * m + 1) % 2 = 1 := by omega
    have hodddiv : (2 * m + 1) / 2 = m := by omega
    have hevenmod : (2 * m + 1 + 1) % 2 = 0 := by omega
    have hevendiv : (2 * m + 1 + 1) / 2 = m + 1 := by omega
    have hevenne : 2 * m + 1 + 1 ≠ 0 := by omega
    simp [ratio, counterexample, hoddmod, hodddiv, hevenmod,
      hevendiv, hevenne]
    rw [div_pow]
    field_simp <;> ring
  · intro m hm
    have hevenmod : (2 * m) % 2 = 0 := by omega
    have hevendiv : (2 * m) / 2 = m := by omega
    have hevenne : 2 * m ≠ 0 := by omega
    have hoddmod : (2 * m + 1) % 2 = 1 := by omega
    have hodddiv : (2 * m + 1) / 2 = m := by omega
    simp [ratio, counterexample, hevenmod, hevendiv, hevenne,
      hoddmod, hodddiv]
    rw [div_pow]
    field_simp <;> ring

theorem gap8
    (hratios :
      (∀ m : ℕ, ratio counterexample (2 * m + 1) =
        (2 / 3 : ℝ) ^ (m + 1)) ∧
      (∀ m : ℕ, 1 ≤ m → ratio counterexample (2 * m) =
        (1 / 2 : ℝ) * (3 / 2 : ℝ) ^ m)) :
    ¬ ∃ q : ℝ, Tendsto (ratio counterexample) atTop (nhds q) := by
  rintro ⟨q, hq⟩
  have hoddMap : Tendsto (fun m : ℕ => 2 * m + 1) atTop atTop := by
    refine Filter.tendsto_atTop.2 ?_
    intro b
    refine Filter.eventually_atTop.2 ⟨b, ?_⟩
    intro m hm
    omega
  have hoddq :
      Tendsto (fun m : ℕ => ratio counterexample (2 * m + 1))
        atTop (nhds q) :=
    hq.comp hoddMap
  have hoddq' :
      Tendsto (fun m : ℕ => (2 / 3 : ℝ) ^ (m + 1))
        atTop (nhds q) := by
    simpa only [hratios.1] using hoddq
  have hbase :
      Tendsto (fun m : ℕ => (2 / 3 : ℝ) ^ m) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by
      norm_num [Real.norm_eq_abs])
  have hconst :
      Tendsto (fun _ : ℕ => (2 / 3 : ℝ)) atTop (nhds (2 / 3 : ℝ)) :=
    tendsto_const_nhds
  have hodd0 :
      Tendsto (fun m : ℕ => (2 / 3 : ℝ) ^ (m + 1))
        atTop (nhds 0) := by
    simpa [pow_succ] using hbase.mul hconst
  have hq0 : q = 0 := tendsto_nhds_unique hoddq' hodd0
  have hzero : Tendsto (ratio counterexample) atTop (nhds 0) := by
    simpa [hq0] using hq
  have hevent : ∀ᶠ n in atTop, ratio counterexample n < (1 / 2 : ℝ) :=
    (tendsto_order.1 hzero).2 (1 / 2 : ℝ) (by norm_num)
  rcases Filter.eventually_atTop.1 hevent with ⟨N, hN⟩
  let m : ℕ := max 1 N
  have hm1 : 1 ≤ m := by simp [m]
  have hNm : N ≤ m := by simp [m]
  have hN2m : N ≤ 2 * m := by omega
  have hlt := hN (2 * m) hN2m
  rw [hratios.2 m hm1] at hlt
  have hp : (1 : ℝ) ≤ (3 / 2 : ℝ) ^ m := by
    induction m with
    | zero => norm_num
    | succ k ih =>
        rw [pow_succ]
        nlinarith
  nlinarith

theorem gap9
    (hsum : Summable counterexample)
    (hnolimit : ¬ ∃ q : ℝ,
      Tendsto (ratio counterexample) atTop (nhds q)) :
    ¬ (Summable counterexample →
      ∃ q : ℝ, Tendsto (ratio counterexample) atTop (nhds q) ∧ q < 1) := by
  intro himp
  rcases himp hsum with ⟨q, hq, hq1⟩
  exact hnolimit ⟨q, hq⟩

theorem gap10
    (hsum : Summable counterexample)
    (hfailure : ¬ (Summable counterexample →
      ∃ q : ℝ, Tendsto (ratio counterexample) atTop (nhds q) ∧ q < 1)) :
    Summable counterexample ∧
      ¬ (Summable counterexample →
        ∃ q : ℝ, Tendsto (ratio counterexample) atTop (nhds q) ∧ q < 1) := by
  exact ⟨hsum, hfailure⟩

end

end ProofGap.Exercise2592
