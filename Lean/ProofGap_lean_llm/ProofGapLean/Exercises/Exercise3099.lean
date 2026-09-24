import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace ProofGap.Exercise3099

noncomputable section

open Filter
open scoped Topology

def alpha (n : ℕ) : ℝ :=
  if n = 0 then 0
  else
    let k := (n + 1) / 2
    if n % 2 = 1 then -(1 / Real.sqrt k)
    else
      1 / Real.sqrt k + 1 / (k : ℝ) +
        1 / ((k : ℝ) * Real.sqrt k)

def beta (k : ℕ) : ℝ :=
  alpha (2 * k - 1) + alpha (2 * k)

def b (k : ℕ) : ℝ :=
  (alpha (2 * k - 1)) ^ 2 + (alpha (2 * k)) ^ 2

def bRemainderScale (k : ℕ) : ℝ :=
  1 / Real.rpow (k : ℝ) (3 / 2 : ℝ)

def v (n : ℕ) : ℝ :=
  Real.log (1 + alpha n)

def c (k : ℕ) : ℝ :=
  v (2 * k - 1) + v (2 * k)

-- Statement correction: use the conditional summation filter for convergence in natural order; bare Summable would require absolute convergence.
def SummableFromOne (f : ℕ → ℝ) : Prop :=
  ProofGap.SeriesConverges (fun k : ℕ => f (k + 1))

private theorem seriesConverges_iff (f : ℕ → ℝ) :
    ProofGap.SeriesConverges f ↔
      ∃ s : ℝ,
        Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, f i) atTop (𝓝 s) := by
  simp only [ProofGap.SeriesConverges, Summable, HasSum,
    SummationFilter.conditional_filter_eq_map_range, tendsto_map'_iff]
  constructor <;> rintro ⟨s, hs⟩
  · exact ⟨s, by simpa [Function.comp_def] using hs⟩
  · exact ⟨s, by simpa [Function.comp_def] using hs⟩

private theorem seriesConverges_of_summable {f : ℕ → ℝ}
    (hf : Summable f) : ProofGap.SeriesConverges f := by
  exact ⟨∑' n, f n,
    hf.hasSum.mono_left (SummationFilter.conditional ℕ).le_atTop⟩

private theorem sum_range_pairs (f : ℕ → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range (2 * n), f i =
      ∑ k ∈ Finset.range n, (f (2 * k) + f (2 * k + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega,
        Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, ih]
      ring

private theorem tendsto_of_even_odd {f : ℕ → ℝ} {L : ℝ}
    (heven : Tendsto (fun n => f (2 * n)) atTop (𝓝 L))
    (hodd : Tendsto (fun n => f (2 * n + 1)) atTop (𝓝 L)) :
    Tendsto f atTop (𝓝 L) := by
  rw [Metric.tendsto_atTop] at heven hodd ⊢
  intro ε hε
  obtain ⟨Ne, hNe⟩ := heven ε hε
  obtain ⟨No, hNo⟩ := hodd ε hε
  refine ⟨2 * max Ne No + 1, ?_⟩
  intro n hn
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · exact hNe k (by omega)
  · exact hNo k (by omega)

private theorem alpha_odd (k : ℕ) (hk : 1 ≤ k) :
    alpha (2 * k - 1) = -(1 / Real.sqrt k) := by
  have hn : 2 * k - 1 ≠ 0 := by omega
  have hmod : (2 * k - 1) % 2 = 1 := by omega
  have hdiv : (2 * k - 1 + 1) / 2 = k := by omega
  simp [alpha, hn, hmod, hdiv]

private theorem alpha_even (k : ℕ) (hk : 1 ≤ k) :
    alpha (2 * k) =
      1 / Real.sqrt k + 1 / (k : ℝ) +
        1 / ((k : ℝ) * Real.sqrt k) := by
  have hn : 2 * k ≠ 0 := by omega
  have hmod : (2 * k) % 2 = 0 := by omega
  have hdiv : (2 * k + 1) / 2 = k := by omega
  simp [alpha, hn, hmod, hdiv]

private theorem alpha_odd_zero (k : ℕ) :
    alpha (2 * k + 1) = -(1 / Real.sqrt (k + 1)) := by
  simpa [show 2 * k + 1 = 2 * (k + 1) - 1 by omega] using
    alpha_odd (k + 1) (by omega)

private theorem alpha_even_zero (k : ℕ) :
    alpha (2 * k + 2) =
      1 / Real.sqrt (k + 1) + 1 / ((k : ℝ) + 1) +
        1 / (((k : ℝ) + 1) * Real.sqrt (k + 1)) := by
  rw [show 2 * k + 2 = 2 * (k + 1) by omega, alpha_even (k + 1) (by omega)]
  push_cast
  rfl

private theorem alpha_tendsto_zero : Tendsto alpha atTop (𝓝 0) := by
  have hsqrt :
      Tendsto (fun k : ℕ => 1 / Real.sqrt (k + 1)) atTop (𝓝 0) := by
    have hn :
        Tendsto (fun k : ℕ => (((k + 1 : ℕ) : ℝ))) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
    simpa [one_div, Nat.cast_add] using
      tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hn)
  have hinv : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) := by
    have hn :
        Tendsto (fun k : ℕ => (((k + 1 : ℕ) : ℝ))) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
    simpa [one_div, Nat.cast_add] using tendsto_inv_atTop_zero.comp hn
  have hprod :
      Tendsto
        (fun k : ℕ => 1 / (((k : ℝ) + 1) * Real.sqrt (k + 1)))
        atTop (𝓝 0) := by
    simpa [div_eq_mul_inv, mul_comm] using hinv.mul hsqrt
  apply tendsto_of_even_odd
  · apply (tendsto_add_atTop_iff_nat 1).1
    simpa [Nat.mul_add, alpha_even_zero] using (hsqrt.add hinv).add hprod
  · simpa [alpha_odd_zero] using hsqrt.neg

private theorem v_tendsto_zero : Tendsto v atTop (𝓝 0) := by
  have hone : Tendsto (fun n : ℕ => 1 + alpha n) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add alpha_tendsto_zero
  simpa [v, Function.comp_def] using
    (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hone

/-- Source: `proof_gap/exercise_3099/1.txt`; use one explicitly defined witness. -/
theorem gap1 :
    ∃ a : ℕ → ℝ, a = alpha ∧ ∀ k : ℕ, 1 ≤ k →
      a (2 * k - 1) = -(1 / Real.sqrt k) := by
  exact ⟨alpha, rfl, alpha_odd⟩

/-- Source: `proof_gap/exercise_3099/2.txt`; use the same explicit witness. -/
theorem gap2 :
    ∃ a : ℕ → ℝ, a = alpha ∧ ∀ k : ℕ, 1 ≤ k →
      a (2 * k) =
        1 / Real.sqrt k + 1 / (k : ℝ) +
          1 / ((k : ℝ) * Real.sqrt k) := by
  exact ⟨alpha, rfl, alpha_even⟩

/-- Source: `proof_gap/exercise_3099/3.txt`; paired indices start at one. -/
theorem gap3 :
    ∀ k : ℕ, 1 ≤ k →
      beta k = 1 / (k : ℝ) + 1 / ((k : ℝ) * Real.sqrt k) := by
  intro k hk
  rw [beta, alpha_odd k hk, alpha_even k hk]
  ring

/-- Source: `proof_gap/exercise_3099/4.txt`. -/
theorem gap4 : ¬SummableFromOne beta := by
  intro hb
  rcases (seriesConverges_iff _).mp hb with ⟨s, hs⟩
  have hnonneg : ∀ n : ℕ, 0 ≤ beta (n + 1) := by
    intro n
    rw [gap3 (n + 1) (by omega)]
    positivity
  have hsum : HasSum (fun n : ℕ => beta (n + 1)) s :=
    (hasSum_iff_tendsto_nat_of_nonneg hnonneg s).2 hs
  have htail : Summable (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ))) := by
    exact hsum.summable.of_nonneg_of_le
      (fun n => by positivity)
      (fun n => by
        rw [gap3 (n + 1) (by omega)]
        exact le_add_of_nonneg_right (by positivity))
  apply Real.not_summable_one_div_natCast
  exact (summable_nat_add_iff 1).1 (by simpa using htail)

/-- Source: `proof_gap/exercise_3099/5.txt`; retain the explicit witness. -/
theorem gap5 :
    ∃ a : ℕ → ℝ, a = alpha ∧ ¬SummableFromOne a := by
  refine ⟨alpha, rfl, ?_⟩
  intro ha
  rcases (seriesConverges_iff _).mp ha with ⟨s, hs⟩
  have hidx : Tendsto (fun n : ℕ => 2 * n) atTop atTop := by
    rw [tendsto_atTop]
    intro N
    exact eventually_atTop.2 ⟨N, fun n hn => by omega⟩
  have hpairs :
      Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, beta (k + 1))
        atTop (𝓝 s) := by
    apply (hs.comp hidx).congr'
    filter_upwards with n
    simp only [Function.comp_apply]
    rw [sum_range_pairs]
    apply Finset.sum_congr rfl
    intro k hk
    unfold beta
    congr 2 <;> omega
  apply gap4
  exact (seriesConverges_iff _).2 ⟨s, hpairs⟩

/-- Source: `proof_gap/exercise_3099/6.txt`; replace the scalar big-O token. -/
theorem gap6 :
    ((fun k => b k - 2 / (k : ℝ)) =O[atTop] bRemainderScale) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨8, eventually_atTop.2 ⟨1, ?_⟩⟩
  intro k hk
  have hkpos : 0 < (k : ℝ) := by positivity
  have hspos : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.2 hkpos
  have hs_sq : Real.sqrt (k : ℝ) ^ 2 = (k : ℝ) :=
    Real.sq_sqrt hkpos.le
  let t : ℝ := 1 / Real.sqrt (k : ℝ)
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have hsone : 1 ≤ Real.sqrt (k : ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hk)
  have ht1 : t ≤ 1 := by
    dsimp [t]
    exact (div_le_one hspos).2 hsone
  have hinvk : 1 / (k : ℝ) = t ^ 2 := by
    dsimp [t]
    field_simp [hspos.ne']
    nlinarith
  have hinvks :
      1 / ((k : ℝ) * Real.sqrt k) = t ^ 3 := by
    dsimp [t]
    field_simp [hspos.ne', hkpos.ne']
    nlinarith
  have hrem :
      b k - 2 / (k : ℝ) =
        2 * t ^ 3 + 3 * t ^ 4 + 2 * t ^ 5 + t ^ 6 := by
    have hinvsqrt : 1 / Real.sqrt (k : ℝ) = t := rfl
    rw [b, alpha_odd k hk, alpha_even k hk, hinvsqrt, hinvk, hinvks,
      show 2 / (k : ℝ) = 2 * (1 / (k : ℝ)) by ring, hinvk]
    change (-t) ^ 2 + (t + t ^ 2 + t ^ 3) ^ 2 - 2 * t ^ 2 =
      2 * t ^ 3 + 3 * t ^ 4 + 2 * t ^ 5 + t ^ 6
    ring
  have hscale : bRemainderScale k = t ^ 3 := by
    unfold bRemainderScale
    have hr :
        Real.rpow (k : ℝ) (3 / 2 : ℝ) =
          Real.rpow (Real.sqrt (k : ℝ)) 3 :=
      Real.rpow_div_two_eq_sqrt 3 hkpos.le
    have hrnat :
        Real.rpow (Real.sqrt (k : ℝ)) (3 : ℝ) =
          Real.sqrt (k : ℝ) ^ (3 : ℕ) :=
      Real.rpow_natCast _ 3
    rw [hr, hrnat]
    dsimp [t]
    exact (one_div_pow _ _).symm
  have h4 : t ^ 4 ≤ t ^ 3 := by
    calc
      t ^ 4 = t * t ^ 3 := by ring
      _ ≤ 1 * t ^ 3 :=
        mul_le_mul_of_nonneg_right ht1 (pow_nonneg ht0 3)
      _ = t ^ 3 := one_mul _
  have h5 : t ^ 5 ≤ t ^ 3 := by
    calc
      t ^ 5 = t * t ^ 4 := by ring
      _ ≤ 1 * t ^ 4 :=
        mul_le_mul_of_nonneg_right ht1 (pow_nonneg ht0 4)
      _ = t ^ 4 := one_mul _
      _ ≤ t ^ 3 := h4
  have h6 : t ^ 6 ≤ t ^ 3 := by
    calc
      t ^ 6 = t * t ^ 5 := by ring
      _ ≤ 1 * t ^ 5 :=
        mul_le_mul_of_nonneg_right ht1 (pow_nonneg ht0 5)
      _ = t ^ 5 := one_mul _
      _ ≤ t ^ 3 := h5
  rw [hrem, hscale, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤
      2 * t ^ 3 + 3 * t ^ 4 + 2 * t ^ 5 + t ^ 6),
    abs_of_nonneg (pow_nonneg ht0 3)]
  nlinarith

/-- Source: `proof_gap/exercise_3099/7.txt`. -/
theorem gap7 : ¬SummableFromOne b := by
  intro hb
  rcases (seriesConverges_iff _).mp hb with ⟨s, hs⟩
  have hnonneg : ∀ n : ℕ, 0 ≤ b (n + 1) := by
    intro n
    unfold b
    positivity
  have hsum : HasSum (fun n : ℕ => b (n + 1)) s :=
    (hasSum_iff_tendsto_nat_of_nonneg hnonneg s).2 hs
  have htail : Summable (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ))) := by
    exact hsum.summable.of_nonneg_of_le
      (fun n => by positivity)
      (fun n => by
        have hk : 1 ≤ n + 1 := by omega
        rw [b, alpha_odd (n + 1) hk]
        have hs_sq :
            Real.sqrt ((n + 1 : ℕ) : ℝ) ^ 2 = ((n + 1 : ℕ) : ℝ) :=
          Real.sq_sqrt (by positivity)
        have hspos : 0 < Real.sqrt ((n + 1 : ℕ) : ℝ) :=
          Real.sqrt_pos.2 (by positivity)
        have heq :
            (-(1 / Real.sqrt ((n + 1 : ℕ) : ℝ))) ^ 2 =
              1 / ((n + 1 : ℕ) : ℝ) := by
          field_simp [hspos.ne']
          nlinarith
        rw [heq]
        exact le_add_of_nonneg_right (sq_nonneg _))
  apply Real.not_summable_one_div_natCast
  exact (summable_nat_add_iff 1).1 (by simpa using htail)

/-- Source: `proof_gap/exercise_3099/8.txt`; retain the explicit witness. -/
theorem gap8 :
    ∃ a : ℕ → ℝ, a = alpha ∧
      ¬SummableFromOne (fun n => (a n) ^ 2) := by
  refine ⟨alpha, rfl, ?_⟩
  intro ha
  rcases (seriesConverges_iff _).mp ha with ⟨s, hs⟩
  have hidx : Tendsto (fun n : ℕ => 2 * n) atTop atTop := by
    rw [tendsto_atTop]
    intro N
    exact eventually_atTop.2 ⟨N, fun n hn => by omega⟩
  have hpairs :
      Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, b (k + 1))
        atTop (𝓝 s) := by
    apply (hs.comp hidx).congr'
    filter_upwards with n
    simp only [Function.comp_apply]
    rw [sum_range_pairs]
    apply Finset.sum_congr rfl
    intro k hk
    unfold b
    congr 2 <;> omega
  apply gap7
  exact (seriesConverges_iff _).2 ⟨s, hpairs⟩

/--
Source: `proof_gap/exercise_3099/9.txt`; the logarithmic product identity
requires `k ≥ 2` because the first odd factor is zero.
-/
theorem gap9 :
    ∀ k : ℕ, 2 ≤ k →
      c k = Real.log (1 - 1 / (k : ℝ) ^ 2) := by
  intro k hk
  have hk1 : 1 ≤ k := by omega
  have hkpos : 0 < (k : ℝ) := by positivity
  have hspos : 0 < Real.sqrt k := Real.sqrt_pos.2 hkpos
  have hs_sq : Real.sqrt (k : ℝ) ^ 2 = (k : ℝ) :=
    Real.sq_sqrt hkpos.le
  have hodd : 1 - 1 / Real.sqrt k ≠ 0 := by
    have hsone : 1 < Real.sqrt k := by
      rw [Real.lt_sqrt (by norm_num)]
      exact_mod_cast (show 1 < k by omega)
    exact ne_of_gt (sub_pos.mpr ((div_lt_one hspos).2 hsone))
  have heven :
      1 + (1 / Real.sqrt k + 1 / (k : ℝ) +
        1 / ((k : ℝ) * Real.sqrt k)) ≠ 0 := by positivity
  rw [c, v, v, alpha_odd k hk1, alpha_even k hk1,
    show 1 + -(1 / Real.sqrt k) = 1 - 1 / Real.sqrt k by ring,
    ← Real.log_mul hodd heven]
  congr 1
  field_simp [hspos.ne', hkpos.ne']
  nlinarith

private theorem c_tail_summable :
    Summable (fun n : ℕ => c (n + 2)) := by
  let q : ℕ → ℝ := fun n => -(1 / ((n : ℝ) + 2) ^ 2)
  have hq : Summable q := by
    have h := (Real.summable_one_div_nat_add_rpow 2 2).2 (by norm_num)
    apply h.neg.congr
    intro n
    rw [abs_of_nonneg (show 0 ≤ (n : ℝ) + 2 by positivity)]
    dsimp [q]
    congr 2
    exact Real.rpow_natCast _ 2
  have hlog := Real.summable_log_one_add_of_summable hq
  apply hlog.congr
  intro n
  rw [gap9 (n + 2) (by omega)]
  dsimp [q]
  push_cast
  congr 1

/-- Source: `proof_gap/exercise_3099/10.txt`. -/
theorem gap10 : SummableFromOne c := by
  apply seriesConverges_of_summable
  exact (summable_nat_add_iff 1).1
    (by simpa [Nat.add_assoc] using c_tail_summable)

/-- Source: `proof_gap/exercise_3099/11.txt`. -/
theorem gap11 : Tendsto v atTop (𝓝 0) := by
  exact v_tendsto_zero

/-- Source: `proof_gap/exercise_3099/12.txt`. -/
theorem gap12 : SummableFromOne v := by
  rcases (seriesConverges_iff _).mp gap10 with ⟨s, hs⟩
  let P : ℕ → ℝ := fun n => ∑ i ∈ Finset.range n, v (i + 1)
  have heven : Tendsto (fun n => P (2 * n)) atTop (𝓝 s) := by
    apply hs.congr'
    filter_upwards with n
    unfold P
    rw [sum_range_pairs]
    apply Finset.sum_congr rfl
    intro k hk
    unfold c
    congr 2 <;> omega
  have hvodd : Tendsto (fun n : ℕ => v (2 * n + 1)) atTop (𝓝 0) := by
    apply v_tendsto_zero.comp
    rw [tendsto_atTop]
    intro N
    exact eventually_atTop.2 ⟨N, fun n hn => by omega⟩
  have hodd : Tendsto (fun n => P (2 * n + 1)) atTop (𝓝 s) := by
    have h :
        Tendsto (fun n => P (2 * n) + v (2 * n + 1)) atTop (𝓝 s) := by
      simpa using heven.add hvodd
    convert h using 1
    funext n
    unfold P
    rw [Finset.sum_range_succ]
  exact (seriesConverges_iff _).2 ⟨s, tendsto_of_even_odd heven hodd⟩

/-- Source: `proof_gap/exercise_3099/13.txt`; provide one witness for all three properties. -/
theorem gap13 :
    ∃ a : ℕ → ℝ, a = alpha ∧
      ¬SummableFromOne a ∧
      ¬SummableFromOne (fun n => (a n) ^ 2) ∧
      SummableFromOne (fun n => Real.log (1 + a n)) := by
  rcases gap5 with ⟨_, rfl, ha⟩
  rcases gap8 with ⟨_, rfl, ha2⟩
  exact ⟨alpha, rfl, ha, ha2, gap12⟩

end

end ProofGap.Exercise3099
