import ProofGapLean.Prelude.Analysis
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Exp

namespace ProofGap.Exercise3089

noncomputable section

open Filter
open scoped BigOperators Topology

def term (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ (n + 1) / Real.sqrt n

def harmonicTerm (n : ℕ) : ℝ :=
  1 / (n : ℝ)

def SummableFromOne (f : ℕ → ℝ) : Prop :=
  Summable (fun k : ℕ => f (k + 1))

def ConditionallySummableFromOne (f : ℕ → ℝ) : Prop :=
  ProofGap.SeriesConverges (fun k : ℕ => f (k + 1)) ∧
    ¬SummableFromOne (fun n => |f n|)

def squarePartialSum (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 n, (term i) ^ 2

def harmonicPartialSum (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 n, harmonicTerm i

def partialProduct (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.Icc 1 n, (1 + term i)

def NonzeroConvergentProduct : Prop :=
  ∃ P : ℝ, P ≠ 0 ∧ Tendsto partialProduct atTop (𝓝 P)

def DivergentProduct : Prop :=
  ¬NonzeroConvergentProduct

private theorem term_odd (k : ℕ) :
    term (2 * k + 1) =
      1 / Real.sqrt ((2 * k + 1 : ℕ) : ℝ) := by
  have hpow : (-1 : ℝ) ^ (2 * k + 2) = 1 := by
    rw [show 2 * k + 2 = 2 * (k + 1) by omega, pow_mul]
    norm_num
  unfold term
  rw [show 2 * k + 1 + 1 = 2 * k + 2 by omega, hpow]

private theorem term_even (k : ℕ) :
    term (2 * k + 2) =
      -(1 / Real.sqrt ((2 * k + 2 : ℕ) : ℝ)) := by
  have hpow : (-1 : ℝ) ^ (2 * k + 3) = -1 := by
    rw [show 2 * k + 3 = 2 * (k + 1) + 1 by omega,
      pow_add, pow_mul]
    norm_num
  unfold term
  rw [show 2 * k + 2 + 1 = 2 * k + 3 by omega, hpow]
  ring

private def pairFactor (k : ℕ) : ℝ :=
  (1 + term (2 * k + 1)) * (1 + term (2 * k + 2))

private theorem pairFactor_pos (k : ℕ) :
    0 < pairFactor k := by
  rw [pairFactor, term_odd, term_even]
  let a := Real.sqrt ((2 * k + 1 : ℕ) : ℝ)
  let b := Real.sqrt ((2 * k + 2 : ℕ) : ℝ)
  have ha : 0 < a := Real.sqrt_pos.2 (by positivity)
  have hb : 0 < b := Real.sqrt_pos.2 (by positivity)
  have hb_sq : b ^ 2 = ((2 * k + 2 : ℕ) : ℝ) := by
    dsimp [b]
    exact Real.sq_sqrt (by positivity)
  have hb_one : 1 < b := by
    have hk : (2 : ℝ) ≤ ((2 * k + 2 : ℕ) : ℝ) := by
      push_cast
      nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℝ))]
    nlinarith
  have hfrac : 1 / b < 1 := (div_lt_one hb).2 (by linarith)
  change 0 < (1 + 1 / a) * (1 - 1 / b)
  exact mul_pos (by positivity) (sub_pos.2 hfrac)

private theorem pairFactor_le (k : ℕ) :
    pairFactor k ≤
      1 - 1 / (4 * ((k + 1 : ℕ) : ℝ)) := by
  rw [pairFactor, term_odd, term_even]
  let a := Real.sqrt ((2 * k + 1 : ℕ) : ℝ)
  let b := Real.sqrt ((2 * k + 2 : ℕ) : ℝ)
  have ha : 0 < a := Real.sqrt_pos.2 (by positivity)
  have hb : 0 < b := Real.sqrt_pos.2 (by positivity)
  have ha_sq : a ^ 2 = ((2 * k + 1 : ℕ) : ℝ) := by
    dsimp [a]
    exact Real.sq_sqrt (by positivity)
  have hb_sq : b ^ 2 = ((2 * k + 2 : ℕ) : ℝ) := by
    dsimp [b]
    exact Real.sq_sqrt (by positivity)
  have hab_sq : b ^ 2 = a ^ 2 + 1 := by
    rw [ha_sq, hb_sq]
    push_cast
    ring
  have ha_one : 1 ≤ a := by
    have hk : (1 : ℝ) ≤ ((2 * k + 1 : ℕ) : ℝ) := by
      push_cast
      nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℝ))]
    nlinarith
  have hab : a ≤ b := by
    apply Real.sqrt_le_sqrt
    exact_mod_cast (by omega : 2 * k + 1 ≤ 2 * k + 2)
  have hsum : 2 ≤ a + b := by nlinarith
  have hsum_pos : 0 < a + b := by positivity
  have hsum' : 2 ≤ b + a := by linarith
  have hsum_pos' : 0 < b + a := by positivity
  have hdiff_mul : (b - a) * (b + a) = 1 := by
    nlinarith [hab_sq]
  have hdiff_eq : b - a = 1 / (b + a) := by
    apply (eq_div_iff hsum_pos'.ne').2
    exact hdiff_mul
  have hdiff : b - a ≤ 1 / 2 := by
    rw [hdiff_eq]
    apply (div_le_div_iff₀ hsum_pos' (by norm_num : (0 : ℝ) < 2)).2
    nlinarith
  have hfrac :
      1 / a - 1 / b ≤ 1 / (2 * a * b) := by
    field_simp [ha.ne', hb.ne']
    nlinarith
  have habmul : 2 * a * b ≤ 2 * b ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hab hb.le]
  have hinv :
      1 / (2 * b ^ 2) ≤ 1 / (2 * a * b) := by
    exact one_div_le_one_div_of_le (by positivity) habmul
  have hq :
      (1 + 1 / a) * (1 - 1 / b) ≤
        1 - 1 / (2 * b ^ 2) := by
    calc
      (1 + 1 / a) * (1 - 1 / b) =
          1 + (1 / a - 1 / b) - 1 / (a * b) := by
            field_simp [ha.ne', hb.ne']
            ring
      _ ≤ 1 + 1 / (2 * a * b) - 1 / (a * b) := by
        linarith
      _ = 1 - 1 / (2 * a * b) := by
        field_simp [ha.ne', hb.ne']
        ring
      _ ≤ 1 - 1 / (2 * b ^ 2) := by linarith
  have hden :
      (2 : ℝ) * b ^ 2 = 4 * ((k + 1 : ℕ) : ℝ) := by
    rw [hb_sq]
    push_cast
    ring
  rw [hden] at hq
  exact hq

private theorem pairFactor_le_exp (k : ℕ) :
    pairFactor k ≤
      Real.exp (-(1 / (4 * ((k + 1 : ℕ) : ℝ)))) := by
  calc
    pairFactor k ≤
        1 - 1 / (4 * ((k + 1 : ℕ) : ℝ)) :=
      pairFactor_le k
    _ ≤ Real.exp (-(1 / (4 * ((k + 1 : ℕ) : ℝ)))) := by
      simpa [sub_eq_add_neg, add_comm] using
        Real.add_one_le_exp (-(1 / (4 * ((k + 1 : ℕ) : ℝ))))

private theorem partialProduct_succ (n : ℕ) :
    partialProduct (n + 1) =
      partialProduct n * (1 + term (n + 1)) := by
  unfold partialProduct
  rw [Finset.prod_Icc_succ_top (by omega)]

private theorem partialProduct_even_eq (N : ℕ) :
    partialProduct (2 * N) =
      ∏ k ∈ Finset.range N, pairFactor k := by
  induction N with
  | zero =>
      simp [partialProduct]
  | succ N ih =>
      calc
        partialProduct (2 * (N + 1)) =
            partialProduct ((2 * N + 1) + 1) := by
              congr 1
        _ = partialProduct (2 * N + 1) * (1 + term (2 * N + 2)) :=
          partialProduct_succ (2 * N + 1)
        _ =
            (partialProduct (2 * N) * (1 + term (2 * N + 1))) *
              (1 + term (2 * N + 2)) := by
          exact congrArg
            (fun z => z * (1 + term (2 * N + 2)))
            (partialProduct_succ (2 * N))
        _ = partialProduct (2 * N) * pairFactor N := by
          unfold pairFactor
          ring
        _ = ∏ k ∈ Finset.range (N + 1), pairFactor k := by
          rw [Finset.prod_range_succ, ih]

private theorem partialProduct_even_nonneg (N : ℕ) :
    0 ≤ partialProduct (2 * N) := by
  rw [partialProduct_even_eq]
  apply Finset.prod_nonneg
  intro k hk
  exact (pairFactor_pos k).le

private theorem partialProduct_even_le (N : ℕ) :
    partialProduct (2 * N) ≤
      Real.exp
        ((-1 / 4 : ℝ) *
          ∑ k ∈ Finset.range N, (1 / ((k : ℝ) + 1))) := by
  rw [partialProduct_even_eq]
  calc
    (∏ k ∈ Finset.range N, pairFactor k) ≤
        ∏ k ∈ Finset.range N,
          Real.exp (-(1 / (4 * ((k + 1 : ℕ) : ℝ)))) := by
      apply Finset.prod_le_prod
      · intro k hk
        exact (pairFactor_pos k).le
      · intro k hk
        exact pairFactor_le_exp k
    _ = Real.exp
        (∑ k ∈ Finset.range N,
          -(1 / (4 * ((k + 1 : ℕ) : ℝ)))) := by
      rw [Real.exp_sum]
    _ = Real.exp
        ((-1 / 4 : ℝ) *
          ∑ k ∈ Finset.range N, (1 / ((k : ℝ) + 1))) := by
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      push_cast
      field_simp

private theorem partialProduct_even_tendsto_zero :
    Tendsto (fun N : ℕ => partialProduct (2 * N)) atTop (𝓝 0) := by
  have hbot :
      Tendsto
        (fun N : ℕ =>
          (-1 / 4 : ℝ) *
            ∑ k ∈ Finset.range N, (1 / ((k : ℝ) + 1)))
        atTop atBot :=
    Real.tendsto_sum_range_one_div_nat_succ_atTop.const_mul_atTop_of_neg
      (by norm_num)
  have hexp :
      Tendsto
        (fun N : ℕ =>
          Real.exp
            ((-1 / 4 : ℝ) *
              ∑ k ∈ Finset.range N, (1 / ((k : ℝ) + 1))))
        atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hbot
  apply squeeze_zero'
  · exact Eventually.of_forall partialProduct_even_nonneg
  · exact Eventually.of_forall partialProduct_even_le
  · exact hexp

private theorem oddFactor_nonneg (N : ℕ) :
    0 ≤ 1 + term (2 * N + 1) := by
  rw [term_odd]
  positivity

private theorem oddFactor_le_two (N : ℕ) :
    1 + term (2 * N + 1) ≤ 2 := by
  rw [term_odd]
  let a := Real.sqrt ((2 * N + 1 : ℕ) : ℝ)
  have ha : 0 < a := Real.sqrt_pos.2 (by positivity)
  have ha_sq : a ^ 2 = ((2 * N + 1 : ℕ) : ℝ) := by
    dsimp [a]
    exact Real.sq_sqrt (by positivity)
  have ha_one : 1 ≤ a := by
    have hcast : (1 : ℝ) ≤ ((2 * N + 1 : ℕ) : ℝ) := by
      push_cast
      nlinarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ (N : ℝ))]
    nlinarith
  have hone : 1 / a ≤ 1 := by
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) ha_one
  linarith

private theorem partialProduct_odd_eq (N : ℕ) :
    partialProduct (2 * N + 1) =
      partialProduct (2 * N) * (1 + term (2 * N + 1)) := by
  exact partialProduct_succ (2 * N)

private theorem partialProduct_odd_tendsto_zero :
    Tendsto (fun N : ℕ => partialProduct (2 * N + 1)) atTop (𝓝 0) := by
  have hupper :
      Tendsto (fun N : ℕ => 2 * partialProduct (2 * N)) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul partialProduct_even_tendsto_zero
  apply squeeze_zero' (f := fun N : ℕ => partialProduct (2 * N + 1))
  · exact Eventually.of_forall fun N => by
      calc
        0 ≤ partialProduct (2 * N) * (1 + term (2 * N + 1)) :=
          mul_nonneg (partialProduct_even_nonneg N) (oddFactor_nonneg N)
        _ = partialProduct (2 * N + 1) :=
          (partialProduct_odd_eq N).symm
  · exact Eventually.of_forall fun N => by
      have he := partialProduct_even_nonneg N
      have hf := oddFactor_le_two N
      calc
        partialProduct (2 * N + 1) =
            partialProduct (2 * N) * (1 + term (2 * N + 1)) :=
          partialProduct_odd_eq N
        _ ≤ 2 * partialProduct (2 * N) := by nlinarith
  · exact hupper

private theorem partialProduct_tendsto_zero :
    Tendsto partialProduct atTop (𝓝 0) := by
  have heven := partialProduct_even_tendsto_zero
  have hodd := partialProduct_odd_tendsto_zero
  rw [Metric.tendsto_atTop] at heven hodd ⊢
  intro ε hε
  obtain ⟨Ne, hNe⟩ := heven ε hε
  obtain ⟨No, hNo⟩ := hodd ε hε
  refine ⟨2 * max Ne No + 1, ?_⟩
  intro n hn
  obtain ⟨k, hk⟩ := Nat.even_or_odd' n
  rcases hk with hk | hk
  · subst n
    have hkNe : Ne ≤ k := by omega
    exact hNe k hkNe
  · subst n
    have hkNo : No ≤ k := by omega
    exact hNo k hkNo

/-- Source: `proof_gap/exercise_3089/1.txt`. -/
theorem gap1 : ConditionallySummableFromOne term := by
  let a : ℕ → ℝ := fun n => 1 / Real.sqrt (((n + 1 : ℕ) : ℝ))
  have ha_anti : Antitone a := by
    refine antitone_nat_of_succ_le (fun n => ?_)
    dsimp [a]
    apply one_div_le_one_div_of_le (Real.sqrt_pos.2 (by positivity))
    apply Real.sqrt_le_sqrt
    exact_mod_cast (by omega : n + 1 ≤ n + 2)
  have ha_zero : Tendsto a atTop (𝓝 0) := by
    have hsqrt := (Real.continuous_sqrt.tendsto 0).comp
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    convert hsqrt using 1
    · funext n
      dsimp [a]
      rw [one_div, ← Real.sqrt_inv]
      congr 1
      norm_num [Nat.cast_add]
    · simp
  have hterm (n : ℕ) : term (n + 1) = (-1 : ℝ) ^ n * a n := by
    dsimp [a]
    unfold term
    rw [show n + 1 + 1 = n + 2 by omega, pow_add]
    norm_num
    rw [div_eq_mul_inv]
  constructor
  · rcases ha_anti.tendsto_alternating_series_of_tendsto_zero ha_zero with ⟨l, hl⟩
    have hpartial :
        (fun N : ℕ => ∑ n ∈ Finset.range N, term (n + 1)) =
          fun N : ℕ => ∑ n ∈ Finset.range N, (-1 : ℝ) ^ n * a n := by
      funext N
      exact Finset.sum_congr rfl (fun n _ => hterm n)
    have htend : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, term (n + 1))
        atTop (𝓝 l) := by
      rw [hpartial]
      exact hl
    rw [ProofGap.SeriesConverges]
    refine ⟨l, ?_⟩
    simpa [HasSum, Function.comp_def] using htend
  · intro habs
    unfold SummableFromOne at habs
    have habs_formula (n : ℕ) : |term (n + 1)| = a n := by
      dsimp [a]
      unfold term
      rw [abs_div, abs_of_pos (Real.sqrt_pos.2 (by positivity))]
      simp
    have hp_shift : Summable
        (fun n : ℕ => 1 / Real.rpow (((n + 1 : ℕ) : ℝ)) (1 / 2 : ℝ)) := by
      refine habs.congr (fun n => ?_)
      change |term (n + 1)| = _
      rw [habs_formula]
      dsimp [a]
      rw [Real.sqrt_eq_rpow]
    have hp : Summable (fun n : ℕ => 1 / Real.rpow (n : ℝ) (1 / 2 : ℝ)) :=
      (summable_nat_add_iff 1).1 hp_shift
    have hgt := Real.summable_one_div_nat_rpow.mp hp
    norm_num at hgt

/--
Source: `proof_gap/exercise_3089/2.txt`; the infinite sums diverge, so state
the exact equality at every finite cutoff.
-/
theorem gap2 :
    ∀ n, squarePartialSum n = harmonicPartialSum n := by
  intro n
  unfold squarePartialSum harmonicPartialSum
  apply Finset.sum_congr rfl
  intro i hi
  unfold term harmonicTerm
  rw [div_pow, Real.sq_sqrt (by positivity)]
  have hsign : ((-1 : ℝ) ^ (i + 1)) ^ 2 = 1 := by
    rw [← pow_mul]
    norm_num
  rw [hsign]

/-- Source: `proof_gap/exercise_3089/3.txt`. -/
theorem gap3 : ¬SummableFromOne harmonicTerm := by
  intro h
  unfold SummableFromOne at h
  have hall : Summable harmonicTerm :=
    (summable_nat_add_iff 1).mp h
  apply Real.not_summable_one_div_natCast
  change Summable (fun n : ℕ => harmonicTerm n) at hall
  simpa only [harmonicTerm, one_div] using hall

/--
Source: `proof_gap/exercise_3089/4.txt`; the partial products tend to zero,
so they diverge in the nonzero infinite-product sense.
-/
theorem gap4 : DivergentProduct := by
  unfold DivergentProduct NonzeroConvergentProduct
  rintro ⟨P, hP0, hP⟩
  have hEq : P = 0 :=
    tendsto_nhds_unique hP partialProduct_tendsto_zero
  exact hP0 hEq

end

end ProofGap.Exercise3089
