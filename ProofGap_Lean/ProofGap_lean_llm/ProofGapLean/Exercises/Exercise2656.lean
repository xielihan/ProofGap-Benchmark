import ProofGapLean.Prelude.Analysis
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise2656

noncomputable section

open scoped BigOperators

def ConditionallySummable (a : ℕ → ℝ) : Prop :=
  Summable (fun n : ℕ => a (n + 1)) ∧
    ¬ Summable (fun n : ℕ => |a (n + 1)|)

def blockSum (a : ℕ → ℝ) (lo hi : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc lo hi, a i

def epsilon (k : ℕ) : ℝ :=
  1 / (2 : ℝ) ^ k

def AbsolutelySummable (A : ℕ → ℝ) : Prop :=
  Summable (fun k : ℕ => |A k|)

private theorem tail_blocks
    (a : ℕ → ℝ)
    (ha : Summable (fun n : ℕ => a (n + 1)))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ m : ℕ, 1 ≤ m →
      |blockSum a (n + 1) (n + m)| < ε := by
  let s : ℕ → ℝ := fun n => ∑ i ∈ Finset.range n, a (i + 1)
  let L : ℝ := ∑' n : ℕ, a (n + 1)
  have ht : Tendsto s atTop (nhds L) := by
    simpa [s, L] using ha.hasSum.tendsto_sum_nat
  rcases (Metric.tendsto_atTop.1 ht) (ε / 2) (by linarith) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn m hm
  have hnlim := hN n hn
  have hnmlim := hN (n + m) (by omega)
  have hnabs : |s n - L| < ε / 2 := by
    simpa [Real.dist_eq] using hnlim
  have hnmabs : |s (n + m) - L| < ε / 2 := by
    simpa [Real.dist_eq] using hnmlim
  have hset : Finset.Icc (n + 1) (n + m) =
      Finset.Ico (n + 1) (n + m + 1) := by
    ext i
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  have hle : n + 1 ≤ n + m + 1 := by omega
  have hsum := Finset.sum_range_add_sum_Ico a hle
  have hdiff :
      (∑ i ∈ Finset.Ico (n + 1) (n + m + 1), a i) =
        (∑ i ∈ Finset.range (n + m + 1), a i) -
          ∑ i ∈ Finset.range (n + 1), a i := by
    linarith
  have hblock : blockSum a (n + 1) (n + m) = s (n + m) - s n := by
    rw [blockSum, hset, hdiff, Finset.sum_range_succ',
      Finset.sum_range_succ']
    simp only [s]
    ring
  rw [hblock]
  calc
    |s (n + m) - s n| = |(s (n + m) - L) + (L - s n)| := by
      congr 1
      ring
    _ ≤ |s (n + m) - L| + |L - s n| := abs_add_le _ _
    _ < ε := by
      rw [abs_sub_comm L (s n)]
      linarith

theorem gap1 :
    ∀ a : ℕ → ℝ, ConditionallySummable a →
      ∃ N₁ : ℕ, ∀ m₁ : ℕ, 1 ≤ m₁ →
        |blockSum a (N₁ + 1) (N₁ + m₁)| < (1 / 2 : ℝ) := by
  intro a ha
  rcases tail_blocks a ha.1 (1 / 2 : ℝ) (by norm_num) with ⟨N, hN⟩
  exact ⟨N, fun m hm => hN N le_rfl m hm⟩

theorem gap2 :
    ∀ a : ℕ → ℝ, ConditionallySummable a →
      ∀ N₁ : ℕ, ∃ N₂ : ℕ, N₁ < N₂ ∧
        ∀ m₂ : ℕ, 1 ≤ m₂ →
          |blockSum a (N₂ + 1) (N₂ + m₂)| < epsilon 2 := by
  intro a ha N₁
  rcases tail_blocks a ha.1 (epsilon 2) (by simp [epsilon]) with ⟨N, hN⟩
  let N₂ := max N (N₁ + 1)
  refine ⟨N₂, ?_, ?_⟩
  · dsimp [N₂]
    omega
  · intro m hm
    exact hN N₂ (by simp [N₂]) m hm

theorem gap3 :
    ∀ a : ℕ → ℝ, ConditionallySummable a →
      ∃ N : ℕ → ℕ, ∀ k : ℕ, 1 ≤ k →
        N (k - 1) < N k ∧
          ∀ m : ℕ, 1 ≤ m →
            |blockSum a (N k + 1) (N k + m)| < epsilon k := by
  intro a ha
  have hepsilon : ∀ k : ℕ, 0 < epsilon k := by
    intro k
    simp [epsilon]
  choose B hB using fun k => tail_blocks a ha.1 (epsilon k) (hepsilon k)
  let N : ℕ → ℕ := fun k =>
    Nat.rec (B 0) (fun j n => max (B (j + 1)) (n + 1)) k
  refine ⟨N, ?_⟩
  intro k hk
  cases k with
  | zero => omega
  | succ j =>
      constructor
      · simp [N]
      · intro m hm
        apply hB (j + 1) (N (j + 1))
        · simp [N]
        · exact hm

theorem gap4
    (a : ℕ → ℝ) (N : ℕ → ℕ) (A : ℕ → ℝ)
    (hA : A 0 = blockSum a 1 (N 1) ∧
      ∀ k : ℕ, 1 ≤ k → A k = blockSum a (N k + 1) (N (k + 1)))
    (hbound : ∀ k : ℕ, 1 ≤ k →
      |blockSum a (N k + 1) (N (k + 1))| < epsilon k) :
    ∀ k : ℕ, 1 ≤ k → |A k| < epsilon k := by
  intro k hk
  rw [hA.2 k hk]
  exact hbound k hk

theorem gap5
    (a : ℕ → ℝ) (N : ℕ → ℕ) (A : ℕ → ℝ)
    (hN : StrictMono N)
    (hA : A 0 = blockSum a 1 (N 1) ∧
      ∀ k : ℕ, 1 ≤ k → A k = blockSum a (N k + 1) (N (k + 1)))
    (ha : Summable (fun n : ℕ => a (n + 1))) :
    ∑' k : ℕ, A k = ∑' n : ℕ, a (n + 1) := by
  have hblock : ∀ (b : ℕ → ℝ) (p q : ℕ), p ≤ q →
      blockSum b (p + 1) q =
        (∑ i ∈ Finset.range q, b (i + 1)) -
          ∑ i ∈ Finset.range p, b (i + 1) := by
    intro b p q hpq
    have hset : Finset.Icc (p + 1) q = Finset.Ico (p + 1) (q + 1) := by
      ext i
      simp only [Finset.mem_Icc, Finset.mem_Ico]
      omega
    have hle : p + 1 ≤ q + 1 := by omega
    have hsum := Finset.sum_range_add_sum_Ico b hle
    have hdiff :
        (∑ i ∈ Finset.Ico (p + 1) (q + 1), b i) =
          (∑ i ∈ Finset.range (q + 1), b i) -
            ∑ i ∈ Finset.range (p + 1), b i := by
      linarith
    rw [blockSum, hset, hdiff, Finset.sum_range_succ',
      Finset.sum_range_succ']
    ring
  have hpartial : ∀ K : ℕ, 1 ≤ K →
      (∑ k ∈ Finset.range K, A k) =
        ∑ n ∈ Finset.range (N K), a (n + 1) := by
    intro K
    induction K with
    | zero =>
        intro hK
        omega
    | succ K ih =>
        intro hK
        by_cases hK0 : K = 0
        · rw [hK0]
          calc
            (∑ k ∈ Finset.range (0 + 1), A k) = A 0 := by simp
            _ = blockSum a 1 (N 1) := hA.1
            _ = ∑ n ∈ Finset.range (N 1), a (n + 1) := by
              simpa using hblock a 0 (N 1) (Nat.zero_le _)
        · rw [Finset.sum_range_succ, hA.2 K (by omega), ih (by omega)]
          rw [hblock a (N K) (N (K + 1))
            (Nat.le_of_lt (hN (Nat.lt_succ_self K)))]
          ring
  have htSub : Tendsto
      (fun K : ℕ => ∑ n ∈ Finset.range (N K), a (n + 1))
      atTop (nhds (∑' n : ℕ, a (n + 1))) :=
    ha.hasSum.tendsto_sum_nat.comp hN.tendsto_atTop
  have htA : Tendsto
      (fun K : ℕ => ∑ k ∈ Finset.range K, A k)
      atTop (nhds (∑' n : ℕ, a (n + 1))) := by
    refine htSub.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with K hK
    exact (hpartial K hK).symm
  have habs_a : Summable (fun n : ℕ => |a (n + 1)|) := by
    have hnorm : Summable (fun n : ℕ => ‖a (n + 1)‖) :=
      (summable_norm_iff).2 ha
    simpa only [Real.norm_eq_abs] using hnorm
  let C : ℕ → ℝ := fun k =>
    if k = 0 then blockSum (fun i => |a i|) 1 (N 1)
    else blockSum (fun i => |a i|) (N k + 1) (N (k + 1))
  have hCzero : C 0 = blockSum (fun i => |a i|) 1 (N 1) := by
    simp [C]
  have hCpos : ∀ k : ℕ, k ≠ 0 →
      C k = blockSum (fun i => |a i|) (N k + 1) (N (k + 1)) := by
    intro k hk
    simp [C, hk]
  have hCnonneg : ∀ k : ℕ, 0 ≤ C k := by
    intro k
    by_cases hk : k = 0
    · rw [hk, hCzero]
      unfold blockSum
      exact Finset.sum_nonneg fun i hi => abs_nonneg (a i)
    · rw [hCpos k hk]
      unfold blockSum
      exact Finset.sum_nonneg fun i hi => abs_nonneg (a i)
  have hCpartial : ∀ K : ℕ, 1 ≤ K →
      (∑ k ∈ Finset.range K, C k) =
        ∑ n ∈ Finset.range (N K), |a (n + 1)| := by
    intro K
    induction K with
    | zero =>
        intro hK
        omega
    | succ K ih =>
        intro hK
        by_cases hK0 : K = 0
        · rw [hK0]
          calc
            (∑ k ∈ Finset.range (0 + 1), C k) = C 0 := by simp
            _ = blockSum (fun i => |a i|) 1 (N 1) := hCzero
            _ = ∑ n ∈ Finset.range (N 1), |a (n + 1)| := by
              simpa using hblock (fun i => |a i|) 0 (N 1) (Nat.zero_le _)
        · rw [Finset.sum_range_succ, hCpos K hK0, ih (by omega)]
          rw [hblock (fun i => |a i|) (N K) (N (K + 1))
            (Nat.le_of_lt (hN (Nat.lt_succ_self K)))]
          ring
  have htCSub : Tendsto
      (fun K : ℕ => ∑ n ∈ Finset.range (N K), |a (n + 1)|)
      atTop (nhds (∑' n : ℕ, |a (n + 1)|)) :=
    habs_a.hasSum.tendsto_sum_nat.comp hN.tendsto_atTop
  have htC : Tendsto
      (fun K : ℕ => ∑ k ∈ Finset.range K, C k)
      atTop (nhds (∑' n : ℕ, |a (n + 1)|)) := by
    refine htCSub.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with K hK
    exact (hCpartial K hK).symm
  have hCsum : HasSum C (∑' n : ℕ, |a (n + 1)|) :=
    (hasSum_iff_tendsto_nat_of_nonneg hCnonneg
      (∑' n : ℕ, |a (n + 1)|)).2 htC
  have habs_sum : ∀ s : Finset ℕ,
      |∑ i ∈ s, a i| ≤ ∑ i ∈ s, |a i| := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert x s hx ih =>
        rw [Finset.sum_insert hx, Finset.sum_insert hx]
        exact (abs_add_le _ _).trans
          (add_le_add (le_refl _) ih)
  have hAC : ∀ k : ℕ, ‖A k‖ ≤ C k := by
    intro k
    rw [Real.norm_eq_abs]
    by_cases hk : k = 0
    · rw [hk, hA.1, hCzero]
      simpa only [blockSum] using habs_sum (Finset.Icc 1 (N 1))
    · have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
      rw [hA.2 k hk1, hCpos k hk]
      simpa only [blockSum] using
        habs_sum (Finset.Icc (N k + 1) (N (k + 1)))
  have hAsummable : Summable A :=
    Summable.of_norm_bounded hCsum.summable hAC
  exact tendsto_nhds_unique hAsummable.hasSum.tendsto_sum_nat htA

theorem gap6 :
    Summable (fun k : ℕ => epsilon (k + 1)) := by
  have hgeom : Summable (fun k : ℕ => ((2 : ℝ)⁻¹) ^ k) :=
    (hasSum_geometric_of_norm_lt_one
      (by norm_num : ‖(2 : ℝ)⁻¹‖ < 1)).summable
  have hshift := hgeom.mul_left ((2 : ℝ)⁻¹)
  simpa [epsilon, one_div, pow_succ] using hshift

theorem gap7 :
    (∑' k : ℕ, epsilon (k + 1)) =
      ∑' k : ℕ, 1 / (2 : ℝ) ^ (k + 1) := by
  rfl

theorem gap8
    (A : ℕ → ℝ)
    (hbound : ∀ k : ℕ, 1 ≤ k → |A k| < epsilon k) :
    Summable (fun k : ℕ => |A k|) := by
  have htail : Summable (fun k : ℕ => |A (k + 1)|) := by
    apply Summable.of_norm_bounded gap6
    intro k
    simpa [Real.norm_eq_abs] using
      le_of_lt (hbound (k + 1) (by omega))
  rw [← summable_nat_add_iff 1]
  simpa [Nat.add_comm] using htail

theorem gap9
    (A : ℕ → ℝ)
    (habsolute : Summable (fun k : ℕ => |A k|)) :
    AbsolutelySummable A := by
  exact habsolute

theorem gap10 :
    ∀ a : ℕ → ℝ, ConditionallySummable a →
      ∃ A : ℕ → ℝ,
        AbsolutelySummable A ∧
          ∑' k : ℕ, A k = ∑' n : ℕ, a (n + 1) := by
  intro a ha
  rcases gap3 a ha with ⟨N, hN⟩
  have hmono : StrictMono N := strictMono_nat_of_lt_succ fun k => by
    simpa only [Nat.add_sub_cancel] using
      (hN (k + 1) (Nat.succ_le_succ (Nat.zero_le k))).1
  let A : ℕ → ℝ := fun k =>
    if k = 0 then blockSum a 1 (N 1)
    else blockSum a (N k + 1) (N (k + 1))
  have hA : A 0 = blockSum a 1 (N 1) ∧
      ∀ k : ℕ, 1 ≤ k →
        A k = blockSum a (N k + 1) (N (k + 1)) := by
    constructor
    · simp [A]
    · intro k hk
      have hk0 : k ≠ 0 := by omega
      simp [A, hk0]
  have hbound : ∀ k : ℕ, 1 ≤ k →
      |blockSum a (N k + 1) (N (k + 1))| < epsilon k := by
    intro k hk
    have hstep := hN k hk
    have hle : N k ≤ N (k + 1) :=
      Nat.le_of_lt (hmono (Nat.lt_succ_self k))
    have hm : 1 ≤ N (k + 1) - N k :=
      Nat.sub_pos_of_lt (hmono (Nat.lt_succ_self k))
    have hb := hstep.2 (N (k + 1) - N k) hm
    have hend : N k + (N (k + 1) - N k) = N (k + 1) :=
      Nat.add_sub_of_le hle
    rw [hend] at hb
    exact hb
  have habs : AbsolutelySummable A :=
    gap9 A (gap8 A (gap4 a N A hA hbound))
  refine ⟨A, habs, ?_⟩
  exact gap5 a N A hmono hA ha.1

end

end ProofGap.Exercise2656
