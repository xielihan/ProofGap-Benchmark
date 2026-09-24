import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Lean.Elab.Tactic.Omega
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise2193
noncomputable section

open Filter
open scoped BigOperators Interval

def IsTaggedPartition (a b : ℝ) (n : ℕ)
    (x ξ θ : ℕ → ℝ) : Prop :=
  x 0 = a ∧ x n = b ∧
    ∀ i < n,
      x i ≤ ξ i ∧ ξ i ≤ x (i + 1) ∧
      x i ≤ θ i ∧ θ i ≤ x (i + 1) ∧
      x i ≤ x (i + 1)

def Fine (n : ℕ) (x : ℕ → ℝ) (δ : ℝ) : Prop :=
  ∀ i < n, |x (i + 1) - x i| < δ

def StandardSum (f φ : ℝ → ℝ) (n : ℕ)
    (x ξ : ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range n,
    f (ξ i) * φ (ξ i) * (x (i + 1) - x i)

def MixedSum (f φ : ℝ → ℝ) (n : ℕ)
    (x ξ θ : ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range n,
    f (ξ i) * φ (θ i) * (x (i + 1) - x i)

def ErrorSum (f φ : ℝ → ℝ) (n : ℕ)
    (x ξ θ : ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range n,
    (f (ξ i) * φ (θ i) - f (ξ i) * φ (ξ i)) *
      (x (i + 1) - x i)

def FineSequence (n : ℕ → ℕ) (x : ℕ → ℕ → ℝ) : Prop :=
  ∀ δ > 0, ∀ᶠ k in atTop, Fine (n k) (x k) δ

private theorem chain_le_of_steps {x : ℕ → ℝ} {n : ℕ}
    (hstep : ∀ i < n, x i ≤ x (i + 1)) :
    ∀ i j, i ≤ j → j ≤ n → x i ≤ x j := by
  intro i j
  induction j with
  | zero =>
      intro hij hjn
      have hi : i = 0 := Nat.eq_zero_of_le_zero hij
      subst i
      exact le_rfl
  | succ j ih =>
      intro hij hjn
      by_cases heq : i = j + 1
      · subst i
        exact le_rfl
      · have hij' : i ≤ j := by omega
        exact (ih hij' (Nat.le_trans (Nat.le_succ j) hjn)).trans
          (hstep j (Nat.lt_of_succ_le hjn))

private theorem partition_x_mem {a b : ℝ} {n : ℕ}
    {x ξ θ : ℕ → ℝ} (hp : IsTaggedPartition a b n x ξ θ)
    {i : ℕ} (hi : i ≤ n) : x i ∈ Set.Icc a b := by
  rcases hp with ⟨hzero, hn, hp⟩
  have hstep : ∀ j < n, x j ≤ x (j + 1) :=
    fun j hj => (hp j hj).2.2.2.2
  constructor
  · rw [← hzero]
    exact chain_le_of_steps hstep 0 i (Nat.zero_le i) hi
  · rw [← hn]
    exact chain_le_of_steps hstep i n hi (le_refl n)

private theorem partition_tags_mem {a b : ℝ} {n : ℕ}
    {x ξ θ : ℕ → ℝ} (hp : IsTaggedPartition a b n x ξ θ)
    {i : ℕ} (hi : i < n) :
    ξ i ∈ Set.Icc a b ∧ θ i ∈ Set.Icc a b := by
  rcases hp.2.2 i hi with ⟨hxi, hξnext, hθi, hθnext, hxnext⟩
  have hleft := partition_x_mem hp (Nat.le_of_lt hi)
  have hright := partition_x_mem hp (Nat.succ_le_iff.mpr hi)
  constructor
  · exact ⟨hleft.1.trans hxi, hξnext.trans hright.2⟩
  · exact ⟨hleft.1.trans hθi, hθnext.trans hright.2⟩

theorem gap1 (f φ : ℝ → ℝ) (a b : ℝ)
    (hf : ContinuousOn f (Set.Icc a b))
    (hφ : ContinuousOn φ (Set.Icc a b)) :
    ContinuousOn (fun x => f x * φ x) (Set.Icc a b) := by
  exact hf.mul hφ

theorem gap2 (f φ : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b))
    (hφ : ContinuousOn φ (Set.Icc a b))
    (n : ℕ → ℕ) (x ξ θ : ℕ → ℕ → ℝ)
    (hp : ∀ k, IsTaggedPartition a b (n k) (x k) (ξ k) (θ k))
    (hmesh : FineSequence n x) :
    Tendsto (fun k => StandardSum f φ (n k) (x k) (ξ k)) atTop
      (nhds (∫ t in a..b, f t * φ t)) := by
  let g : ℝ → ℝ := fun t => f t * φ t
  have hg : ContinuousOn g (Set.Icc a b) := gap1 f φ a b hf hφ
  change Tendsto (fun k => StandardSum f φ (n k) (x k) (ξ k)) atTop
    (nhds (∫ t in a..b, g t))
  by_cases heq : a = b
  · subst b
    have hsumzero : ∀ k, StandardSum f φ (n k) (x k) (ξ k) = 0 := by
      intro k
      unfold StandardSum
      apply Finset.sum_eq_zero
      intro i hi
      have hin : i < n k := Finset.mem_range.mp hi
      have hxi := partition_x_mem (hp k) (Nat.le_of_lt hin)
      have hxnext := partition_x_mem (hp k) (Nat.succ_le_iff.mpr hin)
      have hxi' : x k i = a := by simpa using hxi
      have hxnext' : x k (i + 1) = a := by simpa using hxnext
      simp [hxi', hxnext']
    simpa [hsumzero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
  · have hablt : a < b := lt_of_le_of_ne hab heq
    have hba : 0 < b - a := sub_pos.mpr hablt
    have hug : UniformContinuousOn g (Set.Icc a b) :=
      isCompact_Icc.uniformContinuousOn_of_continuous hg
    rw [Metric.uniformContinuousOn_iff] at hug
    rw [Metric.tendsto_atTop]
    intro ε hε
    let q : ℝ := ε / (2 * (b - a))
    have hq : 0 < q := by
      dsimp [q]
      positivity
    rcases hug q hq with ⟨δ, hδ, hcontrol⟩
    rcases eventually_atTop.1 (hmesh δ hδ) with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro k hk
    have p := hp k
    have hkfine := hN k hk
    have hstep : ∀ i < n k, x k i ≤ x k (i + 1) :=
      fun i hi => (p.2.2 i hi).2.2.2.2
    have hsubint : ∀ {i j : ℕ}, i ≤ j → j ≤ n k →
        IntervalIntegrable g MeasureTheory.volume (x k i) (x k j) := by
      intro i j hij hjn
      have hxi := partition_x_mem p (Nat.le_trans hij hjn)
      have hxj := partition_x_mem p hjn
      have hxij := chain_le_of_steps hstep i j hij hjn
      apply (hg.mono ?_).intervalIntegrable
      rw [Set.uIcc_of_le hxij]
      intro z hz
      exact ⟨hxi.1.trans hz.1, hz.2.trans hxj.2⟩
    have hintsum : ∀ m : ℕ, m ≤ n k →
        (∑ i ∈ Finset.range m, ∫ t in x k i..x k (i + 1), g t) =
          ∫ t in x k 0..x k m, g t := by
      intro m hm
      induction m with
      | zero => simp
      | succ m ih =>
          have hmle : m ≤ n k := Nat.le_trans (Nat.le_succ m) hm
          rw [Finset.sum_range_succ, ih hmle]
          exact intervalIntegral.integral_add_adjacent_intervals
            (hsubint (Nat.zero_le m) hmle)
            (hsubint (Nat.le_succ m) hm)
    have hsumint :
        (∑ i ∈ Finset.range (n k), ∫ t in x k i..x k (i + 1), g t) =
          ∫ t in a..b, g t := by
      simpa [p.1, p.2.1] using hintsum (n k) (le_refl _)
    have htelx : ∀ m : ℕ,
        (∑ i ∈ Finset.range m, (x k (i + 1) - x k i)) =
          x k m - x k 0 := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
          rw [Finset.sum_range_succ, ih]
          ring
    have htel :
        (∑ i ∈ Finset.range (n k), (x k (i + 1) - x k i)) = b - a := by
      simpa [p.1, p.2.1] using htelx (n k)
    have herr : ∀ i ∈ Finset.range (n k),
        |g (ξ k i) * (x k (i + 1) - x k i) -
          ∫ t in x k i..x k (i + 1), g t| ≤
            q * (x k (i + 1) - x k i) := by
      intro i hi
      have hin : i < n k := Finset.mem_range.mp hi
      rcases p.2.2 i hin with ⟨hxi, hξnext, hθi, hθnext, hxnext⟩
      have htags := partition_tags_mem p hin
      have hdx : 0 ≤ x k (i + 1) - x k i := sub_nonneg.mpr hxnext
      have hwidth : x k (i + 1) - x k i < δ := by
        simpa [abs_of_nonneg hdx] using hkfine i hin
      have hgcell : IntervalIntegrable g MeasureTheory.volume
          (x k i) (x k (i + 1)) :=
        hsubint (Nat.le_succ i) (Nat.succ_le_iff.mpr hin)
      have hbound : ∀ t ∈ Set.Icc (x k i) (x k (i + 1)),
          |g (ξ k i) - g t| ≤ q := by
        intro t ht
        have htglobal : t ∈ Set.Icc a b := by
          have hleft := partition_x_mem p (Nat.le_of_lt hin)
          have hright := partition_x_mem p (Nat.succ_le_iff.mpr hin)
          exact ⟨hleft.1.trans ht.1, ht.2.trans hright.2⟩
        have hdist : dist (ξ k i) t < δ := by
          rw [Real.dist_eq]
          have hle : |ξ k i - t| ≤ x k (i + 1) - x k i := by
            rw [abs_le]
            constructor
            · linarith [hxi, ht.2]
            · linarith [hξnext, ht.1]
          exact hle.trans_lt hwidth
        have hout := hcontrol (ξ k i) htags.1 t htglobal hdist
        exact le_of_lt (by simpa [Real.dist_eq] using hout)
      have heq :
          g (ξ k i) * (x k (i + 1) - x k i) -
              ∫ t in x k i..x k (i + 1), g t =
            ∫ t in x k i..x k (i + 1), (g (ξ k i) - g t) := by
        rw [intervalIntegral.integral_sub intervalIntegrable_const hgcell]
        simp [intervalIntegral.integral_const, mul_comm]
      rw [heq]
      have hnormbound :
          ∀ t ∈ Set.uIoc (x k i) (x k (i + 1)),
            ‖g (ξ k i) - g t‖ ≤ q := by
        intro t ht
        have htcell : t ∈ Set.Icc (x k i) (x k (i + 1)) := by
          rw [Set.uIoc_of_le hxnext] at ht
          exact ⟨le_of_lt ht.1, ht.2⟩
        simpa [Real.norm_eq_abs] using hbound t htcell
      simpa [Real.norm_eq_abs, abs_of_nonneg hdx, mul_comm] using
        (intervalIntegral.norm_integral_le_of_norm_le_const hnormbound)
    have hsumsub :
        StandardSum f φ (n k) (x k) (ξ k) - (∫ t in a..b, g t) =
          ∑ i ∈ Finset.range (n k),
            (g (ξ k i) * (x k (i + 1) - x k i) -
              ∫ t in x k i..x k (i + 1), g t) := by
      unfold StandardSum
      simp only [g]
      rw [← hsumint, ← Finset.sum_sub_distrib]
    rw [Real.dist_eq, hsumsub]
    calc
      |∑ i ∈ Finset.range (n k),
          (g (ξ k i) * (x k (i + 1) - x k i) -
            ∫ t in x k i..x k (i + 1), g t)| ≤
          ∑ i ∈ Finset.range (n k),
            |g (ξ k i) * (x k (i + 1) - x k i) -
              ∫ t in x k i..x k (i + 1), g t| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range (n k), q * (x k (i + 1) - x k i) := by
        apply Finset.sum_le_sum
        intro i hi
        exact herr i hi
      _ = q * (b - a) := by
        rw [← Finset.mul_sum, htel]
      _ = ε / 2 := by
        dsimp [q]
        field_simp [ne_of_gt hba]
      _ < ε := by linarith

theorem gap3 (f : ℝ → ℝ) (a b : ℝ)
    (hf : ContinuousOn f (Set.Icc a b)) :
    Bornology.IsBounded (f '' Set.Icc a b) := by
  exact (isCompact_Icc.image_of_continuousOn hf).isBounded

theorem gap4 (f : ℝ → ℝ) (a b : ℝ)
    (hf : ContinuousOn f (Set.Icc a b)) :
    ∃ M > 0, ∀ x ∈ Set.Icc a b, |f x| ≤ M := by
  have hb := gap3 f a b hf
  rcases (Metric.isBounded_iff_subset_ball (0 : ℝ)).mp hb with ⟨r, hr⟩
  refine ⟨max 1 r, lt_max_of_lt_left zero_lt_one, ?_⟩
  intro x hx
  have hmem : f x ∈ Metric.ball (0 : ℝ) r := hr ⟨x, hx, rfl⟩
  have hlt : |f x| < r := by
    simpa [Real.dist_eq] using hmem
  exact (le_of_lt hlt).trans (le_max_right 1 r)

theorem gap5 (φ : ℝ → ℝ) (a b : ℝ)
    (hφ : ContinuousOn φ (Set.Icc a b)) :
    UniformContinuousOn φ (Set.Icc a b) := by
  exact isCompact_Icc.uniformContinuousOn_of_continuous hφ

theorem gap6 (f φ : ℝ → ℝ) (a b M ε : ℝ)
    (hab : a < b) (hM : 0 < M)
    (hf : ∀ x ∈ Set.Icc a b, |f x| ≤ M)
    (hφ : UniformContinuousOn φ (Set.Icc a b))
    (hε : 0 < ε) :
    ∃ δ > 0, ∀ u ∈ Set.Icc a b, ∀ v ∈ Set.Icc a b,
      |u - v| < δ → |φ u - φ v| < ε / (M * (b - a)) := by
  have hba : 0 < b - a := sub_pos.mpr hab
  have hden : 0 < M * (b - a) := mul_pos hM hba
  have hq : 0 < ε / (M * (b - a)) := div_pos hε hden
  rw [Metric.uniformContinuousOn_iff] at hφ
  rcases hφ (ε / (M * (b - a))) hq with ⟨δ, hδ, hcontrol⟩
  refine ⟨δ, hδ, ?_⟩
  intro u hu v hv huv
  have hout := hcontrol u hu v hv
  simpa [Real.dist_eq] using hout huv

theorem gap7 (f φ : ℝ → ℝ) (n : ℕ) (x ξ θ : ℕ → ℝ) :
    |ErrorSum f φ n x ξ θ| ≤
      ∑ i ∈ Finset.range n,
        |f (ξ i)| * |φ (θ i) - φ (ξ i)| *
          |x (i + 1) - x i| := by
  unfold ErrorSum
  calc
    |∑ i ∈ Finset.range n,
        (f (ξ i) * φ (θ i) - f (ξ i) * φ (ξ i)) *
          (x (i + 1) - x i)| ≤
        ∑ i ∈ Finset.range n,
          |(f (ξ i) * φ (θ i) - f (ξ i) * φ (ξ i)) *
            (x (i + 1) - x i)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ Finset.range n,
          |f (ξ i)| * |φ (θ i) - φ (ξ i)| *
            |x (i + 1) - x i| := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [show f (ξ i) * φ (θ i) - f (ξ i) * φ (ξ i) =
          f (ξ i) * (φ (θ i) - φ (ξ i)) by ring]
      simp only [abs_mul]

theorem gap8 (f φ : ℝ → ℝ) (a b M ε δ : ℝ)
    (n : ℕ) (x ξ θ : ℕ → ℝ)
    (hab : a < b) (hM : 0 < M) (hε : 0 < ε)
    (hp : IsTaggedPartition a b n x ξ θ)
    (hf : ∀ u ∈ Set.Icc a b, |f u| ≤ M)
    (hφ : ∀ u ∈ Set.Icc a b, ∀ v ∈ Set.Icc a b,
      |u - v| < δ → |φ u - φ v| < ε / (M * (b - a)))
    (hfine : Fine n x δ) :
    (∑ i ∈ Finset.range n,
      |f (ξ i)| * |φ (θ i) - φ (ξ i)| *
        |x (i + 1) - x i|) < ε := by
  have hstep : ∀ i < n, x i ≤ x (i + 1) :=
    fun i hi => (hp.2.2 i hi).2.2.2.2
  have htelx : ∀ m : ℕ,
      (∑ i ∈ Finset.range m, (x (i + 1) - x i)) = x m - x 0 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
        rw [Finset.sum_range_succ, ih]
        ring
  have htel : (∑ i ∈ Finset.range n, (x (i + 1) - x i)) = b - a := by
    simpa [hp.1, hp.2.1] using htelx n
  have hex : ∃ i ∈ Finset.range n, 0 < x (i + 1) - x i := by
    by_contra hnone
    have hz : ∀ i ∈ Finset.range n, x (i + 1) - x i = 0 := by
      intro i hi
      have hin : i < n := Finset.mem_range.mp hi
      have hnonneg : 0 ≤ x (i + 1) - x i := sub_nonneg.mpr (hstep i hin)
      have hnpos : ¬ 0 < x (i + 1) - x i := by
        intro hpos
        exact hnone ⟨i, hi, hpos⟩
      exact le_antisymm (not_lt.mp hnpos) hnonneg
    have hzero : (∑ i ∈ Finset.range n, (x (i + 1) - x i)) = 0 :=
      Finset.sum_eq_zero hz
    linarith
  have hterm_le : ∀ i ∈ Finset.range n,
      |f (ξ i)| * |φ (θ i) - φ (ξ i)| * |x (i + 1) - x i| ≤
        (M * (ε / (M * (b - a)))) * (x (i + 1) - x i) := by
    intro i hi
    have hin : i < n := Finset.mem_range.mp hi
    rcases hp.2.2 i hin with ⟨hxi, hξnext, hθi, hθnext, hxnext⟩
    have htags := partition_tags_mem hp hin
    have hdx : 0 ≤ x (i + 1) - x i := sub_nonneg.mpr hxnext
    have hdist : |θ i - ξ i| < δ := by
      have hle : |θ i - ξ i| ≤ x (i + 1) - x i := by
        rw [abs_le]
        constructor <;> linarith
      have hwidth : x (i + 1) - x i < δ := by
        simpa [abs_of_nonneg hdx] using hfine i hin
      exact hle.trans_lt hwidth
    have hφi := hφ (θ i) htags.2 (ξ i) htags.1 hdist
    have hfi := hf (ξ i) htags.1
    have hprod : |f (ξ i)| * |φ (θ i) - φ (ξ i)| <
        M * (ε / (M * (b - a))) := by
      calc
        |f (ξ i)| * |φ (θ i) - φ (ξ i)| ≤
            M * |φ (θ i) - φ (ξ i)| :=
          mul_le_mul_of_nonneg_right hfi (abs_nonneg _)
        _ < M * (ε / (M * (b - a))) :=
          mul_lt_mul_of_pos_left hφi hM
    rw [abs_of_nonneg hdx]
    exact mul_le_mul_of_nonneg_right (le_of_lt hprod) hdx
  have hterm_lt : ∀ i ∈ Finset.range n, 0 < x (i + 1) - x i →
      |f (ξ i)| * |φ (θ i) - φ (ξ i)| * |x (i + 1) - x i| <
        (M * (ε / (M * (b - a)))) * (x (i + 1) - x i) := by
    intro i hi hdx
    have hin : i < n := Finset.mem_range.mp hi
    rcases hp.2.2 i hin with ⟨hxi, hξnext, hθi, hθnext, hxnext⟩
    have htags := partition_tags_mem hp hin
    have hdist : |θ i - ξ i| < δ := by
      have hle : |θ i - ξ i| ≤ x (i + 1) - x i := by
        rw [abs_le]
        constructor <;> linarith
      have hwidth : x (i + 1) - x i < δ := by
        simpa [abs_of_pos hdx] using hfine i hin
      exact hle.trans_lt hwidth
    have hφi := hφ (θ i) htags.2 (ξ i) htags.1 hdist
    have hfi := hf (ξ i) htags.1
    have hprod : |f (ξ i)| * |φ (θ i) - φ (ξ i)| <
        M * (ε / (M * (b - a))) := by
      calc
        |f (ξ i)| * |φ (θ i) - φ (ξ i)| ≤
            M * |φ (θ i) - φ (ξ i)| :=
          mul_le_mul_of_nonneg_right hfi (abs_nonneg _)
        _ < M * (ε / (M * (b - a))) :=
          mul_lt_mul_of_pos_left hφi hM
    rw [abs_of_pos hdx]
    exact mul_lt_mul_of_pos_right hprod hdx
  have hsumlt :
      (∑ i ∈ Finset.range n,
        |f (ξ i)| * |φ (θ i) - φ (ξ i)| * |x (i + 1) - x i|) <
      ∑ i ∈ Finset.range n,
        (M * (ε / (M * (b - a)))) * (x (i + 1) - x i) := by
    apply Finset.sum_lt_sum hterm_le
    rcases hex with ⟨i, hi, hdx⟩
    exact ⟨i, hi, hterm_lt i hi hdx⟩
  calc
    (∑ i ∈ Finset.range n,
      |f (ξ i)| * |φ (θ i) - φ (ξ i)| * |x (i + 1) - x i|) <
        ∑ i ∈ Finset.range n,
          (M * (ε / (M * (b - a)))) * (x (i + 1) - x i) := hsumlt
    _ = (M * (ε / (M * (b - a)))) * (b - a) := by
      rw [← Finset.mul_sum, htel]
    _ = ε := by
      field_simp [ne_of_gt hM, ne_of_gt (sub_pos.mpr hab)]

theorem gap9 (f φ : ℝ → ℝ) (a b M ε δ : ℝ)
    (n : ℕ) (x ξ θ : ℕ → ℝ)
    (hab : a < b) (hM : 0 < M) (hε : 0 < ε)
    (hp : IsTaggedPartition a b n x ξ θ)
    (hf : ∀ u ∈ Set.Icc a b, |f u| ≤ M)
    (hφ : ∀ u ∈ Set.Icc a b, ∀ v ∈ Set.Icc a b,
      |u - v| < δ → |φ u - φ v| < ε / (M * (b - a)))
    (hfine : Fine n x δ) :
    |ErrorSum f φ n x ξ θ| < ε := by
  exact lt_of_le_of_lt (gap7 f φ n x ξ θ)
    (gap8 f φ a b M ε δ n x ξ θ hab hM hε hp hf hφ hfine)

theorem gap10 (f φ : ℝ → ℝ) (a b : ℝ)
    (n : ℕ → ℕ) (x ξ θ : ℕ → ℕ → ℝ)
    (hp : ∀ k, IsTaggedPartition a b (n k) (x k) (ξ k) (θ k))
    (hf : ContinuousOn f (Set.Icc a b))
    (hφ : ContinuousOn φ (Set.Icc a b))
    (hmesh : FineSequence n x) :
    Tendsto (fun k => ErrorSum f φ (n k) (x k) (ξ k) (θ k))
      atTop (nhds (0 : ℝ)) := by
  have hab : a ≤ b := by
    have p := hp 0
    have hs : ∀ i < n 0, x 0 i ≤ x 0 (i + 1) :=
      fun i hi => (p.2.2 i hi).2.2.2.2
    have hle := chain_le_of_steps hs 0 (n 0) (Nat.zero_le _) (le_refl _)
    rw [p.1, p.2.1] at hle
    exact hle
  by_cases heq : a = b
  · subst b
    have herr : ∀ k, ErrorSum f φ (n k) (x k) (ξ k) (θ k) = 0 := by
      intro k
      unfold ErrorSum
      apply Finset.sum_eq_zero
      intro i hi
      have hin : i < n k := Finset.mem_range.mp hi
      have hxi := partition_x_mem (hp k) (Nat.le_of_lt hin)
      have hxnext := partition_x_mem (hp k) (Nat.succ_le_iff.mpr hin)
      have hxi' : x k i = a := by simpa using hxi
      have hxnext' : x k (i + 1) = a := by simpa using hxnext
      simp [hxi', hxnext']
    simpa [herr] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
  · have hablt : a < b := lt_of_le_of_ne hab heq
    rcases gap4 f a b hf with ⟨M, hM, hMf⟩
    rw [Metric.tendsto_atTop]
    intro ε hε
    rcases gap6 f φ a b M ε hablt hM hMf
      (gap5 φ a b hφ) hε with ⟨δ, hδ, hcontrol⟩
    rcases eventually_atTop.1 (hmesh δ hδ) with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro k hk
    simpa [Real.dist_eq] using
      (gap9 f φ a b M ε δ (n k) (x k) (ξ k) (θ k)
        hablt hM hε (hp k) hMf hcontrol (hN k hk))

theorem gap11 (f φ : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (n : ℕ → ℕ) (x ξ θ : ℕ → ℕ → ℝ)
    (hp : ∀ k, IsTaggedPartition a b (n k) (x k) (ξ k) (θ k))
    (hf : ContinuousOn f (Set.Icc a b))
    (hφ : ContinuousOn φ (Set.Icc a b))
    (hmesh : FineSequence n x) :
    Tendsto (fun k => MixedSum f φ (n k) (x k) (ξ k) (θ k))
      atTop (nhds (∫ t in a..b, f t * φ t)) := by
  have hdecomp : ∀ k,
      MixedSum f φ (n k) (x k) (ξ k) (θ k) =
        StandardSum f φ (n k) (x k) (ξ k) +
          ErrorSum f φ (n k) (x k) (ξ k) (θ k) := by
    intro k
    simp only [MixedSum, StandardSum, ErrorSum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have ht := (gap2 f φ a b hab hf hφ n x ξ θ hp hmesh).add
    (gap10 f φ a b n x ξ θ hp hf hφ hmesh)
  convert ht using 1
  · funext k
    exact hdecomp k
  · simp

theorem gap12 (f φ : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (n : ℕ → ℕ) (x ξ θ : ℕ → ℕ → ℝ)
    (hp : ∀ k, IsTaggedPartition a b (n k) (x k) (ξ k) (θ k))
    (hf : ContinuousOn f (Set.Icc a b))
    (hφ : ContinuousOn φ (Set.Icc a b))
    (hmesh : FineSequence n x) :
    Tendsto (fun k => MixedSum f φ (n k) (x k) (ξ k) (θ k))
      atTop (nhds (∫ t in a..b, f t * φ t)) := by
  exact gap11 f φ a b hab n x ξ θ hp hf hφ hmesh

end
end ProofGap.Exercise2193
