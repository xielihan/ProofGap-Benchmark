import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Algebra.InfiniteSum.Order

namespace ProofGap.Exercise2787

noncomputable section

open scoped BigOperators

def majorant (φ : ℕ → ℝ → ℝ) (a b : ℝ) (n : ℕ) : ℝ :=
  max |φ n a| |φ n b|

def SeriesUniformlyConvergesOn
    (u : ℕ → ℝ → ℝ) (s : Set ℝ) (g : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ s,
    |(∑ k ∈ Finset.range (n + 1), u k x) - g x| < ε

theorem gap1 (φ : ℕ → ℝ → ℝ) (a : ℝ)
    (ha : Summable (fun n : ℕ => |φ (n + 1) a|)) :
    Summable (fun n : ℕ => |φ (n + 1) a|) := by
  exact ha

theorem gap2 (φ : ℕ → ℝ → ℝ) (b : ℝ)
    (hb : Summable (fun n : ℕ => |φ (n + 1) b|)) :
    Summable (fun n : ℕ => |φ (n + 1) b|) := by
  exact hb

theorem gap3 (φ : ℕ → ℝ → ℝ) (a b : ℝ) (n : ℕ) :
    0 ≤ majorant φ a b n := by
  unfold majorant
  exact le_trans (abs_nonneg _) (le_max_left _ _)

theorem gap4 (φ : ℕ → ℝ → ℝ) (a b : ℝ) (n : ℕ) :
    majorant φ a b n ≤ |φ n a| + |φ n b| := by
  unfold majorant
  refine max_le ?_ ?_
  · exact le_add_of_nonneg_right (abs_nonneg _)
  · exact le_add_of_nonneg_left (abs_nonneg _)

theorem gap5 (φ : ℕ → ℝ → ℝ) (a b : ℝ) (n : ℕ) :
    0 ≤ |φ n a| + |φ n b| := by
  exact add_nonneg (abs_nonneg _) (abs_nonneg _)

theorem gap6 (φ : ℕ → ℝ → ℝ) (a b : ℝ)
    (ha : Summable (fun n : ℕ => |φ (n + 1) a|))
    (hb : Summable (fun n : ℕ => |φ (n + 1) b|)) :
    Summable (fun n : ℕ => majorant φ a b (n + 1)) := by
  apply Summable.of_norm_bounded (ha.add hb)
  intro n
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg (gap3 φ a b (n + 1)),
    abs_of_nonneg (gap5 φ a b (n + 1))] using
    (gap4 φ a b (n + 1))

theorem gap7 (φ : ℕ → ℝ → ℝ) (a b x : ℝ) (n : ℕ)
    (hx : x ∈ Set.Icc a b)
    (hmono : MonotoneOn (φ n) (Set.Icc a b) ∨
      AntitoneOn (φ n) (Set.Icc a b)) :
    |φ n x| ≤ majorant φ a b n := by
  unfold majorant
  have hab : a ≤ b := hx.1.trans hx.2
  have haI : a ∈ Set.Icc a b := ⟨le_rfl, hab⟩
  have hbI : b ∈ Set.Icc a b := ⟨hab, le_rfl⟩
  apply (abs_le).2
  rcases hmono with hm | hm
  · have hax : φ n a ≤ φ n x := hm haI hx hx.1
    have hxb : φ n x ≤ φ n b := hm hx hbI hx.2
    constructor
    · exact (neg_le_neg (le_max_left |φ n a| |φ n b|)).trans
        ((neg_abs_le (φ n a)).trans hax)
    · exact hxb.trans ((le_abs_self (φ n b)).trans
        (le_max_right |φ n a| |φ n b|))
  · have hxa : φ n x ≤ φ n a := hm haI hx hx.1
    have hbx : φ n b ≤ φ n x := hm hx hbI hx.2
    constructor
    · exact (neg_le_neg (le_max_right |φ n a| |φ n b|)).trans
        ((neg_abs_le (φ n b)).trans hbx)
    · exact hxa.trans ((le_abs_self (φ n a)).trans
        (le_max_left |φ n a| |φ n b|))

theorem gap8 (φ : ℕ → ℝ → ℝ) (a b x : ℝ)
    (hx : x ∈ Set.Icc a b)
    (hmono : ∀ n : ℕ, 1 ≤ n →
      (MonotoneOn (φ n) (Set.Icc a b) ∨
        AntitoneOn (φ n) (Set.Icc a b)))
    (ha : Summable (fun n : ℕ => |φ (n + 1) a|))
    (hb : Summable (fun n : ℕ => |φ (n + 1) b|)) :
    Summable (fun n : ℕ => |φ (n + 1) x|) := by
  apply Summable.of_norm_bounded (gap6 φ a b ha hb)
  intro n
  have hbound := gap7 φ a b x (n + 1) hx
    (hmono (n + 1) (Nat.succ_le_succ (Nat.zero_le n)))
  simpa only [Real.norm_eq_abs, abs_abs,
    abs_of_nonneg (gap3 φ a b (n + 1))] using hbound

theorem gap9 (φ : ℕ → ℝ → ℝ) (a b : ℝ)
    (hmono : ∀ n : ℕ, 1 ≤ n →
      (MonotoneOn (φ n) (Set.Icc a b) ∨
        AntitoneOn (φ n) (Set.Icc a b)))
    (ha : Summable (fun n : ℕ => |φ (n + 1) a|))
    (hb : Summable (fun n : ℕ => |φ (n + 1) b|)) :
    SeriesUniformlyConvergesOn
      (fun n x => φ (n + 1) x)
      (Set.Icc a b)
      (fun x => ∑' n : ℕ, φ (n + 1) x) := by
  intro ε hε
  let M : ℕ → ℝ := fun k => majorant φ a b (k + 1)
  have hM : Summable M := by
    simpa only [M] using gap6 φ a b ha hb
  have hMtend :
      Tendsto (fun m => ∑ k ∈ Finset.range m, M k) Filter.atTop
        (nhds (∑' k, M k)) :=
    hM.hasSum.tendsto_sum_nat
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hMtend) ε hε
  refine ⟨N, ?_⟩
  intro n hn x hx
  let f : ℕ → ℝ := fun k => φ (k + 1) x
  let m : ℕ := n + 1
  have habs : Summable (fun k : ℕ => |φ (k + 1) x|) :=
    gap8 φ a b x hx hmono ha hb
  have hf : Summable f := by
    apply Summable.of_norm
    simpa only [f, Real.norm_eq_abs] using habs
  have hnormTail : Summable (fun k : ℕ => ‖f (m + k)‖) := by
    simpa only [Function.comp_apply, f, Real.norm_eq_abs] using
      habs.comp_injective (fun i j hij => Nat.add_left_cancel hij)
  have hMTail : Summable (fun k : ℕ => M (m + k)) := by
    simpa only [Function.comp_apply] using
      hM.comp_injective (fun i j hij => Nat.add_left_cancel hij)
  have htailOrder :
      (∑' k : ℕ, ‖f (m + k)‖) ≤ ∑' k : ℕ, M (m + k) := by
    apply sub_nonneg.mp
    have hdiff :
        HasSum (fun k : ℕ => M (m + k) - ‖f (m + k)‖)
          ((∑' k : ℕ, M (m + k)) -
            ∑' k : ℕ, ‖f (m + k)‖) :=
      hMTail.hasSum.sub hnormTail.hasSum
    rw [← hdiff.tsum_eq]
    apply tsum_nonneg
    intro k
    apply sub_nonneg.mpr
    have hk := gap7 φ a b x (m + k + 1) hx
      (hmono (m + k + 1)
        (Nat.succ_le_succ (Nat.zero_le (m + k))))
    simpa only [f, M, Real.norm_eq_abs] using hk
  have htail :
      |∑' k : ℕ, f (m + k)| ≤ ∑' k : ℕ, M (m + k) := by
    calc
      |∑' k : ℕ, f (m + k)| = ‖∑' k : ℕ, f (m + k)‖ := by
        rw [Real.norm_eq_abs]
      _ ≤ ∑' k : ℕ, ‖f (m + k)‖ :=
        norm_tsum_le_tsum_norm hnormTail
      _ ≤ ∑' k : ℕ, M (m + k) := htailOrder
  have hsplitf := hf.sum_add_tsum_nat_add m
  have hsplitM := hM.sum_add_tsum_nat_add m
  have hsplitf' :
      (∑ k ∈ Finset.range m, f k) + ∑' k, f (m + k) = ∑' k, f k := by
    simpa only [Nat.add_comm] using hsplitf
  have hsplitM' :
      (∑ k ∈ Finset.range m, M k) + ∑' k, M (m + k) = ∑' k, M k := by
    simpa only [Nat.add_comm] using hsplitM
  have herrf :
      (∑ k ∈ Finset.range m, f k) - ∑' k, f k =
        -(∑' k, f (m + k)) := by
    rw [← hsplitf']
    ring
  have herrM :
      (∑ k ∈ Finset.range m, M k) - ∑' k, M k =
        -(∑' k, M (m + k)) := by
    rw [← hsplitM']
    ring
  have htailMnonneg : 0 ≤ ∑' k : ℕ, M (m + k) := by
    apply tsum_nonneg
    intro k
    exact gap3 φ a b (m + k + 1)
  have hbound :
      |(∑ k ∈ Finset.range m, f k) - ∑' k, f k| ≤
        |(∑ k ∈ Finset.range m, M k) - ∑' k, M k| := by
    calc
      |(∑ k ∈ Finset.range m, f k) - ∑' k, f k| =
          |∑' k, f (m + k)| := by rw [herrf, abs_neg]
      _ ≤ ∑' k, M (m + k) := htail
      _ = |(∑ k ∈ Finset.range m, M k) - ∑' k, M k| := by
        rw [herrM, abs_neg, abs_of_nonneg htailMnonneg]
  have hmge : N ≤ m := by
    exact hn.trans (Nat.le_succ n)
  have hMclose :
      |(∑ k ∈ Finset.range m, M k) - ∑' k, M k| < ε := by
    simpa only [Real.dist_eq] using hN m hmge
  have hfinal :
      |(∑ k ∈ Finset.range m, f k) - ∑' k, f k| < ε :=
    hbound.trans_lt hMclose
  simpa only [f, m] using hfinal

theorem gap10 (φ : ℕ → ℝ → ℝ) (a b x : ℝ)
    (hmono : ∀ n : ℕ, 1 ≤ n →
      (MonotoneOn (φ n) (Set.Icc a b) ∨
        AntitoneOn (φ n) (Set.Icc a b)))
    (ha : Summable (fun n : ℕ => |φ (n + 1) a|))
    (hb : Summable (fun n : ℕ => |φ (n + 1) b|))
    (hx : x ∈ Set.Icc a b) :
    Summable (fun n : ℕ => |φ (n + 1) x|) ∧
    SeriesUniformlyConvergesOn
      (fun n x => φ (n + 1) x)
      (Set.Icc a b)
      (fun y => ∑' n : ℕ, φ (n + 1) y) := by
  constructor
  · exact gap8 φ a b x hx hmono ha hb
  · exact gap9 φ a b hmono ha hb

end

end ProofGap.Exercise2787
