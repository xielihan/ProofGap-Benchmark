import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise2625

noncomputable section

open Filter
open scoped BigOperators

def dyadic (m : ℕ) : ℝ := Real.rpow 2 (-(m : ℝ))

def ValidCutoff (a : ℕ → ℝ) (p : ℕ → ℕ) : Prop :=
  (∀ m, 1 ≤ p m) ∧ Monotone p ∧
    ∀ m n, 1 ≤ n → (dyadic m ≤ a n ↔ n ≤ p m)

def blockSum (a : ℕ → ℝ) (p : ℕ → ℕ) (m : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc (p (m - 1) + 1) (p m), a n

def blockCount (p : ℕ → ℕ) (m : ℕ) : ℝ :=
  (p m - p (m - 1) : ℕ)

def lowerBlock (p : ℕ → ℕ) (m : ℕ) : ℝ :=
  blockCount p m * dyadic m

def upperBlock (p : ℕ → ℕ) (m : ℕ) : ℝ :=
  blockCount p m * dyadic (m - 1)

def weighted (p : ℕ → ℕ) (m : ℕ) : ℝ :=
  p m * dyadic m

def differenceWeighted (p : ℕ → ℕ) (m : ℕ) : ℝ :=
  blockCount p m * dyadic (m - 1)

def blockPartial (a : ℕ → ℝ) (p : ℕ → ℕ) (N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N, blockSum a p m

def lowerPartial (p : ℕ → ℕ) (N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N, lowerBlock p m

def differencePartial (p : ℕ → ℕ) (N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N, differenceWeighted p m

def weightedPartial (p : ℕ → ℕ) (N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 (N - 1), weighted p m

def originalConverges (a : ℕ → ℝ) : Prop :=
  Summable (fun n : ℕ => a (n + 1))

def differenceConverges (p : ℕ → ℕ) : Prop :=
  Summable (fun m : ℕ => differenceWeighted p (m + 1))

def weightedConverges (p : ℕ → ℕ) : Prop :=
  Summable (weighted p)

private theorem dyadic_pos_aux (m : ℕ) : 0 < dyadic m := by
  unfold dyadic
  exact Real.rpow_pos_of_pos (by norm_num) _

private theorem dyadic_pred_eq_aux (m : ℕ) (hm : 1 ≤ m) :
    dyadic (m - 1) = 2 * dyadic m := by
  unfold dyadic
  have he : -((m - 1 : ℕ) : ℝ) = -(m : ℝ) + 1 := by
    rw [Nat.cast_sub hm]
    ring
  rw [he]
  calc
    Real.rpow 2 (-(m : ℝ) + 1) =
        Real.rpow 2 (-(m : ℝ)) * Real.rpow 2 1 := by
      exact Real.rpow_add (by norm_num : (0 : ℝ) < 2) _ _
    _ = 2 * Real.rpow 2 (-(m : ℝ)) := by
      norm_num
      ring

private theorem dyadic_eq_inv_pow_aux (m : ℕ) :
    dyadic m = ((2 : ℝ)⁻¹) ^ m := by
  induction m with
  | zero => simp [dyadic]
  | succ m ih =>
      have hrec := dyadic_pred_eq_aux (m + 1) (by omega)
      simp only [Nat.add_sub_cancel] at hrec
      rw [pow_succ, ← ih]
      norm_num
      linarith

private theorem finite_sum_le_tsum_aux {f : ℕ → ℝ} (s : Finset ℕ)
    (hf : ∀ n, 0 ≤ f n) (hs : Summable f) :
    ∑ n ∈ s, f n ≤ ∑' n : ℕ, f n := by
  exact hs.sum_le_tsum s (fun n _ => hf n)

theorem gap1 (a : ℕ → ℝ) (p : ℕ → ℕ) (hcut : ValidCutoff a p)
    (m : ℕ) (hm : 1 ≤ m) (hstep : p (m - 1) < p m) :
    dyadic m ≤ a (p (m - 1) + 1) := by
  have hn : 1 ≤ p (m - 1) + 1 := by omega
  apply (hcut.2.2 m (p (m - 1) + 1) hn).2
  omega

theorem gap2 (a : ℕ → ℝ) (p : ℕ → ℕ) (hcut : ValidCutoff a p)
    (m : ℕ) (hm : 1 ≤ m) :
    a (p (m - 1) + 1) < dyadic (m - 1) := by
  have hn : 1 ≤ p (m - 1) + 1 := by omega
  apply lt_of_not_ge
  intro h
  have hle := (hcut.2.2 (m - 1) (p (m - 1) + 1) hn).1 h
  omega

theorem gap3 (m : ℕ) (hm : 1 ≤ m) :
    dyadic m < dyadic (m - 1) := by
  rw [dyadic_pred_eq_aux m hm]
  have hpos := dyadic_pos_aux m
  linarith

theorem gap4 (a : ℕ → ℝ) (p : ℕ → ℕ) (hcut : ValidCutoff a p)
    (m : ℕ) (hm : 1 ≤ m) (hstep : p (m - 1) + 2 ≤ p m) :
    dyadic m ≤ a (p (m - 1) + 2) := by
  have hn : 1 ≤ p (m - 1) + 2 := by omega
  apply (hcut.2.2 m (p (m - 1) + 2) hn).2
  omega

theorem gap5 (a : ℕ → ℝ) (p : ℕ → ℕ) (hcut : ValidCutoff a p)
    (m : ℕ) (hm : 1 ≤ m) :
    a (p (m - 1) + 2) < dyadic (m - 1) := by
  have hn : 1 ≤ p (m - 1) + 2 := by omega
  apply lt_of_not_ge
  intro h
  have hle := (hcut.2.2 (m - 1) (p (m - 1) + 2) hn).1 h
  omega

theorem gap6 (m : ℕ) (hm : 1 ≤ m) :
    dyadic m < dyadic (m - 1) := by
  exact gap3 m hm

theorem gap7 (a : ℕ → ℝ) (p : ℕ → ℕ) (hcut : ValidCutoff a p)
    (m : ℕ) :
    dyadic m ≤ a (p m) := by
  have hn : 1 ≤ p m := hcut.1 m
  exact (hcut.2.2 m (p m) hn).2 le_rfl

theorem gap8 (a : ℕ → ℝ) (p : ℕ → ℕ) (hcut : ValidCutoff a p)
    (m : ℕ) (hm : 1 ≤ m) (hstep : p (m - 1) < p m) :
    a (p m) < dyadic (m - 1) := by
  have hn : 1 ≤ p m := hcut.1 m
  apply lt_of_not_ge
  intro h
  have hle := (hcut.2.2 (m - 1) (p m) hn).1 h
  omega

theorem gap9 (a : ℕ → ℝ) (p : ℕ → ℕ) (hcut : ValidCutoff a p)
    (m : ℕ) :
    a (p m + 1) < dyadic m := by
  have hn : 1 ≤ p m + 1 := by omega
  apply lt_of_not_ge
  intro h
  have hle := (hcut.2.2 m (p m + 1) hn).1 h
  omega

theorem gap10 (a : ℕ → ℝ) (p : ℕ → ℕ) (hcut : ValidCutoff a p)
    (m : ℕ) (hm : 1 ≤ m) :
    lowerBlock p m ≤ blockSum a p m := by
  have hcard : (Finset.Icc (p (m - 1) + 1) (p m)).card =
      p m - p (m - 1) := by
    simp [Nat.card_Icc]
  change ((p m - p (m - 1) : ℕ) : ℝ) * dyadic m ≤
    ∑ n ∈ Finset.Icc (p (m - 1) + 1) (p m), a n
  calc
    ((p m - p (m - 1) : ℕ) : ℝ) * dyadic m =
        ∑ _n ∈ Finset.Icc (p (m - 1) + 1) (p m), dyadic m := by
      simp [hcard]
    _ ≤ ∑ n ∈ Finset.Icc (p (m - 1) + 1) (p m), a n := by
      apply Finset.sum_le_sum
      intro n hn
      have hn' := Finset.mem_Icc.mp hn
      exact (hcut.2.2 m n (by omega)).2 hn'.2

theorem gap11 (a : ℕ → ℝ) (p : ℕ → ℕ) (hcut : ValidCutoff a p)
    (m : ℕ) (hm : 1 ≤ m) :
    blockSum a p m ≤ upperBlock p m := by
  have hcard : (Finset.Icc (p (m - 1) + 1) (p m)).card =
      p m - p (m - 1) := by
    simp [Nat.card_Icc]
  change (∑ n ∈ Finset.Icc (p (m - 1) + 1) (p m), a n) ≤
    ((p m - p (m - 1) : ℕ) : ℝ) * dyadic (m - 1)
  calc
    (∑ n ∈ Finset.Icc (p (m - 1) + 1) (p m), a n) ≤
        ∑ _n ∈ Finset.Icc (p (m - 1) + 1) (p m), dyadic (m - 1) := by
      apply Finset.sum_le_sum
      intro n hn
      have hn' := Finset.mem_Icc.mp hn
      apply le_of_lt
      apply lt_of_not_ge
      intro h
      have hle := (hcut.2.2 (m - 1) n (by omega)).1 h
      omega
    _ = ((p m - p (m - 1) : ℕ) : ℝ) * dyadic (m - 1) := by
      simp [hcard]

theorem gap12 (a : ℕ → ℝ) (p : ℕ → ℕ) (hcut : ValidCutoff a p)
    (N : ℕ) :
    lowerPartial p N ≤ blockPartial a p N := by
  change (∑ m ∈ Finset.Icc 1 N, lowerBlock p m) ≤
    ∑ m ∈ Finset.Icc 1 N, blockSum a p m
  apply Finset.sum_le_sum
  intro m hm
  exact gap10 a p hcut m (Finset.mem_Icc.mp hm).1

theorem gap13 (a : ℕ → ℝ) (p : ℕ → ℕ) (hcut : ValidCutoff a p)
    (N : ℕ) :
    blockPartial a p N ≤ differencePartial p N := by
  change (∑ m ∈ Finset.Icc 1 N, blockSum a p m) ≤
    ∑ m ∈ Finset.Icc 1 N, differenceWeighted p m
  apply Finset.sum_le_sum
  intro m hm
  simpa [upperBlock, differenceWeighted] using
    gap11 a p hcut m (Finset.mem_Icc.mp hm).1

theorem gap14 (a : ℕ → ℝ) (p : ℕ → ℕ) (hcut : ValidCutoff a p)
    (hpos : ∀ n ≥ 1, 0 < a n) (hzero : Tendsto a atTop (nhds 0)) :
    originalConverges a ↔ differenceConverges p := by
  let q : ℕ → ℝ := fun m => blockSum a p (m + 1)
  have ha_nonneg : ∀ n, 0 ≤ a (n + 1) := by
    intro n
    exact le_of_lt (hpos (n + 1) (by omega))
  have hq_nonneg : ∀ m, 0 ≤ q m := by
    intro m
    change 0 ≤ ∑ n ∈ Finset.Icc (p ((m + 1) - 1) + 1) (p (m + 1)), a n
    apply Finset.sum_nonneg
    intro n hn
    have hn' := Finset.mem_Icc.mp hn
    exact le_of_lt (hpos n (by omega))
  have hshift : ∀ K, (∑ n ∈ Finset.Icc 1 K, a n) =
      ∑ n ∈ Finset.range K, a (n + 1) := by
    intro K
    classical
    have hs : Finset.Icc 1 K =
        (Finset.range K).image (fun n => n + 1) := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
      constructor
      · intro hn
        refine ⟨n - 1, by omega, by omega⟩
      · rintro ⟨k, hk, rfl⟩
        omega
    rw [hs, Finset.sum_image]
    intro x hx y hy hxy
    exact Nat.add_right_cancel hxy
  have hblocks : ∀ N, (∑ m ∈ Finset.range N, q m) =
      ∑ n ∈ Finset.Icc (p 0 + 1) (p N), a n := by
    intro N
    induction N with
    | zero => simp [q, blockSum]
    | succ N ih =>
        rw [Finset.sum_range_succ, ih]
        change (∑ n ∈ Finset.Icc (p 0 + 1) (p N), a n) +
            (∑ n ∈ Finset.Icc (p N + 1) (p (N + 1)), a n) =
          ∑ n ∈ Finset.Icc (p 0 + 1) (p (N + 1)), a n
        have hd : Disjoint (Finset.Icc (p 0 + 1) (p N))
            (Finset.Icc (p N + 1) (p (N + 1))) := by
          rw [Finset.disjoint_left]
          intro x hx hy
          have hx' := Finset.mem_Icc.mp hx
          have hy' := Finset.mem_Icc.mp hy
          omega
        have hu : Finset.Icc (p 0 + 1) (p N) ∪
              Finset.Icc (p N + 1) (p (N + 1)) =
              Finset.Icc (p 0 + 1) (p (N + 1)) := by
          ext x
          simp only [Finset.mem_union, Finset.mem_Icc]
          have h0N : p 0 ≤ p N := hcut.2.1 (Nat.zero_le N)
          have hNN : p N ≤ p (N + 1) := hcut.2.1 (by omega)
          omega
        rw [← Finset.sum_union hd, hu]
  have hdy : Tendsto dyadic atTop (nhds 0) := by
    have hpw : Tendsto (fun n : ℕ => ((2 : ℝ)⁻¹) ^ n) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by norm_num)
    have hfun : dyadic = (fun n : ℕ => ((2 : ℝ)⁻¹) ^ n) := by
      funext n
      exact dyadic_eq_inv_pow_aux n
    rw [hfun]
    exact hpw
  have hp_cofinal : ∀ K, ∃ M, K ≤ p M := by
    intro K
    by_cases hK : K = 0
    · exact ⟨0, by omega⟩
    have hK1 : 1 ≤ K := by omega
    have hev : ∀ᶠ m in atTop, dyadic m < a K :=
      (tendsto_order.1 hdy).2 _ (hpos K hK1)
    rcases eventually_atTop.1 hev with ⟨M, hM⟩
    exact ⟨M, (hcut.2.2 M K hK1).1 (le_of_lt (hM M le_rfl))⟩
  have horig_iff_q : originalConverges a ↔ Summable q := by
    constructor
    · intro horig
      unfold originalConverges at horig
      refine summable_of_sum_le
        (c := ∑' n : ℕ, a (n + 1)) hq_nonneg ?_
      intro s
      let B : ℕ := ∑ i ∈ s, (i + 1)
      have hsB : s ⊆ Finset.range B := by
        intro i hi
        simp only [Finset.mem_range]
        have hiB : i + 1 ≤ B := by
          dsimp [B]
          exact Finset.single_le_sum (fun j hj => Nat.zero_le (j + 1)) hi
        omega
      calc
        (∑ i ∈ s, q i) ≤ ∑ i ∈ Finset.range B, q i := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hsB
          intro i hi hni
          exact hq_nonneg i
        _ = ∑ n ∈ Finset.Icc (p 0 + 1) (p B), a n := hblocks B
        _ ≤ ∑ n ∈ Finset.Icc 1 (p B), a n := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro n hn
            simp only [Finset.mem_Icc] at hn ⊢
            omega
          · intro n hn hni
            exact le_of_lt (hpos n (Finset.mem_Icc.mp hn).1)
        _ = ∑ n ∈ Finset.range (p B), a (n + 1) := hshift (p B)
        _ ≤ ∑' n : ℕ, a (n + 1) :=
          finite_sum_le_tsum_aux (Finset.range (p B)) ha_nonneg horig
    · intro hq
      unfold originalConverges
      refine summable_of_sum_le
        (c := (∑ n ∈ Finset.Icc 1 (p 0), a n) + ∑' m : ℕ, q m)
        ha_nonneg ?_
      intro s
      let B : ℕ := ∑ i ∈ s, (i + 1)
      have hsB : s ⊆ Finset.range B := by
        intro i hi
        simp only [Finset.mem_range]
        have hiB : i + 1 ≤ B := by
          dsimp [B]
          exact Finset.single_le_sum (fun j hj => Nat.zero_le (j + 1)) hi
        omega
      rcases hp_cofinal B with ⟨M, hBM⟩
      have h0M : p 0 ≤ p M := hcut.2.1 (Nat.zero_le M)
      have hunion : Finset.Icc 1 (p 0) ∪
            Finset.Icc (p 0 + 1) (p M) = Finset.Icc 1 (p M) := by
        ext n
        simp only [Finset.mem_union, Finset.mem_Icc]
        omega
      have hdisj : Disjoint (Finset.Icc 1 (p 0))
          (Finset.Icc (p 0 + 1) (p M)) := by
        rw [Finset.disjoint_left]
        intro n hn hn'
        have hn1 := Finset.mem_Icc.mp hn
        have hn2 := Finset.mem_Icc.mp hn'
        omega
      calc
        (∑ i ∈ s, a (i + 1)) ≤ ∑ i ∈ Finset.range B, a (i + 1) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg hsB
          intro i hi hni
          exact ha_nonneg i
        _ = ∑ n ∈ Finset.Icc 1 B, a n := (hshift B).symm
        _ ≤ ∑ n ∈ Finset.Icc 1 (p M), a n := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro n hn
            simp only [Finset.mem_Icc] at hn ⊢
            omega
          · intro n hn hni
            exact le_of_lt (hpos n (Finset.mem_Icc.mp hn).1)
        _ = (∑ n ∈ Finset.Icc 1 (p 0), a n) +
            ∑ n ∈ Finset.Icc (p 0 + 1) (p M), a n := by
          rw [← Finset.sum_union hdisj, hunion]
        _ = (∑ n ∈ Finset.Icc 1 (p 0), a n) +
            ∑ m ∈ Finset.range M, q m := by
          rw [hblocks M]
        _ ≤ (∑ n ∈ Finset.Icc 1 (p 0), a n) + ∑' m : ℕ, q m := by
          have htail : (∑ m ∈ Finset.range M, q m) ≤ ∑' m : ℕ, q m :=
            finite_sum_le_tsum_aux (Finset.range M) hq_nonneg hq
          simpa [add_comm] using
            (add_le_add_left htail (∑ n ∈ Finset.Icc 1 (p 0), a n))
  have hd_nonneg : ∀ m, 0 ≤ differenceWeighted p (m + 1) := by
    intro m
    change 0 ≤ ((p (m + 1) - p m : ℕ) : ℝ) * dyadic m
    exact mul_nonneg (Nat.cast_nonneg _) (le_of_lt (dyadic_pos_aux m))
  have hq_le_d : ∀ m, q m ≤ differenceWeighted p (m + 1) := by
    intro m
    simpa [q, upperBlock, differenceWeighted, blockCount] using
      gap11 a p hcut (m + 1) (by omega)
  have hd_le_q : ∀ m, differenceWeighted p (m + 1) ≤ 2 * q m := by
    intro m
    have hd := dyadic_pred_eq_aux (m + 1) (by omega)
    simp only [Nat.add_sub_cancel] at hd
    have hl : ((p (m + 1) - p m : ℕ) : ℝ) * dyadic (m + 1) ≤ q m := by
      simpa [q, lowerBlock, blockCount] using
        gap10 a p hcut (m + 1) (by omega)
    change ((p (m + 1) - p m : ℕ) : ℝ) * dyadic m ≤ 2 * q m
    calc
      ((p (m + 1) - p m : ℕ) : ℝ) * dyadic m =
          2 * (((p (m + 1) - p m : ℕ) : ℝ) * dyadic (m + 1)) := by
        rw [hd]
        ring
      _ ≤ 2 * q m := mul_le_mul_of_nonneg_left hl (by norm_num)
  have hq_iff_diff : Summable q ↔ differenceConverges p := by
    constructor
    · intro hqsum
      unfold differenceConverges
      exact Summable.of_nonneg_of_le hd_nonneg hd_le_q (hqsum.mul_left 2)
    · intro hdiff
      unfold differenceConverges at hdiff
      exact Summable.of_nonneg_of_le hq_nonneg hq_le_d hdiff
  exact horig_iff_q.trans hq_iff_diff

theorem gap15 (p : ℕ → ℕ) (hmono : Monotone p) :
    weightedConverges p → differenceConverges p := by
  intro hweighted
  unfold weightedConverges at hweighted
  have hshifted : Summable (fun m : ℕ => weighted p (m + 1)) :=
    hweighted.comp_injective Nat.succ_injective
  have hmajor : Summable (fun m : ℕ => 2 * weighted p (m + 1)) :=
    hshifted.mul_left 2
  unfold differenceConverges
  refine Summable.of_nonneg_of_le ?_ ?_ hmajor
  · intro m
    change 0 ≤ ((p (m + 1) - p m : ℕ) : ℝ) * dyadic m
    exact mul_nonneg (Nat.cast_nonneg _) (le_of_lt (dyadic_pos_aux m))
  · intro m
    have hsub : p (m + 1) - p m ≤ p (m + 1) := Nat.sub_le _ _
    have hd := dyadic_pred_eq_aux (m + 1) (by omega)
    simp only [Nat.add_sub_cancel] at hd
    change ((p (m + 1) - p m : ℕ) : ℝ) * dyadic m ≤
      2 * weighted p (m + 1)
    calc
      ((p (m + 1) - p m : ℕ) : ℝ) * dyadic m ≤
          (p (m + 1) : ℝ) * dyadic m := by
        apply mul_le_mul_of_nonneg_right
        · exact Nat.cast_le.2 hsub
        · exact le_of_lt (dyadic_pos_aux m)
      _ = 2 * weighted p (m + 1) := by
        unfold weighted
        rw [hd]
        ring

theorem gap16 (p : ℕ → ℕ) (hmono : Monotone p) (m : ℕ) :
    0 ≤ blockCount p m := by
  unfold blockCount
  exact Nat.cast_nonneg _

theorem gap17 (p : ℕ → ℕ) (hmono : Monotone p)
    (hconv : differenceConverges p)
    (A : ℝ) (hsum : ∑' m : ℕ, differenceWeighted p (m + 1) = A)
    (N : ℕ) :
    differencePartial p N ≤ A := by
  have hnonneg : ∀ m, 0 ≤ differenceWeighted p (m + 1) := by
    intro m
    change 0 ≤ ((p (m + 1) - p m : ℕ) : ℝ) * dyadic m
    exact mul_nonneg (Nat.cast_nonneg _) (le_of_lt (dyadic_pos_aux m))
  have hshift : differencePartial p N =
      ∑ m ∈ Finset.range N, differenceWeighted p (m + 1) := by
    change (∑ m ∈ Finset.Icc 1 N, differenceWeighted p m) =
      ∑ m ∈ Finset.range N, differenceWeighted p (m + 1)
    classical
    have hs : Finset.Icc 1 N =
        (Finset.range N).image (fun m => m + 1) := by
      ext m
      simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
      constructor
      · intro hm
        refine ⟨m - 1, by omega, by omega⟩
      · rintro ⟨k, hk, rfl⟩
        omega
    rw [hs, Finset.sum_image]
    intro x hx y hy hxy
    exact Nat.add_right_cancel hxy
  rw [hshift, ← hsum]
  exact finite_sum_le_tsum_aux (Finset.range N) hnonneg hconv

theorem gap18 (p : ℕ → ℕ) (hmono : Monotone p) (N : ℕ) :
    differencePartial p N =
      (∑ m ∈ Finset.Icc 1 N, (p m : ℝ) * dyadic (m - 1)) -
        ∑ l ∈ Finset.range N, (p l : ℝ) * dyadic l := by
  change (∑ m ∈ Finset.Icc 1 N,
      ((p m - p (m - 1) : ℕ) : ℝ) * dyadic (m - 1)) = _
  have hterm : ∀ m,
      (((p m - p (m - 1) : ℕ) : ℝ) * dyadic (m - 1)) =
        (p m : ℝ) * dyadic (m - 1) -
          (p (m - 1) : ℝ) * dyadic (m - 1) := by
    intro m
    rw [Nat.cast_sub (hmono (Nat.sub_le m 1))]
    ring
  calc
    (∑ m ∈ Finset.Icc 1 N,
        ((p m - p (m - 1) : ℕ) : ℝ) * dyadic (m - 1)) =
        ∑ m ∈ Finset.Icc 1 N,
          ((p m : ℝ) * dyadic (m - 1) -
            (p (m - 1) : ℝ) * dyadic (m - 1)) := by
      apply Finset.sum_congr rfl
      intro m hm
      exact hterm m
    _ = (∑ m ∈ Finset.Icc 1 N, (p m : ℝ) * dyadic (m - 1)) -
          ∑ m ∈ Finset.Icc 1 N,
            (p (m - 1) : ℝ) * dyadic (m - 1) := by
      rw [Finset.sum_sub_distrib]
    _ = (∑ m ∈ Finset.Icc 1 N, (p m : ℝ) * dyadic (m - 1)) -
          ∑ l ∈ Finset.range N, (p l : ℝ) * dyadic l := by
      congr 1
      classical
      have hs : Finset.Icc 1 N =
          (Finset.range N).image (fun l => l + 1) := by
        ext m
        simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
        constructor
        · intro hm
          refine ⟨m - 1, by omega, by omega⟩
        · rintro ⟨l, hl, rfl⟩
          omega
      rw [hs, Finset.sum_image]
      · simp
      · intro x hx y hy hxy
        exact Nat.add_right_cancel hxy

theorem gap19 (p : ℕ → ℕ) (hmono : Monotone p)
    (hconv : differenceConverges p)
    (A : ℝ) (hsum : ∑' m : ℕ, differenceWeighted p (m + 1) = A)
    (N : ℕ) :
    (∑ m ∈ Finset.Icc 1 N, (p m : ℝ) * dyadic (m - 1)) -
      ∑ l ∈ Finset.range N, (p l : ℝ) * dyadic l ≤ A := by
  rw [← gap18 p hmono N]
  exact gap17 p hmono hconv A hsum N

theorem gap20 (p : ℕ → ℕ) (hmono : Monotone p)
    (hconv : differenceConverges p)
    (A : ℝ) (hsum : ∑' m : ℕ, differenceWeighted p (m + 1) = A)
    (N : ℕ) (hN : 1 ≤ N) :
    weightedPartial p N + dyadic (N - 1) * p N - p 0 ≤ A := by
  have hprefix : (∑ m ∈ Finset.Icc 1 (N - 1),
      (p m : ℝ) * dyadic (m - 1)) = 2 * weightedPartial p N := by
    change (∑ m ∈ Finset.Icc 1 (N - 1),
      (p m : ℝ) * dyadic (m - 1)) =
      2 * ∑ m ∈ Finset.Icc 1 (N - 1), weighted p m
    calc
      (∑ m ∈ Finset.Icc 1 (N - 1),
          (p m : ℝ) * dyadic (m - 1)) =
          ∑ m ∈ Finset.Icc 1 (N - 1),
            2 * weighted p m := by
        apply Finset.sum_congr rfl
        intro m hm
        have hm1 := (Finset.mem_Icc.mp hm).1
        unfold weighted
        rw [dyadic_pred_eq_aux m hm1]
        ring
      _ = 2 * ∑ m ∈ Finset.Icc 1 (N - 1), weighted p m := by
        rw [Finset.mul_sum]
  have hsplit : Finset.Icc 1 N =
      insert N (Finset.Icc 1 (N - 1)) := by
    ext m
    simp
    omega
  have hNnot : N ∉ Finset.Icc 1 (N - 1) := by
    simp
    omega
  have hfirst : (∑ m ∈ Finset.Icc 1 N,
      (p m : ℝ) * dyadic (m - 1)) =
      2 * weightedPartial p N + (p N : ℝ) * dyadic (N - 1) := by
    rw [hsplit, Finset.sum_insert hNnot, hprefix]
    ring
  have hrangeSet : Finset.range N =
      insert 0 (Finset.Icc 1 (N - 1)) := by
    ext m
    simp
    omega
  have hzeroNot : 0 ∉ Finset.Icc 1 (N - 1) := by simp
  have hrange : (∑ l ∈ Finset.range N,
      (p l : ℝ) * dyadic l) = (p 0 : ℝ) + weightedPartial p N := by
    rw [hrangeSet, Finset.sum_insert hzeroNot]
    simp [weightedPartial, weighted, dyadic]
  have hformula : differencePartial p N =
      weightedPartial p N + dyadic (N - 1) * (p N : ℝ) -
        (p 0 : ℝ) := by
    rw [gap18 p hmono N, hfirst, hrange]
    ring
  rw [← hformula]
  exact gap17 p hmono hconv A hsum N

theorem gap21 (p : ℕ → ℕ) (hmono : Monotone p) (N : ℕ) :
    weightedPartial p N ≤ (p 0 : ℝ) + differencePartial p N := by
  by_cases hN : N = 0
  · subst N
    simp [weightedPartial, differencePartial]
  have hprefix : (∑ m ∈ Finset.Icc 1 (N - 1),
      (p m : ℝ) * dyadic (m - 1)) = 2 * weightedPartial p N := by
    change (∑ m ∈ Finset.Icc 1 (N - 1),
      (p m : ℝ) * dyadic (m - 1)) =
      2 * ∑ m ∈ Finset.Icc 1 (N - 1), weighted p m
    calc
      (∑ m ∈ Finset.Icc 1 (N - 1),
          (p m : ℝ) * dyadic (m - 1)) =
          ∑ m ∈ Finset.Icc 1 (N - 1), 2 * weighted p m := by
        apply Finset.sum_congr rfl
        intro m hm
        have hm1 := (Finset.mem_Icc.mp hm).1
        unfold weighted
        rw [dyadic_pred_eq_aux m hm1]
        ring
      _ = 2 * ∑ m ∈ Finset.Icc 1 (N - 1), weighted p m := by
        rw [Finset.mul_sum]
  have hsplit : Finset.Icc 1 N =
      insert N (Finset.Icc 1 (N - 1)) := by
    ext m
    simp
    omega
  have hNnot : N ∉ Finset.Icc 1 (N - 1) := by
    simp
    omega
  have hfirst : (∑ m ∈ Finset.Icc 1 N,
      (p m : ℝ) * dyadic (m - 1)) =
      2 * weightedPartial p N + (p N : ℝ) * dyadic (N - 1) := by
    rw [hsplit, Finset.sum_insert hNnot, hprefix]
    ring
  have hrangeSet : Finset.range N =
      insert 0 (Finset.Icc 1 (N - 1)) := by
    ext m
    simp
    omega
  have hzeroNot : 0 ∉ Finset.Icc 1 (N - 1) := by simp
  have hrange : (∑ l ∈ Finset.range N,
      (p l : ℝ) * dyadic l) = (p 0 : ℝ) + weightedPartial p N := by
    rw [hrangeSet, Finset.sum_insert hzeroNot]
    simp [weightedPartial, weighted, dyadic]
  have hformula : differencePartial p N =
      weightedPartial p N + dyadic (N - 1) * (p N : ℝ) -
        (p 0 : ℝ) := by
    rw [gap18 p hmono N, hfirst, hrange]
    ring
  rw [hformula]
  have hnonneg : 0 ≤ dyadic (N - 1) * (p N : ℝ) :=
    mul_nonneg (le_of_lt (dyadic_pos_aux (N - 1))) (Nat.cast_nonneg _)
  linarith

theorem gap22 (p : ℕ → ℕ) (hmono : Monotone p)
    (hconv : differenceConverges p)
    (A : ℝ) (hsum : ∑' m : ℕ, differenceWeighted p (m + 1) = A)
    (N : ℕ) :
    (p 0 : ℝ) + differencePartial p N ≤ p 0 + A := by
  have h := gap17 p hmono hconv A hsum N
  linarith

theorem gap23 (p : ℕ → ℕ) (hmono : Monotone p)
    (hconv : differenceConverges p)
    (A : ℝ) (hsum : ∑' m : ℕ, differenceWeighted p (m + 1) = A)
    (N : ℕ) :
    weightedPartial p N ≤ p 0 + A := by
  exact (gap21 p hmono N).trans (gap22 p hmono hconv A hsum N)

theorem gap24 (p : ℕ → ℕ) :
    Monotone (weightedPartial p) := by
  intro M N hMN
  change (∑ m ∈ Finset.Icc 1 (M - 1), weighted p m) ≤
    ∑ m ∈ Finset.Icc 1 (N - 1), weighted p m
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro m hm
    simp only [Finset.mem_Icc] at hm ⊢
    omega
  · intro m hm hnot
    unfold weighted
    exact mul_nonneg (Nat.cast_nonneg _) (le_of_lt (dyadic_pos_aux m))

theorem gap25 (p : ℕ → ℕ) (hmono : Monotone p)
    (hconv : differenceConverges p)
    (A : ℝ) (hsum : ∑' m : ℕ, differenceWeighted p (m + 1) = A) :
    ∃ C : ℝ, ∀ N, weightedPartial p N ≤ C := by
  refine ⟨(p 0 : ℝ) + A, ?_⟩
  intro N
  exact gap23 p hmono hconv A hsum N

theorem gap26 (p : ℕ → ℕ) (hmono : Monotone p) :
    differenceConverges p → weightedConverges p := by
  intro hconv
  let A : ℝ := ∑' m : ℕ, differenceWeighted p (m + 1)
  have hsum : ∑' m : ℕ, differenceWeighted p (m + 1) = A := rfl
  rcases gap25 p hmono hconv A hsum with ⟨C, hC⟩
  have hnonneg : ∀ m, 0 ≤ weighted p m := by
    intro m
    unfold weighted
    exact mul_nonneg (Nat.cast_nonneg _) (le_of_lt (dyadic_pos_aux m))
  unfold weightedConverges
  refine summable_of_sum_le
    (c := (p 0 : ℝ) + C) hnonneg ?_
  intro s
  let B : ℕ := ∑ i ∈ s, (i + 1)
  have hsB : s ⊆ insert 0 (Finset.Icc 1 B) := by
    intro i hi
    have hiB : i + 1 ≤ B := by
      dsimp [B]
      exact Finset.single_le_sum (fun j hj => Nat.zero_le (j + 1)) hi
    simp only [Finset.mem_insert, Finset.mem_Icc]
    omega
  have hzeroNot : 0 ∉ Finset.Icc 1 B := by simp
  calc
    (∑ i ∈ s, weighted p i) ≤
        ∑ i ∈ insert 0 (Finset.Icc 1 B), weighted p i := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsB
      intro i hi hni
      exact hnonneg i
    _ = (p 0 : ℝ) + weightedPartial p (B + 1) := by
      rw [Finset.sum_insert hzeroNot]
      simp [weightedPartial, weighted, dyadic]
    _ ≤ (p 0 : ℝ) + C := by
      simpa [add_comm] using
        (add_le_add_left (hC (B + 1)) (p 0 : ℝ))

theorem gap27 (a : ℕ → ℝ) (p : ℕ → ℕ) (hcut : ValidCutoff a p)
    (hpos : ∀ n ≥ 1, 0 < a n) (hzero : Tendsto a atTop (nhds 0)) :
    originalConverges a ↔ weightedConverges p := by
  constructor
  · intro horig
    have hdiff := (gap14 a p hcut hpos hzero).1 horig
    exact gap26 p hcut.2.1 hdiff
  · intro hweighted
    have hdiff := gap15 p hcut.2.1 hweighted
    exact (gap14 a p hcut hpos hzero).2 hdiff

theorem gap28 (a : ℕ → ℝ) (p : ℕ → ℕ) (hcut : ValidCutoff a p)
    (hpos : ∀ n ≥ 1, 0 < a n) (hzero : Tendsto a atTop (nhds 0)) :
    originalConverges a ↔ weightedConverges p := by
  exact gap27 a p hcut hpos hzero

end

end ProofGap.Exercise2625
