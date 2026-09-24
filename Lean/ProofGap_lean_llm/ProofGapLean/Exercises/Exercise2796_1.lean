import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Order.Filter.AtTopBot.Defs

namespace ProofGap.Exercise2796_1

noncomputable section

open scoped BigOperators

def term (r : ℕ → ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  |x - r k| / (3 : ℝ) ^ k

def f (r : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑' n : ℕ, term r (n + 1) x

def SeriesUniformlyConvergesOn
    (u : ℕ → ℝ → ℝ) (s : Set ℝ) (g : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ s,
    |(∑ k ∈ Finset.range (n + 1), u k x) - g x| < ε

private theorem term_continuous (r : ℕ → ℝ) (k : ℕ) : Continuous (term r k) := by
  unfold term
  exact (continuous_id.sub continuous_const).abs.div_const ((3 : ℝ) ^ k)

theorem gap1 (r : ℕ → ℝ)
    (hr : ∀ k : ℕ, 1 ≤ k → r k ∈ Set.Icc (0 : ℝ) 1)
    (x : ℝ) (k : ℕ) (hx : x ∈ Set.Icc (0 : ℝ) 1) (hk : 1 ≤ k) :
    |(x - r k) / (3 : ℝ) ^ k| ≤ 1 / (3 : ℝ) ^ k := by
  have hrk := hr k hk
  have hdiff : |x - r k| ≤ (1 : ℝ) := by
    apply abs_le.2
    constructor <;> linarith [hx.1, hx.2, hrk.1, hrk.2]
  rw [abs_div, abs_pow, abs_of_nonneg (show (0 : ℝ) ≤ 3 by norm_num)]
  exact div_le_div_of_nonneg_right hdiff (pow_nonneg (by norm_num) k)

theorem gap2 :
    Summable (fun n : ℕ => 1 / (3 : ℝ) ^ (n + 1)) := by
  have h : Summable (fun n : ℕ => (1 / 3 : ℝ) ^ n) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  simpa [one_div, inv_pow, pow_succ, mul_comm] using
    h.mul_left (1 / 3 : ℝ)

theorem gap3 (r : ℕ → ℝ)
    (hr : ∀ k : ℕ, 1 ≤ k → r k ∈ Set.Icc (0 : ℝ) 1) :
    SeriesUniformlyConvergesOn
      (fun n x => term r (n + 1) x)
      (Set.Icc (0 : ℝ) 1)
      (f r) := by
  intro ε hε
  have hb : Summable (fun j : ℕ => 1 / (3 : ℝ) ^ (j + 1)) := gap2
  rcases (Metric.tendsto_atTop.1 hb.hasSum.tendsto_sum_nat ε hε) with
    ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn x hx
  have habound (j : ℕ) :
      ‖term r (j + 1) x‖ ≤ 1 / (3 : ℝ) ^ (j + 1) := by
    have hpoint := gap1 r hr x (j + 1) hx (by omega)
    rw [abs_div, abs_pow,
      abs_of_nonneg (show (0 : ℝ) ≤ 3 by norm_num)] at hpoint
    have hterm : 0 ≤ term r (j + 1) x := by
      unfold term
      exact div_nonneg (abs_nonneg _) (pow_nonneg (by norm_num) _)
    rw [Real.norm_eq_abs, abs_of_nonneg hterm]
    simpa [term] using hpoint
  have ha : Summable (fun j : ℕ => term r (j + 1) x) :=
    Summable.of_norm_bounded hb habound
  have hnorm : Summable (fun j : ℕ => ‖term r (j + 1) x‖) := by
    apply Summable.of_norm_bounded hb
    intro j
    simpa using habound j
  have hinj : Function.Injective (fun j : ℕ => j + (n + 1)) := by
    intro i j hij
    exact Nat.add_right_cancel hij
  have hbTail :
      Summable (fun j : ℕ => 1 / (3 : ℝ) ^ ((j + (n + 1)) + 1)) := by
    exact hb.comp_injective hinj
  have hnormTail :
      Summable (fun j : ℕ => ‖term r ((j + (n + 1)) + 1) x‖) := by
    exact hnorm.comp_injective hinj
  have htail :
      ‖∑' j : ℕ, term r ((j + (n + 1)) + 1) x‖ ≤
        ∑' j : ℕ, 1 / (3 : ℝ) ^ ((j + (n + 1)) + 1) := by
    calc
      ‖∑' j : ℕ, term r ((j + (n + 1)) + 1) x‖ ≤
          ∑' j : ℕ, ‖term r ((j + (n + 1)) + 1) x‖ :=
        norm_tsum_le_tsum_norm hnormTail
      _ ≤ ∑' j : ℕ, 1 / (3 : ℝ) ^ ((j + (n + 1)) + 1) :=
        hnormTail.tsum_le_tsum (fun j => habound (j + (n + 1))) hbTail
  have haSplit :
      (∑ j ∈ Finset.range (n + 1), term r (j + 1) x) +
          (∑' j : ℕ, term r ((j + (n + 1)) + 1) x) =
        ∑' j : ℕ, term r (j + 1) x := by
    simpa [Nat.add_assoc] using ha.sum_add_tsum_nat_add (n + 1)
  have hbSplit :
      (∑ j ∈ Finset.range (n + 1), 1 / (3 : ℝ) ^ (j + 1)) +
          (∑' j : ℕ, 1 / (3 : ℝ) ^ ((j + (n + 1)) + 1)) =
        ∑' j : ℕ, 1 / (3 : ℝ) ^ (j + 1) := by
    simpa [Nat.add_assoc] using hb.sum_add_tsum_nat_add (n + 1)
  have hbTailNonneg :
      0 ≤ ∑' j : ℕ, 1 / (3 : ℝ) ^ ((j + (n + 1)) + 1) :=
    tsum_nonneg (fun _ => div_nonneg (by norm_num) (pow_nonneg (by norm_num) _))
  have hbAbs :
      (∑' j : ℕ, 1 / (3 : ℝ) ^ ((j + (n + 1)) + 1)) =
        |(∑ j ∈ Finset.range (n + 1), 1 / (3 : ℝ) ^ (j + 1)) -
          ∑' j : ℕ, 1 / (3 : ℝ) ^ (j + 1)| := by
    rw [abs_of_nonpos]
    · linarith [hbSplit]
    · linarith [hbSplit, hbTailNonneg]
  have haDiff :
      (∑ j ∈ Finset.range (n + 1), term r (j + 1) x) -
          ∑' j : ℕ, term r (j + 1) x =
        -(∑' j : ℕ, term r ((j + (n + 1)) + 1) x) := by
    rw [← haSplit]
    ring
  change
    |(∑ j ∈ Finset.range (n + 1), term r (j + 1) x) -
      ∑' j : ℕ, term r (j + 1) x| < ε
  rw [haDiff, abs_neg, ← Real.norm_eq_abs]
  calc
    ‖∑' j : ℕ, term r ((j + (n + 1)) + 1) x‖ ≤
        ∑' j : ℕ, 1 / (3 : ℝ) ^ ((j + (n + 1)) + 1) := htail
    _ = |(∑ j ∈ Finset.range (n + 1), 1 / (3 : ℝ) ^ (j + 1)) -
          ∑' j : ℕ, 1 / (3 : ℝ) ^ (j + 1)| := hbAbs
    _ = dist
          (∑ j ∈ Finset.range (n + 1), 1 / (3 : ℝ) ^ (j + 1))
          (∑' j : ℕ, 1 / (3 : ℝ) ^ (j + 1)) := by
        rw [Real.dist_eq]
    _ < ε := hN (n + 1) (by omega)

theorem gap4 (r : ℕ → ℝ) (k : ℕ) :
    ContinuousOn (term r k) (Set.Icc (0 : ℝ) 1) := by
  exact (term_continuous r k).continuousOn

theorem gap5 (r : ℕ → ℝ)
    (hr : ∀ k : ℕ, 1 ≤ k → r k ∈ Set.Icc (0 : ℝ) 1) :
    ContinuousOn (f r) (Set.Icc (0 : ℝ) 1) := by
  have hu : TendstoUniformlyOn
      (fun n x => ∑ k ∈ Finset.range (n + 1), term r (k + 1) x)
      (f r) atTop (Set.Icc (0 : ℝ) 1) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    rcases gap3 r hr ε hε with ⟨N, hN⟩
    refine Filter.eventually_atTop.2 ⟨N, ?_⟩
    intro n hn x hx
    simpa [Real.dist_eq, abs_sub_comm] using hN n hn x hx
  refine hu.continuousOn ?_
  exact (Filter.Eventually.of_forall (fun n =>
    (continuous_finset_sum _ fun k _ =>
      term_continuous r (k + 1)).continuousOn)).frequently

theorem gap6 (r : ℕ → ℝ)
    (hr : ∀ k : ℕ, 1 ≤ k → r k ∈ Set.Icc (0 : ℝ) 1) :
    ContinuousOn (f r) (Set.Icc (0 : ℝ) 1) := by
  exact gap5 r hr

end

end ProofGap.Exercise2796_1
