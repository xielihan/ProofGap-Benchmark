import ProofGapLean.Prelude.Analysis
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods

open scoped BigOperators

namespace ProofGap.Exercise2599

noncomputable section

def numeratorProduct (a d : ℝ) (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range n, (a + (k : ℝ) * d)

def denominatorProduct (b d : ℝ) (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range n, (b + (k : ℝ) * d)

def term (a b d : ℝ) (n : ℕ) : ℝ :=
  numeratorProduct a d n / denominatorProduct b d n

def raabeRatio (a b d : ℝ) (n : ℕ) : ℝ :=
  term a b d n / term a b d (n + 1)

def explicitRatio (a b d : ℝ) (n : ℕ) : ℝ :=
  (b + (n : ℝ) * d) / (a + (n : ℝ) * d)

def raabeQuantity (a b d : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) * (raabeRatio a b d n - 1)

def explicitQuantity (a b d : ℝ) (n : ℕ) : ℝ :=
  (b - a) * (n : ℝ) / (a + (n : ℝ) * d)

private theorem not_summable_one_div_natCast :
    ¬ Summable (fun n : ℕ => 1 / (n : ℝ)) := by
  intro hh
  rcases hh with ⟨s, hs⟩
  let P : ℕ → ℝ := fun m =>
    Finset.sum (Finset.range m) (fun k => 1 / (k : ℝ))
  have hpartial : Tendsto P atTop (nhds s) := by
    simpa [P] using hs.tendsto_sum_nat
  obtain ⟨N0, hclose⟩ :=
    (Metric.tendsto_atTop.mp hpartial) (1 / 8 : ℝ) (by norm_num)
  let N : ℕ := max N0 1
  have hN0 : N0 ≤ N := by
    dsimp [N]
    exact le_max_left _ _
  have hNpos : 0 < N := by
    exact lt_of_lt_of_le Nat.zero_lt_one (by
      dsimp [N]
      exact le_max_right _ _)
  have hPN : dist (P N) s < (1 / 8 : ℝ) := hclose N hN0
  have hP2N : dist (P (N + N)) s < (1 / 8 : ℝ) :=
    hclose (N + N) (by omega)
  rw [Real.dist_eq] at hPN hP2N
  have hsmall : P (N + N) - P N < (1 / 4 : ℝ) := by
    rcases abs_lt.mp hPN with ⟨hPNlo, hPNhi⟩
    rcases abs_lt.mp hP2N with ⟨hP2Nlo, hP2Nhi⟩
    linarith
  have hblock : (1 / 2 : ℝ) ≤ P (N + N) - P N := by
    have hNreal : (0 : ℝ) < (N : ℝ) := by positivity
    have hconst :
        (1 / 2 : ℝ) =
          Finset.sum (Finset.range N)
            (fun _k => 1 / (2 * (N : ℝ))) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp [hNreal.ne'] <;> ring
    dsimp [P]
    rw [Finset.sum_range_add]
    simp only [add_sub_cancel_left]
    calc
      (1 / 2 : ℝ) =
          Finset.sum (Finset.range N)
            (fun _k => 1 / (2 * (N : ℝ))) := hconst
      _ ≤ Finset.sum (Finset.range N)
          (fun k => 1 / ((N + k : ℕ) : ℝ)) := by
        apply Finset.sum_le_sum
        intro k hk
        have hklt : k < N := Finset.mem_range.mp hk
        have hden_le :
            ((N + k : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by
          norm_cast <;> omega
        have hden : 0 < ((N + k : ℕ) : ℝ) := by positivity
        have htwo : 0 < 2 * (N : ℝ) := by positivity
        exact (div_le_div_iff₀ htwo hden).2 (by
          simpa using hden_le)
  linarith

theorem gap1
    (a b d : ℝ) (u : ℕ → ℝ)
    (ha : 0 < a) (hb : 0 < b) (hd : 0 < d)
    (hu : ∀ n, u n = term a b d n) :
    ∀ n, u n / u (n + 1) = explicitRatio a b d n := by
  intro n
  have hnum : 0 < numeratorProduct a d n := by
    unfold numeratorProduct
    apply Finset.prod_pos
    intro k hk
    positivity
  have hden : 0 < denominatorProduct b d n := by
    unfold denominatorProduct
    apply Finset.prod_pos
    intro k hk
    positivity
  have han : 0 < a + (n : ℝ) * d := by positivity
  have hbn : 0 < b + (n : ℝ) * d := by positivity
  have hnum_succ :
      numeratorProduct a d (n + 1) =
        numeratorProduct a d n * (a + (n : ℝ) * d) := by
    simp [numeratorProduct, Finset.prod_range_succ]
  have hden_succ :
      denominatorProduct b d (n + 1) =
        denominatorProduct b d n * (b + (n : ℝ) * d) := by
    simp [denominatorProduct, Finset.prod_range_succ]
  rw [hu n, hu (n + 1)]
  simp only [term, explicitRatio, hnum_succ, hden_succ]
  field_simp [hnum.ne', hden.ne', han.ne', hbn.ne'] <;> ring

theorem gap2
    (a b d : ℝ)
    (hratio : ∀ n, raabeRatio a b d n = explicitRatio a b d n) :
    ∀ n, raabeQuantity a b d n =
      (n : ℝ) * (explicitRatio a b d n - 1) := by
  intro n
  simp [raabeQuantity, hratio n]

theorem gap3
    (a b d : ℝ) (ha : 0 < a) (hd : 0 < d) :
    ∀ n : ℕ, (n : ℝ) * (explicitRatio a b d n - 1) =
      explicitQuantity a b d n := by
  intro n
  have hden : a + (n : ℝ) * d ≠ 0 := by positivity
  unfold explicitRatio explicitQuantity
  field_simp [hden]
  ring

theorem gap4
    (a b d : ℝ) (ha : 0 < a) (hd : 0 < d) :
    Tendsto (explicitQuantity a b d) atTop (nhds ((b - a) / d)) := by
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ)⁻¹)) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hlim :
      Tendsto
        (fun n : ℕ => (b - a) / (a * ((n : ℝ)⁻¹) + d))
        atTop (nhds ((b - a) / d)) := by
    simpa using
      (tendsto_const_nhds.div
        ((tendsto_const_nhds.mul hinv).add tendsto_const_nhds)
        (by simpa using hd.ne'))
  refine hlim.congr' (Filter.eventually_atTop.2 ?_)
  refine ⟨1, ?_⟩
  intro n hn
  have hn_nat : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by positivity
  have hn0 : (n : ℝ) ≠ 0 := hnpos.ne'
  have hden₁ : a + (n : ℝ) * d ≠ 0 := by positivity
  have hden₂ : a * ((n : ℝ)⁻¹) + d ≠ 0 := by positivity
  unfold explicitQuantity
  field_simp [hn0, hden₁, hden₂]

theorem gap5
    (a b d : ℝ)
    (hidentity : ∀ n, raabeQuantity a b d n =
      explicitQuantity a b d n)
    (hlimit : Tendsto (explicitQuantity a b d) atTop
      (nhds ((b - a) / d))) :
    Tendsto (raabeQuantity a b d) atTop (nhds ((b - a) / d)) := by
  exact hlimit.congr' (Filter.Eventually.of_forall fun n => (hidentity n).symm)

theorem gap6
    (a b d : ℝ) (ha : 0 < a) (hb : 0 < b) (hd : 0 < d)
    (hraabe : Tendsto (raabeQuantity a b d) atTop
      (nhds ((b - a) / d))) :
    (b - a) / d > 1 → Summable (term a b d) := by
  intro hlimit_gt
  have hC : 0 < b - a - d := by
    have h := (lt_div_iff₀ hd).mp hlimit_gt
    linarith
  have htpos : ∀ n : ℕ, 0 < term a b d n := by
    intro n
    unfold term numeratorProduct denominatorProduct
    positivity
  have hratio : ∀ n : ℕ, term a b d n / term a b d (n + 1) =
      explicitRatio a b d n :=
    gap1 a b d (term a b d) ha hb hd (fun n => rfl)
  have hcross : ∀ n : ℕ,
      (b + (n : ℝ) * d) * term a b d (n + 1) =
        (a + (n : ℝ) * d) * term a b d n := by
    intro n
    have hr := hratio n
    unfold explicitRatio at hr
    have htn : term a b d (n + 1) ≠ 0 := (htpos (n + 1)).ne'
    have han : a + (n : ℝ) * d ≠ 0 := by positivity
    have hx := (div_eq_div_iff htn han).mp hr
    calc
      (b + (n : ℝ) * d) * term a b d (n + 1) =
          term a b d n * (a + (n : ℝ) * d) := hx.symm
      _ = (a + (n : ℝ) * d) * term a b d n := by ring
  have hdelta : ∀ n : ℕ,
      (a + (n : ℝ) * d) * term a b d n -
          (a + ((n + 1 : ℕ) : ℝ) * d) * term a b d (n + 1) =
        (b - a - d) * term a b d (n + 1) := by
    intro n
    rw [← hcross n]
    push_cast
    ring
  have htel : ∀ n : ℕ,
      (b - a - d) * (∑ k ∈ Finset.range n, term a b d (k + 1)) =
        a * term a b d 0 -
          (a + (n : ℝ) * d) * term a b d n := by
    intro n
    rw [Finset.mul_sum]
    calc
      ∑ k ∈ Finset.range n, (b - a - d) * term a b d (k + 1) =
          ∑ k ∈ Finset.range n,
            ((a + (k : ℝ) * d) * term a b d k -
              (a + ((k + 1 : ℕ) : ℝ) * d) * term a b d (k + 1)) := by
                apply Finset.sum_congr rfl
                intro k hk
                exact (hdelta k).symm
      _ = a * term a b d 0 -
          (a + (n : ℝ) * d) * term a b d n := by
            rw [Finset.sum_sub_distrib]
            have ht :=
              Finset.sum_range_sub
                (fun k : ℕ => (a + (k : ℝ) * d) * term a b d k) n
            rw [Finset.sum_sub_distrib] at ht
            have ht' := congrArg (fun x : ℝ => -x) ht
            simpa [neg_sub] using ht'
  have hbound : ∀ n : ℕ,
      (∑ k ∈ Finset.range n, term a b d (k + 1)) ≤
        a * term a b d 0 / (b - a - d) := by
    intro n
    apply (le_div_iff₀ hC).2
    have hsnonneg :
        0 ≤ (a + (n : ℝ) * d) * term a b d n :=
      mul_nonneg (by positivity) (htpos n).le
    calc
      (∑ k ∈ Finset.range n, term a b d (k + 1)) * (b - a - d) =
          (b - a - d) * (∑ k ∈ Finset.range n, term a b d (k + 1)) := by ring
      _ = a * term a b d 0 -
          (a + (n : ℝ) * d) * term a b d n := htel n
      _ ≤ a * term a b d 0 := sub_le_self _ hsnonneg
  have htail : Summable (fun n => term a b d (n + 1)) :=
    summable_of_sum_range_le
      (fun n => (htpos (n + 1)).le) hbound
  apply (summable_nat_add_iff 1).mp
  simpa [Nat.add_comm] using htail

theorem gap7
    (a b d : ℝ) (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) :
    (b - a) / d > 1 ↔ Summable (term a b d) := by
  have htpos : ∀ n : ℕ, 0 < term a b d n := by
    intro n
    unfold term numeratorProduct denominatorProduct
    positivity
  have hratio : ∀ n : ℕ, term a b d n / term a b d (n + 1) =
      explicitRatio a b d n :=
    gap1 a b d (term a b d) ha hb hd (fun n => rfl)
  have hcross : ∀ n : ℕ,
      (b + (n : ℝ) * d) * term a b d (n + 1) =
        (a + (n : ℝ) * d) * term a b d n := by
    intro n
    have hr := hratio n
    unfold explicitRatio at hr
    have htn : term a b d (n + 1) ≠ 0 := (htpos (n + 1)).ne'
    have han : a + (n : ℝ) * d ≠ 0 := by positivity
    have hx := (div_eq_div_iff htn han).mp hr
    calc
      (b + (n : ℝ) * d) * term a b d (n + 1) =
          term a b d n * (a + (n : ℝ) * d) := hx.symm
      _ = (a + (n : ℝ) * d) * term a b d n := by ring
  have hstep : ∀ n : ℕ,
      term a b d (n + 1) =
        term a b d n * (a + (n : ℝ) * d) /
          (b + (n : ℝ) * d) := by
    intro n
    have hB : b + (n : ℝ) * d ≠ 0 := by positivity
    apply (eq_div_iff hB).2
    simpa [mul_comm] using hcross n
  constructor
  · intro hgt
    have hquantity : ∀ n, raabeQuantity a b d n =
        explicitQuantity a b d n := by
      intro n
      rw [gap2 a b d hratio n]
      exact gap3 a b d ha hd n
    have hraabe : Tendsto (raabeQuantity a b d) atTop
        (nhds ((b - a) / d)) :=
      gap5 a b d hquantity (gap4 a b d ha hd)
    exact gap6 a b d ha hb hd hraabe hgt
  · intro hs
    by_contra hnot
    have hle : (b - a) / d ≤ 1 := le_of_not_gt hnot
    have hbad : b ≤ a + d := by
      have h := (div_le_iff₀ hd).mp hle
      linarith
    have hlower : ∀ n : ℕ, a / (a + (n : ℝ) * d) ≤ term a b d n := by
      intro n
      induction n with
      | zero =>
          simp [term, numeratorProduct, denominatorProduct, ha.ne']
      | succ n ih =>
          rw [hstep n]
          have hA : 0 < a + (n : ℝ) * d := by positivity
          have hB : 0 < b + (n : ℝ) * d := by positivity
          have hnext : 0 < a + ((n + 1 : ℕ) : ℝ) * d := by positivity
          have hden_le :
              b + (n : ℝ) * d ≤ a + ((n + 1 : ℕ) : ℝ) * d := by
            push_cast
            linarith
          calc
            a / (a + ((n + 1 : ℕ) : ℝ) * d) ≤
                a / (b + (n : ℝ) * d) := by
                  apply (div_le_div_iff₀ hnext hB).2
                  nlinarith
            _ = (a / (a + (n : ℝ) * d)) *
                (a + (n : ℝ) * d) / (b + (n : ℝ) * d) := by
                  field_simp [hA.ne', hB.ne']
            _ ≤ term a b d n * (a + (n : ℝ) * d) /
                (b + (n : ℝ) * d) := by
                  exact div_le_div_of_nonneg_right
                    (mul_le_mul_of_nonneg_right ih hA.le) hB.le
    have hsaff : Summable (fun n : ℕ => a / (a + (n : ℝ) * d)) :=
      Summable.of_nonneg_of_le
        (fun n : ℕ => (div_pos ha (by positivity)).le)
        (fun n : ℕ => hlower n) hs
    have hsmajor : Summable (fun n : ℕ =>
        ((a + d) / a) * (a / (a + (n : ℝ) * d))) :=
      hsaff.mul_left ((a + d) / a)
    have hharm_tail : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1)) := by
      apply Summable.of_nonneg_of_le
        (fun n : ℕ => by positivity)
        (fun n : ℕ => ?_)
        hsmajor
      have hn : 0 ≤ (n : ℝ) := by positivity
      have hn1 : 0 < (n : ℝ) + 1 := by positivity
      have hAn : 0 < a + (n : ℝ) * d := by positivity
      have han : 0 ≤ a * (n : ℝ) := mul_nonneg ha.le hn
      calc
        1 / ((n : ℝ) + 1) ≤ (a + d) / (a + (n : ℝ) * d) := by
          apply (div_le_div_iff₀ hn1 hAn).2
          nlinarith
        _ = ((a + d) / a) * (a / (a + (n : ℝ) * d)) := by
          field_simp [ha.ne', hAn.ne']
    have hharm : Summable (fun n : ℕ => 1 / (n : ℝ)) := by
      apply (summable_nat_add_iff 1).mp
      simpa [Nat.cast_add, Nat.cast_one, add_comm] using hharm_tail
    exact not_summable_one_div_natCast hharm

end

end ProofGap.Exercise2599
