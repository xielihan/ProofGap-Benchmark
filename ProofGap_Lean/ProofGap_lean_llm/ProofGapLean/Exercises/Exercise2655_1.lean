import ProofGapLean.Prelude.Sequences
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise2655_1

noncomputable section

open scoped BigOperators

def term (n : ℕ) : ℝ :=
  1 / (n : ℝ) ^ 2

def remainder (N : ℕ) : ℝ :=
  ∑' l : ℕ, term (N + 1 + l)

def majorant (n : ℕ) : ℝ :=
  1 / ((n : ℝ) * (n - 1 : ℝ))

def telescopingTerm (n : ℕ) : ℝ :=
  1 / (n - 1 : ℝ) - 1 / n

private theorem majorant_eq_telescoping (n : ℕ) (hn : 2 ≤ n) :
    majorant n = telescopingTerm n := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by linarith
  have hnm1 : (n : ℝ) - 1 ≠ 0 := by linarith
  unfold majorant telescopingTerm
  field_simp [hn0, hnm1] <;> ring

private theorem telescoping_hasSum (N : ℕ) (hN : 1 ≤ N) :
    HasSum (fun l : ℕ => telescopingTerm (N + 1 + l)) (1 / N) := by
  have hnonneg : ∀ l : ℕ, 0 ≤ telescopingTerm (N + 1 + l) := by
    intro l
    have hn : 2 ≤ N + 1 + l := by omega
    have hx : (2 : ℝ) ≤ ((N + 1 + l : ℕ) : ℝ) := by
      exact_mod_cast hn
    rw [← majorant_eq_telescoping (N + 1 + l) hn]
    unfold majorant
    exact div_nonneg (by norm_num) (mul_nonneg (by linarith) (by linarith))
  refine (hasSum_iff_tendsto_nat_of_nonneg hnonneg (1 / (N : ℝ))).2 ?_
  have hpartial : ∀ n : ℕ,
      (∑ i ∈ Finset.range n, telescopingTerm (N + 1 + i)) =
        1 / (N : ℝ) - 1 / (N + n : ℕ) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      have hleft :
          ((N + 1 + n : ℕ) : ℝ) - 1 = ((N + n : ℕ) : ℝ) := by
        norm_num [Nat.cast_add]
        <;> ring
      have hright :
          ((N + 1 + n : ℕ) : ℝ) = ((N + Nat.succ n : ℕ) : ℝ) := by
        norm_num [Nat.cast_add]
        <;> ring
      rw [telescopingTerm, hleft, hright]
      ring
  simp_rw [hpartial]
  have hncast :
      Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hden :
      Tendsto (fun n : ℕ => (N : ℝ) + (n : ℝ)) atTop atTop :=
    tendsto_const_nhds.add_atTop hncast
  have hinv :
      Tendsto (fun n : ℕ => 1 / ((N : ℝ) + (n : ℝ))) atTop (nhds 0) := by
    simpa [one_div] using (tendsto_inv_atTop_zero.comp hden)
  simpa [Nat.cast_add] using
    (tendsto_const_nhds.sub hinv :
      Tendsto
        (fun n : ℕ => 1 / (N : ℝ) - 1 / ((N : ℝ) + (n : ℝ)))
        atTop (nhds (1 / (N : ℝ) - 0)))

theorem gap1 (N : ℕ) (hN : 1 ≤ N) :
    remainder N < ∑' l : ℕ, majorant (N + 1 + l) := by
  have hlt : ∀ l : ℕ, term (N + 1 + l) < majorant (N + 1 + l) := by
    intro l
    have hn : 2 ≤ N + 1 + l := by omega
    have hx : (2 : ℝ) ≤ ((N + 1 + l : ℕ) : ℝ) := by
      exact_mod_cast hn
    have hxpos : (0 : ℝ) < ((N + 1 + l : ℕ) : ℝ) := by linarith
    have hxm1 : (0 : ℝ) < ((N + 1 + l : ℕ) : ℝ) - 1 := by linarith
    unfold term majorant
    apply (div_lt_div_iff₀ (pow_pos hxpos 2) (mul_pos hxpos hxm1)).2
    nlinarith
  have hg : Summable (fun l : ℕ => majorant (N + 1 + l)) := by
    have hfun :
        (fun l : ℕ => majorant (N + 1 + l)) =
          (fun l : ℕ => telescopingTerm (N + 1 + l)) := by
      funext l
      apply majorant_eq_telescoping
      omega
    rw [hfun]
    exact (telescoping_hasSum N hN).summable
  have hf : Summable (fun l : ℕ => term (N + 1 + l)) :=
    Summable.of_nonneg_of_le
      (fun l => by
        unfold term
        exact div_nonneg (by norm_num) (sq_nonneg _))
      (fun l => le_of_lt (hlt l)) hg
  exact hf.tsum_lt_tsum (fun l => le_of_lt (hlt l)) (hlt 0) hg

theorem gap2 :
    ∀ n : ℕ, 2 ≤ n → majorant n = telescopingTerm n := by
  intro n hn
  exact majorant_eq_telescoping n hn

theorem gap3 (N : ℕ) (hN : 1 ≤ N) :
    (∑' l : ℕ, telescopingTerm (N + 1 + l)) = 1 / N := by
  exact (telescoping_hasSum N hN).tsum_eq

theorem gap4 (N : ℕ) (hN : 1 ≤ N) :
    remainder N < 1 / N := by
  calc
    remainder N < ∑' l : ℕ, majorant (N + 1 + l) := gap1 N hN
    _ = ∑' l : ℕ, telescopingTerm (N + 1 + l) := by
      apply tsum_congr
      intro l
      exact gap2 (N + 1 + l) (by omega)
    _ = 1 / N := gap3 N hN

theorem gap5 (N : ℕ) (hbound : remainder N < 1 / N) :
    1 / (N : ℝ) < (10 : ℝ) ^ (-5 : ℤ) →
      remainder N < (10 : ℝ) ^ (-5 : ℤ) := by
  intro h
  exact lt_trans hbound h

theorem gap6 (N : ℕ) :
    100000 < N → 1 / (N : ℝ) < (10 : ℝ) ^ (-5 : ℤ) := by
  intro h
  have hNr : (100000 : ℝ) < (N : ℝ) := by
    exact_mod_cast h
  rw [show (10 : ℝ) ^ (-5 : ℤ) = (1 : ℝ) / 100000 by norm_num]
  exact one_div_lt_one_div_of_lt (by norm_num) hNr

theorem gap7 (N : ℕ) (hN : 1 ≤ N) :
    100000 < N → remainder N < (10 : ℝ) ^ (-5 : ℤ) := by
  intro h
  exact gap5 N (gap4 N hN) (gap6 N h)

theorem gap8 (N : ℕ) (hN : 100000 < N) :
    100000 < N := by
  exact hN

end

end ProofGap.Exercise2655_1
