import ProofGapLean.Prelude.Analysis
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Order.Filter.Tendsto
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise2516

noncomputable section

def meshWidth (n : ℕ) : ℝ := 10 / n
def massApprox (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 n,
    (6 + (3 / 10 : ℝ) * (10 / n) * i) * (10 / n)
def simplifiedApprox (n : ℕ) : ℝ :=
  60 + 15 * (n + 1 : ℝ) / n

theorem gap1 (n : ℕ) (Δx : ℝ)
    (hΔ : Δx = meshWidth n) :
    Δx = 10 / n := by
  simpa [meshWidth] using hΔ

theorem gap2 (n : ℕ) (hn : 0 < n) :
    massApprox n =
      ∑ i ∈ Finset.Icc 1 n,
        (6 + (3 / 10 : ℝ) * (10 / n) * i) * (10 / n) := by
  rfl

theorem gap3 (M : ℝ)
    (hM : Filter.Tendsto massApprox Filter.atTop (nhds M)) :
    Filter.Tendsto massApprox Filter.atTop (nhds M) := by
  exact hM

theorem gap4 (n : ℕ) (hn : 0 < n) :
    massApprox n = simplifiedApprox n := by
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  have hnR : (n : ℝ) ≠ 0 := by
    exact_mod_cast hn0
  have hIcc :
      Finset.Icc 1 n = (Finset.range (n + 1)).erase 0 := by
    ext i
    simp only [Finset.mem_Icc, Finset.mem_erase, Finset.mem_range]
    omega
  have hcard : (Finset.Icc 1 n).card = n := by
    rw [hIcc]
    simp
  have hsumRange : ∀ k : ℕ,
      (∑ i ∈ Finset.range (k + 1), (i : ℝ)) =
        (k : ℝ) * ((k : ℝ) + 1) / 2 := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih =>
      rw [show k.succ + 1 = (k + 1) + 1 by omega,
        Finset.sum_range_succ, ih]
      simp only [Nat.cast_succ]
      ring
  have hsum :
      (∑ i ∈ Finset.Icc 1 n, (i : ℝ)) =
        (n : ℝ) * ((n : ℝ) + 1) / 2 := by
    calc
      (∑ i ∈ Finset.Icc 1 n, (i : ℝ)) =
          ∑ i ∈ Finset.range (n + 1), (i : ℝ) := by
        apply Finset.sum_subset
        · intro i hi
          simp only [Finset.mem_Icc] at hi
          simp only [Finset.mem_range]
          omega
        · intro i hi hni
          simp only [Finset.mem_range] at hi
          simp only [Finset.mem_Icc] at hni
          have hi0 : i = 0 := by omega
          subst i
          norm_num
      _ = (n : ℝ) * ((n : ℝ) + 1) / 2 := hsumRange n
  unfold massApprox simplifiedApprox
  calc
    (∑ i ∈ Finset.Icc 1 n,
        (6 + (3 / 10 : ℝ) * (10 / n) * i) * (10 / n)) =
        ∑ i ∈ Finset.Icc 1 n,
          (60 / (n : ℝ) + (30 / (n : ℝ) ^ 2) * (i : ℝ)) := by
      apply Finset.sum_congr rfl
      intro i hi
      field_simp [hnR] <;> ring
    _ = (n : ℝ) * (60 / (n : ℝ)) +
        (30 / (n : ℝ) ^ 2) *
          ((n : ℝ) * ((n : ℝ) + 1) / 2) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp [hcard, hsum]
    _ = 60 + 15 * (n + 1 : ℝ) / n := by
      field_simp [hnR] <;> ring

theorem gap5 :
    Filter.Tendsto simplifiedApprox Filter.atTop (nhds 75) := by
  have hinv :
      Filter.Tendsto (fun n : ℕ => ((n : ℝ)⁻¹))
        Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hlim :
      Filter.Tendsto (fun n : ℕ => (75 : ℝ) + 15 * (n : ℝ)⁻¹)
        Filter.atTop (nhds 75) := by
    simpa using
      (tendsto_const_nhds.add (tendsto_const_nhds.mul hinv) :
        Filter.Tendsto (fun n : ℕ => (75 : ℝ) + 15 * (n : ℝ)⁻¹)
          Filter.atTop (nhds ((75 : ℝ) + 15 * 0)))
  apply hlim.congr'
  filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with n hn
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  unfold simplifiedApprox
  field_simp [hn0] <;> ring

theorem gap6 (M : ℝ)
    (hM : Filter.Tendsto massApprox Filter.atTop (nhds M)) :
    M = 75 := by
  have heq :
      massApprox =ᶠ[Filter.atTop] simplifiedApprox := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with n hn
    exact gap4 n hn
  have h75 :
      Filter.Tendsto massApprox Filter.atTop (nhds 75) :=
    gap5.congr' heq.symm
  exact tendsto_nhds_unique hM h75

end

end ProofGap.Exercise2516
