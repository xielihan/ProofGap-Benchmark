import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

open Filter Topology
open scoped Interval

namespace ProofGap.Exercise2221

noncomputable section

def originalSum (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 n, (n : ℝ) / ((n : ℝ) ^ 2 + (i : ℝ) ^ 2)

def riemannSum (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 n,
    (1 / (1 + ((i : ℝ) / n) ^ 2)) * (1 / (n : ℝ))

theorem gap1 :
    ∀ L : ℝ, Tendsto originalSum atTop (𝓝 L) ↔
      Tendsto riemannSum atTop (𝓝 L) := by
  have heq : originalSum = riemannSum := by
    funext n
    by_cases hn : n = 0
    · subst n
      simp [originalSum, riemannSum]
    · unfold originalSum riemannSum
      apply Finset.sum_congr rfl
      intro i hi
      have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
      field_simp [hnR]
  rw [heq]
  intro L
  rfl

theorem gap2 :
    Tendsto riemannSum atTop
      (𝓝 (∫ x in (0 : ℝ)..1, 1 / (1 + x ^ 2))) := by
  let f : ℝ → ℝ := fun x => 1 / (1 + x ^ 2)
  let F : ℝ → ℝ := Real.arctan
  have hcont : Continuous f := by
    dsimp [f]
    exact continuous_const.div
      (continuous_const.add (continuous_id.pow 2)) (fun x => by positivity)
  have hanti : ∀ {u v : ℝ}, 0 ≤ u → u ≤ v → f v ≤ f u := by
    intro u v hu huv
    have hv : 0 ≤ v := hu.trans huv
    have hs : u ^ 2 ≤ v ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr huv) (add_nonneg hu hv)]
    dsimp [f]
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have hzero : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (nhds 0) := by
    have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    simpa [one_div] using tendsto_inv_atTop_zero.comp hcast
  have hbnds : ∀ n : ℕ, 0 < n →
      (∫ x in (0 : ℝ)..1, 1 / (1 + x ^ 2)) - 1 / (n : ℝ) ≤
        riemannSum n ∧
      riemannSum n ≤ (∫ x in (0 : ℝ)..1, 1 / (1 + x ^ 2)) := by
    intro n hn
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
    have hcell_right (i : ℕ) :
        f (((i + 1 : ℕ) : ℝ) / n) * (1 / (n : ℝ)) ≤
          F (((i + 1 : ℕ) : ℝ) / n) - F ((i : ℝ) / n) := by
      have hab : (i : ℝ) / n ≤ ((i + 1 : ℕ) : ℝ) / n := by
        apply div_le_div_of_nonneg_right
        · exact_mod_cast Nat.le_succ i
        · exact hnR.le
      have hwidth : ((i + 1 : ℕ) : ℝ) / n - (i : ℝ) / n =
          1 / (n : ℝ) := by
        rw [Nat.cast_add, Nat.cast_one]
        ring
      calc
        f (((i + 1 : ℕ) : ℝ) / n) * (1 / (n : ℝ)) =
            ∫ _ in ((i : ℝ) / n)..(((i + 1 : ℕ) : ℝ) / n),
              f (((i + 1 : ℕ) : ℝ) / n) := by
                simp [hwidth]
                ring
        _ ≤ ∫ x in ((i : ℝ) / n)..(((i + 1 : ℕ) : ℝ) / n), f x := by
          apply intervalIntegral.integral_mono_on hab
            continuous_const.continuousOn.intervalIntegrable
            hcont.continuousOn.intervalIntegrable
          intro x hx
          apply hanti
          · exact le_trans (by positivity) hx.1
          · exact hx.2
        _ = F (((i + 1 : ℕ) : ℝ) / n) - F ((i : ℝ) / n) := by
          simpa [f, F] using
            (integral_one_div_one_add_sq
              (a := (i : ℝ) / n) (b := ((i + 1 : ℕ) : ℝ) / n))
    have hcell_left (i : ℕ) :
        F (((i + 1 : ℕ) : ℝ) / n) - F ((i : ℝ) / n) ≤
          f ((i : ℝ) / n) * (1 / (n : ℝ)) := by
      have hab : (i : ℝ) / n ≤ ((i + 1 : ℕ) : ℝ) / n := by
        apply div_le_div_of_nonneg_right
        · exact_mod_cast Nat.le_succ i
        · exact hnR.le
      have hwidth : ((i + 1 : ℕ) : ℝ) / n - (i : ℝ) / n =
          1 / (n : ℝ) := by
        rw [Nat.cast_add, Nat.cast_one]
        ring
      calc
        F (((i + 1 : ℕ) : ℝ) / n) - F ((i : ℝ) / n) =
            ∫ x in ((i : ℝ) / n)..(((i + 1 : ℕ) : ℝ) / n), f x := by
          simpa [f, F] using
            (integral_one_div_one_add_sq
              (a := (i : ℝ) / n) (b := ((i + 1 : ℕ) : ℝ) / n)).symm
        _ ≤ ∫ _ in ((i : ℝ) / n)..(((i + 1 : ℕ) : ℝ) / n),
              f ((i : ℝ) / n) := by
          apply intervalIntegral.integral_mono_on hab
            hcont.continuousOn.intervalIntegrable
            continuous_const.continuousOn.intervalIntegrable
          intro x hx
          exact hanti (by positivity) hx.1
        _ = f ((i : ℝ) / n) * (1 / (n : ℝ)) := by
          simp [hwidth]
          ring
    have htel : ∀ m : ℕ,
        ∑ i ∈ Finset.range m,
            (F (((i + 1 : ℕ) : ℝ) / n) - F ((i : ℝ) / n)) =
          F ((m : ℝ) / n) - F 0 := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
          rw [Finset.sum_range_succ, ih]
          simp only [Nat.cast_add, Nat.cast_one]
          ring
    have hsum_eq :
        ∑ i ∈ Finset.range n,
            (F (((i + 1 : ℕ) : ℝ) / n) - F ((i : ℝ) / n)) =
          ∫ x in (0 : ℝ)..1, 1 / (1 + x ^ 2) := by
      rw [htel n]
      simpa [F, hn0] using
        (integral_one_div_one_add_sq (a := (0 : ℝ)) (b := 1)).symm
    have hright :
        ∑ i ∈ Finset.range n,
            f (((i + 1 : ℕ) : ℝ) / n) * (1 / (n : ℝ)) ≤
          ∫ x in (0 : ℝ)..1, 1 / (1 + x ^ 2) := by
      rw [← hsum_eq]
      exact Finset.sum_le_sum fun i hi => hcell_right i
    have hleft :
        (∫ x in (0 : ℝ)..1, 1 / (1 + x ^ 2)) ≤
          ∑ i ∈ Finset.range n, f ((i : ℝ) / n) * (1 / (n : ℝ)) := by
      rw [← hsum_eq]
      exact Finset.sum_le_sum fun i hi => hcell_left i
    have hrepr : riemannSum n =
        ∑ i ∈ Finset.range n,
          f (((i + 1 : ℕ) : ℝ) / n) * (1 / (n : ℝ)) := by
      have hIcc : Finset.Icc 1 n = Finset.Ico 1 (n + 1) := by
        ext i
        simp only [Finset.mem_Icc, Finset.mem_Ico]
        omega
      unfold riemannSum
      rw [hIcc, Finset.sum_Ico_eq_sum_range]
      simp only [Nat.add_sub_cancel_right]
      apply Finset.sum_congr rfl
      intro i hi
      simp [f, Nat.add_comm]
    have hshift :
        (∑ i ∈ Finset.range n, f ((i : ℝ) / n) * (1 / (n : ℝ))) ≤
          (∑ i ∈ Finset.range n,
            f (((i + 1 : ℕ) : ℝ) / n) * (1 / (n : ℝ))) +
              1 / (n : ℝ) := by
      let g : ℕ → ℝ := fun i => f ((i : ℝ) / n) * (1 / (n : ℝ))
      have hfirst := Finset.sum_range_succ' g n
      have hlast := Finset.sum_range_succ g n
      have hg0 : g 0 = 1 / (n : ℝ) := by simp [g, f]
      have hgn : 0 ≤ g n := by
        dsimp [g, f]
        positivity
      have hs : (∑ i ∈ Finset.range n, g i) ≤
          (∑ i ∈ Finset.range n, g (i + 1)) + 1 / (n : ℝ) := by
        rw [hg0] at hfirst
        linarith
      simpa [g, Nat.cast_add, Nat.cast_one] using hs
    rw [hrepr]
    constructor
    · linarith
    · exact hright
  have hlower : Tendsto
      (fun n : ℕ => (∫ x in (0 : ℝ)..1, 1 / (1 + x ^ 2)) - 1 / (n : ℝ))
      atTop (nhds (∫ x in (0 : ℝ)..1, 1 / (1 + x ^ 2))) := by
    simpa using tendsto_const_nhds.sub hzero
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hlower tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact (hbnds n hn).1
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact (hbnds n hn).2

theorem gap3 :
    (∫ x in (0 : ℝ)..1, 1 / (1 + x ^ 2)) = Real.pi / 4 := by
  rw [integral_one_div_one_add_sq]
  simp [Real.arctan_one, Real.arctan_zero]

theorem gap4 :
    Tendsto originalSum atTop (𝓝 (Real.pi / 4)) := by
  rw [← gap3]
  exact (gap1 _).mpr gap2

end

end ProofGap.Exercise2221
