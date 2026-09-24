import ProofGapLean.Prelude.Analysis
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Neighborhoods

open Filter Topology
open scoped Interval

namespace ProofGap.Exercise2223

noncomputable section

def riemannSum (p : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 n,
    Real.rpow ((i : ℝ) / n) p * (1 / (n : ℝ))

private lemma rpow_interval_integral (p : ℝ) (hp : 0 < p) (a b : ℝ) :
    (∫ x in a..b, Real.rpow x p) =
      Real.rpow b (p + 1) / (p + 1) -
        Real.rpow a (p + 1) / (p + 1) := by
  have hpone : p + 1 ≠ 0 := by linarith
  have hpge : 1 ≤ p + 1 := by linarith
  have hcont : Continuous (fun x : ℝ => Real.rpow x p) := by
    rw [continuous_iff_continuousAt]
    intro x
    have hpair : ContinuousAt (fun y : ℝ => (y, p)) x :=
      continuousAt_id.prodMk continuousAt_const
    have hcomp :
        ContinuousAt
          ((fun z : ℝ × ℝ => Real.rpow z.1 z.2) ∘
            (fun y : ℝ => (y, p))) x := by
      exact
        (Real.continuousAt_rpow (x, p) (Or.inr hp)).comp
          (f := fun y : ℝ => (y, p)) hpair
    simpa only [Function.comp_apply] using hcomp
  have hderiv (x : ℝ) :
      HasDerivAt
        (fun y : ℝ => Real.rpow y (p + 1) / (p + 1))
        (Real.rpow x p) x := by
    have hbase :
        HasDerivAt (fun y : ℝ => Real.rpow y (p + 1))
          ((p + 1) * Real.rpow x (p + 1 - 1)) x :=
      Real.hasDerivAt_rpow_const (p := p + 1) (Or.inr hpge)
    simpa [hpone] using hbase.div_const (p + 1)
  have hint :
      IntervalIntegrable (fun x : ℝ => Real.rpow x p)
        MeasureTheory.volume a b :=
    hcont.continuousOn.intervalIntegrable
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hderiv x) hint

theorem gap1 (p : ℝ) (hp : 0 < p) :
    Tendsto (riemannSum p) atTop
      (𝓝 (∫ x in (0 : ℝ)..1, Real.rpow x p)) := by
  have hcont : Continuous (fun x : ℝ => Real.rpow x p) := by
    rw [continuous_iff_continuousAt]
    intro x
    have hpair : ContinuousAt (fun y : ℝ => (y, p)) x :=
      continuousAt_id.prodMk continuousAt_const
    have hcomp :
        ContinuousAt
          ((fun z : ℝ × ℝ => Real.rpow z.1 z.2) ∘
            (fun y : ℝ => (y, p))) x := by
      exact
        (Real.continuousAt_rpow (x, p) (Or.inr hp)).comp
          (f := fun y : ℝ => (y, p)) hpair
    simpa only [Function.comp_apply] using hcomp
  have hzero :
      Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (nhds 0) := by
    have hcast :
        Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    simpa [one_div] using tendsto_inv_atTop_zero.comp hcast
  have hbnds : ∀ n : ℕ, 0 < n →
      (∫ x in (0 : ℝ)..1, Real.rpow x p) ≤ riemannSum p n ∧
        riemannSum p n ≤
          (∫ x in (0 : ℝ)..1, Real.rpow x p) + 1 / (n : ℝ) := by
    intro n hn
    have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
    have hnzero : (n : ℝ) ≠ 0 := ne_of_gt hnreal
    let f : ℝ → ℝ := fun x => Real.rpow x p
    let F : ℝ → ℝ := fun x => Real.rpow x (p + 1) / (p + 1)
    have hcell_upper (i : ℕ) :
        F (((i + 1 : ℕ) : ℝ) / n) - F ((i : ℝ) / n) ≤
          f (((i + 1 : ℕ) : ℝ) / n) * (1 / (n : ℝ)) := by
      have hab : (i : ℝ) / n ≤ ((i + 1 : ℕ) : ℝ) / n := by
        apply div_le_div_of_nonneg_right
        · exact_mod_cast Nat.le_succ i
        · exact le_of_lt hnreal
      have hwidth :
          ((i + 1 : ℕ) : ℝ) / n - (i : ℝ) / n = 1 / (n : ℝ) := by
        rw [Nat.cast_add, Nat.cast_one]
        ring
      calc
        F (((i + 1 : ℕ) : ℝ) / n) - F ((i : ℝ) / n) =
            ∫ x in ((i : ℝ) / n)..(((i + 1 : ℕ) : ℝ) / n), f x := by
              simpa [f, F] using
                (rpow_interval_integral p hp ((i : ℝ) / n)
                  (((i + 1 : ℕ) : ℝ) / n)).symm
        _ ≤ ∫ _ in ((i : ℝ) / n)..(((i + 1 : ℕ) : ℝ) / n),
              f (((i + 1 : ℕ) : ℝ) / n) := by
            apply intervalIntegral.integral_mono_on hab
              hcont.continuousOn.intervalIntegrable
              continuous_const.continuousOn.intervalIntegrable
            intro x hx
            dsimp [f]
            apply Real.rpow_le_rpow
            · exact le_trans (by positivity) hx.1
            · exact hx.2
            · exact hp.le
        _ = ((((i + 1 : ℕ) : ℝ) / n - (i : ℝ) / n) *
              f (((i + 1 : ℕ) : ℝ) / n)) := by
            simp
        _ = f (((i + 1 : ℕ) : ℝ) / n) * (1 / (n : ℝ)) := by
            rw [hwidth]
            ring
    have hcell_lower (i : ℕ) :
        f ((i : ℝ) / n) * (1 / (n : ℝ)) ≤
          F (((i + 1 : ℕ) : ℝ) / n) - F ((i : ℝ) / n) := by
      have hab : (i : ℝ) / n ≤ ((i + 1 : ℕ) : ℝ) / n := by
        apply div_le_div_of_nonneg_right
        · exact_mod_cast Nat.le_succ i
        · exact le_of_lt hnreal
      have hwidth :
          ((i + 1 : ℕ) : ℝ) / n - (i : ℝ) / n = 1 / (n : ℝ) := by
        rw [Nat.cast_add, Nat.cast_one]
        ring
      calc
        f ((i : ℝ) / n) * (1 / (n : ℝ)) =
            (((i + 1 : ℕ) : ℝ) / n - (i : ℝ) / n) *
              f ((i : ℝ) / n) := by
            rw [hwidth]
            ring
        _ = ∫ _ in ((i : ℝ) / n)..(((i + 1 : ℕ) : ℝ) / n),
              f ((i : ℝ) / n) := by
            simp
        _ ≤ ∫ x in ((i : ℝ) / n)..(((i + 1 : ℕ) : ℝ) / n), f x := by
            apply intervalIntegral.integral_mono_on hab
              continuous_const.continuousOn.intervalIntegrable
              hcont.continuousOn.intervalIntegrable
            intro x hx
            dsimp [f]
            apply Real.rpow_le_rpow
            · positivity
            · exact hx.1
            · exact hp.le
        _ = F (((i + 1 : ℕ) : ℝ) / n) - F ((i : ℝ) / n) := by
            simpa [f, F] using
              rpow_interval_integral p hp ((i : ℝ) / n)
                (((i + 1 : ℕ) : ℝ) / n)
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
          ∫ x in (0 : ℝ)..1, Real.rpow x p := by
      rw [htel n]
      rw [rpow_interval_integral p hp]
      simp [F, hnzero]
    have hlower :
        ∑ i ∈ Finset.range n, f ((i : ℝ) / n) * (1 / (n : ℝ)) ≤
          ∫ x in (0 : ℝ)..1, Real.rpow x p := by
      rw [← hsum_eq]
      exact Finset.sum_le_sum fun i _ => hcell_lower i
    have hupper :
        (∫ x in (0 : ℝ)..1, Real.rpow x p) ≤
          ∑ i ∈ Finset.range n,
            f (((i + 1 : ℕ) : ℝ) / n) * (1 / (n : ℝ)) := by
      rw [← hsum_eq]
      exact Finset.sum_le_sum fun i _ => hcell_upper i
    have hrepr :
        riemannSum p n =
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
        (∑ i ∈ Finset.range n,
            f (((i + 1 : ℕ) : ℝ) / n) * (1 / (n : ℝ))) =
          (∑ i ∈ Finset.range n,
            f ((i : ℝ) / n) * (1 / (n : ℝ))) + 1 / (n : ℝ) := by
      let g : ℕ → ℝ := fun i => f ((i : ℝ) / n) * (1 / (n : ℝ))
      have hfirst := Finset.sum_range_succ' g n
      have hlast := Finset.sum_range_succ g n
      have hg0 : g 0 = 0 := by simp [g, f, hp.ne']
      have hgn : g n = 1 / (n : ℝ) := by simp [g, f, hnzero]
      have hs :
          ∑ i ∈ Finset.range n, g (i + 1) =
            (∑ i ∈ Finset.range n, g i) + 1 / (n : ℝ) := by
        rw [hg0] at hfirst
        rw [hgn] at hlast
        linarith
      simpa [g, Nat.cast_add, Nat.cast_one] using hs
    constructor
    · rw [hrepr]
      exact hupper
    · rw [hrepr, hshift]
      linarith
  have hupperlim :
      Tendsto
        (fun n : ℕ =>
          (∫ x in (0 : ℝ)..1, Real.rpow x p) + 1 / (n : ℝ))
        atTop (nhds (∫ x in (0 : ℝ)..1, Real.rpow x p)) := by
    simpa using tendsto_const_nhds.add hzero
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hupperlim ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact (hbnds n hn).1
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    exact (hbnds n hn).2

theorem gap2 (p : ℝ) (hp : 0 < p) :
    (∫ x in (0 : ℝ)..1, Real.rpow x p) = 1 / (p + 1) := by
  rw [rpow_interval_integral p hp]
  have hpone : p + 1 ≠ 0 := by linarith
  simp [hpone]

theorem gap3 (p : ℝ) (hp : 0 < p) :
    Tendsto (riemannSum p) atTop (𝓝 (1 / (p + 1))) := by
  rw [← gap2 p hp]
  exact gap1 p hp

end

end ProofGap.Exercise2223
