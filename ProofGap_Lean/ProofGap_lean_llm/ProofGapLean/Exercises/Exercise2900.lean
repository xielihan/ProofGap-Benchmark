import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith

namespace ProofGap.Exercise2900

noncomputable section

open Filter
open scoped BigOperators Topology

def powerTerm (a : ℕ → ℝ) (x : ℝ) (n : ℕ) : ℝ :=
  a n * x ^ n

def powerSum (a : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑' n, powerTerm a x n

def partialSum (a : ℕ → ℝ) (x : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1), powerTerm a x n

def InteriorConvergent (a : ℕ → ℝ) (R : ℝ) : Prop :=
  ∀ x : ℝ, 0 ≤ x → x < R → Summable (powerTerm a x)

def InverseAbelData (a : ℕ → ℝ) (R S : ℝ) : Prop :=
  0 < R ∧ (∀ n, 0 ≤ a n) ∧ InteriorConvergent a R ∧
    Tendsto (powerSum a) (𝓝[<] R) (𝓝 S)

theorem gap1
    (a : ℕ → ℝ) (R : ℝ) (hR : 0 < R) :
    Summable (powerTerm a R) →
      ContinuousWithinAt (powerSum a) (Set.Iic R) R := by
  intro hsum
  have hbound : Summable (fun n => ‖powerTerm a R n‖) := by
    simpa [Real.norm_eq_abs] using hsum.abs
  have hterm :
      ∀ n, Tendsto (fun x => powerTerm a x n) (𝓝[Set.Iic R] R)
        (𝓝 (powerTerm a R n)) := by
    intro n
    have hc : Continuous (fun x : ℝ => powerTerm a x n) := by
      simp only [powerTerm]
      fun_prop
    exact hc.continuousAt.mono_left nhdsWithin_le_nhds
  have hx0 : ∀ᶠ x in 𝓝[Set.Iic R] R, 0 ≤ x :=
    nhdsWithin_le_nhds (Ici_mem_nhds hR)
  have hdom :
      ∀ᶠ x in 𝓝[Set.Iic R] R,
        ∀ n, ‖powerTerm a x n‖ ≤ ‖powerTerm a R n‖ := by
    filter_upwards [hx0, self_mem_nhdsWithin] with x hx0 hxR
    intro n
    simp only [powerTerm, norm_mul, norm_pow, Real.norm_eq_abs,
      abs_of_nonneg hx0, abs_of_nonneg hR.le]
    gcongr
    exact hxR
  show Tendsto (powerSum a) (𝓝[Set.Iic R] R) (𝓝 (powerSum a R))
  simpa only [powerSum] using
    tendsto_tsum_of_dominated_convergence hbound hterm hdom

theorem gap2
    (a : ℕ → ℝ) (R : ℝ) (hR : 0 < R) :
    Summable (powerTerm a R) →
      Tendsto (powerSum a) (𝓝[<] R) (𝓝 (powerSum a R)) := by
  intro hsum
  exact (gap1 a R hR hsum).mono_left
    (nhdsWithin_mono R Set.Iio_subset_Iic_self)

theorem gap3
    (a : ℕ → ℝ) (R S : ℝ) (h : InverseAbelData a R S) :
    Summable (powerTerm a R) → powerSum a R = S := by
  intro hsum
  exact tendsto_nhds_unique (gap2 a R h.1 hsum) h.2.2.2

theorem gap4
    (a : ℕ → ℝ) (R S : ℝ) (h : InverseAbelData a R S) :
    Summable (powerTerm a R) →
      Tendsto (powerSum a) (𝓝[<] R) (𝓝 S) := by
  intro hsum
  exact h.2.2.2

theorem gap5
    (a : ℕ → ℝ) (R S : ℝ) (h : InverseAbelData a R S) :
    ¬ Summable (powerTerm a R) →
      Tendsto (fun N => partialSum a R N) atTop atTop := by
  intro hnsum
  have hnonneg : ∀ n, 0 ≤ powerTerm a R n := by
    intro n
    exact mul_nonneg (h.2.1 n) (pow_nonneg h.1.le n)
  have ht :=
    (not_summable_iff_tendsto_nat_atTop_of_nonneg hnonneg).mp hnsum
  have ht' := ht.comp (tendsto_add_atTop_nat 1)
  simpa only [partialSum, Function.comp_apply] using ht'

theorem gap6
    (a : ℕ → ℝ) (R S : ℝ) (h : InverseAbelData a R S) :
    ¬ Summable (powerTerm a R) →
      ∀ A : ℝ, S < A → ∃ N : ℕ, A < partialSum a R N := by
  intro hnsum A hSA
  have ht := gap5 a R S h hnsum
  have hev :
      ∀ᶠ N in atTop, A < partialSum a R N := by
    filter_upwards [(tendsto_atTop.1 ht) (A + 1)] with N hN
    linarith
  exact hev.exists

theorem gap7 (a : ℕ → ℝ) (R A : ℝ) :
    ∀ N : ℕ,
      Tendsto (fun x => partialSum a x N) (𝓝[<] R)
        (𝓝 (partialSum a R N)) := by
  intro N
  have hc : Continuous (fun x : ℝ => partialSum a x N) := by
    simp only [partialSum, powerTerm]
    fun_prop
  exact hc.continuousAt.mono_left nhdsWithin_le_nhds

theorem gap8
    (a : ℕ → ℝ) (R S : ℝ) (h : InverseAbelData a R S) :
    ¬ Summable (powerTerm a R) →
      ∀ A : ℝ, S < A → ∃ N : ℕ, A < partialSum a R N := by
  exact gap6 a R S h

theorem gap9 (S A : ℝ) :
    S < A → S < A := by
  intro h
  exact h

theorem gap10
    (a : ℕ → ℝ) (x : ℝ) (hx0 : 0 ≤ x)
    (hsum : Summable (powerTerm a x)) (ha : ∀ n, 0 ≤ a n) :
    ∀ N : ℕ, partialSum a x N ≤ powerSum a x := by
  intro N
  change
    (∑ n ∈ Finset.range (N + 1), powerTerm a x n) ≤
      ∑' n, powerTerm a x n
  exact hsum.sum_le_tsum (Finset.range (N + 1)) fun n hn =>
    mul_nonneg (ha n) (pow_nonneg hx0 n)

theorem gap11
    (a : ℕ → ℝ) (R S : ℝ) (h : InverseAbelData a R S) :
    ¬ Summable (powerTerm a R) →
      ∀ A : ℝ, S < A →
        ∀ᶠ x in 𝓝[<] R, A < powerSum a x := by
  intro hnsum A hSA
  obtain ⟨N, hAN⟩ := gap6 a R S h hnsum A hSA
  have hpartial :
      ∀ᶠ x in 𝓝[<] R, A < partialSum a x N :=
    (gap7 a R A N).eventually (Ioi_mem_nhds hAN)
  have hx0 : ∀ᶠ x in 𝓝[<] R, 0 ≤ x :=
    nhdsWithin_le_nhds (Ici_mem_nhds h.1)
  filter_upwards [hpartial, hx0, self_mem_nhdsWithin] with x hAx hx0 hxR
  exact hAx.trans_le
    (gap10 a x hx0 (h.2.2.1 x hx0 hxR) h.2.1 N)

theorem gap12 (S A : ℝ) :
    S < A → S < A := by
  intro h
  exact h

theorem gap13
    (a : ℕ → ℝ) (R S : ℝ) (h : InverseAbelData a R S) :
    ¬ (¬ Summable (powerTerm a R)) := by
  intro hnsum
  have hlarge :
      ∀ᶠ x in 𝓝[<] R, S + 1 < powerSum a x :=
    gap11 a R S h hnsum (S + 1) (by linarith)
  have hsmall :
      ∀ᶠ x in 𝓝[<] R, powerSum a x < S + 1 :=
    h.2.2.2.eventually (Iio_mem_nhds (by linarith))
  obtain ⟨x, hxlarge, hxsmall⟩ := (hlarge.and hsmall).exists
  linarith

theorem gap14
    (a : ℕ → ℝ) (R S : ℝ) (h : InverseAbelData a R S) :
    ¬ (¬ Summable (powerTerm a R)) := by
  exact gap13 a R S h

theorem gap15
    (a : ℕ → ℝ) (R S : ℝ) (h : InverseAbelData a R S) :
    Summable (powerTerm a R) := by
  exact Classical.not_not.mp (gap13 a R S h)

theorem gap16
    (a : ℕ → ℝ) (R S : ℝ) (h : InverseAbelData a R S) :
    powerSum a R = S := by
  exact gap3 a R S h (gap15 a R S h)

theorem gap17
    (a : ℕ → ℝ) (R S : ℝ) (h : InverseAbelData a R S) :
    powerSum a R = S := by
  exact gap16 a R S h

end

end ProofGap.Exercise2900
