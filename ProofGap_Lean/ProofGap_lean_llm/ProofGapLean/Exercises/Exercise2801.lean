import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.Positivity
import Mathlib.Order.Filter.AtTopBot.Defs

namespace ProofGap.Exercise2801

noncomputable section

open scoped Topology

def f (n : ℕ) (x : ℝ) : ℝ :=
  x ^ 2 + (1 / (n : ℝ)) *
    Real.sin ((n : ℝ) * (x + Real.pi / 2))

def limitFunction (x : ℝ) : ℝ :=
  x ^ 2

def UniformlyConvergesOn
    (u : ℕ → ℝ → ℝ) (s : Set ℝ) (g : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ s, |u n x - g x| < ε

private theorem uniform_core :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ x : ℝ,
      |f (n + 1) x - limitFunction x| < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  refine ⟨N, ?_⟩
  intro n hn x
  have hnonneg : 0 ≤ 1 / (((n + 1 : ℕ) : ℝ)) := by positivity
  have herr :
      |f (n + 1) x - limitFunction x| ≤
        1 / (((n + 1 : ℕ) : ℝ)) := by
    rw [show
      f (n + 1) x - limitFunction x =
        (1 / (((n + 1 : ℕ) : ℝ))) *
          Real.sin ((((n + 1 : ℕ) : ℝ)) * (x + Real.pi / 2)) by
            simp only [f, limitFunction]
            ring]
    rw [abs_mul, abs_of_nonneg hnonneg]
    calc
      (1 / (((n + 1 : ℕ) : ℝ))) *
            |Real.sin ((((n + 1 : ℕ) : ℝ)) *
              (x + Real.pi / 2))| ≤
          (1 / (((n + 1 : ℕ) : ℝ))) * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) hnonneg
      _ = 1 / (((n + 1 : ℕ) : ℝ)) := by ring
  have hNle : (N : ℝ) ≤ (((n + 1 : ℕ) : ℝ)) := by
    exact_mod_cast (le_trans hn (Nat.le_succ n))
  have hfrac : 1 / ε < (((n + 1 : ℕ) : ℝ)) :=
    lt_of_lt_of_le hN hNle
  have hmul : 1 < (((n + 1 : ℕ) : ℝ)) * ε :=
    (div_lt_iff₀ hε).mp hfrac
  have hden : 0 < (((n + 1 : ℕ) : ℝ)) := by positivity
  have hrecip : 1 / (((n + 1 : ℕ) : ℝ)) < ε := by
    apply (div_lt_iff₀ hden).2
    simpa [mul_comm] using hmul
  exact lt_of_le_of_lt herr hrecip

private theorem cosine_multiples_not_tendsto_zero (a : ℝ) :
    ¬Tendsto
      (fun n : ℕ =>
        Real.cos ((((n + 1 : ℕ) : ℝ)) * a))
      atTop (𝓝 0) := by
  intro h
  have hmap : Tendsto (fun n : ℕ => 2 * n + 1) atTop atTop := by
    refine Filter.tendsto_atTop.2 ?_
    intro b
    filter_upwards [Filter.eventually_ge_atTop b] with n hn
    exact hn.trans (by omega)
  have hdouble :
      Tendsto
        (fun n : ℕ =>
          Real.cos (2 * ((((n + 1 : ℕ) : ℝ)) * a)))
        atTop (𝓝 0) := by
    have hs := h.comp hmap
    convert hs using 1
    funext n
    congr 1
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one]
    ring
  have hp :
      Tendsto
        (fun n : ℕ =>
          2 * Real.cos ((((n + 1 : ℕ) : ℝ)) * a) *
              Real.cos ((((n + 1 : ℕ) : ℝ)) * a) - 1)
        atTop (𝓝 (2 * 0 * 0 - 1)) :=
    ((tendsto_const_nhds.mul h).mul h).sub tendsto_const_nhds
  have hneg :
      Tendsto
        (fun n : ℕ =>
          Real.cos (2 * ((((n + 1 : ℕ) : ℝ)) * a)))
        atTop (𝓝 (-1)) := by
    convert hp using 1
    · funext n
      rw [Real.cos_two_mul]
      ring
    · norm_num
  have hbad : (0 : ℝ) = -1 := tendsto_nhds_unique hdouble hneg
  norm_num at hbad

theorem gap1 (x : ℝ) :
    Tendsto (fun n : ℕ => f (n + 1) x) atTop (𝓝 (x ^ 2)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := uniform_core ε hε
  refine ⟨N, ?_⟩
  intro n hn
  simpa [Real.dist_eq, limitFunction] using hN n hn x

theorem gap2 (x : ℝ) :
    x ^ 2 = limitFunction x := by
  rfl

theorem gap3 (x : ℝ) :
    Tendsto
      (fun n : ℕ => f (n + 1) x)
      atTop (𝓝 (limitFunction x)) := by
  simpa [limitFunction] using gap1 x

theorem gap4 (x : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    |f n x - limitFunction x| =
      |(1 / (n : ℝ)) *
        Real.sin ((n : ℝ) * (x + Real.pi / 2))| := by
  simp only [f, limitFunction]
  congr 1
  ring

theorem gap5 (x : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    |(1 / (n : ℝ)) *
        Real.sin ((n : ℝ) * (x + Real.pi / 2))| ≤
      1 / (n : ℝ) := by
  have hnonneg : 0 ≤ 1 / (n : ℝ) := by positivity
  rw [abs_mul, abs_of_nonneg hnonneg]
  calc
    (1 / (n : ℝ)) *
          |Real.sin ((n : ℝ) * (x + Real.pi / 2))| ≤
        (1 / (n : ℝ)) * 1 :=
      mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) hnonneg
    _ = 1 / (n : ℝ) := by ring

theorem gap6 (x : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    |f n x - limitFunction x| ≤ 1 / (n : ℝ) := by
  rw [gap4 x n hn]
  exact gap5 x n hn

theorem gap7 :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ x : ℝ,
      |f (n + 1) x - limitFunction x| < ε := by
  exact uniform_core

theorem gap8 :
    UniformlyConvergesOn
      (fun n => f (n + 1)) Set.univ limitFunction := by
  intro ε hε
  obtain ⟨N, hN⟩ := gap7 ε hε
  refine ⟨N, ?_⟩
  intro n hn x hx
  exact hN n hn x

theorem gap9 (x : ℝ) :
    deriv (fun y => limitFunction y) x =
      deriv (fun y : ℝ => y ^ 2) x := by
  rfl

theorem gap10 (x : ℝ) :
    deriv (fun y : ℝ => y ^ 2) x = 2 * x := by
  simpa using ((hasDerivAt_id x).pow 2).deriv

theorem gap11 (x : ℝ) :
    deriv limitFunction x = 2 * x := by
  change deriv (fun y : ℝ => y ^ 2) x = 2 * x
  exact gap10 x

theorem gap12 (n : ℕ) (x : ℝ) (hn : 1 ≤ n) :
    HasDerivAt (f n)
      (2 * x + Real.cos ((n : ℝ) * (x + Real.pi / 2))) x := by
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  have hsq : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    simpa using (hasDerivAt_id x).pow 2
  have hinner :
      HasDerivAt
        (fun y : ℝ => (n : ℝ) * (y + Real.pi / 2))
        (n : ℝ) x := by
    simpa using
      ((hasDerivAt_id x).add_const (Real.pi / 2)).const_mul (n : ℝ)
  have hsin :
      HasDerivAt
        (fun y : ℝ =>
          Real.sin ((n : ℝ) * (y + Real.pi / 2)))
        (Real.cos ((n : ℝ) * (x + Real.pi / 2)) * (n : ℝ)) x := by
    simpa using
      (Real.hasDerivAt_sin
        ((n : ℝ) * (x + Real.pi / 2))).comp x hinner
  have hscaled := hsin.const_mul (1 / (n : ℝ))
  have hosc :
      HasDerivAt
        (fun y : ℝ =>
          (1 / (n : ℝ)) *
            Real.sin ((n : ℝ) * (y + Real.pi / 2)))
        (Real.cos ((n : ℝ) * (x + Real.pi / 2))) x := by
    convert hscaled using 1
    field_simp [hn0]
  change HasDerivAt
    (fun y : ℝ =>
      y ^ 2 + (1 / (n : ℝ)) *
        Real.sin ((n : ℝ) * (y + Real.pi / 2)))
    (2 * x + Real.cos ((n : ℝ) * (x + Real.pi / 2))) x
  simpa only [Pi.add_apply] using hsq.add hosc

theorem gap13 :
    ¬ConvergentSeq (fun n : ℕ => deriv (f (n + 1)) 0) := by
  rintro ⟨l, hl⟩
  have hd (n : ℕ) :
      deriv (f (n + 1)) 0 =
        Real.cos ((((n + 1 : ℕ) : ℝ)) * (Real.pi / 2)) := by
    have h := (gap12 (n + 1) 0 (by omega)).deriv
    simpa using h
  have hc :
      Tendsto
        (fun n : ℕ =>
          Real.cos ((((n + 1 : ℕ) : ℝ)) * (Real.pi / 2)))
        atTop (𝓝 l) := by
    convert hl using 1
    funext n
    exact (hd n).symm
  have hshiftMap : Tendsto (fun n : ℕ => n + 2) atTop atTop := by
    refine Filter.tendsto_atTop.2 ?_
    intro b
    filter_upwards [Filter.eventually_ge_atTop b] with n hn
    exact hn.trans (by omega)
  have hs := hc.comp hshiftMap
  have hneg :
      Tendsto
        (fun n : ℕ =>
          -Real.cos ((((n + 1 : ℕ) : ℝ)) * (Real.pi / 2)))
        atTop (𝓝 l) := by
    convert hs using 1
    funext n
    change
      -Real.cos ((((n + 1 : ℕ) : ℝ)) * (Real.pi / 2)) =
        Real.cos ((((n + 2 + 1 : ℕ) : ℝ)) * (Real.pi / 2))
    have hangle :
        ((((n + 2 + 1 : ℕ) : ℝ)) * (Real.pi / 2)) =
          (((n + 1 : ℕ) : ℝ) * (Real.pi / 2)) + Real.pi := by
      simp only [Nat.cast_add, Nat.cast_one]
      ring
    rw [hangle, Real.cos_add_pi]
  have hlneg : l = -l := tendsto_nhds_unique hneg hc.neg
  have hl0 : l = 0 := by linarith
  apply cosine_multiples_not_tendsto_zero (Real.pi / 2)
  simpa [hl0] using hc

theorem gap14 (x : ℝ) :
    ¬Tendsto
      (fun n : ℕ => deriv (f (n + 1)) x)
      atTop (𝓝 (deriv limitFunction x)) := by
  intro h
  have ht := h.sub
    (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (2 * x : ℝ)) atTop (𝓝 (2 * x)))
  have hz :
      Tendsto
        (fun n : ℕ => deriv (f (n + 1)) x - 2 * x)
        atTop (𝓝 0) := by
    simpa [gap11] using ht
  apply cosine_multiples_not_tendsto_zero (x + Real.pi / 2)
  convert hz using 1
  funext n
  have hd := (gap12 (n + 1) x (by omega)).deriv
  rw [hd]
  ring

theorem gap15 :
    UniformlyConvergesOn
        (fun n => f (n + 1)) Set.univ limitFunction ∧
      ∀ x : ℝ,
        ¬Tendsto
          (fun n : ℕ => deriv (f (n + 1)) x)
          atTop (𝓝 (deriv limitFunction x)) := by
  exact ⟨gap8, gap14⟩

end

end ProofGap.Exercise2801
