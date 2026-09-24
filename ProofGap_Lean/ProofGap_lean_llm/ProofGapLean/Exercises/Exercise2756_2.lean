import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ProofGap.Exercise2756_2

noncomputable section

open Filter
open scoped Topology

def term (n : ℕ) (x : ℝ) : ℝ :=
  x * Real.arctan (n * x)

def limitFunction (x : ℝ) : ℝ :=
  Real.pi / 2 * x

def UniformlyConvergesOn
    (f : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N < n → ∀ x ∈ s, |f n x - F x| < ε

private theorem Real.abs_arctan_le_abs (x : ℝ) :
    |Real.arctan x| ≤ |x| := by
  have hnonneg : ∀ y : ℝ, 0 ≤ y → Real.arctan y ≤ y := by
    intro y hy
    by_cases hy0 : y = 0
    · subst y
      simp
    · have hypos : 0 < y := lt_of_le_of_ne hy (Ne.symm hy0)
      have hcont : ContinuousOn Real.arctan (Set.Icc 0 y) := by
        intro z hz
        exact (Real.hasDerivAt_arctan z).continuousAt.continuousWithinAt
      have hderiv :
          ∀ z ∈ Set.Ioo (0 : ℝ) y,
            HasDerivAt Real.arctan (1 / (1 + z ^ 2)) z := by
        intro z hz
        exact Real.hasDerivAt_arctan z
      obtain ⟨c, hc, heq⟩ :=
        exists_hasDerivAt_eq_slope Real.arctan
          (fun z : ℝ => 1 / (1 + z ^ 2)) hypos hcont hderiv
      have hden : 0 < 1 + c ^ 2 := by
        nlinarith [sq_nonneg c]
      have hderivle : 1 / (1 + c ^ 2) ≤ (1 : ℝ) := by
        apply (div_le_iff₀ hden).2
        nlinarith [sq_nonneg c]
      have hslope : Real.arctan y / y ≤ (1 : ℝ) := by
        calc
          Real.arctan y / y =
              (Real.arctan y - Real.arctan 0) / (y - 0) := by simp
          _ = 1 / (1 + c ^ 2) := heq.symm
          _ ≤ 1 := hderivle
      simpa using (div_le_iff₀ hypos).mp hslope
  rcases le_total x 0 with hx | hx
  · have hnx : 0 ≤ -x := neg_nonneg.mpr hx
    calc
      |Real.arctan x| = |Real.arctan (-x)| := by
        rw [Real.arctan_neg, abs_neg]
      _ = Real.arctan (-x) :=
        abs_of_nonneg (Real.arctan_nonneg.mpr hnx)
      _ ≤ -x := hnonneg (-x) hnx
      _ = |x| := by rw [abs_of_nonpos hx]
  · calc
      |Real.arctan x| = Real.arctan x :=
        abs_of_nonneg (Real.arctan_nonneg.mpr hx)
      _ ≤ x := hnonneg x hx
      _ = |x| := by rw [abs_of_nonneg hx]

theorem gap1 :
    ∀ x : ℝ, 0 < x →
      Tendsto (fun n : ℕ => term n x) atTop (𝓝 (limitFunction x)) := by
  intro x hx
  have hnx :
      Tendsto (fun n : ℕ => (n : ℝ) * x) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    obtain ⟨N, hN⟩ := exists_nat_gt (b / x)
    refine (eventually_ge_atTop N).mono ?_
    intro n hn
    have hcast : (N : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hn
    have hdiv : b / x < (n : ℝ) := lt_of_lt_of_le hN hcast
    exact le_of_lt ((div_lt_iff₀ hx).mp hdiv)
  have hatanWithin :
      Tendsto (fun n : ℕ => Real.arctan ((n : ℝ) * x)) atTop
        (𝓝[<] (Real.pi / 2)) := by
    simpa only [Function.comp_apply] using
      (Real.tendsto_arctan_atTop.comp hnx)
  have hatan :
      Tendsto (fun n : ℕ => Real.arctan ((n : ℝ) * x)) atTop
        (𝓝 (Real.pi / 2)) :=
    hatanWithin.mono_right inf_le_left
  have hmul :
      Tendsto (fun n : ℕ => x * Real.arctan ((n : ℝ) * x)) atTop
        (𝓝 (x * (Real.pi / 2))) :=
    tendsto_const_nhds.mul hatan
  simpa [term, limitFunction, mul_comm] using hmul

theorem gap2 :
    ∀ x : ℝ, 0 < x → Real.pi / 2 * x = limitFunction x := by
  intro x hx
  rfl

theorem gap3 :
    ∀ x : ℝ, 0 < x →
      Tendsto (fun n : ℕ => term n x) atTop (𝓝 (limitFunction x)) := by
  exact gap1

theorem gap4 :
    ∀ (n : ℕ) (x : ℝ), 0 < x →
      |term n x - limitFunction x| =
        x * |Real.arctan (n * x) - Real.pi / 2| := by
  intro n x hx
  calc
    |term n x - limitFunction x| =
        |x * (Real.arctan ((n : ℝ) * x) - Real.pi / 2)| := by
      simp only [term, limitFunction]
      congr 1
      ring
    _ = x * |Real.arctan ((n : ℝ) * x) - Real.pi / 2| := by
      rw [abs_mul, abs_of_pos hx]

theorem gap5 :
    ∀ (n : ℕ) (x : ℝ), 0 < n → 0 < x →
      x * |Real.arctan (n * x) - Real.pi / 2| =
        x * |-Real.arctan (1 / (n * x))| := by
  intro n x hn hx
  have hnR : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast hn
  have hprod : 0 < (n : ℝ) * x := mul_pos hnR hx
  have hrecip :
      Real.arctan (1 / ((n : ℝ) * x)) =
        Real.pi / 2 - Real.arctan ((n : ℝ) * x) := by
    simpa [one_div] using (Real.arctan_inv_of_pos hprod)
  have hdiff :
      Real.arctan ((n : ℝ) * x) - Real.pi / 2 =
        -Real.arctan (1 / ((n : ℝ) * x)) := by
    rw [hrecip]
    ring
  rw [hdiff]

theorem gap6 :
    ∀ (n : ℕ) (x : ℝ), 0 < n → 0 < x →
      x * |-Real.arctan (1 / (n * x))| ≤ x * (1 / (n * x)) := by
  intro n x hn hx
  have hnR : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast hn
  have hprod : 0 < (n : ℝ) * x := mul_pos hnR hx
  have hz : 0 ≤ 1 / ((n : ℝ) * x) :=
    le_of_lt (one_div_pos.mpr hprod)
  have harctan :
      |-Real.arctan (1 / ((n : ℝ) * x))| ≤
        1 / ((n : ℝ) * x) := by
    calc
      |-Real.arctan (1 / ((n : ℝ) * x))| =
          |Real.arctan (1 / ((n : ℝ) * x))| := abs_neg _
      _ ≤ |1 / ((n : ℝ) * x)| :=
        Real.abs_arctan_le_abs _
      _ = 1 / ((n : ℝ) * x) := abs_of_nonneg hz
  exact mul_le_mul_of_nonneg_left harctan (le_of_lt hx)

theorem gap7 :
    ∀ (n : ℕ) (x : ℝ), 0 < n → 0 < x →
      x * (1 / (n * x)) = 1 / (n : ℝ) := by
  intro n x hn hx
  have hnR : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hx0 : x ≠ 0 := ne_of_gt hx
  field_simp [hn0, hx0]

theorem gap8 :
    ∀ (n : ℕ) (x : ℝ), 0 < n → 0 < x →
      |term n x - limitFunction x| ≤ 1 / (n : ℝ) := by
  intro n x hn hx
  calc
    |term n x - limitFunction x| =
        x * |Real.arctan ((n : ℝ) * x) - Real.pi / 2| :=
      gap4 n x hx
    _ = x * |-Real.arctan (1 / ((n : ℝ) * x))| :=
      gap5 n x hn hx
    _ ≤ x * (1 / ((n : ℝ) * x)) :=
      gap6 n x hn hx
    _ = 1 / (n : ℝ) :=
      gap7 n x hn hx

theorem gap9 :
    ∀ (n : ℕ) (x ε : ℝ), 0 < x → 0 < ε →
      1 / ε < (n : ℝ) → |term n x - limitFunction x| < ε := by
  intro n x ε hx hε hN
  have hnR : (0 : ℝ) < (n : ℝ) :=
    lt_trans (one_div_pos.mpr hε) hN
  have hn : 0 < n := by
    exact_mod_cast hnR
  have hbound := gap8 n x hn hx
  have hone : 1 < (n : ℝ) * ε :=
    (div_lt_iff₀ hε).mp hN
  have hinv : 1 / (n : ℝ) < ε := by
    apply (div_lt_iff₀ hnR).2
    simpa [mul_comm] using hone
  exact lt_of_le_of_lt hbound hinv

theorem gap10 :
    ∀ (n : ℕ) (x ε : ℝ), 0 < x → 0 < ε →
      1 / ε < (n : ℝ) → |term n x - limitFunction x| < ε := by
  exact gap9

theorem gap11 :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n : ℕ, N < n →
        ∀ x : ℝ, 0 < x → |term n x - limitFunction x| < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  refine ⟨N, ?_⟩
  intro n hn x hx
  apply gap9 n x ε hx hε
  have hcast : (N : ℝ) < (n : ℝ) := by
    exact_mod_cast hn
  exact lt_trans hN hcast

theorem gap12 :
    UniformlyConvergesOn term limitFunction (Set.Ioi (0 : ℝ)) := by
  intro ε hε
  obtain ⟨N, hN⟩ := gap11 ε hε
  refine ⟨N, ?_⟩
  intro n hn x hx
  exact hN n hn x hx

theorem gap13 :
    UniformlyConvergesOn term limitFunction (Set.Ioi (0 : ℝ)) := by
  exact gap12

end

end ProofGap.Exercise2756_2
