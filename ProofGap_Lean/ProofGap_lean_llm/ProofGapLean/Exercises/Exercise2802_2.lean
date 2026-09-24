import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Topology.Defs.Filter
import Mathlib.Order.Filter.AtTopBot.Defs

namespace ProofGap.Exercise2802_2

noncomputable section

open Filter
open scoped Topology

def term (α : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  Real.rpow (n : ℝ) α * x * Real.exp (-(n : ℝ) * x)

def UniformlyConvergesOn
    (f : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N < n → ∀ x ∈ s, |f n x - F x| < ε

theorem gap1 :
    ∀ (α x : ℝ) (n : ℕ),
      deriv (term α n) x =
        Real.rpow (n : ℝ) α * Real.exp (-(n : ℝ) * x) *
          (1 - (n : ℝ) * x) := by
  intro α x n
  have hleft :
      HasDerivAt (fun y : ℝ => Real.rpow (n : ℝ) α * y)
        (Real.rpow (n : ℝ) α) x := by
    convert
      (hasDerivAt_const x (Real.rpow (n : ℝ) α)).mul
        (hasDerivAt_id x) using 1 <;> simp
  have hneg :
      HasDerivAt (fun y : ℝ => -(n : ℝ) * y) (-(n : ℝ)) x := by
    convert
      (hasDerivAt_const x (-(n : ℝ))).mul (hasDerivAt_id x) using 1 <;>
      simp
  have hexp :
      HasDerivAt (fun y : ℝ => Real.exp (-(n : ℝ) * y))
        (-(n : ℝ) * Real.exp (-(n : ℝ) * x)) x := by
    convert (Real.hasDerivAt_exp (-(n : ℝ) * x)).comp x hneg using 1 <;>
      simp [Function.comp_def] <;> ring
  unfold term
  convert (hleft.mul hexp).deriv using 1 <;>
    simp [Function.comp_def] <;> ring

theorem gap2 :
    ∀ (α : ℝ) (n : ℕ), 0 < n →
      deriv (term α n) (1 / (n : ℝ)) = 0 := by
  intro α n hn
  rw [gap1]
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hn
  simp [hn0]

theorem gap3 :
    ∀ (α x : ℝ) (n : ℕ), 0 < n → 0 < x → x < 1 / (n : ℝ) →
      deriv (term α n) x > 0 := by
  intro α x n hn hx hxcrit
  rw [gap1]
  have hnR : 0 < (n : ℝ) := by
    exact_mod_cast hn
  have hlast : 0 < 1 - (n : ℝ) * x := by
    apply sub_pos.mpr
    simpa [mul_comm] using (lt_div_iff₀ hnR).mp hxcrit
  exact mul_pos
    (mul_pos (Real.rpow_pos_of_pos hnR α) (Real.exp_pos _)) hlast

theorem gap4 :
    ∀ (α x : ℝ) (n : ℕ), 0 < n → 1 / (n : ℝ) < x →
      deriv (term α n) x < 0 := by
  intro α x n hn hxcrit
  rw [gap1]
  have hnR : 0 < (n : ℝ) := by
    exact_mod_cast hn
  have hlast : 1 - (n : ℝ) * x < 0 := by
    apply sub_neg.mpr
    simpa [mul_comm] using (div_lt_iff₀ hnR).mp hxcrit
  exact mul_neg_of_pos_of_neg
    (mul_pos (Real.rpow_pos_of_pos hnR α) (Real.exp_pos _)) hlast

theorem gap5 :
    ∀ (α : ℝ) (n : ℕ), 1 ≤ n →
      1 / (n : ℝ) ∈ Set.Icc (0 : ℝ) 1 ∧
        ∀ x ∈ Set.Icc (0 : ℝ) 1,
          term α n x ≤ term α n (1 / (n : ℝ)) := by
  intro α n hn
  have hnR : 1 ≤ (n : ℝ) := by
    exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := lt_of_lt_of_le zero_lt_one hnR
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  constructor
  · constructor
    · positivity
    · exact (div_le_iff₀ hnpos).2 (by simpa using hnR)
  · intro x hx
    have hy : (n : ℝ) * x ≤ Real.exp ((n : ℝ) * x - 1) := by
      have h := Real.add_one_le_exp ((n : ℝ) * x - 1)
      nlinarith
    have hmul :=
      mul_le_mul_of_nonneg_right hy (Real.exp_pos (-(n : ℝ) * x)).le
    have heq :
        Real.exp ((n : ℝ) * x - 1) * Real.exp (-(n : ℝ) * x) =
          Real.exp (-1) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [heq] at hmul
    have hdiv :
        x * Real.exp (-(n : ℝ) * x) ≤ Real.exp (-1) / (n : ℝ) := by
      apply (le_div_iff₀ hnpos).2
      calc
        (x * Real.exp (-(n : ℝ) * x)) * (n : ℝ) =
            ((n : ℝ) * x) * Real.exp (-(n : ℝ) * x) := by ring
        _ ≤ Real.exp (-1) := hmul
    have hcore :
        x * Real.exp (-(n : ℝ) * x) ≤
          (1 / (n : ℝ)) * Real.exp (-1) := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdiv
    have hcrit : -(n : ℝ) * (1 / (n : ℝ)) = -1 := by
      field_simp [hn0]
    unfold term
    rw [hcrit]
    have hc : 0 ≤ Real.rpow (n : ℝ) α :=
      (Real.rpow_pos_of_pos hnpos α).le
    simpa [mul_assoc] using mul_le_mul_of_nonneg_left hcore hc

theorem gap6 :
    ∀ (α x : ℝ) (n : ℕ), 0 < n → x ∈ Set.Icc (0 : ℝ) 1 →
      0 ≤ term α n x := by
  intro α x n hn hx
  have hnR : 0 < (n : ℝ) := by
    exact_mod_cast hn
  have hc : 0 ≤ Real.rpow (n : ℝ) α :=
    (Real.rpow_pos_of_pos hnR α).le
  have he : 0 ≤ Real.exp (-(n : ℝ) * x) :=
    (Real.exp_pos _).le
  unfold term
  exact mul_nonneg (mul_nonneg hc hx.1) he

theorem gap7 :
    ∀ (α x : ℝ) (n : ℕ), 1 ≤ n → x ∈ Set.Icc (0 : ℝ) 1 →
      term α n x ≤ term α n (1 / (n : ℝ)) := by
  intro α x n hn hx
  exact (gap5 α n hn).2 x hx

theorem gap8 :
    ∀ (α : ℝ) (n : ℕ), 0 < n →
      term α n (1 / (n : ℝ)) =
        Real.rpow (n : ℝ) (α - 1) * Real.exp (-1) := by
  intro α n hn
  have hnR : 0 < (n : ℝ) := by
    exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have he : -(n : ℝ) * (1 / (n : ℝ)) = -1 := by
    field_simp [hn0]
  have hr :
      Real.rpow (n : ℝ) (α - 1) =
        Real.rpow (n : ℝ) α / Real.rpow (n : ℝ) 1 := by
    exact Real.rpow_sub hnR α 1
  have hr1 : Real.rpow (n : ℝ) (1 : ℝ) = (n : ℝ) := by
    simpa [Real.rpow_def_of_pos hnR] using Real.exp_log hnR
  rw [hr1] at hr
  unfold term
  rw [he, hr]
  field_simp [hn0]

theorem gap9 :
    ∀ (α : ℝ) (n : ℕ), 0 < n →
      0 ≤ Real.rpow (n : ℝ) (α - 1) * Real.exp (-1) := by
  intro α n hn
  have hnR : 0 < (n : ℝ) := by
    exact_mod_cast hn
  exact mul_nonneg
    (Real.rpow_pos_of_pos hnR (α - 1)).le (Real.exp_pos (-1)).le

theorem gap10 :
    ∀ α : ℝ, α < 1 →
      Tendsto
        (fun n : ℕ => Real.rpow (n : ℝ) (α - 1) * Real.exp (-1))
        atTop (𝓝 0) := by
  intro α hα
  have hp : 0 < 1 - α := by linarith
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hlog :
      Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hnat
  have hscaled :
      Tendsto (fun n : ℕ => Real.log (n : ℝ) * (1 - α)) atTop atTop := by
    rw [tendsto_atTop] at hlog ⊢
    intro b
    filter_upwards [hlog (b / (1 - α))] with n hn
    exact (div_le_iff₀ hp).mp hn
  have hexp :
      Tendsto
        (fun n : ℕ => Real.exp (Real.log (n : ℝ) * (1 - α)))
        atTop atTop :=
    Real.tendsto_exp_atTop.comp hscaled
  have hpow :
      Tendsto (fun n : ℕ => Real.rpow (n : ℝ) (1 - α)) atTop atTop := by
    apply hexp.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    simp [Real.rpow_def_of_pos hnR]
  have hinv : Tendsto (fun y : ℝ => y⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero
  have hlim :
      Tendsto
        (fun n : ℕ => (Real.rpow (n : ℝ) (1 - α))⁻¹ * Real.exp (-1))
        atTop (𝓝 0) := by
    simpa only [Function.comp_apply, zero_mul] using
      (hinv.comp hpow).mul_const (Real.exp (-1))
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hrsub :
      Real.rpow (n : ℝ) (0 - (1 - α)) =
        Real.rpow (n : ℝ) 0 / Real.rpow (n : ℝ) (1 - α) := by
    exact Real.rpow_sub hnR 0 (1 - α)
  have hrzero : Real.rpow (n : ℝ) (0 : ℝ) = 1 := by
    simp [Real.rpow_def_of_pos hnR]
  symm
  calc
    Real.rpow (n : ℝ) (α - 1) * Real.exp (-1) =
        Real.rpow (n : ℝ) (0 - (1 - α)) * Real.exp (-1) := by
          congr 2 <;> ring
    _ = (Real.rpow (n : ℝ) 0 / Real.rpow (n : ℝ) (1 - α)) *
          Real.exp (-1) := congrArg (fun z : ℝ => z * Real.exp (-1)) hrsub
    _ = (Real.rpow (n : ℝ) (1 - α))⁻¹ * Real.exp (-1) := by
          rw [hrzero]
          simp [div_eq_mul_inv]

theorem gap11 :
    ∀ α : ℝ, α < 1 →
      ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, ∀ n : ℕ, N < n →
          ∀ x ∈ Set.Icc (0 : ℝ) 1, |term α n x| < ε := by
  intro α hα ε hε
  rcases (Metric.tendsto_atTop.1 (gap10 α hα)) ε hε with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hNn x hx
  have hnpos : 0 < n := by omega
  have hn1 : 1 ≤ n := by omega
  have hnon := gap6 α x n hnpos hx
  have hmax := gap7 α x n hn1 hx
  rw [gap8 α n hnpos] at hmax
  have hseqnon := gap9 α n hnpos
  have hsmall :
      Real.rpow (n : ℝ) (α - 1) * Real.exp (-1) < ε := by
    have hd := hN n (Nat.le_of_lt hNn)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hseqnon] at hd
    exact hd
  rw [abs_of_nonneg hnon]
  exact lt_of_le_of_lt hmax hsmall

theorem gap12 :
    ∀ α : ℝ, α < 1 →
      UniformlyConvergesOn (term α) (fun _ => 0) (Set.Icc (0 : ℝ) 1) := by
  intro α hα
  intro ε hε
  rcases gap11 α hα ε hε with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn x hx
  simpa using hN n hn x hx

theorem gap13 :
    ∀ α : ℝ, 1 ≤ α →
      ¬ Tendsto
          (fun n : ℕ => Real.rpow (n : ℝ) (α - 1) * Real.exp (-1))
          atTop (𝓝 0) := by
  intro α hα ht
  have hc : 0 < Real.exp (-1) / 2 := by positivity
  rcases (Metric.tendsto_atTop.1 ht) (Real.exp (-1) / 2) hc with ⟨N, hN⟩
  let n : ℕ := max N 1
  have hnN : N ≤ n := by
    exact le_max_left N 1
  have hn1 : 1 ≤ n := by
    exact le_max_right N 1
  have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn1
  have hnR : 1 ≤ (n : ℝ) := by
    exact_mod_cast hn1
  have hrpow : 1 ≤ Real.rpow (n : ℝ) (α - 1) :=
    Real.one_le_rpow hnR (sub_nonneg.mpr hα)
  have hseq :
      Real.exp (-1) ≤
        Real.rpow (n : ℝ) (α - 1) * Real.exp (-1) := by
    simpa using
      mul_le_mul_of_nonneg_right hrpow (Real.exp_pos (-1)).le
  have hnon := gap9 α n hnpos
  have hsmall :
      Real.rpow (n : ℝ) (α - 1) * Real.exp (-1) <
        Real.exp (-1) / 2 := by
    have hd := hN n hnN
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hnon] at hd
    exact hd
  nlinarith [Real.exp_pos (-1)]

theorem gap14 :
    ∀ α : ℝ, 1 ≤ α →
      ¬ UniformlyConvergesOn (term α) (fun _ => 0) (Set.Icc (0 : ℝ) 1) := by
  intro α hα hu
  apply gap13 α hα
  refine Metric.tendsto_atTop.2 ?_
  intro ε hε
  rcases hu ε hε with ⟨N, hN⟩
  refine ⟨N + 1, ?_⟩
  intro n hn
  have hNn : N < n := by omega
  have hn1 : 1 ≤ n := by omega
  have hnpos : 0 < n := by omega
  have hx := (gap5 α n hn1).1
  have hb := hN n hNn (1 / (n : ℝ)) hx
  rw [gap8 α n hnpos] at hb
  simpa [Real.dist_eq] using hb

theorem gap15 :
    ∀ α : ℝ,
      α ∈ {a : ℝ | a < 1} ↔
        UniformlyConvergesOn (term α) (fun _ => 0) (Set.Icc (0 : ℝ) 1) := by
  intro α
  change α < 1 ↔
    UniformlyConvergesOn (term α) (fun _ => 0) (Set.Icc (0 : ℝ) 1)
  constructor
  · exact gap12 α
  · intro hu
    by_contra hnot
    have hge : 1 ≤ α := le_of_not_gt hnot
    exact gap14 α hge hu

end

end ProofGap.Exercise2802_2
