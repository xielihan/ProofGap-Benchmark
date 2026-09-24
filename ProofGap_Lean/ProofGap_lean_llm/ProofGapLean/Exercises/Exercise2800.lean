import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise2800

noncomputable section

open scoped Topology

def f (n : ℕ) (x : ℝ) : ℝ :=
  (1 / (n : ℝ)) * Real.arctan (x ^ n)

def limitFunction (_x : ℝ) : ℝ :=
  0

def UniformlyConvergesOn
    (u : ℕ → ℝ → ℝ) (s : Set ℝ) (g : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ s, |u n x - g x| < ε

theorem gap1 (x : ℝ) (n : ℕ) :
    |Real.arctan (x ^ n)| < Real.pi / 2 := by
  rw [abs_lt]
  constructor
  · exact Real.neg_pi_div_two_lt_arctan _
  · exact Real.arctan_lt_pi_div_two _

theorem gap2 (x : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    |f n x| < Real.pi / (2 * (n : ℝ)) := by
  unfold f
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (n : ℝ))]
  have h := gap1 x n
  calc
    1 / (n : ℝ) * |Real.arctan (x ^ n)| < 1 / (n : ℝ) * (Real.pi / 2) :=
      mul_lt_mul_of_pos_left h (by positivity)
    _ = Real.pi / (2 * (n : ℝ)) := by field_simp

theorem gap3 (x : ℝ) :
    Tendsto (fun n : ℕ => f (n + 1) x) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.pi / (2 * ε))
  refine ⟨N, fun n hn => ?_⟩
  rw [Real.dist_eq]
  simp only [sub_zero]
  have hb := gap2 x (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
  have hNreal : Real.pi / (2 * ε) < (n : ℝ) + 1 := by
    have hcast : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hden : (0 : ℝ) < 2 * ((n : ℝ) + 1) := by positivity
  have hpilt : Real.pi < ((n : ℝ) + 1) * (2 * ε) :=
    (div_lt_iff₀ (mul_pos (by norm_num) hε)).1 hNreal
  have hbound : Real.pi / (2 * ((n : ℝ) + 1)) < ε := by
    apply (div_lt_iff₀ hden).2
    simpa [mul_comm, mul_left_comm, mul_assoc] using hpilt
  apply lt_trans hb
  simpa [Nat.cast_add, Nat.cast_one] using hbound

theorem gap4 (x : ℝ) :
    limitFunction x = 0 := by
  rfl

theorem gap5 (x : ℝ) :
    Tendsto (fun n : ℕ => f (n + 1) x) atTop (𝓝 (limitFunction x)) := by
  simpa [gap4 x] using gap3 x

theorem gap6 :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ x : ℝ,
      |f (n + 1) x - limitFunction x| <
        Real.pi / (2 * ((n : ℝ) + 1)) ∧
      Real.pi / (2 * ((n : ℝ) + 1)) < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.pi / (2 * ε))
  refine ⟨N, fun n hn x => ?_⟩
  have hb := gap2 x (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
  have hNreal : Real.pi / (2 * ε) < (n : ℝ) + 1 := by
    have hcast : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hden : (0 : ℝ) < 2 * ((n : ℝ) + 1) := by positivity
  have hpilt : Real.pi < ((n : ℝ) + 1) * (2 * ε) :=
    (div_lt_iff₀ (mul_pos (by norm_num) hε)).1 hNreal
  have hbound : Real.pi / (2 * ((n : ℝ) + 1)) < ε := by
    apply (div_lt_iff₀ hden).2
    simpa [mul_comm, mul_left_comm, mul_assoc] using hpilt
  constructor
  · simpa [limitFunction, Nat.cast_add, Nat.cast_one] using hb
  · exact hbound

theorem gap7 :
    UniformlyConvergesOn
      (fun n => f (n + 1)) Set.univ limitFunction := by
  intro ε hε
  obtain ⟨N, hN⟩ := gap6 ε hε
  refine ⟨N, fun n hn x _ => ?_⟩
  exact (hN n hn x).1.trans (hN n hn x).2

theorem gap8 (n : ℕ) (x : ℝ) (hn : 1 ≤ n) :
    HasDerivAt (f n)
      (x ^ (n - 1) / (1 + x ^ (2 * n))) x := by
  unfold f
  have hn0 : n ≠ 0 := by omega
  have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast hn0
  have hpow : HasDerivAt (fun y : ℝ => y ^ n) ((n : ℝ) * x ^ (n - 1)) x := by
    simpa using (hasDerivAt_id x).pow n
  have hpow2 : (x ^ n) ^ 2 = x ^ (2 * n) := by
    calc
      (x ^ n) ^ 2 = x ^ (n * 2) := (pow_mul x n 2).symm
      _ = x ^ (2 * n) := by rw [Nat.mul_comm]
  have hnonneg : (0 : ℝ) ≤ x ^ (2 * n) := by
    rw [← hpow2]
    exact sq_nonneg (x ^ n)
  have hden : (1 + x ^ (2 * n) : ℝ) ≠ 0 := by
    nlinarith
  have hcoef :
      (1 / (n : ℝ)) *
          ((1 / (1 + (x ^ n) ^ 2)) * ((n : ℝ) * x ^ (n - 1))) =
        x ^ (n - 1) / (1 + x ^ (2 * n)) := by
    rw [hpow2]
    field_simp [hnreal, hden] <;> ring
  simpa only [hcoef] using
    (Real.hasDerivAt_arctan (x ^ n)).comp x hpow |>.const_mul (1 / (n : ℝ))

theorem gap9 :
    HasDerivAt limitFunction 0 1 := by
  simpa [limitFunction] using (hasDerivAt_const (x := (1 : ℝ)) (c := (0 : ℝ)))

theorem gap10 :
    deriv limitFunction 1 = 0 := by
  exact gap9.deriv

theorem gap11 :
    deriv limitFunction 1 = 0 := by
  exact gap10

theorem gap12 :
    Tendsto
      (fun n : ℕ => deriv (f (n + 1)) 1)
      atTop (𝓝 (1 / 2 : ℝ)) := by
  have hderiv : ∀ n : ℕ, deriv (f (n + 1)) 1 = (1 / 2 : ℝ) := by
    intro n
    have h := gap8 (n + 1) 1 (Nat.succ_le_succ (Nat.zero_le n))
    have hd := h.deriv
    convert hd using 1 <;> norm_num
  have hc : Tendsto (fun _ : ℕ => (1 / 2 : ℝ)) atTop (𝓝 (1 / 2 : ℝ)) := tendsto_const_nhds
  exact hc.congr' (Filter.Eventually.of_forall fun n => (hderiv n).symm)

theorem gap13 :
    (1 / 2 : ℝ) ≠ 0 := by
  norm_num

theorem gap14 :
    ¬Tendsto
      (fun n : ℕ => deriv (f (n + 1)) 1)
      atTop (𝓝 0) := by
  intro h0
  have heq : (1 / 2 : ℝ) = 0 := tendsto_nhds_unique gap12 h0
  exact gap13 heq

theorem gap15 :
    deriv limitFunction 1 ≠ (1 / 2 : ℝ) := by
  rw [gap11]
  exact ne_comm.mp gap13

theorem gap16 :
    UniformlyConvergesOn
        (fun n => f (n + 1)) Set.univ limitFunction ∧
      Tendsto
        (fun n : ℕ => deriv (f (n + 1)) 1)
        atTop (𝓝 (1 / 2 : ℝ)) ∧
      deriv limitFunction 1 ≠ (1 / 2 : ℝ) := by
  exact ⟨gap7, gap12, gap15⟩

end

end ProofGap.Exercise2800
