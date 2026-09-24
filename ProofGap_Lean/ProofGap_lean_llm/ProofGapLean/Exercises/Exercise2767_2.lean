import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise2767_2

noncomputable section

open Filter
open scoped BigOperators

def geomPartial (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), x ^ k

def badPoint (n : ℕ) : ℝ :=
  Real.rpow 2 (-1 / ((n + 1 : ℕ) : ℝ))

def SeriesUniformlyConvergesOn
    (u : ℕ → ℝ → ℝ) (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ s,
    |(∑ k ∈ Finset.range (n + 1), u k x) - f x| < ε

private lemma badPoint_exp (n : ℕ) :
    badPoint n =
      Real.exp
        (Real.log 2 * (-1 / ((n + 1 : ℕ) : ℝ))) := by
  unfold badPoint
  exact Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)
    (-1 / ((n + 1 : ℕ) : ℝ))

private lemma badPoint_pow (n : ℕ) :
    badPoint n ^ (n + 1) = (1 / 2 : ℝ) := by
  rw [badPoint_exp, ← Real.exp_nat_mul]
  have hn : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by
    positivity
  have heq :
      ((n + 1 : ℕ) : ℝ) *
          (Real.log 2 * (-1 / ((n + 1 : ℕ) : ℝ))) =
        -Real.log 2 := by
    field_simp [hn] <;> ring
  rw [heq, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  norm_num

private lemma badPoint_pos_lt_one (n : ℕ) :
    0 < badPoint n ∧ badPoint n < 1 := by
  constructor
  · rw [badPoint_exp]
    exact Real.exp_pos _
  · rw [badPoint_exp]
    have hden : 0 < (((n + 1 : ℕ) : ℝ)) := by
      positivity
    have hexp :
        (-1 : ℝ) / ((n + 1 : ℕ) : ℝ) < 0 :=
      div_neg_of_neg_of_pos (by norm_num) hden
    have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hprod :
        Real.log 2 * (-1 / ((n + 1 : ℕ) : ℝ)) < 0 :=
      mul_neg_of_pos_of_neg hlog hexp
    calc
      Real.exp (Real.log 2 * (-1 / ((n + 1 : ℕ) : ℝ))) <
          Real.exp 0 := (Real.exp_lt_exp).2 hprod
      _ = 1 := Real.exp_zero

theorem gap1 (S : ℕ → ℝ → ℝ) (n : ℕ) (x : ℝ)
    (hS : S n x = geomPartial n x) :
    S n x = geomPartial n x := by
  exact hS

theorem gap2 (n : ℕ) (x : ℝ) (hx : x ≠ 1) :
    geomPartial n x = (1 - x ^ (n + 1)) / (1 - x) := by
  have hden : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  unfold geomPartial
  induction n with
  | zero =>
      simp only [Nat.zero_add, Finset.sum_range_succ,
        Finset.sum_range_zero, zero_add, pow_zero, pow_one]
      exact (div_self hden).symm
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      field_simp [hden, pow_succ] <;> ring

theorem gap3 (S : ℕ → ℝ → ℝ) (n : ℕ) (x : ℝ)
    (hS : S n x = geomPartial n x)
    (hgeom : geomPartial n x = (1 - x ^ (n + 1)) / (1 - x)) :
    S n x = (1 - x ^ (n + 1)) / (1 - x) := by
  calc
    S n x = geomPartial n x := hS
    _ = (1 - x ^ (n + 1)) / (1 - x) := hgeom

theorem gap4 (S : ℕ → ℝ → ℝ) (limit : ℝ → ℝ) (x : ℝ)
    (hx : |x| < 1)
    (hpartial : ∀ n, S n x = geomPartial n x)
    (hlimit : Tendsto (fun n => S n x) atTop (nhds (limit x))) :
    limit x = 1 / (1 - x) := by
  have hxlt : x < 1 := lt_of_le_of_lt (le_abs_self x) hx
  have hxne : x ≠ 1 := ne_of_lt hxlt
  have hnorm : ‖x‖ < 1 := by
    simpa [Real.norm_eq_abs] using hx
  have hpow : Tendsto (fun n : ℕ => x ^ (n + 1)) atTop (nhds 0) := by
    have h :=
      (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hnorm).mul_const x
    simpa [pow_succ] using h
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have hrhs :
      Tendsto
        (fun n : ℕ => (1 - x ^ (n + 1)) / (1 - x))
        atTop (nhds (1 / (1 - x))) := by
    simpa using (hone.sub hpow).div_const (1 - x)
  have heq :
      (fun n : ℕ => S n x) =ᶠ[atTop]
        (fun n : ℕ => (1 - x ^ (n + 1)) / (1 - x)) :=
    Filter.Eventually.of_forall (fun n => by
      change S n x = (1 - x ^ (n + 1)) / (1 - x)
      rw [hpartial n, gap2 n x hxne])
  have hcomputed :
      Tendsto (fun n : ℕ => S n x) atTop (nhds (1 / (1 - x))) :=
    (tendsto_congr' heq).2 hrhs
  exact tendsto_nhds_unique hlimit hcomputed

theorem gap5 (n : ℕ) :
    |geomPartial n (badPoint n) - 1 / (1 - badPoint n)| =
      |(1 / 2 : ℝ) / (1 - badPoint n)| := by
  have hne : badPoint n ≠ 1 := by
    intro h
    have hp := badPoint_pow n
    rw [h] at hp
    norm_num at hp
  rw [gap2 n (badPoint n) hne, badPoint_pow]
  have hden : 1 - badPoint n ≠ 0 :=
    sub_ne_zero.mpr (Ne.symm hne)
  have halg :
      (1 - (1 / 2 : ℝ)) / (1 - badPoint n) -
          1 / (1 - badPoint n) =
        -((1 / 2 : ℝ) / (1 - badPoint n)) := by
    field_simp [hden] <;> ring
  rw [halg, abs_neg]

theorem gap6 (n : ℕ) (ε : ℝ) (hε : 0 < ε) (hεhalf : ε < 1 / 2) :
    |(1 / 2 : ℝ) / (1 - badPoint n)| > 1 / 2 := by
  obtain ⟨hbpos, hblt⟩ := badPoint_pos_lt_one n
  have hdpos : 0 < 1 - badPoint n := by
    linarith
  rw [abs_of_pos (div_pos (by norm_num) hdpos)]
  apply (lt_div_iff₀ hdpos).2
  nlinarith

theorem gap7 (ε : ℝ) (hε : 0 < ε) (hεhalf : ε < 1 / 2) :
    (1 / 2 : ℝ) > ε := by
  exact hεhalf

theorem gap8 (n : ℕ) (ε : ℝ) (hε : 0 < ε) (hεhalf : ε < 1 / 2) :
    |geomPartial n (badPoint n) - 1 / (1 - badPoint n)| > ε := by
  rw [gap5 n]
  exact lt_trans hεhalf (gap6 n ε hε hεhalf)

theorem gap9 :
    ¬ SeriesUniformlyConvergesOn
        (fun (n : ℕ) (x : ℝ) => x ^ n)
        (Set.Ioo (-1 : ℝ) 1)
        (fun x => 1 / (1 - x)) := by
  intro h
  rcases h (1 / 4 : ℝ) (by norm_num) with ⟨N, hN⟩
  obtain ⟨hbpos, hblt⟩ := badPoint_pos_lt_one N
  have hu := hN N le_rfl (badPoint N) (by
    constructor
    · linarith
    · exact hblt)
  change
    |geomPartial N (badPoint N) - 1 / (1 - badPoint N)| < (1 / 4 : ℝ)
    at hu
  have hlower := gap8 N (1 / 4 : ℝ) (by norm_num) (by norm_num)
  linarith

theorem gap10 :
    (∀ x : ℝ, |x| < 1 →
      HasSum (fun n : ℕ => x ^ n) (1 / (1 - x))) ∧
    ¬ SeriesUniformlyConvergesOn
        (fun (n : ℕ) (x : ℝ) => x ^ n)
        (Set.Ioo (-1 : ℝ) 1)
        (fun x => 1 / (1 - x)) := by
  constructor
  · intro x hx
    have hnorm : ‖x‖ < 1 := by
      simpa [Real.norm_eq_abs] using hx
    simpa [one_div] using
      (hasSum_geometric_of_norm_lt_one hnorm)
  · exact gap9

end

end ProofGap.Exercise2767_2
