import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise2817

noncomputable section

open Filter
open scoped BigOperators Topology

def coefficient (a : ℝ) (n : ℕ) : ℝ :=
  (Nat.factorial n : ℝ) / a ^ (n ^ 2)

def powerTerm (a : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  coefficient a n * x ^ n

def SeriesConvergesAt (a x : ℝ) : Prop :=
  Summable (fun k : ℕ => powerTerm a (k + 1) x)

def HasInfiniteConvergenceRadius (a : ℝ) : Prop :=
  ∀ x : ℝ, SeriesConvergesAt a x

def ratioFormula (a : ℝ) (n : ℕ) : ℝ :=
  a ^ (2 * n + 1) / (n + 1 : ℝ)

theorem gap1 :
    ∀ a : ℝ, 1 < a →
      (fun n : ℕ => |coefficient a (n + 1) / coefficient a (n + 2)|) =
        fun n : ℕ => ratioFormula a (n + 1) := by
  intro a ha
  funext n
  have ha0 : 0 < a := lt_trans (by norm_num) ha
  have hc1 : 0 < coefficient a (n + 1) := by
    unfold coefficient
    positivity
  have hc2 : 0 < coefficient a (n + 2) := by
    unfold coefficient
    positivity
  rw [abs_of_pos (div_pos hc1 hc2)]
  unfold coefficient ratioFormula
  have hexponent :
      (n + 2) ^ 2 = (n + 1) ^ 2 + (2 * (n + 1) + 1) := by ring
  have hfac :
      ((Nat.factorial (n + 2) : ℕ) : ℝ) =
        ((n + 2 : ℕ) : ℝ) * (Nat.factorial (n + 1) : ℝ) := by
    rw [show n + 2 = (n + 1) + 1 by omega, Nat.factorial_succ, Nat.cast_mul]
  rw [hexponent, pow_add, hfac]
  push_cast
  field_simp [ha0.ne']
  <;> ring

theorem gap2 :
    ∀ a : ℝ, 1 < a →
      Tendsto (ratioFormula a) atTop atTop := by
  intro a ha
  have ha0 : 0 < a := lt_trans (by norm_num) ha
  have ha2 : 1 < a ^ 2 := by nlinarith
  have hbase : Tendsto
      (fun n : ℕ => (n : ℝ) ^ 1 / (a ^ 2) ^ n) atTop (𝓝 0) :=
    tendsto_pow_const_div_const_pow_of_one_lt 1 ha2
  have hshift := hbase.comp (tendsto_add_atTop_nat 1)
  have hzero : Tendsto
      (fun n : ℕ => ((n + 1 : ℕ) : ℝ) / a ^ (2 * n + 1))
      atTop (𝓝 0) := by
    have hmul : Tendsto
        (fun n : ℕ => a * (((n + 1 : ℕ) : ℝ) ^ 1 / (a ^ 2) ^ (n + 1)))
        atTop (𝓝 0) := by
      simpa using tendsto_const_nhds.mul hshift
    convert hmul using 1
    funext n
    change ((n + 1 : ℕ) : ℝ) / a ^ (2 * n + 1) =
      a * (((n + 1 : ℕ) : ℝ) ^ 1 / (a ^ 2) ^ (n + 1))
    rw [show (a ^ 2) ^ (n + 1) = a ^ (2 * (n + 1)) by rw [← pow_mul]]
    field_simp [ha0.ne']
    <;> ring
  have hzeroGT : Tendsto
      (fun n : ℕ => ((n + 1 : ℕ) : ℝ) / a ^ (2 * n + 1))
      atTop (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hzero, Filter.Eventually.of_forall (fun n => by
      change 0 < ((n + 1 : ℕ) : ℝ) / a ^ (2 * n + 1)
      positivity)⟩
  have hinv := hzeroGT.inv_tendsto_nhdsGT_zero
  apply hinv.congr'
  filter_upwards with n
  unfold ratioFormula
  have hn : (0 : ℝ) < n + 1 := by positivity
  change ((((n + 1 : ℕ) : ℝ) / a ^ (2 * n + 1))⁻¹) =
    a ^ (2 * n + 1) / ((n : ℝ) + 1)
  field_simp [ha0.ne', hn.ne']
  norm_num [Nat.cast_add, Nat.cast_one]

theorem gap3 :
    ∀ a : ℝ, 1 < a →
      Tendsto
        (fun n : ℕ => |coefficient a (n + 1) / coefficient a (n + 2)|)
        atTop atTop := by
  intro a ha
  rw [gap1 a ha]
  exact (gap2 a ha).comp (tendsto_add_atTop_nat 1)

theorem gap4 :
    ∀ a : ℝ, 1 < a → HasInfiniteConvergenceRadius a := by
  intro a ha
  have ha0 : 0 < a := lt_trans (by norm_num) ha
  unfold HasInfiniteConvergenceRadius SeriesConvergesAt
  intro x
  by_cases hx : x = 0
  · subst x
    simp [powerTerm]
  · let u : ℕ → ℝ := fun n => powerTerm a (n + 1) x
    have hune : ∀ n : ℕ, u n ≠ 0 := by
      intro n
      unfold u powerTerm coefficient
      exact mul_ne_zero
        (div_ne_zero (by positivity) (pow_ne_zero _ ha0.ne'))
        (pow_ne_zero _ hx)
    have hbig : Tendsto (fun n : ℕ => ratioFormula a (n + 1)) atTop atTop :=
      (gap2 a ha).comp (tendsto_add_atTop_nat 1)
    have hinv : Tendsto
        (fun n : ℕ => (ratioFormula a (n + 1))⁻¹) atTop (𝓝 0) :=
      (tendsto_inv_atTop_zero :
        Tendsto (fun y : ℝ => y⁻¹) atTop (𝓝 0)).comp hbig
    have hratioLim : Tendsto
        (fun n : ℕ => |x| * (ratioFormula a (n + 1))⁻¹)
        atTop (𝓝 0) := by
      simpa using tendsto_const_nhds.mul hinv
    have hratioEq :
        (fun n : ℕ => ‖u (n + 1)‖ / ‖u n‖) =
          fun n : ℕ => |x| * (ratioFormula a (n + 1))⁻¹ := by
      funext n
      have hc1 : 0 < coefficient a (n + 1) := by
        unfold coefficient
        positivity
      have hc2 : 0 < coefficient a (n + 2) := by
        unfold coefficient
        positivity
      have hforward :
          coefficient a (n + 1) / coefficient a (n + 2) =
            ratioFormula a (n + 1) := by
        have h := congrFun (gap1 a ha) n
        simpa [abs_of_pos (div_pos hc1 hc2)] using h
      unfold u powerTerm
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul,
        abs_of_pos hc2, abs_of_pos hc1, abs_pow, abs_pow, ← hforward]
      rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
      field_simp [hc1.ne', hc2.ne', abs_ne_zero.mpr hx]
      <;> ring
    change Summable u
    apply summable_of_ratio_test_tendsto_lt_one (by norm_num : (0 : ℝ) < 1)
      (Filter.Eventually.of_forall hune)
    rw [hratioEq]
    exact hratioLim

theorem gap5 :
    ∀ (a x : ℝ), 1 < a → SeriesConvergesAt a x := by
  intro a x ha
  exact gap4 a ha x

theorem gap6 :
    ∀ (a x : ℝ), 1 < a →
      (x ∈ Set.univ ↔ SeriesConvergesAt a x) := by
  intro a x ha
  constructor
  · intro _
    exact gap5 a x ha
  · intro _
    exact Set.mem_univ x

end

end ProofGap.Exercise2817
