import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecificLimits.Normed

namespace ProofGap.Exercise2815

noncomputable section

open Filter
open scoped BigOperators Topology

def coefficient (a : ℝ) (n : ℕ) : ℝ :=
  a ^ (n ^ 2)

def powerTerm (a : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  coefficient a n * x ^ n

def SeriesConvergesAt (a x : ℝ) : Prop :=
  Summable (fun k : ℕ => powerTerm a (k + 1) x)

def HasInfiniteConvergenceRadius (a : ℝ) : Prop :=
  ∀ x : ℝ, SeriesConvergesAt a x

def ratioFormula (a : ℝ) (n : ℕ) : ℝ :=
  1 / a ^ (2 * n + 1)

theorem gap1 :
    ∀ a : ℝ, 0 < a → a < 1 →
      (fun n : ℕ => |coefficient a (n + 1) / coefficient a (n + 2)|) =
        fun n : ℕ => ratioFormula a (n + 1) := by
  intro a ha ha1
  funext n
  unfold coefficient ratioFormula
  rw [abs_of_pos (div_pos (pow_pos ha _) (pow_pos ha _))]
  have hexponent :
      (n + 2) ^ 2 = (n + 1) ^ 2 + (2 * (n + 1) + 1) := by
    ring
  rw [hexponent, pow_add]
  field_simp [ha.ne']

theorem gap2 :
    ∀ a : ℝ, 0 < a → a < 1 →
      Tendsto (ratioFormula a) atTop atTop := by
  intro a ha ha1
  have hexponent : Tendsto (fun n : ℕ => 2 * n + 1) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro N
    refine Filter.eventually_atTop.2 ⟨N, ?_⟩
    intro n hn
    omega
  have hzero : Tendsto (fun n : ℕ => a ^ (2 * n + 1)) atTop (nhds 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one ha.le ha1).comp hexponent
  have hzeroGT : Tendsto (fun n : ℕ => a ^ (2 * n + 1))
      atTop (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hzero, ?_⟩
    exact Filter.Eventually.of_forall (fun n => pow_pos ha _)
  apply hzeroGT.inv_tendsto_nhdsGT_zero.congr'
  exact Filter.Eventually.of_forall (fun n => by
    simp [ratioFormula, one_div])

theorem gap3 :
    ∀ a : ℝ, 0 < a → a < 1 →
      Tendsto
        (fun n : ℕ => |coefficient a (n + 1) / coefficient a (n + 2)|)
        atTop atTop := by
  intro a ha ha1
  rw [gap1 a ha ha1]
  exact (gap2 a ha ha1).comp (tendsto_add_atTop_nat 1)

theorem gap4 :
    ∀ a : ℝ, 0 < a → a < 1 → HasInfiniteConvergenceRadius a := by
  intro a ha ha1
  unfold HasInfiniteConvergenceRadius SeriesConvergesAt
  intro x
  by_cases hx : x = 0
  · subst x
    simp [powerTerm]
  · let f : ℕ → ℝ := fun n => powerTerm a (n + 1) x
    have hfne : ∀ n : ℕ, f n ≠ 0 := by
      intro n
      exact mul_ne_zero (pow_ne_zero _ ha.ne') (pow_ne_zero _ hx)
    have hratio_eq :
        (fun n : ℕ => ‖f (n + 1)‖ / ‖f n‖) =
          fun n : ℕ => |x| * a ^ (2 * n + 3) := by
      funext n
      have hexponent :
          (n + 2) ^ 2 = (n + 1) ^ 2 + (2 * n + 3) := by
        ring
      have hrec : f (n + 1) = a ^ (2 * n + 3) * x * f n := by
        dsimp [f, powerTerm, coefficient]
        have hxpow : x ^ (n + 2) = x * x ^ (n + 1) := by
          rw [show n + 2 = 1 + (n + 1) by omega, pow_add, pow_one]
        rw [hexponent, pow_add, hxpow]
        ring
      rw [hrec, norm_mul, norm_mul]
      have hfn : ‖f n‖ ≠ 0 := norm_ne_zero_iff.mpr (hfne n)
      field_simp [hfn]
      simp [Real.norm_eq_abs, abs_of_pos ha, abs_mul, mul_comm]
    have hexponent : Tendsto (fun n : ℕ => 2 * n + 3) atTop atTop := by
      refine tendsto_atTop.2 ?_
      intro N
      refine Filter.eventually_atTop.2 ⟨N, ?_⟩
      intro n hn
      omega
    have hpow : Tendsto (fun n : ℕ => a ^ (2 * n + 3)) atTop (nhds 0) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one ha.le ha1).comp hexponent
    have hratio : Tendsto (fun n : ℕ => |x| * a ^ (2 * n + 3))
        atTop (nhds 0) := by
      simpa using tendsto_const_nhds.mul hpow
    change Summable f
    apply summable_of_ratio_test_tendsto_lt_one (by norm_num : (0 : ℝ) < 1)
      (Filter.Eventually.of_forall hfne)
    rw [hratio_eq]
    exact hratio

theorem gap5 :
    ∀ (a x : ℝ), 0 < a → a < 1 → SeriesConvergesAt a x := by
  intro a x ha ha1
  exact gap4 a ha ha1 x

theorem gap6 :
    ∀ (a x : ℝ), 0 < a → a < 1 →
      (x ∈ Set.univ ↔ SeriesConvergesAt a x) := by
  intro a x ha ha1
  constructor
  · intro _
    exact gap5 a x ha ha1
  · intro _
    exact Set.mem_univ x

end

end ProofGap.Exercise2815
