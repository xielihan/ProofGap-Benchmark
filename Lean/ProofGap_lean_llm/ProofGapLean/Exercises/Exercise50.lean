import ProofGapLean.Prelude.Sequences
import ProofGapLean.Prelude.Finite
import Mathlib.Analysis.SpecificLimits.Normed

open scoped Topology

/-!
# Exercise 50

Semantic formalization of `proof_gap/exercise_50/{1,2,3}.txt`.
The source ellipses are represented by finite geometric sums.
-/

namespace ProofGap.Exercise50

noncomputable section

def geomSum (a : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), a ^ k

def ratio (a b : ℝ) (n : ℕ) : ℝ :=
  geomSum a n / geomSum b n

def closedRatio (a b : ℝ) (n : ℕ) : ℝ :=
  ((1 - a ^ (n + 1)) / (1 - a)) /
    ((1 - b ^ (n + 1)) / (1 - b))

def SameLimit (u v : ℕ → ℝ) : Prop :=
  ∀ l : ℝ, Tendsto u atTop (𝓝 l) ↔ Tendsto v atTop (𝓝 l)

/-- Source: `proof_gap/exercise_50/1.txt`. -/
theorem gap1
    (a b : ℝ)
    (ha : |a| < 1)
    (hb : |b| < 1) :
    SameLimit (ratio a b) (closedRatio a b) := by
  have hane : a ≠ 1 := by
    rintro rfl
    norm_num at ha
  have hbne : b ≠ 1 := by
    rintro rfl
    norm_num at hb
  have heq : ∀ n, ratio a b n = closedRatio a b n := by
    intro n
    have hga :
        geomSum a n = (1 - a ^ (n + 1)) / (1 - a) := by
      unfold geomSum
      rw [geom_sum_eq hane]
      rw [show 1 - a ^ (n + 1) = -(a ^ (n + 1) - 1) by ring,
        show 1 - a = -(a - 1) by ring, neg_div_neg_eq]
    have hgb :
        geomSum b n = (1 - b ^ (n + 1)) / (1 - b) := by
      unfold geomSum
      rw [geom_sum_eq hbne]
      rw [show 1 - b ^ (n + 1) = -(b ^ (n + 1) - 1) by ring,
        show 1 - b = -(b - 1) by ring, neg_div_neg_eq]
    unfold ratio closedRatio
    rw [hga, hgb]
  intro l
  exact Filter.tendsto_congr heq

/-- Source: `proof_gap/exercise_50/2.txt`. -/
theorem gap2
    (a b : ℝ)
    (ha : |a| < 1)
    (hb : |b| < 1)
    (h1 : SameLimit (ratio a b) (closedRatio a b)) :
    Tendsto (closedRatio a b) atTop (𝓝 ((1 - b) / (1 - a))) := by
  have hane : a ≠ 1 := by
    rintro rfl
    norm_num at ha
  have hbne : b ≠ 1 := by
    rintro rfl
    norm_num at hb
  have haone : 1 - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hane)
  have hbone : 1 - b ≠ 0 := sub_ne_zero.mpr (Ne.symm hbne)
  have hpa :
      Tendsto (fun n : ℕ => a ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one ha
  have hpb :
      Tendsto (fun n : ℕ => b ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one hb
  have hpas :
      Tendsto (fun n : ℕ => a ^ (n + 1)) atTop (𝓝 0) := by
    simpa [pow_succ] using hpa.mul_const a
  have hpbs :
      Tendsto (fun n : ℕ => b ^ (n + 1)) atTop (𝓝 0) := by
    simpa [pow_succ] using hpb.mul_const b
  have hca :
      Tendsto (fun n : ℕ => (1 - a ^ (n + 1)) / (1 - a))
        atTop (𝓝 (1 / (1 - a))) := by
    simpa using
      ((tendsto_const_nhds (x := (1 : ℝ))).sub hpas).div
        (tendsto_const_nhds (x := 1 - a)) haone
  have hcb :
      Tendsto (fun n : ℕ => (1 - b ^ (n + 1)) / (1 - b))
        atTop (𝓝 (1 / (1 - b))) := by
    simpa using
      ((tendsto_const_nhds (x := (1 : ℝ))).sub hpbs).div
        (tendsto_const_nhds (x := 1 - b)) hbone
  have hfinal := hca.div hcb (one_div_ne_zero hbone)
  convert hfinal using 1
  field_simp [haone, hbone]

/-- Source: `proof_gap/exercise_50/3.txt`. -/
theorem gap3
    (a b : ℝ)
    (ha : |a| < 1)
    (hb : |b| < 1)
    (h1 : SameLimit (ratio a b) (closedRatio a b))
    (h2 : Tendsto (closedRatio a b) atTop (𝓝 ((1 - b) / (1 - a)))) :
    Tendsto (ratio a b) atTop (𝓝 ((1 - b) / (1 - a))) := by
  exact (h1 ((1 - b) / (1 - a))).mpr h2

end

end ProofGap.Exercise50
