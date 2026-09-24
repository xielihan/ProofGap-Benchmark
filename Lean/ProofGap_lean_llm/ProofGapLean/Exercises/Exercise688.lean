import ProofGapLean.Prelude.Sequences
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise688

noncomputable section

def y (x : ℝ) : ℝ := (1 + x) / (1 + x ^ 3)
def SingularPoint (f : ℝ → ℝ) (a : ℝ) : Prop := ¬ ContinuousAt f a

/-- Source: `proof_gap/exercise_688/1.txt`; use the punctured limit at the removable singularity. -/
private theorem rational_limit_at_neg_one :
    Filter.Tendsto (fun x : ℝ => 1 / (x ^ 2 - x + 1))
      (nhds (-1)) (nhds (1 / 3 : ℝ)) := by
  have hden :
      ContinuousAt (fun x : ℝ => x ^ 2 - x + 1) (-1) :=
    ((continuousAt_id.pow 2).sub continuousAt_id).add continuousAt_const
  have hne : ((-1 : ℝ) ^ 2 - (-1) + 1) ≠ 0 := by
    norm_num
  have hcont :
      ContinuousAt (fun x : ℝ => 1 / (x ^ 2 - x + 1)) (-1) := by
    exact continuousAt_const.div hden hne
  change Filter.Tendsto (fun x : ℝ => 1 / (x ^ 2 - x + 1))
    (nhds (-1))
    (nhds (1 / (((-1 : ℝ) ^ 2 - (-1) + 1)))) at hcont
  norm_num at hcont
  simpa only [one_div] using hcont

theorem gap1 (L : ℝ) :
    Filter.Tendsto y (nhdsWithin (-1) ({-1} : Set ℝ)ᶜ) (nhds L) ↔
      Filter.Tendsto (fun x : ℝ => 1 / (x ^ 2 - x + 1))
        (nhds (-1)) (nhds L) := by
  have hEq :
      y =ᶠ[nhdsWithin (-1) ({-1} : Set ℝ)ᶜ]
        (fun x : ℝ => 1 / (x ^ 2 - x + 1)) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hxne : x ≠ (-1 : ℝ) := by
      simpa using hx
    have hxone : 1 + x ≠ 0 := by
      intro h
      apply hxne
      linarith
    have hqpos : 0 < x ^ 2 - x + 1 := by
      nlinarith [sq_nonneg (2 * x - 1)]
    have hq : x ^ 2 - x + 1 ≠ 0 := ne_of_gt hqpos
    dsimp only [y]
    rw [show 1 + x ^ 3 = (1 + x) * (x ^ 2 - x + 1) by ring]
    field_simp [hxone, hq]
  constructor
  · intro hy
    have hgL :
        Filter.Tendsto (fun x : ℝ => 1 / (x ^ 2 - x + 1))
          (nhdsWithin (-1) ({-1} : Set ℝ)ᶜ) (nhds L) :=
      (Filter.tendsto_congr' hEq).mp hy
    have hgWithin :
        Filter.Tendsto (fun x : ℝ => 1 / (x ^ 2 - x + 1))
          (nhdsWithin (-1) ({-1} : Set ℝ)ᶜ) (nhds (1 / 3 : ℝ)) :=
      rational_limit_at_neg_one.mono_left inf_le_left
    have hL : L = (1 / 3 : ℝ) :=
      tendsto_nhds_unique hgL hgWithin
    simpa [hL] using rational_limit_at_neg_one
  · intro hg
    exact (Filter.tendsto_congr' hEq).mpr (hg.mono_left inf_le_left)

/-- Source: `proof_gap/exercise_688/2.txt`. -/
theorem gap2 :
    Filter.Tendsto (fun x : ℝ => 1 / (x ^ 2 - x + 1))
      (nhds (-1)) (nhds (1 / 3 : ℝ)) := by
  exact rational_limit_at_neg_one

/-- Source: `proof_gap/exercise_688/3.txt`. -/
theorem gap3 :
    Filter.Tendsto y (nhdsWithin (-1) ({-1} : Set ℝ)ᶜ)
      (nhds (1 / 3 : ℝ)) := by
  exact (gap1 (1 / 3 : ℝ)).2 gap2

/-- Source: `proof_gap/exercise_688/4.txt`; bind the actual singular point rather than a free `x`. -/
theorem gap4 : SingularPoint y (-1) := by
  rw [SingularPoint]
  intro hy
  have hyWithin :
      Filter.Tendsto y (nhdsWithin (-1) ({-1} : Set ℝ)ᶜ)
        (nhds (y (-1))) :=
    hy.mono_left inf_le_left
  have hy0 :
      Filter.Tendsto y (nhdsWithin (-1) ({-1} : Set ℝ)ᶜ)
        (nhds (0 : ℝ)) := by
    convert hyWithin using 1 <;> norm_num [y]
  have hg0 :
      Filter.Tendsto (fun x : ℝ => 1 / (x ^ 2 - x + 1))
        (nhds (-1)) (nhds (0 : ℝ)) :=
    (gap1 0).mp hy0
  have hfalse : (0 : ℝ) = 1 / 3 :=
    tendsto_nhds_unique hg0 gap2
  norm_num at hfalse

/-- Source: `proof_gap/exercise_688/5.txt`; state existence of the finite punctured limit. -/
theorem gap5 :
    ∃ L : ℝ, Filter.Tendsto y (nhdsWithin (-1) ({-1} : Set ℝ)ᶜ)
      (nhds L) := by
  exact ⟨1 / 3, gap3⟩

/-- Source: `proof_gap/exercise_688/6.txt`. -/
theorem gap6 (x : ℝ) (hx : x ∈ ({-1} : Set ℝ)) :
    SingularPoint y x := by
  have hx' : x = (-1 : ℝ) := by
    simpa only [Set.mem_singleton_iff] using hx
  rw [hx']
  exact gap4

end

end ProofGap.Exercise688
