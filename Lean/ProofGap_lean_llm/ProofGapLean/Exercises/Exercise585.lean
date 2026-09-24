import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise585

noncomputable section

def original (x h : ℝ) : ℝ := (Real.arctan (x + h) - Real.arctan x) / h
def transformed (x h : ℝ) : ℝ :=
  (Real.arctan (h / (1 + x * (x + h))) / (h / (1 + x * (x + h)))) *
    (1 / (1 + x * (x + h)))
def HasLimitAtZero (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds L)

/-- Source: `proof_gap/exercise_585/1.txt`. -/
theorem gap1 (x L : ℝ) :
    HasLimitAtZero (original x) L ↔ HasLimitAtZero (transformed x) L := by
  unfold HasLimitAtZero
  have heq :
      original x =ᶠ[nhdsWithin 0 ({0} : Set ℝ)ᶜ] transformed x := by
    have hdcont :
        ContinuousAt (fun h : ℝ => 1 + x * (x + h)) 0 :=
      continuousAt_const.add
        (continuousAt_const.mul (continuousAt_const.add continuousAt_id))
    have hd0 : 0 < 1 + x * (x + 0) := by
      nlinarith [sq_nonneg x]
    have hd :
        ∀ᶠ h : ℝ in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
          0 < 1 + x * (x + h) :=
      (hdcont.tendsto.mono_left inf_le_left) (Ioi_mem_nhds hd0)
    have hn :
        ∀ᶠ h : ℝ in nhdsWithin 0 ({0} : Set ℝ)ᶜ, h ≠ 0 := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using
        (self_mem_nhdsWithin :
          ∀ᶠ h : ℝ in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
            h ∈ ({0} : Set ℝ)ᶜ)
    filter_upwards [hd, hn] with h hdh hh
    have hp : (x + h) * (-x) < 1 := by
      nlinarith [hdh]
    have ha0 :
        Real.arctan (x + h) + Real.arctan (-x) =
          Real.arctan (((x + h) + (-x)) / (1 - (x + h) * (-x))) :=
      Real.arctan_add hp
    have ha :
        Real.arctan (x + h) - Real.arctan x =
          Real.arctan (h / (1 + x * (x + h))) := by
      calc
        Real.arctan (x + h) - Real.arctan x =
            Real.arctan (x + h) + Real.arctan (-x) := by
              rw [Real.arctan_neg]
              ring
        _ = Real.arctan (h / (1 + x * (x + h))) := by
              convert ha0 using 1 <;> ring_nf
    have hdne : 1 + x * (x + h) ≠ 0 := ne_of_gt hdh
    have hqne : h / (1 + x * (x + h)) ≠ 0 := div_ne_zero hh hdne
    unfold original transformed
    rw [ha]
    field_simp [hh, hdne, hqne]
  constructor
  · intro horiginal
    exact horiginal.congr' heq
  · intro htransformed
    exact htransformed.congr' heq.symm

/-- Source: `proof_gap/exercise_585/2.txt`. -/
theorem gap2 (x : ℝ) :
    HasLimitAtZero (transformed x) (1 / (1 + x ^ 2)) := by
  apply (gap1 x (1 / (1 + x ^ 2))).mp
  unfold HasLimitAtZero
  have hs := (Real.hasDerivAt_arctan x).tendsto_slope_zero
  have heq :
      (fun h : ℝ => h⁻¹ * (Real.arctan (x + h) - Real.arctan x))
        =ᶠ[nhdsWithin 0 ({0} : Set ℝ)ᶜ] original x := by
    apply Filter.Eventually.of_forall
    intro h
    unfold original
    rw [div_eq_mul_inv]
    exact mul_comm _ _
  have ht := hs.congr' heq
  simpa only [one_div] using ht

/-- Source: `proof_gap/exercise_585/3.txt`. -/
theorem gap3 (x : ℝ) :
    HasLimitAtZero (original x) (1 / (1 + x ^ 2)) := by
  exact (gap1 x (1 / (1 + x ^ 2))).mpr (gap2 x)

end

end ProofGap.Exercise585
