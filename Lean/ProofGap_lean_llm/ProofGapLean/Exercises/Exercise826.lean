import ProofGapLean.Prelude.Sequences
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise826

noncomputable section

def secantSlope (h : ℝ) : ℝ := ((1 + h) ^ 3 - 1 ^ 3) / h

/-- Source: `proof_gap/exercise_826/1.txt`; type the secant slope explicitly. -/
theorem gap1 (h : ℝ) : secantSlope h = ((1 + h) ^ 3 - 1 ^ 3) / h := by
  rfl

/-- Source: `proof_gap/exercise_826/2.txt`; add the omitted `h≠0`. -/
theorem gap2 (h : ℝ) (hh : h ≠ 0) :
    ((1 + h) ^ 3 - 1 ^ 3) / h = 3 + 3 * h + h ^ 2 := by
  field_simp [hh]
  ring

/-- Source: `proof_gap/exercise_826/3.txt`; add the omitted `h≠0`. -/
theorem gap3 (h : ℝ) (hh : h ≠ 0) :
    secantSlope h = 3 + 3 * h + h ^ 2 := by
  exact (gap1 h).trans (gap2 h hh)

/-- Source: `proof_gap/exercise_826/4.txt`; specialize the source value `h=0.001`. -/
theorem gap4 : secantSlope 0.001 = 3 + 3 * 0.001 + 0.001 ^ 2 := by
  exact gap3 0.001 (by norm_num)

/-- Source: `proof_gap/exercise_826/5.txt`. -/
theorem gap5 : (3 : ℝ) + 3 * 0.001 + 0.001 ^ 2 = 3.003001 := by
  norm_num

/-- Source: `proof_gap/exercise_826/6.txt`. -/
theorem gap6 : secantSlope 0.001 = 3.003001 := by
  exact gap4.trans gap5

/-- Source: `proof_gap/exercise_826/7.txt`; express the limit by `Tendsto`. -/
theorem gap7 (l₁ : ℝ)
    (hl : Filter.Tendsto secantSlope (nhdsWithin 0 {0}ᶜ) (nhds l₁)) :
    Filter.Tendsto secantSlope (nhdsWithin 0 {0}ᶜ) (nhds l₁) := by
  exact hl

/-- Source: `proof_gap/exercise_826/8.txt`; express the punctured limit by `Tendsto`. -/
theorem gap8 :
    Filter.Tendsto secantSlope (nhdsWithin 0 {0}ᶜ) (nhds 3) := by
  let F : Filter ℝ := nhdsWithin (0 : ℝ) (({0} : Set ℝ)ᶜ)
  have hx : Filter.Tendsto (fun h : ℝ => h) F (nhds 0) := by
    change Filter.map (fun h : ℝ => h) F ≤ nhds 0
    intro s hs
    change s ∈ F
    exact (inf_le_left : F ≤ nhds 0) hs
  have hp :
      Filter.Tendsto (fun h : ℝ => 3 + 3 * h + h * h) F
        (nhds (3 + 3 * 0 + 0 * 0)) :=
    (tendsto_const_nhds.add (tendsto_const_nhds.mul hx)).add (hx.mul hx)
  have hmem : ∀ᶠ h : ℝ in F, h ∈ (({0} : Set ℝ)ᶜ) := by
    exact self_mem_nhdsWithin
  have heq :
      secantSlope =ᶠ[F] (fun h : ℝ => 3 + 3 * h + h ^ 2) :=
    Filter.Eventually.mono hmem
      (fun (h : ℝ) (hh : h ∈ (({0} : Set ℝ)ᶜ)) =>
        gap3 h (by
          simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hh))
  have hpoly :
      Filter.Tendsto (fun h : ℝ => 3 + 3 * h + h ^ 2) F (nhds 3) := by
    simpa [pow_two] using hp
  exact Filter.Tendsto.congr' heq.symm hpoly

/-- Source: `proof_gap/exercise_826/9.txt`. -/
theorem gap9 (l₁ : ℝ)
    (hl : Filter.Tendsto secantSlope (nhdsWithin 0 {0}ᶜ) (nhds l₁)) :
    l₁ = 3 := by
  have hsub : Set.Ioi (0 : ℝ) ⊆ {0}ᶜ := by
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact ne_of_gt hx
  letI : Filter.NeBot (nhdsWithin (0 : ℝ) {0}ᶜ) :=
    Filter.NeBot.mono (by infer_instance) (nhdsWithin_mono 0 hsub)
  exact tendsto_nhds_unique hl gap8

end

end ProofGap.Exercise826
