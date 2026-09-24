import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.NormNum
import Mathlib.Order.Filter.Tendsto

namespace ProofGap.Exercise1421

noncomputable section

def y (x : ℝ) : ℝ := |x|

theorem gap1 (x : ℝ) (hx : x = 0) : y x = 0 := by
  subst x
  simp [y]

theorem gap2 :
    ∃ δ > 0, ∀ x ∈ Set.Ioo (-δ) δ, x ≠ 0 → y x = |x| := by
  refine ⟨1, by norm_num, ?_⟩
  intro x hx hne
  rfl

theorem gap3 :
    ∃ δ > 0, ∀ x ∈ Set.Ioo (-δ) δ, x ≠ 0 → 0 < |x| := by
  refine ⟨1, by norm_num, ?_⟩
  intro x hx hne
  exact abs_pos.mpr hne

theorem gap4 :
    ∃ δ > 0, ∀ x ∈ Set.Ioo (-δ) δ, x ≠ 0 → 0 < y x := by
  refine ⟨1, by norm_num, ?_⟩
  intro x hx hne
  simpa [y] using (abs_pos.mpr hne)

theorem gap5 : IsMinOn y Set.univ 0 := by
  simp [IsMinOn, IsMinFilter, y]

theorem gap6 : y 0 = 0 := by
  simp [y]

theorem gap7 :
    ¬ ∃ L : ℝ,
      Filter.Tendsto (fun x : ℝ => (|x| - 0) / (x - 0))
        (nhdsWithin 0 {0}ᶜ) (nhds L) := by
  rintro ⟨L, hL⟩
  have hpos_sub : Set.Ioi (0 : ℝ) ⊆ ({0}ᶜ : Set ℝ) := by
    intro x hx
    have hx' : (0 : ℝ) < x := hx
    simpa using hx'.ne'
  have hneg_sub : Set.Iio (0 : ℝ) ⊆ ({0}ᶜ : Set ℝ) := by
    intro x hx
    have hx' : x < (0 : ℝ) := hx
    simpa using hx'.ne
  have hpos := hL.mono_left (nhdsWithin_mono 0 hpos_sub)
  have hneg := hL.mono_left (nhdsWithin_mono 0 hneg_sub)
  have heqpos :
      (fun x : ℝ => (|x| - 0) / (x - 0)) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
        (fun _ : ℝ => 1) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx' : (0 : ℝ) < x := hx
    simp [abs_of_pos hx', hx'.ne']
  have heqneg :
      (fun x : ℝ => (|x| - 0) / (x - 0)) =ᶠ[nhdsWithin 0 (Set.Iio 0)]
        (fun _ : ℝ => -1) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx' : x < (0 : ℝ) := hx
    simp [abs_of_neg hx', hx'.ne]
  have hone :
      Filter.Tendsto (fun x : ℝ => (|x| - 0) / (x - 0))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 : ℝ)) :=
    (tendsto_const_nhds :
      Filter.Tendsto (fun _ : ℝ => (1 : ℝ))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 : ℝ))).congr' heqpos.symm
  have hminus_one :
      Filter.Tendsto (fun x : ℝ => (|x| - 0) / (x - 0))
        (nhdsWithin 0 (Set.Iio 0)) (nhds (-1 : ℝ)) :=
    (tendsto_const_nhds :
      Filter.Tendsto (fun _ : ℝ => (-1 : ℝ))
        (nhdsWithin 0 (Set.Iio 0)) (nhds (-1 : ℝ))).congr' heqneg.symm
  have hL_one : L = (1 : ℝ) := tendsto_nhds_unique hpos hone
  have hL_minus_one : L = (-1 : ℝ) := tendsto_nhds_unique hneg hminus_one
  have hbad : (1 : ℝ) = -1 := hL_one.symm.trans hL_minus_one
  norm_num at hbad

end
end ProofGap.Exercise1421
