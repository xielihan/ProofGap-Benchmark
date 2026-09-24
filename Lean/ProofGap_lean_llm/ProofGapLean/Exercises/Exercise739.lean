import ProofGapLean.Prelude.Sequences

namespace ProofGap.Exercise739

noncomputable section

def core (x : ℝ) : ℝ := 1 / (1 - x)

/-- Source: `proof_gap/exercise_739/1.txt`. -/
theorem gap1 (f : ℝ → ℝ) (hf : ∀ x : ℝ, f x = core x) :
    Filter.Tendsto f (nhdsWithin 1 (Set.Ioi 1)) atBot := by
  have hfun : f = fun x : ℝ => (1 - x)⁻¹ := by
    funext x
    simpa [core] using hf x
  rw [hfun]
  have hcont : ContinuousAt (fun x : ℝ => 1 - x) 1 :=
    continuousAt_const.sub continuousAt_id
  change Filter.Tendsto (fun x : ℝ => 1 - x) (nhds 1) (nhds (1 - 1)) at hcont
  have hglobal :
      Filter.Tendsto (fun x : ℝ => 1 - x) (nhds 1) (nhds 0) := by
    simpa using hcont
  have hnear :
      Filter.Tendsto (fun x : ℝ => 1 - x)
        (nhdsWithin 1 (Set.Ioi 1)) (nhds 0) := by
    apply hglobal.mono_left
    exact inf_le_left
  have hsub :
      Filter.Tendsto (fun x : ℝ => 1 - x)
        (nhdsWithin 1 (Set.Ioi 1)) (nhdsWithin 0 (Set.Iio 0)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hnear, ?_⟩
    exact Filter.Eventually.mono
      (show ∀ᶠ x : ℝ in nhdsWithin 1 (Set.Ioi 1), x ∈ Set.Ioi 1 from
        (self_mem_nhdsWithin : Set.Ioi (1 : ℝ) ∈ nhdsWithin 1 (Set.Ioi 1)))
      (fun x hx => by
        change 1 - x < 0
        change 1 < x at hx
        exact sub_neg.mpr hx)
  simpa only [Function.comp_apply] using
    ((tendsto_inv_nhdsLT_zero :
      Filter.Tendsto (fun x : ℝ => x⁻¹)
        (nhdsWithin 0 (Set.Iio 0)) atBot).comp hsub)

/-- Source: `proof_gap/exercise_739/2.txt`. -/
theorem gap2 (f : ℝ → ℝ) (hf : ∀ x : ℝ, f x = core x) :
    Filter.Tendsto f (nhdsWithin 1 (Set.Iio 1)) atTop := by
  have hfun : f = fun x : ℝ => (1 - x)⁻¹ := by
    funext x
    simpa [core] using hf x
  rw [hfun]
  have hcont : ContinuousAt (fun x : ℝ => 1 - x) 1 :=
    continuousAt_const.sub continuousAt_id
  change Filter.Tendsto (fun x : ℝ => 1 - x) (nhds 1) (nhds (1 - 1)) at hcont
  have hglobal :
      Filter.Tendsto (fun x : ℝ => 1 - x) (nhds 1) (nhds 0) := by
    simpa using hcont
  have hnear :
      Filter.Tendsto (fun x : ℝ => 1 - x)
        (nhdsWithin 1 (Set.Iio 1)) (nhds 0) := by
    apply hglobal.mono_left
    exact inf_le_left
  have hsub :
      Filter.Tendsto (fun x : ℝ => 1 - x)
        (nhdsWithin 1 (Set.Iio 1)) (nhdsWithin 0 (Set.Ioi 0)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hnear, ?_⟩
    exact Filter.Eventually.mono
      (show ∀ᶠ x : ℝ in nhdsWithin 1 (Set.Iio 1), x ∈ Set.Iio 1 from
        (self_mem_nhdsWithin : Set.Iio (1 : ℝ) ∈ nhdsWithin 1 (Set.Iio 1)))
      (fun x hx => by
        change 0 < 1 - x
        change x < 1 at hx
        exact sub_pos.mpr hx)
  simpa only [Function.comp_apply] using
    ((tendsto_inv_nhdsGT_zero :
      Filter.Tendsto (fun x : ℝ => x⁻¹)
        (nhdsWithin 0 (Set.Ioi 0)) atTop).comp hsub)

/-- Source: `proof_gap/exercise_739/3.txt`; make explicit that no assigned
value at `1` can make the given totalized formula continuous. -/
theorem gap3 (f : ℝ → ℝ) (hf : ∀ x : ℝ, f x = core x) :
    ¬ ∃ c : ℝ, f 1 = c ∧ ContinuousAt f 1 := by
  intro hex
  obtain ⟨c, hfc, hc⟩ := hex
  change Filter.Tendsto f (nhds 1) (nhds (f 1)) at hc
  rw [hfc] at hc
  have hcont_right :
      Filter.Tendsto f (nhdsWithin 1 (Set.Ioi 1)) (nhds c) := by
    apply hc.mono_left
    exact inf_le_left
  have hle :
      ∀ᶠ x in nhdsWithin 1 (Set.Ioi 1), f x ≤ c - 1 :=
    (Filter.tendsto_atBot.1 (gap1 f hf)) (c - 1)
  have hgt :
      ∀ᶠ x in nhdsWithin 1 (Set.Ioi 1), c - 1 < f x :=
    hcont_right (Ioi_mem_nhds (sub_lt_self c zero_lt_one))
  obtain ⟨x, hxle, hxgt⟩ := (hle.and hgt).exists
  exact (not_lt_of_ge hxle) hxgt

/-- Source: `proof_gap/exercise_739/4.txt`. -/
theorem gap4 (f : ℝ → ℝ) (hf : ∀ x : ℝ, f x = core x) :
    ∀ c : ℝ, f 1 = c → ¬ ContinuousAt f 1 := by
  intro c hfc hc
  exact gap3 f hf ⟨c, hfc, hc⟩

end

end ProofGap.Exercise739
