import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.Linarith

namespace ProofGap.Exercise748

noncomputable section

noncomputable def runningInf (f : ℝ → ℝ) (a x : ℝ) : ℝ :=
  sInf (f '' Set.Icc a x)

noncomputable def runningSup (f : ℝ → ℝ) (a x : ℝ) : ℝ :=
  sSup (f '' Set.Icc a x)

/-- Source: `proof_gap/exercise_748/1.txt`. -/
private theorem runningSup_continuousOn_aux (f : ℝ → ℝ) (a b : ℝ)
    (hf : ContinuousOn f (Set.Icc a b)) :
    ContinuousOn (runningSup f a) (Set.Icc a b) := by
  intro x hx
  have hB : BddAbove (f '' Set.Icc a b) :=
    (isCompact_Icc.image_of_continuousOn hf).bddAbove
  have hbdd : ∀ t ∈ Set.Icc a b, BddAbove (f '' Set.Icc a t) := by
    intro t ht
    apply hB.mono
    apply Set.image_mono
    intro z hz
    exact ⟨hz.1, hz.2.trans ht.2⟩
  have hne : ∀ t ∈ Set.Icc a b, (f '' Set.Icc a t).Nonempty := by
    intro t ht
    exact ⟨f a, ⟨a, ⟨le_rfl, ht.1⟩, rfl⟩⟩
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  let q : ℝ := ε / 4
  have hq : 0 < q := by
    dsimp [q]
    linarith
  have hqeq : q = ε / 4 := rfl
  obtain ⟨δ, hδ, hfδ⟩ :=
    (Metric.continuousWithinAt_iff.mp (hf x hx)) q hq
  refine ⟨δ, hδ, ?_⟩
  intro y hy hyd
  have hfx_le : f x ≤ runningSup f a x := by
    unfold runningSup
    exact le_csSup (hbdd x hx) ⟨x, ⟨hx.1, le_rfl⟩, rfl⟩
  have hfy_le : f y ≤ runningSup f a y := by
    unfold runningSup
    exact le_csSup (hbdd y hy) ⟨y, ⟨hy.1, le_rfl⟩, rfl⟩
  have hy_upper : runningSup f a y ≤ runningSup f a x + q := by
    change sSup (f '' Set.Icc a y) ≤ runningSup f a x + q
    apply csSup_le (hne y hy)
    rintro v ⟨z, hz, rfl⟩
    by_cases hzx : z ≤ x
    · have hz_le : f z ≤ runningSup f a x := by
        unfold runningSup
        exact le_csSup (hbdd x hx) ⟨z, ⟨hz.1, hzx⟩, rfl⟩
      linarith
    · have hxz : x < z := lt_of_not_ge hzx
      have hzab : z ∈ Set.Icc a b := ⟨hz.1, hz.2.trans hy.2⟩
      have hxy : x ≤ y := le_trans (le_of_lt hxz) hz.2
      have hdist_zx : dist z x < δ := by
        rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (le_of_lt hxz))]
        rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hxy)] at hyd
        linarith [hz.2]
      have hfclose := hfδ hzab hdist_zx
      have hfclose' : |f z - f x| < q := by
        simpa [Real.dist_eq] using hfclose
      have hfz_lt : f z < f x + q := by
        linarith [(abs_lt.mp hfclose').2]
      linarith
  have hx_upper : runningSup f a x ≤ runningSup f a y + 2 * q := by
    change sSup (f '' Set.Icc a x) ≤ runningSup f a y + 2 * q
    apply csSup_le (hne x hx)
    rintro v ⟨z, hz, rfl⟩
    by_cases hzy : z ≤ y
    · have hz_le : f z ≤ runningSup f a y := by
        unfold runningSup
        exact le_csSup (hbdd y hy) ⟨z, ⟨hz.1, hzy⟩, rfl⟩
      linarith
    · have hyz : y < z := lt_of_not_ge hzy
      have hyx : y ≤ x := le_trans (le_of_lt hyz) hz.2
      have hzab : z ∈ Set.Icc a b := ⟨hz.1, hz.2.trans hx.2⟩
      have hdist_zx : dist z x < δ := by
        rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hz.2)]
        rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hyx)] at hyd
        linarith
      have hzclose := hfδ hzab hdist_zx
      have hyclose := hfδ hy hyd
      have hzclose' : |f z - f x| < q := by
        simpa [Real.dist_eq] using hzclose
      have hyclose' : |f y - f x| < q := by
        simpa [Real.dist_eq] using hyclose
      have hfz_upper : f z - f x < q := (abs_lt.mp hzclose').2
      have hfy_lower : -q < f y - f x := (abs_lt.mp hyclose').1
      linarith
  rw [Real.dist_eq]
  apply (abs_lt).2
  constructor <;> linarith [hy_upper, hx_upper, hqeq]

theorem gap1 (f : ℝ → ℝ) (a b : ℝ) (hf : ContinuousOn f (Set.Icc a b)) :
    ∀ x₀ ∈ Set.Icc a b, ∀ ε > 0,
      ∃ δ > 0, ∀ x ∈ Set.Icc a b,
        |x - x₀| < δ → |f x - f x₀| < ε := by
  intro x₀ hx₀ ε hε
  have hcont := hf x₀ hx₀
  rw [Metric.continuousWithinAt_iff] at hcont
  obtain ⟨δ, hδ, hmain⟩ := hcont ε hε
  refine ⟨δ, hδ, ?_⟩
  intro x hx hdist
  have hout := hmain hx (by simpa [Real.dist_eq] using hdist)
  simpa [Real.dist_eq] using hout

/-- Source: `proof_gap/exercise_748/2.txt`; move `δ` under `x₀, ε`. -/
theorem gap2 (f : ℝ → ℝ) (a b : ℝ) (hf : ContinuousOn f (Set.Icc a b)) :
    ∀ x₀ ∈ Set.Icc a b, ∀ ε > 0,
      ∃ δ > 0, ∀ x ∈ Set.Icc a b,
        x₀ < x → x < x₀ + δ → f x > f x₀ - ε := by
  intro x₀ hx₀ ε hε
  obtain ⟨δ, hδ, hmain⟩ := gap1 f a b hf x₀ hx₀ ε hε
  refine ⟨δ, hδ, ?_⟩
  intro x hx hxgt hxlt
  have hdist : |x - x₀| < δ := by
    rw [abs_of_pos (sub_pos.mpr hxgt)]
    linarith
  have hclose := hmain x hx hdist
  linarith [(abs_lt.mp hclose).1]

/-- Source: `proof_gap/exercise_748/3.txt`; remove the irrelevant existential `δ`. -/
theorem gap3 (f : ℝ → ℝ) (a x₀ ε : ℝ) (ha : a ≤ x₀)
    (hbdd : BddBelow (f '' Set.Icc a x₀)) :
    f x₀ - ε ≥ runningInf f a x₀ - ε := by
  unfold runningInf
  have hle : sInf (f '' Set.Icc a x₀) ≤ f x₀ :=
    csInf_le hbdd ⟨x₀, ⟨ha, le_rfl⟩, rfl⟩
  linarith

/-- Source: `proof_gap/exercise_748/4.txt`; move `δ` under `x₀, ε`. -/
theorem gap4 (f : ℝ → ℝ) (a b : ℝ)
    (hright : ∀ x₀ ∈ Set.Icc a b, ∀ ε > 0,
      ∃ δ > 0, ∀ x, x₀ < x → x < x₀ + δ → f x > f x₀ - ε) :
    (hbdd : ∀ x₀ ∈ Set.Icc a b, BddBelow (f '' Set.Icc a x₀)) →
    ∀ x₀ ∈ Set.Icc a b, ∀ ε > 0,
      ∃ δ > 0, ∀ x, x₀ < x → x < x₀ + δ →
        f x > runningInf f a x₀ - ε := by
  intro hbdd x₀ hx₀ ε hε
  obtain ⟨δ, hδ, hmain⟩ := hright x₀ hx₀ ε hε
  refine ⟨δ, hδ, ?_⟩
  intro x hxgt hxlt
  have hpoint := hmain x hxgt hxlt
  have hinf := gap3 f a x₀ ε hx₀.1 (hbdd x₀ hx₀)
  linarith

/-- Source: `proof_gap/exercise_748/5.txt`; move `δ` under `x₀, ε`. -/
theorem gap5 (f : ℝ → ℝ) (a b : ℝ)
    (hpoint : ∀ x₀ ∈ Set.Icc a b, ∀ ε > 0,
      ∃ δ > 0, ∀ x, x₀ < x → x < x₀ + δ →
        f x > runningInf f a x₀ - ε) :
    ∀ x₀ ∈ Set.Icc a b, ∀ ε > 0,
      ∃ δ > 0, ∀ x, x₀ < x → x < x₀ + δ →
        runningInf f a x ≥ runningInf f a x₀ - ε := by
  intro x₀ hx₀ ε hε
  obtain ⟨δ, hδ, hpointδ⟩ := hpoint x₀ hx₀ ε hε
  refine ⟨δ, hδ, ?_⟩
  intro x hxx₀ hxxδ
  change sInf (f '' Set.Icc a x₀) - ε ≤ sInf (f '' Set.Icc a x)
  have hsubset : f '' Set.Icc a x₀ ⊆ f '' Set.Icc a x := by
    rintro y ⟨z, hz, rfl⟩
    exact ⟨z, ⟨hz.1, hz.2.trans (le_of_lt hxx₀)⟩, rfl⟩
  by_cases hb : BddBelow (f '' Set.Icc a x₀)
  · apply le_csInf
    · exact ⟨f a, ⟨a, ⟨le_rfl, hx₀.1.trans (le_of_lt hxx₀)⟩, rfl⟩⟩
    · rintro y ⟨z, hz, rfl⟩
      by_cases hzx₀ : z ≤ x₀
      · have hzmem : f z ∈ f '' Set.Icc a x₀ :=
          ⟨z, ⟨hz.1, hzx₀⟩, rfl⟩
        have hzlower : sInf (f '' Set.Icc a x₀) ≤ f z := csInf_le hb hzmem
        exact le_trans (sub_le_self _ (le_of_lt hε)) hzlower
      · have hx₀z : x₀ < z := lt_of_not_ge hzx₀
        have hzδ : z < x₀ + δ := lt_of_le_of_lt hz.2 hxxδ
        have hzpoint : sInf (f '' Set.Icc a x₀) - ε < f z := by
          simpa [runningInf] using hpointδ z hx₀z hzδ
        exact le_of_lt hzpoint
  · have hbx : ¬ BddBelow (f '' Set.Icc a x) := by
      intro hbx
      exact hb (hbx.mono hsubset)
    rw [Real.sInf_of_not_bddBelow hb, Real.sInf_of_not_bddBelow hbx]
    linarith

/-- Source: `proof_gap/exercise_748/6.txt`; state monotonicity without irrelevant `δ, ε`. -/
theorem gap6 (f : ℝ → ℝ) (a : ℝ) :
    ∀ x₀ x, a ≤ x₀ → x₀ ≤ x → BddBelow (f '' Set.Icc a x) →
      runningInf f a x ≤ runningInf f a x₀ := by
  intro x₀ x ha hx₀x hbdd
  unfold runningInf
  apply le_csInf
  · exact ⟨f a, ⟨a, ⟨le_rfl, ha⟩, rfl⟩⟩
  · rintro y ⟨z, hz, rfl⟩
    exact csInf_le hbdd ⟨z, ⟨hz.1, hz.2.trans hx₀x⟩, rfl⟩

/-- Source: `proof_gap/exercise_748/7.txt`; retain the local lower estimate. -/
theorem gap7 (f : ℝ → ℝ) (a b : ℝ)
    (hlower : ∀ x₀ ∈ Set.Icc a b, ∀ ε > 0,
      ∃ δ > 0, ∀ x, x₀ < x → x < x₀ + δ →
        runningInf f a x ≥ runningInf f a x₀ - ε) :
    ∀ x₀ ∈ Set.Icc a b, ∀ ε > 0,
      ∃ δ > 0, ∀ x, x₀ < x → x < x₀ + δ →
        runningInf f a x ≥ runningInf f a x₀ - ε := by
  exact hlower

/-- Source: `proof_gap/exercise_748/8.txt`; remove irrelevant `x, δ`. -/
theorem gap8 (f : ℝ → ℝ) (a b : ℝ) :
    ∀ x₀ ∈ Set.Icc a b, ∀ ε > 0,
      runningInf f a x₀ ≥ runningInf f a x₀ - ε := by
  intro x₀ hx₀ ε hε
  linarith

/-- Source: `proof_gap/exercise_748/9.txt`; express the right limit by `nhdsWithin`. -/
theorem gap9 (f : ℝ → ℝ) (a b : ℝ)
    (hright : ∀ x₀ ∈ Set.Icc a b, ∀ ε > 0,
      ∃ δ > 0, ∀ x, x₀ < x → x < x₀ + δ →
        |runningInf f a x - runningInf f a x₀| < ε) :
    ∀ x₀ ∈ Set.Icc a b,
      Filter.Tendsto (runningInf f a) (nhdsWithin x₀ (Set.Ioi x₀))
        (nhds (runningInf f a x₀)) := by
  intro x₀ hx₀
  apply Metric.tendsto_nhds.2
  intro ε hε
  obtain ⟨δ, hδ, hmain⟩ := hright x₀ hx₀ ε hε
  have hinterval :
      Set.Ioo (x₀ - δ) (x₀ + δ) ∈ nhdsWithin x₀ (Set.Ioi x₀) :=
    mem_nhdsWithin_of_mem_nhds
      (Ioo_mem_nhds (sub_lt_self x₀ hδ) (lt_add_of_pos_right x₀ hδ))
  filter_upwards [self_mem_nhdsWithin, hinterval] with x hx hnear
  rw [Real.dist_eq]
  exact hmain x hx hnear.2

/-- Source: `proof_gap/exercise_748/10.txt`. -/
theorem gap10 (f : ℝ → ℝ) (a b x₀ : ℝ)
    (hf : ContinuousOn f (Set.Icc a b)) (hx₀ : x₀ ∈ Set.Icc a b)
    (hmin : runningInf f a x₀ = f x₀) :
    ∀ ε > 0, ∃ δ > 0, ∀ x ∈ Set.Icc a b,
      x₀ - δ < x → x < x₀ → f x < f x₀ + ε := by
  intro ε hε
  obtain ⟨δ, hδ, hmain⟩ := gap1 f a b hf x₀ hx₀ ε hε
  refine ⟨δ, hδ, ?_⟩
  intro x hx hxleft hxright
  have hdist : |x - x₀| < δ := by
    rw [abs_of_neg (sub_neg.mpr hxright)]
    linarith
  have hclose := hmain x hx hdist
  linarith [(abs_lt.mp hclose).2]

/-- Source: `proof_gap/exercise_748/11.txt`; add the missing restriction `x≤x₀`. -/
theorem gap11 (f : ℝ → ℝ) (a x₀ x : ℝ)
    (hx : a ≤ x) (hxx₀ : x ≤ x₀)
    (hbdd : BddBelow (f '' Set.Icc a x₀))
    (hmin : runningInf f a x₀ = f x₀) :
    runningInf f a x₀ ≤ runningInf f a x := by
  unfold runningInf
  apply le_csInf
  · exact ⟨f a, ⟨a, ⟨le_rfl, hx⟩, rfl⟩⟩
  · rintro y ⟨z, hz, rfl⟩
    exact csInf_le hbdd ⟨z, ⟨hz.1, hz.2.trans hxx₀⟩, rfl⟩

/-- Source: `proof_gap/exercise_748/12.txt`; add the missing left-neighborhood condition. -/
theorem gap12 (f : ℝ → ℝ) (a x₀ ε : ℝ) (hε : 0 < ε)
    (hleft : ∃ δ > 0, ∀ x, x₀ - δ < x → x < x₀ →
      runningInf f a x < runningInf f a x₀ + ε) :
    ∃ δ > 0, ∀ x, x₀ - δ < x → x < x₀ →
      runningInf f a x < runningInf f a x₀ + ε := by
  exact hleft

/-- Source: `proof_gap/exercise_748/13.txt`; remove the irrelevant quantified `x`. -/
theorem gap13 (f : ℝ → ℝ) (a b : ℝ) :
    ∀ x₀ ∈ Set.Icc a b, ∀ ε > 0,
      runningInf f a x₀ < runningInf f a x₀ + ε := by
  intro x₀ hx₀ ε hε
  linarith

/-- Source: `proof_gap/exercise_748/14.txt`; add the omitted left-neighborhood condition. -/
theorem gap14 (f : ℝ → ℝ) (a b x₀ x₁ : ℝ)
    (hx₀ : x₀ ∈ Set.Icc a b)
    (hattain : runningInf f a x₀ = f x₁) (ha : a ≤ x₁) (hx₁ : x₁ < x₀)
    (hbdd : BddBelow (f '' Set.Icc a x₀)) :
    ∃ δ > 0, ∀ x, x₀ - δ < x → x < x₀ →
      runningInf f a x = runningInf f a x₀ := by
  refine ⟨x₀ - x₁, sub_pos.mpr hx₁, ?_⟩
  intro x hxleft hxx₀
  have hx₁x : x₁ < x := by linarith
  have hax : a ≤ x := ha.trans (le_of_lt hx₁x)
  have hsubset : f '' Set.Icc a x ⊆ f '' Set.Icc a x₀ := by
    rintro y ⟨z, hz, rfl⟩
    exact ⟨z, ⟨hz.1, hz.2.trans (le_of_lt hxx₀)⟩, rfl⟩
  have hbddx : BddBelow (f '' Set.Icc a x) := hbdd.mono hsubset
  apply le_antisymm
  · calc
      runningInf f a x ≤ f x₁ := by
        unfold runningInf
        exact csInf_le hbddx ⟨x₁, ⟨ha, le_of_lt hx₁x⟩, rfl⟩
      _ = runningInf f a x₀ := hattain.symm
  · exact gap6 f a x x₀ hax (le_of_lt hxx₀) hbdd

/-- Source: `proof_gap/exercise_748/15.txt`; express the left limit by `nhdsWithin`. -/
theorem gap15 (f : ℝ → ℝ) (a b : ℝ)
    (hleft : ∀ x₀ ∈ Set.Icc a b, ∀ ε > 0,
      ∃ δ > 0, ∀ x, x₀ - δ < x → x < x₀ →
        |runningInf f a x - runningInf f a x₀| < ε) :
    ∀ x₀ ∈ Set.Icc a b,
      Filter.Tendsto (runningInf f a) (nhdsWithin x₀ (Set.Iio x₀))
        (nhds (runningInf f a x₀)) := by
  intro x₀ hx₀
  apply Metric.tendsto_nhds.2
  intro ε hε
  obtain ⟨δ, hδ, hmain⟩ := hleft x₀ hx₀ ε hε
  have hinterval :
      Set.Ioo (x₀ - δ) (x₀ + δ) ∈ nhdsWithin x₀ (Set.Iio x₀) :=
    mem_nhdsWithin_of_mem_nhds
      (Ioo_mem_nhds (sub_lt_self x₀ hδ) (lt_add_of_pos_right x₀ hδ))
  filter_upwards [self_mem_nhdsWithin, hinterval] with x hx hnear
  rw [Real.dist_eq]
  exact hmain x hnear.1 hx

/-- Source: `proof_gap/exercise_748/16.txt`. -/
theorem gap16 (f : ℝ → ℝ) (a b : ℝ)
    (hcont : ∀ x₀ ∈ Set.Icc a b, ContinuousAt (runningInf f a) x₀) :
    ∀ x₀ ∈ Set.Icc a b, ContinuousAt (runningInf f a) x₀ := by
  exact hcont

/-- Source: `proof_gap/exercise_748/17.txt`; formalize “similarly” for the running supremum. -/
theorem gap17 (f : ℝ → ℝ) (a b : ℝ) (hf : ContinuousOn f (Set.Icc a b)) :
    ContinuousOn (runningSup f a) (Set.Icc a b) := by
  exact runningSup_continuousOn_aux f a b hf

/-- Source: `proof_gap/exercise_748/18.txt`. -/
theorem gap18 (f : ℝ → ℝ) (a b : ℝ)
    (hmin : ContinuousOn (runningInf f a) (Set.Icc a b))
    (hmax : ContinuousOn (runningSup f a) (Set.Icc a b)) :
    ContinuousOn (runningInf f a) (Set.Icc a b) ∧
      ContinuousOn (runningSup f a) (Set.Icc a b) := by
  exact ⟨hmin, hmax⟩

end

end ProofGap.Exercise748
