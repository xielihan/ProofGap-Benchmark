import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Order.Filter.AtTopBot.Ring
import Mathlib.Topology.Order.MonotoneContinuity

namespace ProofGap.Exercise762

noncomputable section

def cot (x : ℝ) : ℝ := Real.cos x / Real.sin x
def f (x : ℝ) : ℝ := cot x / x

private theorem hasDerivAt_cot {x : ℝ} (hx : Real.sin x ≠ 0) :
    HasDerivAt cot (-1 / Real.sin x ^ 2) x := by
  have h :=
    (Real.hasDerivAt_cos x).div (Real.hasDerivAt_sin x) hx
  convert h using 1
  · field_simp
    nlinarith [Real.sin_sq_add_cos_sq x]

private theorem hasDerivAt_f {x : ℝ} (hx : x ≠ 0) (hsin : Real.sin x ≠ 0) :
    HasDerivAt f
      (-(x + Real.sin x * Real.cos x) / (x ^ 2 * Real.sin x ^ 2)) x := by
  have h := (hasDerivAt_cot hsin).div (hasDerivAt_id x) hx
  simp only [id_eq] at h
  convert h using 1
  · field_simp [cot, hx, hsin]
    rw [cot]
    field_simp [hsin]
    ring

/-- Exercise 762, gap 1. -/
theorem gap1 : ContinuousOn cot (Set.Ioo 0 Real.pi) := by
  intro x hx
  have hsin : Real.sin x ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2)
  exact (hasDerivAt_cot hsin).continuousAt.continuousWithinAt

/-- Exercise 762, gap 2. -/
theorem gap2 : StrictAntiOn cot (Set.Ioo 0 Real.pi) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioo 0 Real.pi) gap1
  intro x hx
  have hxi : x ∈ Set.Ioo 0 Real.pi := by simpa only [interior_Ioo] using hx
  have hsin : Real.sin x ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hxi.1 hxi.2)
  rw [(hasDerivAt_cot hsin).deriv]
  have hsquare : 0 < Real.sin x ^ 2 := sq_pos_of_ne_zero hsin
  exact div_neg_of_neg_of_pos (by norm_num) hsquare

/-- Exercise 762, gap 3. -/
theorem gap3 : ContinuousOn (fun x : ℝ => 1 / x) (Set.Ioo 0 Real.pi) := by
  intro x hx
  have hx0 : x ≠ 0 := ne_of_gt hx.1
  exact (continuousAt_const.div continuousAt_id hx0).continuousWithinAt

/-- Exercise 762, gap 4. -/
theorem gap4 : StrictAntiOn (fun x : ℝ => 1 / x) (Set.Ioo 0 Real.pi) := by
  intro a ha b hb hab
  exact one_div_lt_one_div_of_lt ha.1 hab

/-- Exercise 762, gap 5. -/
theorem gap5 : ContinuousOn f (Set.Ioo 0 Real.pi) := by
  intro x hx
  have hsin : Real.sin x ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2)
  exact (hasDerivAt_f (ne_of_gt hx.1) hsin).continuousAt.continuousWithinAt

/-- Exercise 762, gap 6; preserve the intended monotonicity claim. -/
theorem gap6 : StrictAntiOn f (Set.Ioo 0 Real.pi) := by
  apply strictAntiOn_of_deriv_neg (convex_Ioo 0 Real.pi) gap5
  intro x hx
  have hxi : x ∈ Set.Ioo 0 Real.pi := by simpa only [interior_Ioo] using hx
  have hx0 : x ≠ 0 := ne_of_gt hxi.1
  have hsin : Real.sin x ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hxi.1 hxi.2)
  rw [(hasDerivAt_f hx0 hsin).deriv]
  have h2x : 0 < 2 * x := mul_pos zero_lt_two hxi.1
  have hsabs := Real.abs_sin_lt_abs (ne_of_gt h2x)
  have htwox : |2 * x| = 2 * x := abs_of_pos h2x
  have hsin2 : Real.sin (2 * x) = 2 * Real.sin x * Real.cos x := by
    rw [Real.sin_two_mul]
  have hnum : 0 < x + Real.sin x * Real.cos x := by
    rw [htwox, abs_lt] at hsabs
    rw [hsin2] at hsabs
    nlinarith
  have hden : 0 < x ^ 2 * Real.sin x ^ 2 := mul_pos (sq_pos_of_ne_zero hx0)
    (sq_pos_of_ne_zero hsin)
  exact div_neg_of_neg_of_pos (neg_neg_of_pos hnum) hden

private theorem tendsto_sin_div_right :
    Filter.Tendsto (fun x : ℝ => Real.sin x / x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have h :=
    (Real.continuous_sinc.tendsto 0).mono_left
      (show nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhds 0 from inf_le_left)
  have heq :
      Real.sinc =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
        (fun x : ℝ => Real.sin x / x) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact Real.sinc_of_ne_zero (ne_of_gt hx)
  simpa using h.congr' heq

private theorem tendsto_cot_factor_right :
    Filter.Tendsto
      (fun x : ℝ => Real.cos x / (Real.sin x / x))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have hcos :
      Filter.Tendsto Real.cos (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    simpa using
      (Real.continuous_cos.tendsto 0).mono_left
        (show nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhds 0 from inf_le_left)
  simpa using hcos.div tendsto_sin_div_right (by norm_num)

/-- Exercise 762, gap 7. -/
theorem gap7 : Filter.Tendsto f (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop := by
  have hinv :
      Filter.Tendsto (fun x : ℝ => x⁻¹)
        (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop :=
    tendsto_inv_nhdsGT_zero
  have hinv2 :
      Filter.Tendsto (fun x : ℝ => (x⁻¹) ^ 2)
        (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop :=
    (Filter.tendsto_pow_atTop (n := 2) (by norm_num)).comp hinv
  have ht := hinv2.atTop_mul_pos zero_lt_one tendsto_cot_factor_right
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin,
    Filter.Eventually.filter_mono inf_le_left
      (Iio_mem_nhds Real.pi_pos)] with x hx hxpi
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hsin : Real.sin x ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hx hxpi)
  unfold f cot
  field_simp [hx0, hsin]

/-- Exercise 762, gap 8. -/
theorem gap8 :
    Filter.Tendsto f (nhdsWithin Real.pi (Set.Iio Real.pi)) Filter.atBot := by
  let q : ℝ → ℝ :=
    fun t => (Real.cos t / (Real.sin t / t)) / (Real.pi - t)
  have hden :
      Filter.Tendsto (fun t : ℝ => Real.pi - t)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds Real.pi) := by
    simpa using
      (tendsto_const_nhds.sub Filter.tendsto_id).mono_left
        (show nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhds 0 from inf_le_left)
  have hq :
      Filter.Tendsto q (nhdsWithin 0 (Set.Ioi 0))
        (nhds (1 / Real.pi)) := by
    dsimp [q]
    simpa using tendsto_cot_factor_right.div hden Real.pi_ne_zero
  have hinv :
      Filter.Tendsto (fun t : ℝ => t⁻¹)
        (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop :=
    tendsto_inv_nhdsGT_zero
  have htop :
      Filter.Tendsto (fun t : ℝ => t⁻¹ * q t)
        (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop :=
    hinv.atTop_mul_pos (one_div_pos.mpr Real.pi_pos) hq
  have hg :
      Filter.Tendsto (fun t : ℝ => f (Real.pi - t))
        (nhdsWithin 0 (Set.Ioi 0)) Filter.atBot := by
    have hneg := Filter.tendsto_neg_atTop_atBot.comp htop
    apply hneg.congr'
    filter_upwards [self_mem_nhdsWithin,
      Filter.Eventually.filter_mono inf_le_left
        (Iio_mem_nhds Real.pi_pos)] with t ht htpi
    have ht0 : t ≠ 0 := ne_of_gt ht
    have hpit0 : Real.pi - t ≠ 0 := ne_of_gt (sub_pos.mpr htpi)
    have hsint : Real.sin t ≠ 0 :=
      ne_of_gt (Real.sin_pos_of_pos_of_lt_pi ht htpi)
    dsimp [q]
    unfold f cot
    rw [Real.sin_pi_sub, Real.cos_pi_sub]
    field_simp [ht0, hpit0, hsint]
  have hsub :
      Filter.Tendsto (fun x : ℝ => Real.pi - x)
        (nhdsWithin Real.pi (Set.Iio Real.pi))
        (nhdsWithin 0 (Set.Ioi 0)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have hc :
          Filter.Tendsto (fun _ : ℝ => Real.pi)
            (nhdsWithin Real.pi (Set.Iio Real.pi)) (nhds Real.pi) :=
        tendsto_const_nhds
      have hid :
          Filter.Tendsto (fun x : ℝ => x)
            (nhdsWithin Real.pi (Set.Iio Real.pi)) (nhds Real.pi) :=
        Filter.tendsto_id.mono_left
          (show nhdsWithin Real.pi (Set.Iio Real.pi) ≤ nhds Real.pi from inf_le_left)
      simpa using hc.sub hid
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact sub_pos.mpr (by simpa using hx)
  have hcomp := hg.comp hsub
  convert hcomp using 1
  ext x
  simp only [Function.comp_apply]
  congr 1
  ring

/-- Exercise 762, gap 9; repair malformed function-valued witnesses. -/
theorem gap9 (k : ℝ) :
    ∃! x : ℝ, x ∈ Set.Ioo 0 Real.pi ∧ f x = k := by
  have haev :
      ∀ᶠ x : ℝ in nhdsWithin 0 (Set.Ioi 0),
        k < f x ∧ x < Real.pi ∧ 0 < x := by
    filter_upwards [Filter.tendsto_atTop.1 gap7 (k + 1),
      Filter.Eventually.filter_mono inf_le_left
        (Iio_mem_nhds Real.pi_pos),
      self_mem_nhdsWithin] with x hfx hxpi hxpos
    exact ⟨by linarith, hxpi, hxpos⟩
  obtain ⟨a, hfa, hapi, hapos⟩ := haev.exists
  have hbev :
      ∀ᶠ x : ℝ in nhdsWithin Real.pi (Set.Iio Real.pi),
        f x < k ∧ 0 < x ∧ x < Real.pi := by
    filter_upwards [Filter.tendsto_atBot.1 gap8 (k - 1),
      Filter.Eventually.filter_mono inf_le_left
        (Ioi_mem_nhds Real.pi_pos),
      self_mem_nhdsWithin] with x hfx hxpos hxpi
    exact ⟨by linarith, hxpos, hxpi⟩
  obtain ⟨b, hfb, hbpos, hbpi⟩ := hbev.exists
  have hab : a ≤ b := by
    by_contra h
    have hba : b < a := lt_of_not_ge h
    have hanti := gap6 ⟨hbpos, hbpi⟩ ⟨hapos, hapi⟩ hba
    linarith
  have hcont : ContinuousOn f (Set.Icc a b) := by
    apply gap5.mono
    intro z hz
    exact ⟨lt_of_lt_of_le hapos hz.1, lt_of_le_of_lt hz.2 hbpi⟩
  have hkrange : k ∈ Set.Icc (f b) (f a) :=
    ⟨le_of_lt hfb, le_of_lt hfa⟩
  obtain ⟨z, hzab, hfz⟩ := intermediate_value_Icc' hab hcont hkrange
  have hzmem : z ∈ Set.Ioo 0 Real.pi :=
    ⟨lt_of_lt_of_le hapos hzab.1, lt_of_le_of_lt hzab.2 hbpi⟩
  refine ⟨z, ⟨hzmem, hfz⟩, ?_⟩
  intro w hw
  rcases lt_trichotomy w z with hwz | hwz | hwz
  · have hanti := gap6 hw.1 hzmem hwz
    rw [hw.2, hfz] at hanti
    exact (lt_irrefl k hanti).elim
  · exact hwz
  · have hanti := gap6 hzmem hw.1 hwz
    rw [hfz, hw.2] at hanti
    exact (lt_irrefl k hanti).elim

/-- Exercise 762, gap 10. -/
theorem gap10 (k : ℝ) :
    ∃! x : ℝ, x ∈ Set.Ioo 0 Real.pi ∧ cot x = k * x := by
  obtain ⟨x, hx, huniq⟩ := gap9 k
  have hx0 : x ≠ 0 := ne_of_gt hx.1.1
  have hcot : cot x = k * x := by
    unfold f at hx
    exact (div_eq_iff hx0).1 hx.2
  refine ⟨x, ⟨hx.1, hcot⟩, ?_⟩
  intro z hz
  apply huniq z
  refine ⟨hz.1, ?_⟩
  unfold f
  exact (div_eq_iff (ne_of_gt hz.1.1)).2 hz.2

/-- Exercise 762, gap 11; bind a choice of the unique root. -/
theorem gap11 (r : ℝ → ℝ)
    (hr : ∀ k, r k ∈ Set.Ioo 0 Real.pi ∧ f (r k) = k) :
    Function.RightInverse r f := by
  intro k
  exact (hr k).2

private theorem root_strictAnti (r : ℝ → ℝ)
    (hr : ∀ k, r k ∈ Set.Ioo 0 Real.pi ∧ f (r k) = k) :
    StrictAnti r := by
  intro a b hab
  by_contra h
  have hle : r a ≤ r b := le_of_not_gt h
  rcases lt_or_eq_of_le hle with hlt | heq
  · have hanti := gap6 (hr a).1 (hr b).1 hlt
    rw [(hr a).2, (hr b).2] at hanti
    exact (not_lt_of_ge (le_of_lt hab)) hanti
  · have hab' : a = b := by
      calc
        a = f (r a) := (hr a).2.symm
        _ = f (r b) := congrArg f heq
        _ = b := (hr b).2
    exact (ne_of_lt hab) hab'

/-- Exercise 762, gap 12; add the defining root property. -/
theorem gap12 (r : ℝ → ℝ)
    (hr : ∀ k, r k ∈ Set.Ioo 0 Real.pi ∧ f (r k) = k) :
    Continuous r := by
  letI : Set.OrdConnected (Set.Ioo (0 : ℝ) Real.pi) :=
    Set.ordConnected_Ioo
  let I := {x : ℝ // x ∈ Set.Ioo 0 Real.pi}
  letI : OrderTopology I := orderTopology_of_ordConnected
  let g : I → OrderDual ℝ := fun x => f x
  have hg : StrictMono g := by
    intro a b hab
    change f b < f a
    exact gap6 a.property b.property hab
  have hsurj : Function.Surjective g := by
    intro k
    obtain ⟨x, hx, huniq⟩ := gap9 (show ℝ from k)
    exact ⟨⟨x, hx.1⟩, hx.2⟩
  let e : I ≃o OrderDual ℝ := hg.orderIsoOfSurjective g hsurj
  have hc :
      Continuous (fun k : OrderDual ℝ => ((e.symm k : I) : ℝ)) :=
    continuous_subtype_val.comp e.symm.continuous
  have heq :
      (fun k : ℝ => ((e.symm (show OrderDual ℝ from k) : I) : ℝ)) = r := by
    funext k
    have hroot : f ((e.symm (show OrderDual ℝ from k) : I) : ℝ) = k := by
      have h :=
        StrictMono.orderIsoOfSurjective_self_symm_apply
          g hg hsurj (show OrderDual ℝ from k)
      simpa [g] using h
    obtain ⟨z, hz, huniq⟩ := gap9 k
    calc
      ((e.symm (show OrderDual ℝ from k) : I) : ℝ) = z :=
        huniq _ ⟨(e.symm (show OrderDual ℝ from k) : I).property, hroot⟩
      _ = r k := (huniq _ (hr k)).symm
  rw [← heq]
  exact hc

/-- Exercise 762, gap 13; add the defining root property. -/
theorem gap13 (r : ℝ → ℝ)
    (hr : ∀ k, r k ∈ Set.Ioo 0 Real.pi ∧ f (r k) = k) :
    StrictAnti r := by
  exact root_strictAnti r hr

/-- Exercise 762, gap 14; express uniqueness pointwise. -/
theorem gap14 :
    ∃! r : ℝ → ℝ,
      Continuous r ∧
        ∀ k, r k ∈ Set.Ioo 0 Real.pi ∧ cot (r k) = k * r k := by
  let r : ℝ → ℝ := fun k => Classical.choose (gap10 k)
  have hr (k : ℝ) :
      r k ∈ Set.Ioo 0 Real.pi ∧ cot (r k) = k * r k :=
    (Classical.choose_spec (gap10 k)).1
  have hrf (k : ℝ) : r k ∈ Set.Ioo 0 Real.pi ∧ f (r k) = k := by
    refine ⟨(hr k).1, ?_⟩
    unfold f
    exact (div_eq_iff (ne_of_gt (hr k).1.1)).2 (hr k).2
  refine ⟨r, ⟨gap12 r hrf, hr⟩, ?_⟩
  intro r' hr'
  funext k
  exact (Classical.choose_spec (gap10 k)).2 (r' k) (hr'.2 k)

end

end ProofGap.Exercise762
