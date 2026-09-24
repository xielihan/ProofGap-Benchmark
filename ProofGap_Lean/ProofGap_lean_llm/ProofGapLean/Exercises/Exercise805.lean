import ProofGapLean.Prelude.Sequences
import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.Linarith

namespace ProofGap.Exercise805

noncomputable section

def BoundedOn (f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∃ C : ℝ, ∀ x ∈ s, |f x| ≤ C

private theorem monotone_bounded_endpoint_limits
    (f : ℝ → ℝ) (a b : ℝ) (hmono : Monotone f)
    (hbd : BoundedOn f (Set.Ioo a b)) (hab : a < b) :
    (∃ La, Filter.Tendsto f (nhdsWithin a (Set.Ioi a)) (nhds La)) ∧
    (∃ Lb, Filter.Tendsto f (nhdsWithin b (Set.Iio b)) (nhds Lb)) := by
  rcases hbd with ⟨C, hC⟩
  let s : Set ℝ := f '' Set.Ioo a b
  have hsne : s.Nonempty := by
    refine ⟨f ((a + b) / 2), ?_⟩
    refine ⟨(a + b) / 2, ⟨?_, ?_⟩, rfl⟩ <;> linarith
  have hsbelow : BddBelow s := by
    refine ⟨-C, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    exact (abs_le.mp (hC x hx)).1
  have hsabove : BddAbove s := by
    refine ⟨C, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    exact (abs_le.mp (hC x hx)).2
  constructor
  · refine ⟨sInf s, tendsto_order.2 ⟨?_, ?_⟩⟩
    · intro c hc
      have hright : ∀ᶠ x in nhdsWithin a (Set.Ioi a), x < b :=
        (show nhdsWithin a (Set.Ioi a) ≤ nhds a from inf_le_left)
          (Iio_mem_nhds hab)
      filter_upwards [self_mem_nhdsWithin, hright] with x hax hxb
      exact lt_of_lt_of_le hc
        (csInf_le hsbelow ⟨x, ⟨hax, hxb⟩, rfl⟩)
    · intro c hc
      have hex : ∃ z ∈ s, z < c := by
        by_contra hn
        push_neg at hn
        have hle : c ≤ sInf s := le_csInf hsne hn
        exact (not_le_of_gt hc) hle
      rcases hex with ⟨z, ⟨y, hy, rfl⟩, hyc⟩
      have hy_event : ∀ᶠ x in nhdsWithin a (Set.Ioi a), x < y :=
        (show nhdsWithin a (Set.Ioi a) ≤ nhds a from inf_le_left)
          (Iio_mem_nhds hy.1)
      filter_upwards [hy_event] with x hxy
      exact lt_of_le_of_lt (hmono (le_of_lt hxy)) hyc
  · refine ⟨sSup s, tendsto_order.2 ⟨?_, ?_⟩⟩
    · intro c hc
      have hex : ∃ z ∈ s, c < z := by
        by_contra hn
        push_neg at hn
        have hle : sSup s ≤ c := csSup_le hsne hn
        exact (not_le_of_gt hc) hle
      rcases hex with ⟨z, ⟨y, hy, rfl⟩, hcy⟩
      have hy_event : ∀ᶠ x in nhdsWithin b (Set.Iio b), y < x :=
        (show nhdsWithin b (Set.Iio b) ≤ nhds b from inf_le_left)
          (Ioi_mem_nhds hy.2)
      filter_upwards [hy_event] with x hyx
      exact lt_of_lt_of_le hcy (hmono (le_of_lt hyx))
    · intro c hc
      have hleft : ∀ᶠ x in nhdsWithin b (Set.Iio b), a < x :=
        (show nhdsWithin b (Set.Iio b) ≤ nhds b from inf_le_left)
          (Ioi_mem_nhds hab)
      filter_upwards [hleft, self_mem_nhdsWithin] with x hax hxb
      exact lt_of_le_of_lt
        (le_csSup hsabove ⟨x, ⟨hax, hxb⟩, rfl⟩) hc

private theorem monotone_bounded_limit_atTop
    (f : ℝ → ℝ) (a : ℝ) (hmono : Monotone f)
    (hbd : BoundedOn f (Set.Ici a)) :
    ∃ L, Filter.Tendsto f Filter.atTop (nhds L) := by
  rcases hbd with ⟨C, hC⟩
  let s : Set ℝ := f '' Set.Ici a
  have hsne : s.Nonempty := by
    refine ⟨f a, a, ?_, rfl⟩
    show a ≤ a
    exact le_rfl
  have hsabove : BddAbove s := by
    refine ⟨C, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    exact (abs_le.mp (hC x hx)).2
  refine ⟨sSup s, tendsto_order.2 ⟨?_, ?_⟩⟩
  · intro c hc
    have hex : ∃ z ∈ s, c < z := by
      by_contra hn
      push_neg at hn
      have hle : sSup s ≤ c := csSup_le hsne hn
      exact (not_le_of_gt hc) hle
    rcases hex with ⟨z, ⟨y, hy, rfl⟩, hcy⟩
    have hxy : ∀ᶠ x : ℝ in Filter.atTop, y ≤ x :=
      Filter.eventually_atTop.2 ⟨y, fun x hx => hx⟩
    filter_upwards [hxy] with x hx
    exact lt_of_lt_of_le hcy (hmono hx)
  · intro c hc
    have hxa : ∀ᶠ x : ℝ in Filter.atTop, a ≤ x :=
      Filter.eventually_atTop.2 ⟨a, fun x hx => hx⟩
    filter_upwards [hxa] with x hx
    exact lt_of_le_of_lt (le_csSup hsabove ⟨x, hx, rfl⟩) hc

private theorem exists_limit_atTop_of_monotone_or_antitone_bounded
    (f : ℝ → ℝ) (a : ℝ) (hmono : Monotone f ∨ Antitone f)
    (hbd : BoundedOn f (Set.Ici a)) :
    ∃ L, Filter.Tendsto f Filter.atTop (nhds L) := by
  rcases hmono with hmono | hanti
  · exact monotone_bounded_limit_atTop f a hmono hbd
  · let g : ℝ → ℝ := fun x => -f x
    have hgmono : Monotone g := by
      intro x y hxy
      exact neg_le_neg (hanti hxy)
    have hgbd : BoundedOn g (Set.Ici a) := by
      rcases hbd with ⟨C, hC⟩
      refine ⟨C, ?_⟩
      intro x hx
      simpa [g] using hC x hx
    rcases monotone_bounded_limit_atTop g a hgmono hgbd with ⟨L, hL⟩
    refine ⟨-L, ?_⟩
    simpa [Function.comp_def, g] using
      continuousAt_id.neg.tendsto.comp hL

private theorem uniformContinuousOn_Ici_of_tendsto_atTop
    (f : ℝ → ℝ) (a L : ℝ) (hcont : ContinuousOn f (Set.Ici a))
    (hL : Filter.Tendsto f Filter.atTop (nhds L)) :
    UniformContinuousOn f (Set.Ici a) := by
  rw [Metric.uniformContinuousOn_iff]
  intro ε hε
  have hε3 : 0 < ε / 3 := by linarith
  have hev : ∀ᶠ x in Filter.atTop, dist (f x) L < ε / 3 :=
    (Metric.tendsto_nhds.1 hL) (ε / 3) hε3
  rcases Filter.eventually_atTop.1 hev with ⟨M, hM⟩
  let T : ℝ := max a M
  have haT : a ≤ T := le_max_left _ _
  have htail : ∀ x, T ≤ x → dist (f x) L < ε / 3 := by
    intro x hx
    exact hM x (le_trans (le_max_right _ _) hx)
  have hcompact_cont : ContinuousOn f (Set.Icc a (T + 1)) :=
    hcont.mono fun x hx => hx.1
  have hcompact : UniformContinuousOn f (Set.Icc a (T + 1)) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hcompact_cont
  rcases (Metric.uniformContinuousOn_iff.1 hcompact) ε hε with
    ⟨δ, hδ, hδf⟩
  refine ⟨min δ 1, lt_min hδ zero_lt_one, ?_⟩
  intro x hx y hy hxy
  have hxyδ : dist x y < δ :=
    lt_of_lt_of_le hxy (min_le_left _ _)
  have hxy1 : dist x y < 1 :=
    lt_of_lt_of_le hxy (min_le_right _ _)
  by_cases hxupper : x ≤ T + 1
  · by_cases hyupper : y ≤ T + 1
    · exact hδf x ⟨hx, hxupper⟩ y ⟨hy, hyupper⟩ hxyδ
    · have hyT : T ≤ y := by linarith
      have habs : |x - y| < 1 := by
        simpa [Real.dist_eq] using hxy1
      have hxT : T ≤ x := by
        rw [abs_lt] at habs
        linarith
      calc
        dist (f x) (f y) ≤ dist (f x) L + dist (f y) L :=
          dist_triangle_right _ _ _
        _ < ε := by linarith [htail x hxT, htail y hyT]
  · have hxT : T ≤ x := by linarith
    have habs : |x - y| < 1 := by
      simpa [Real.dist_eq] using hxy1
    have hyT : T ≤ y := by
      rw [abs_lt] at habs
      linarith
    calc
      dist (f x) (f y) ≤ dist (f x) L + dist (f y) L :=
        dist_triangle_right _ _ _
      _ < ε := by linarith [htail x hxT, htail y hyT]

theorem gap1 (f : ℝ → ℝ) (a b : ℝ)
    (hmono : Monotone f ∨ Antitone f) (hbd : BoundedOn f (Set.Ioo a b))
    (hcont : ContinuousOn f (Set.Ioo a b)) (hab : a < b) :
    (∃ La, Filter.Tendsto f (nhdsWithin a (Set.Ioi a)) (nhds La)) ∧
    (∃ Lb, Filter.Tendsto f (nhdsWithin b (Set.Iio b)) (nhds Lb)) := by
  rcases hmono with hmono | hanti
  · exact monotone_bounded_endpoint_limits f a b hmono hbd hab
  · let g : ℝ → ℝ := fun x => -f x
    have hgmono : Monotone g := by
      intro x y hxy
      exact neg_le_neg (hanti hxy)
    have hgbd : BoundedOn g (Set.Ioo a b) := by
      rcases hbd with ⟨C, hC⟩
      refine ⟨C, ?_⟩
      intro x hx
      simpa [g] using hC x hx
    rcases monotone_bounded_endpoint_limits g a b hgmono hgbd hab with
      ⟨⟨La, ha⟩, ⟨Lb, hb⟩⟩
    constructor
    · refine ⟨-La, ?_⟩
      simpa [Function.comp_def, g] using
        continuousAt_id.neg.tendsto.comp ha
    · refine ⟨-Lb, ?_⟩
      simpa [Function.comp_def, g] using
        continuousAt_id.neg.tendsto.comp hb

theorem gap2 (f fstar : ℝ → ℝ) (a b La Lb : ℝ)
    (hcont : ContinuousOn f (Set.Ioo a b))
    (ha : Filter.Tendsto f (nhdsWithin a (Set.Ioi a)) (nhds La))
    (hb : Filter.Tendsto f (nhdsWithin b (Set.Iio b)) (nhds Lb))
    (hext : ∀ x, fstar x = if x = a then La else if x = b then Lb else f x) :
    ContinuousOn fstar (Set.Icc a b) := by
  have heq : Set.EqOn fstar f (Set.Ioo a b) := by
    intro x hx
    simp [hext x, ne_of_gt hx.1, ne_of_lt hx.2]
  have hcontstar : ContinuousOn fstar (Set.Ioo a b) :=
    hcont.congr fun x hx => heq hx
  intro x hx
  by_cases hxa : x = a
  · subst x
    by_cases hab0 : a = b
    · subst b
      rw [Metric.continuousWithinAt_iff]
      intro ε hε
      refine ⟨1, zero_lt_one, ?_⟩
      intro y hy hyd
      have hya : y = a := le_antisymm hy.2 hy.1
      subst y
      simpa using hε
    · have hab : a < b := lt_of_le_of_ne hx.2 hab0
      rw [Metric.continuousWithinAt_iff]
      intro ε hε
      have hev : {y | dist (f y) La < ε} ∈ nhdsWithin a (Set.Ioi a) :=
        (Metric.tendsto_nhds.1 ha) ε hε
      rw [mem_nhdsWithin_iff_exists_mem_nhds_inter] at hev
      rcases hev with ⟨u, hu, hu_sub⟩
      rcases Metric.mem_nhds_iff.1 hu with ⟨δ, hδ, hδu⟩
      refine ⟨min δ (b - a), lt_min hδ (sub_pos.mpr hab), ?_⟩
      intro y hy hyd
      by_cases hya : y = a
      · subst y
        simpa using hε
      · have hay : a < y := lt_of_le_of_ne hy.1 (Ne.symm hya)
        have hyd' : dist y a < δ :=
          lt_of_lt_of_le hyd (min_le_left _ _)
        have hyu : y ∈ u := hδu (by simpa [Metric.mem_ball] using hyd')
        have hyb : y ≠ b := by
          intro hyb
          subst y
          have hbad : dist b a < b - a :=
            lt_of_lt_of_le hyd (min_le_right _ _)
          simpa [Real.dist_eq, abs_of_pos (sub_pos.mpr hab)] using hbad
        have hp := hu_sub ⟨hyu, hay⟩
        simpa [hext, hya, hyb, hab0] using hp
  · by_cases hxb : x = b
    · subst x
      have hab : a < b := lt_of_le_of_ne hx.1 (Ne.symm hxa)
      rw [Metric.continuousWithinAt_iff]
      intro ε hε
      have hev : {y | dist (f y) Lb < ε} ∈ nhdsWithin b (Set.Iio b) :=
        (Metric.tendsto_nhds.1 hb) ε hε
      rw [mem_nhdsWithin_iff_exists_mem_nhds_inter] at hev
      rcases hev with ⟨u, hu, hu_sub⟩
      rcases Metric.mem_nhds_iff.1 hu with ⟨δ, hδ, hδu⟩
      refine ⟨min δ (b - a), lt_min hδ (sub_pos.mpr hab), ?_⟩
      intro y hy hyd
      by_cases hyb : y = b
      · subst y
        simpa using hε
      · have hyb' : y < b := lt_of_le_of_ne hy.2 hyb
        have hyd' : dist y b < δ :=
          lt_of_lt_of_le hyd (min_le_left _ _)
        have hyu : y ∈ u := hδu (by simpa [Metric.mem_ball] using hyd')
        have hya : y ≠ a := by
          intro hya
          subst y
          have hbad : dist a b < b - a :=
            lt_of_lt_of_le hyd (min_le_right _ _)
          simpa [Real.dist_eq, abs_of_neg (sub_neg.mpr hab)] using hbad
        have hp := hu_sub ⟨hyu, hyb'⟩
        simpa [hext, hxa, hya, hyb] using hp
    · have hax : a < x := lt_of_le_of_ne hx.1 (Ne.symm hxa)
      have hxb' : x < b := lt_of_le_of_ne hx.2 hxb
      have hc : ContinuousAt fstar x :=
        (hcontstar x ⟨hax, hxb'⟩).continuousAt (Ioo_mem_nhds hax hxb')
      exact hc.continuousWithinAt
theorem gap3 (fstar : ℝ → ℝ) (a b : ℝ)
    (h : ContinuousOn fstar (Set.Icc a b)) :
    UniformContinuousOn fstar (Set.Icc a b) := by
  exact isCompact_Icc.uniformContinuousOn_of_continuous h
theorem gap4 (f fstar : ℝ → ℝ) (a b : ℝ)
    (heq : Set.EqOn f fstar (Set.Ioo a b))
    (h : UniformContinuousOn fstar (Set.Icc a b)) :
    UniformContinuousOn f (Set.Ioo a b) := by
  exact (h.mono Set.Ioo_subset_Icc_self).congr heq.symm

theorem gap5 (f fstar : ℝ → ℝ) (a La : ℝ)
    (hcont : ContinuousOn f (Set.Ioi a))
    (ha : Filter.Tendsto f (nhdsWithin a (Set.Ioi a)) (nhds La))
    (hext : ∀ x, fstar x = if x = a then La else f x) :
    ContinuousOn fstar (Set.Ici a) := by
  have heq : Set.EqOn fstar f (Set.Ioi a) := by
    intro x hx
    change a < x at hx
    simp [hext x, ne_of_gt hx]
  have hcontstar : ContinuousOn fstar (Set.Ioi a) :=
    hcont.congr fun x hx => heq hx
  intro x hx
  by_cases hxa : x = a
  · subst x
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    have hev : {y | dist (f y) La < ε} ∈ nhdsWithin a (Set.Ioi a) :=
      (Metric.tendsto_nhds.1 ha) ε hε
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter] at hev
    rcases hev with ⟨u, hu, hu_sub⟩
    rcases Metric.mem_nhds_iff.1 hu with ⟨δ, hδ, hδu⟩
    refine ⟨δ, hδ, ?_⟩
    intro y hy hyd
    by_cases hya : y = a
    · subst y
      simpa using hε
    · have hay : a < y := lt_of_le_of_ne hy (Ne.symm hya)
      have hyu : y ∈ u := hδu (by simpa [Metric.mem_ball] using hyd)
      have hp := hu_sub ⟨hyu, hay⟩
      simpa [hext, hya] using hp
  · have hax : a < x := lt_of_le_of_ne hx (Ne.symm hxa)
    have hc : ContinuousAt fstar x :=
      (hcontstar x hax).continuousAt (Ioi_mem_nhds hax)
    exact hc.continuousWithinAt
theorem gap6 (f fstar : ℝ → ℝ)
    (heq : Filter.EventuallyEq Filter.atTop fstar f) :
    Filter.Tendsto fstar Filter.atTop (Filter.map f Filter.atTop) ↔
      Filter.Tendsto f Filter.atTop (Filter.map f Filter.atTop) := by
  constructor
  · exact Filter.Tendsto.congr' heq
  · exact Filter.Tendsto.congr' heq.symm
theorem gap7 (fstar : ℝ → ℝ) (a : ℝ)
    (hmono : Monotone fstar ∨ Antitone fstar) (hbd : BoundedOn fstar (Set.Ici a))
    (hcont : ContinuousOn fstar (Set.Ici a)) :
    UniformContinuousOn fstar (Set.Ici a) := by
  rcases exists_limit_atTop_of_monotone_or_antitone_bounded fstar a hmono hbd with
    ⟨L, hL⟩
  exact uniformContinuousOn_Ici_of_tendsto_atTop fstar a L hcont hL
theorem gap8 (f fstar : ℝ → ℝ) (a : ℝ)
    (heq : Set.EqOn f fstar (Set.Ioi a))
    (h : UniformContinuousOn fstar (Set.Ici a)) :
    UniformContinuousOn f (Set.Ioi a) := by
  exact (h.mono Set.Ioi_subset_Ici_self).congr heq.symm

theorem gap9 (g : ℝ → ℝ) (b : ℝ)
    (hmono : Monotone g ∨ Antitone g) (hbd : BoundedOn g (Set.Ioi (-b)))
    (hcont : ContinuousOn g (Set.Ioi (-b))) :
    UniformContinuousOn g (Set.Ioi (-b)) := by
  have hab : -b < -b + 1 := by linarith
  have hbdloc : BoundedOn g (Set.Ioo (-b) (-b + 1)) := by
    rcases hbd with ⟨C, hC⟩
    exact ⟨C, fun x hx => hC x hx.1⟩
  have hcontloc : ContinuousOn g (Set.Ioo (-b) (-b + 1)) :=
    hcont.mono fun x hx => hx.1
  rcases gap1 g (-b) (-b + 1) hmono hbdloc hcontloc hab with
    ⟨⟨Lzero, hLzero⟩, _⟩
  let gstar : ℝ → ℝ := fun x => if x = -b then Lzero else g x
  have hgstarcont : ContinuousOn gstar (Set.Ici (-b)) := by
    apply gap5 g gstar (-b) Lzero hcont hLzero
    intro x
    rfl
  have hbdtail : BoundedOn g (Set.Ici (-b + 1)) := by
    rcases hbd with ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro x hx
    apply hC x
    change -b + 1 ≤ x at hx
    change -b < x
    linarith
  rcases exists_limit_atTop_of_monotone_or_antitone_bounded
      g (-b + 1) hmono hbdtail with ⟨Linf, hLinf⟩
  have hevent : Filter.EventuallyEq Filter.atTop gstar g := by
    have hgt : ∀ᶠ x : ℝ in Filter.atTop, -b < x :=
      Filter.eventually_atTop.2 ⟨-b + 1, by
        intro x hx
        linarith⟩
    filter_upwards [hgt] with x hx
    simp [gstar, ne_of_gt hx]
  have hgstarL : Filter.Tendsto gstar Filter.atTop (nhds Linf) :=
    Filter.Tendsto.congr' hevent.symm hLinf
  have hucstar : UniformContinuousOn gstar (Set.Ici (-b)) :=
    uniformContinuousOn_Ici_of_tendsto_atTop
      gstar (-b) Linf hgstarcont hgstarL
  have heq : Set.EqOn g gstar (Set.Ioi (-b)) := by
    intro x hx
    change -b < x at hx
    simp [gstar, ne_of_gt hx]
  exact (hucstar.mono Set.Ioi_subset_Ici_self).congr heq.symm
theorem gap10 (f g : ℝ → ℝ) (b : ℝ)
    (hg : ∀ x, g x = f (-x)) (h : UniformContinuousOn g (Set.Ioi (-b))) :
    UniformContinuousOn f (Set.Iio b) := by
  rw [Metric.uniformContinuousOn_iff] at h ⊢
  intro ε hε
  rcases h ε hε with ⟨δ, hδ, hδg⟩
  refine ⟨δ, hδ, ?_⟩
  intro x hx y hy hxy
  have hnx : -x ∈ Set.Ioi (-b) := by
    change x < b at hx
    change -b < -x
    linarith
  have hny : -y ∈ Set.Ioi (-b) := by
    change y < b at hy
    change -b < -y
    linarith
  have hnxy : dist (-x) (-y) < δ := by
    simpa [Real.dist_eq] using hxy
  have hout := hδg (-x) hnx (-y) hny hnxy
  simpa [hg, Real.dist_eq] using hout

theorem gap11 (f : ℝ → ℝ) (ε : ℝ) (hε : 0 < ε)
    (h : UniformContinuousOn f (Set.Ioi 0)) :
    ∃ δ > 0, ∀ x ∈ Set.Ioi (0 : ℝ), ∀ y ∈ Set.Ioi (0 : ℝ),
      |x - y| < δ → |f x - f y| < ε := by
  rw [Metric.uniformContinuousOn_iff] at h
  rcases h ε hε with ⟨δ, hδ, hδf⟩
  refine ⟨δ, hδ, ?_⟩
  intro x hx y hy hxy
  simpa only [Real.dist_eq] using hδf x hx y hy hxy
theorem gap12 (f : ℝ → ℝ) (ε : ℝ) (hε : 0 < ε)
    (h : UniformContinuousOn f (Set.Iio 1)) :
    ∃ δ > 0, ∀ x ∈ Set.Iio (1 : ℝ), ∀ y ∈ Set.Iio (1 : ℝ),
      |x - y| < δ → |f x - f y| < ε := by
  rw [Metric.uniformContinuousOn_iff] at h
  rcases h ε hε with ⟨δ, hδ, hδf⟩
  refine ⟨δ, hδ, ?_⟩
  intro x hx y hy hxy
  simpa only [Real.dist_eq] using hδf x hx y hy hxy

/-- Correct the quantifier order: the overlap argument chooses `δ` for each `ε`. -/
theorem gap13 (f : ℝ → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hpos : UniformContinuousOn f (Set.Ioi 0))
    (hneg : UniformContinuousOn f (Set.Iio 1)) :
    ∃ δ > 0, ∀ x y : ℝ, |x - y| < δ →
      ((x ∈ Set.Ioi 0 ∧ y ∈ Set.Ioi 0) ∨
       (x ∈ Set.Iio 1 ∧ y ∈ Set.Iio 1)) := by
  refine ⟨1, zero_lt_one, ?_⟩
  intro x y hxy
  simp only [Set.mem_Ioi, Set.mem_Iio]
  rw [abs_lt] at hxy
  by_cases hx : 0 < x
  · by_cases hy : 0 < y
    · exact Or.inl ⟨hx, hy⟩
    · exact Or.inr ⟨by linarith, by linarith⟩
  · by_cases hy : y < 1
    · exact Or.inr ⟨by linarith, hy⟩
    · exfalso
      linarith
theorem gap14 (f : ℝ → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hpos : UniformContinuousOn f (Set.Ioi 0))
    (hneg : UniformContinuousOn f (Set.Iio 1)) :
    ∃ δ > 0, ∀ x y : ℝ, |x - y| < δ → |f x - f y| < ε := by
  rcases gap11 f ε hε hpos with ⟨δp, hδp, hp⟩
  rcases gap12 f ε hε hneg with ⟨δn, hδn, hn⟩
  rcases gap13 f ε hε hpos hneg with ⟨δo, hδo, hoverlap⟩
  let δ := min δo (min δp δn)
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min hδo (lt_min hδp hδn)
  refine ⟨δ, hδ, ?_⟩
  intro x y hxy
  have hxo : |x - y| < δo :=
    lt_of_lt_of_le hxy (by dsimp [δ]; exact min_le_left _ _)
  rcases hoverlap x y hxo with hboth | hboth
  · apply hp x hboth.1 y hboth.2
    exact lt_of_lt_of_le hxy (by
      dsimp [δ]
      exact le_trans (min_le_right _ _) (min_le_left _ _))
  · apply hn x hboth.1 y hboth.2
    exact lt_of_lt_of_le hxy (by
      dsimp [δ]
      exact le_trans (min_le_right _ _) (min_le_right _ _))
theorem gap15 (f : ℝ → ℝ)
    (hpos : UniformContinuousOn f (Set.Ioi 0))
    (hneg : UniformContinuousOn f (Set.Iio 1)) :
    UniformContinuous f := by
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  rcases gap14 f ε hε hpos hneg with ⟨δ, hδ, hδf⟩
  refine ⟨δ, hδ, ?_⟩
  intro x y hxy
  simpa only [Real.dist_eq] using
    hδf x y (by simpa only [Real.dist_eq] using hxy)
theorem gap16 (f : ℝ → ℝ) (a b : ℝ)
    (hmono : Monotone f ∨ Antitone f) (hbd : BoundedOn f (Set.Ioo a b))
    (hcont : ContinuousOn f (Set.Ioo a b)) :
    UniformContinuousOn f (Set.Ioo a b) := by
  by_cases hab : a < b
  · rcases gap1 f a b hmono hbd hcont hab with
      ⟨⟨La, ha⟩, ⟨Lb, hb⟩⟩
    let fstar : ℝ → ℝ := fun x =>
      if x = a then La else if x = b then Lb else f x
    have hfstar : ContinuousOn fstar (Set.Icc a b) := by
      apply gap2 f fstar a b La Lb hcont ha hb
      intro x
      rfl
    have hucstar : UniformContinuousOn fstar (Set.Icc a b) :=
      gap3 fstar a b hfstar
    have heq : Set.EqOn f fstar (Set.Ioo a b) := by
      intro x hx
      simp [fstar, ne_of_gt hx.1, ne_of_lt hx.2]
    exact gap4 f fstar a b heq hucstar
  · rw [Metric.uniformContinuousOn_iff]
    intro ε hε
    refine ⟨1, zero_lt_one, ?_⟩
    intro x hx
    exfalso
    exact hab (lt_trans hx.1 hx.2)

end

end ProofGap.Exercise805
