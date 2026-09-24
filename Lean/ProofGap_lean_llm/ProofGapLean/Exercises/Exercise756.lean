import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise756

noncomputable section

def osc (a x : ℝ) : ℝ := if x = a then 0 else Real.sin (1 / (x - a))

theorem gap1 (a b : ℝ) (hab : a < b) :
    osc a '' Set.Icc a b = Set.Icc (-1) 1 := by
  apply Set.Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    unfold osc
    split_ifs
    · norm_num
    · exact ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
  · intro y hy
    have hba : 0 < b - a := sub_pos.mpr hab
    have htwo_pi : 0 < 2 * Real.pi := by positivity
    obtain ⟨n : ℕ, hn⟩ :=
      exists_nat_gt ((1 / (b - a) - Real.arcsin y) / (2 * Real.pi))
    let t : ℝ := Real.arcsin y + (n : ℝ) * (2 * Real.pi)
    have ht : 1 / (b - a) < t := by
      have hmul := (div_lt_iff₀ htwo_pi).mp hn
      dsimp [t]
      linarith
    have htpos : 0 < t := lt_trans (one_div_pos.mpr hba) ht
    have hinv : 1 / t < b - a := by
      apply (div_lt_iff₀ htpos).2
      have hmul := (div_lt_iff₀ hba).mp ht
      simpa [mul_comm] using hmul
    have hperiod (m : ℕ) :
        Real.sin (Real.arcsin y + (m : ℝ) * (2 * Real.pi)) =
          Real.sin (Real.arcsin y) := by
      induction m with
      | zero => simp
      | succ m ihm =>
          calc
            Real.sin (Real.arcsin y + (↑(Nat.succ m) : ℝ) * (2 * Real.pi)) =
                Real.sin ((Real.arcsin y + (m : ℝ) * (2 * Real.pi)) +
                  2 * Real.pi) := by
                    congr 1
                    rw [Nat.cast_succ]
                    ring
            _ = Real.sin (Real.arcsin y + (m : ℝ) * (2 * Real.pi)) :=
              Real.sin_add_two_pi _
            _ = Real.sin (Real.arcsin y) := ihm
    refine ⟨a + 1 / t, ?_, ?_⟩
    · constructor
      · have hrecip : 0 < 1 / t := one_div_pos.mpr htpos
        linarith
      · linarith
    · have hne : a + 1 / t ≠ a := by
        have hrecip : 0 < 1 / t := one_div_pos.mpr htpos
        linarith
      rw [osc, if_neg hne]
      have harg : 1 / (a + 1 / t - a) = t := by
        field_simp [ne_of_gt htpos]
        ring
      rw [harg]
      dsimp [t]
      calc
        Real.sin (Real.arcsin y + (n : ℝ) * (2 * Real.pi)) =
            Real.sin (Real.arcsin y) := hperiod n
        _ = y := Real.sin_arcsin hy.1 hy.2
theorem gap2 (a : ℝ) : osc a a = 0 := by
  simp [osc]
theorem gap3 (a b : ℝ) : |osc a b| ≤ 1 := by
  unfold osc
  split_ifs
  · norm_num
  · apply (abs_le).2
    exact ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
theorem gap4 (a b y : ℝ) (hab : a ≤ b)
    (hy : min (osc a a) (osc a b) ≤ y)
    (hy' : y ≤ max (osc a a) (osc a b)) :
    ∃ ξ ∈ Set.Icc a b, osc a ξ = y := by
  by_cases heq : a = b
  · subst b
    have hy0 : y = 0 := by
      simp [gap2] at hy hy'
      linarith
    refine ⟨a, by simp, ?_⟩
    rw [hy0, gap2]
  · have hab' : a < b := lt_of_le_of_ne hab heq
    have ha := abs_le.mp (gap3 a a)
    have hb := abs_le.mp (gap3 a b)
    have hymem : y ∈ Set.Icc (-1 : ℝ) 1 :=
      ⟨le_trans (le_min ha.1 hb.1) hy,
        le_trans hy' (max_le ha.2 hb.2)⟩
    have him : y ∈ osc a '' Set.Icc a b := by
      rw [gap1 a b hab']
      exact hymem
    rcases him with ⟨ξ, hξ, hval⟩
    exact ⟨ξ, hξ, hval⟩
theorem gap5 (a : ℝ) : ¬ ContinuousAt (osc a) a := by
  intro hcont
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨δ, hδ, hclose⟩ := hcont (1 / 2 : ℝ) (by norm_num)
  have hac : a < a + δ / 2 := by linarith
  have hone : (1 : ℝ) ∈ osc a '' Set.Icc a (a + δ / 2) := by
    rw [gap1 a (a + δ / 2) hac]
    norm_num
  rcases hone with ⟨x, hx, hval⟩
  have hdist : dist x a < δ := by
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hx.1)]
    linarith [hx.2]
  have hout := hclose hdist
  rw [hval, gap2] at hout
  norm_num [Real.dist_eq] at hout
theorem gap6 (a b : ℝ) (hab : a < b) :
    ¬ ContinuousOn (osc a) (Set.Icc a b) := by
  intro hcont
  have hca := hcont a ⟨le_rfl, hab.le⟩
  rw [Metric.continuousWithinAt_iff] at hca
  obtain ⟨δ, hδ, hclose⟩ := hca (1 / 2 : ℝ) (by norm_num)
  let c : ℝ := min b (a + δ / 2)
  have hac : a < c := by
    dsimp [c]
    exact lt_min hab (by linarith)
  have hone : (1 : ℝ) ∈ osc a '' Set.Icc a c := by
    rw [gap1 a c hac]
    norm_num
  rcases hone with ⟨x, hx, hval⟩
  have hxin : x ∈ Set.Icc a b :=
    ⟨hx.1, le_trans hx.2 (min_le_left b (a + δ / 2))⟩
  have hdist : dist x a < δ := by
    rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hx.1)]
    have hcupper : c ≤ a + δ / 2 := by
      dsimp [c]
      exact min_le_right _ _
    linarith [hx.2]
  have hout := hclose hxin hdist
  rw [hval, gap2] at hout
  norm_num [Real.dist_eq] at hout
theorem gap7 (a b : ℝ) (hab : a < b) :
    (∀ y, min (osc a a) (osc a b) ≤ y →
      y ≤ max (osc a a) (osc a b) → ∃ ξ ∈ Set.Icc a b, osc a ξ = y) ∧
      ¬ ContinuousOn (osc a) (Set.Icc a b) := by
  constructor
  · intro y hy hy'
    have ha := (abs_le.mp (gap3 a a))
    have hb := (abs_le.mp (gap3 a b))
    have hylow : -1 ≤ y := le_trans (le_min ha.1 hb.1) hy
    have hyhigh : y ≤ 1 := le_trans hy' (max_le ha.2 hb.2)
    have him : y ∈ osc a '' Set.Icc a b := by
      rw [gap1 a b hab]
      exact ⟨hylow, hyhigh⟩
    rcases him with ⟨ξ, hξ, hval⟩
    exact ⟨ξ, hξ, hval⟩
  · intro hcont
    have hca := hcont a ⟨le_rfl, hab.le⟩
    rw [Metric.continuousWithinAt_iff] at hca
    obtain ⟨δ, hδ, hclose⟩ := hca (1 / 2 : ℝ) (by norm_num)
    let c : ℝ := min b (a + δ / 2)
    have hac : a < c := by
      dsimp [c]
      exact lt_min hab (by linarith)
    have hone : (1 : ℝ) ∈ osc a '' Set.Icc a c := by
      rw [gap1 a c hac]
      norm_num
    rcases hone with ⟨x, hx, hval⟩
    have hxin : x ∈ Set.Icc a b :=
      ⟨hx.1, le_trans hx.2 (min_le_left b (a + δ / 2))⟩
    have hdist : dist x a < δ := by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hx.1)]
      have hcupper : c ≤ a + δ / 2 := by
        dsimp [c]
        exact min_le_right _ _
      linarith [hx.2]
    have hout := hclose hxin hdist
    rw [hval, gap2] at hout
    norm_num [Real.dist_eq] at hout

end
end ProofGap.Exercise756
