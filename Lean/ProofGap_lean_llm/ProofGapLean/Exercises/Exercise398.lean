import ProofGapLean.Prelude.Elementary
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise398

noncomputable section

def f (x : ℝ) : ℝ := Real.arctan (1 / x)
def imageOn (g : ℝ → ℝ) (s : Set ℝ) : Set ℝ :=
  {y | ∃ x ∈ s, y = g x}
def OscillationOn (g : ℝ → ℝ) (s : Set ℝ) : ℝ :=
  sSup (imageOn g s) - sInf (imageOn g s)

/-- Exercise 398, gap 1. -/
private theorem oscillationOn_symmetric_interval (a : ℝ) (ha : 0 < a) :
    OscillationOn f (Set.Ioo (-a) a) =
      Real.pi / 2 - (-Real.pi / 2) := by
  have hnonempty : (imageOn f (Set.Ioo (-a) a)).Nonempty := by
    refine ⟨0, ?_⟩
    refine ⟨0, ⟨by linarith, by linarith⟩, ?_⟩
    simp [f]
  have hbddAbove : BddAbove (imageOn f (Set.Ioo (-a) a)) := by
    refine ⟨Real.pi / 2, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    simpa [f] using (Real.arctan_lt_pi_div_two (1 / x)).le
  have hbddBelow : BddBelow (imageOn f (Set.Ioo (-a) a)) := by
    refine ⟨-(Real.pi / 2), ?_⟩
    rintro y ⟨x, hx, rfl⟩
    simpa [f] using (Real.neg_pi_div_two_lt_arctan (1 / x)).le
  have hexists_gt : ∀ b : ℝ, b < Real.pi / 2 →
      ∃ y ∈ imageOn f (Set.Ioo (-a) a), b < y := by
    intro b hb
    by_cases hb0 : b < 0
    · refine ⟨0, ?_, hb0⟩
      refine ⟨0, ⟨by linarith, by linarith⟩, ?_⟩
      simp [f]
    · have hb0' : 0 ≤ b := le_of_not_gt hb0
      have hlow : -(Real.pi / 2) < b := by
        linarith [Real.pi_pos]
      let t : ℝ := Real.tan b + |Real.tan b| + 2 * (1 / a)
      have hainv : 0 < 1 / a := one_div_pos.mpr ha
      have ht_tan : Real.tan b < t := by
        dsimp [t]
        linarith [abs_nonneg (Real.tan b), hainv]
      have ht_large : 1 / a < t := by
        dsimp [t]
        linarith [neg_le_abs (Real.tan b), hainv]
      have ht_pos : 0 < t := lt_trans hainv ht_large
      have hxpos : 0 < 1 / t := one_div_pos.mpr ht_pos
      have hxlt : 1 / t < a := by
        have hmul : 1 < t * a := (div_lt_iff₀ ha).1 ht_large
        apply (div_lt_iff₀ ht_pos).2
        nlinarith
      have harctan : b < Real.arctan t := by
        calc
          b = Real.arctan (Real.tan b) :=
            (Real.arctan_tan hlow hb).symm
          _ < Real.arctan t := Real.arctan_strictMono ht_tan
      refine ⟨Real.arctan t, ?_, harctan⟩
      refine ⟨1 / t, ⟨by linarith, hxlt⟩, ?_⟩
      simp [f]
  have hexists_lt : ∀ b : ℝ, -(Real.pi / 2) < b →
      ∃ y ∈ imageOn f (Set.Ioo (-a) a), y < b := by
    intro b hb
    by_cases hb0 : 0 < b
    · refine ⟨0, ?_, hb0⟩
      refine ⟨0, ⟨by linarith, by linarith⟩, ?_⟩
      simp [f]
    · have hb0' : b ≤ 0 := le_of_not_gt hb0
      have hupp : b < Real.pi / 2 := by
        linarith [Real.pi_pos]
      let t : ℝ := Real.tan b - |Real.tan b| - 2 * (1 / a)
      have hainv : 0 < 1 / a := one_div_pos.mpr ha
      have ht_tan : t < Real.tan b := by
        dsimp [t]
        linarith [abs_nonneg (Real.tan b), hainv]
      have ht_small : t < -(1 / a) := by
        dsimp [t]
        linarith [le_abs_self (Real.tan b), hainv]
      have ht_neg : t < 0 := by
        linarith
      have hxneg : 1 / t < 0 := one_div_neg.mpr ht_neg
      have hxgt : -a < 1 / t := by
        have htfrac : t < (-1) / a := by
          simpa only [neg_div] using ht_small
        have hmul : t * a < -1 := (lt_div_iff₀ ha).1 htfrac
        apply (lt_div_iff_of_neg ht_neg).2
        nlinarith
      have harctan : Real.arctan t < b := by
        calc
          Real.arctan t < Real.arctan (Real.tan b) :=
            Real.arctan_strictMono ht_tan
          _ = b := Real.arctan_tan hb hupp
      refine ⟨Real.arctan t, ?_, harctan⟩
      refine ⟨1 / t, ⟨hxgt, by linarith⟩, ?_⟩
      simp [f]
  have hsup_le : sSup (imageOn f (Set.Ioo (-a) a)) ≤ Real.pi / 2 := by
    apply csSup_le hnonempty
    rintro y ⟨x, hx, rfl⟩
    simpa [f] using (Real.arctan_lt_pi_div_two (1 / x)).le
  have hsup_ge : Real.pi / 2 ≤ sSup (imageOn f (Set.Ioo (-a) a)) := by
    by_contra h
    have hlt : sSup (imageOn f (Set.Ioo (-a) a)) < Real.pi / 2 :=
      lt_of_not_ge h
    obtain ⟨y, hy, hygt⟩ := hexists_gt _ hlt
    have hyle := le_csSup hbddAbove hy
    linarith
  have hsup : sSup (imageOn f (Set.Ioo (-a) a)) = Real.pi / 2 :=
    le_antisymm hsup_le hsup_ge
  have hinf_ge : -(Real.pi / 2) ≤ sInf (imageOn f (Set.Ioo (-a) a)) := by
    apply le_csInf hnonempty
    rintro y ⟨x, hx, rfl⟩
    simpa [f] using (Real.neg_pi_div_two_lt_arctan (1 / x)).le
  have hinf_le : sInf (imageOn f (Set.Ioo (-a) a)) ≤ -(Real.pi / 2) := by
    by_contra h
    have hlt : -(Real.pi / 2) < sInf (imageOn f (Set.Ioo (-a) a)) :=
      lt_of_not_ge h
    obtain ⟨y, hy, hylt⟩ := hexists_lt _ hlt
    have hle := csInf_le hbddBelow hy
    linarith
  have hinf : sInf (imageOn f (Set.Ioo (-a) a)) = -(Real.pi / 2) :=
    le_antisymm hinf_le hinf_ge
  unfold OscillationOn
  rw [hsup, hinf]
  ring

theorem gap1 : OscillationOn f (Set.Ioo (-1) 1) =
    Real.pi / 2 - (-Real.pi / 2) := by
  simpa using
    (oscillationOn_symmetric_interval (1 : ℝ) (by norm_num))

/-- Exercise 398, gap 2. -/
theorem gap2 : Real.pi / 2 - (-Real.pi / 2) = Real.pi := by
  ring

/-- Exercise 398, gap 3. -/
theorem gap3 : OscillationOn f (Set.Ioo (-1) 1) = Real.pi := by
  calc
    OscillationOn f (Set.Ioo (-1) 1) =
        Real.pi / 2 - (-Real.pi / 2) := gap1
    _ = Real.pi := gap2

/-- Exercise 398, gap 4. -/
theorem gap4 : OscillationOn f (Set.Ioo (-0.1) 0.1) = Real.pi := by
  calc
    OscillationOn f (Set.Ioo (-0.1) 0.1) =
        Real.pi / 2 - (-Real.pi / 2) :=
      oscillationOn_symmetric_interval (0.1 : ℝ) (by norm_num)
    _ = Real.pi := gap2

/-- Exercise 398, gap 5. -/
theorem gap5 : OscillationOn f (Set.Ioo (-0.01) 0.01) = Real.pi := by
  calc
    OscillationOn f (Set.Ioo (-0.01) 0.01) =
        Real.pi / 2 - (-Real.pi / 2) :=
      oscillationOn_symmetric_interval (0.01 : ℝ) (by norm_num)
    _ = Real.pi := gap2

/-- Exercise 398, gap 6. -/
theorem gap6 : OscillationOn f (Set.Ioo (-0.001) 0.001) = Real.pi := by
  calc
    OscillationOn f (Set.Ioo (-0.001) 0.001) =
        Real.pi / 2 - (-Real.pi / 2) :=
      oscillationOn_symmetric_interval (0.001 : ℝ) (by norm_num)
    _ = Real.pi := gap2

end

end ProofGap.Exercise398
