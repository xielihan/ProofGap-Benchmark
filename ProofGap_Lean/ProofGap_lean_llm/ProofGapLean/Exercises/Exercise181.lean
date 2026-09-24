import ProofGapLean.Prelude.Elementary
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise181

noncomputable section

def cot (x : ℝ) : ℝ := Real.cos x / Real.sin x
def y (x : ℝ) : ℝ := cot (Real.pi * x / 4)
def domain : Set ℝ := {x | 0 < |x| ∧ |x| ≤ 1}
def valueSet : Set ℝ := {t | ∃ x ∈ domain, t = y x}

private lemma y_neg (x : ℝ) : y (-x) = -y x := by
  have harg : Real.pi * (-x) / 4 = -(Real.pi * x / 4) := by ring
  unfold y cot
  rw [harg, Real.cos_neg, Real.sin_neg]
  ring

private lemma exists_positive_preimage (t : ℝ) (ht : 1 ≤ t) :
    ∃ x ∈ Set.Ioc (0 : ℝ) 1, y x = t := by
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  let theta : ℝ := Real.arctan (1 / t)
  let x : ℝ := 4 * theta / Real.pi
  have honepos : 0 < 1 / t := by positivity
  have honele : 1 / t ≤ 1 := by
    apply (div_le_iff₀ ht0).2
    simpa only [one_mul] using ht
  have htheta0 : 0 < theta := by
    dsimp [theta]
    exact (Real.arctan_pos).2 honepos
  have hthetap : theta ≤ Real.pi / 4 := by
    dsimp [theta]
    rw [← Real.arctan_one]
    exact Real.arctan_mono honele
  have hx0 : 0 < x := by
    dsimp [x]
    positivity
  have hx1 : x ≤ 1 := by
    dsimp [x]
    apply (div_le_iff₀ Real.pi_pos).2
    linarith
  refine ⟨x, ⟨hx0, hx1⟩, ?_⟩
  have htheta_mem : theta ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    constructor
    · exact htheta0
    · linarith [Real.pi_pos]
  have hsin : Real.sin theta ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi htheta0
      (by linarith [Real.pi_pos]))
  have hcos : Real.cos theta ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_pos], htheta_mem.2⟩)
  have htan : Real.sin theta / Real.cos theta = 1 / t := by
    rw [← Real.tan_eq_sin_div_cos]
    dsimp [theta]
    exact Real.tan_arctan _
  have hcot : Real.cos theta / Real.sin theta = t := by
    field_simp [hsin, hcos, ne_of_gt ht0] at htan ⊢
    nlinarith
  unfold y cot
  have harg : Real.pi * x / 4 = theta := by
    dsimp [x]
    field_simp [Real.pi_ne_zero]
  rw [harg]
  exact hcot

/-- Exercise 181, gap 1. -/
theorem gap1 : domain = Set.Ico (-1) 0 ∪ Set.Ioc 0 1 := by
  ext x
  constructor
  · rintro ⟨hx0, hx1⟩
    have hxne : x ≠ 0 := (abs_pos.mp hx0)
    have hbounds := abs_le.mp hx1
    rcases lt_or_gt_of_ne hxne with hxneg | hxpos
    · exact Or.inl ⟨hbounds.1, hxneg⟩
    · exact Or.inr ⟨hxpos, hbounds.2⟩
  · intro hx
    rcases hx with ⟨hxlo, hxhi⟩ | ⟨hxlo, hxhi⟩
    · change 0 < |x| ∧ |x| ≤ 1
      rw [abs_of_neg hxhi]
      constructor <;> linarith
    · change 0 < |x| ∧ |x| ≤ 1
      rw [abs_of_pos hxlo]
      exact ⟨hxlo, hxhi⟩

/-- Exercise 181, gap 2. -/
theorem gap2 : ∀ x : ℝ, x ∈ Set.Ioc 0 1 →
    Real.pi * x / 4 ∈ Set.Ioc 0 (Real.pi / 4) := by
  intro x hx
  constructor
  · exact div_pos (mul_pos Real.pi_pos hx.1) (by norm_num)
  · apply (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 4)).2
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hx.2 Real.pi_pos.le

/-- Exercise 181, gap 3. -/
theorem gap3 : ∀ x : ℝ, x ∈ Set.Ioc 0 1 → y x ∈ Set.Ici 1 := by
  intro x hx
  have htheta := gap2 x hx
  let theta := Real.pi * x / 4
  have htheta_pi2 : theta < Real.pi / 2 := by
    dsimp [theta]
    linarith [Real.pi_pos, htheta.2]
  have hsin : 0 < Real.sin theta :=
    Real.sin_pos_of_pos_of_lt_pi htheta.1 (by linarith [Real.pi_pos])
  have hcos : 0 < Real.cos theta :=
    Real.cos_pos_of_mem_Ioo
      ⟨lt_trans (by linarith [Real.pi_pos]) htheta.1, htheta_pi2⟩
  have htheta_mem : theta ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨lt_trans (by linarith [Real.pi_pos]) htheta.1, htheta_pi2⟩
  have hp4mem : Real.pi / 4 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [Real.pi_pos]
  have htan : Real.tan theta ≤ 1 := by
    have h := Real.strictMonoOn_tan.monotoneOn htheta_mem hp4mem htheta.2
    simpa [Real.tan_pi_div_four] using h
  rw [Real.tan_eq_sin_div_cos] at htan
  have hsincos : Real.sin theta ≤ Real.cos theta :=
    (div_le_one hcos).1 htan
  unfold y cot
  change 1 ≤ Real.cos theta / Real.sin theta
  exact (le_div_iff₀ hsin).2 (by simpa using hsincos)

/-- Exercise 181, gap 4. -/
theorem gap4 : ∀ x : ℝ, x ∈ Set.Ico (-1) 0 →
    Real.pi * x / 4 ∈ Set.Ico (-Real.pi / 4) 0 := by
  intro x hx
  constructor
  · apply (div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 4)).2
    have h := mul_le_mul_of_nonneg_left hx.1 Real.pi_pos.le
    simpa using h
  · exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg Real.pi_pos hx.2)
      (by norm_num)

/-- Exercise 181, gap 5. -/
theorem gap5 : ∀ x : ℝ, x ∈ Set.Ico (-1) 0 → y x ∈ Set.Iic (-1) := by
  intro x hx
  have hnegx : -x ∈ Set.Ioc (0 : ℝ) 1 := by
    constructor <;> linarith [hx.1, hx.2]
  have h := gap3 (-x) hnegx
  rw [y_neg] at h
  change 1 ≤ -y x at h
  change y x ≤ -1
  linarith

/-- Exercise 181, gap 6; endpoints ±1 are attained, so the source's strict `1<|t|` is corrected. -/
theorem gap6 : valueSet = {t : ℝ | 1 ≤ |t|} := by
  ext t
  constructor
  · rintro ⟨x, hxdom, rfl⟩
    change 1 ≤ |y x|
    rw [gap1] at hxdom
    rcases hxdom with hxneg | hxpos
    · have h := gap5 x hxneg
      change y x ≤ -1 at h
      rw [abs_of_nonpos (by linarith [h])]
      linarith
    · have h := gap3 x hxpos
      change 1 ≤ y x at h
      rw [abs_of_nonneg (by linarith [h])]
      exact h
  · intro ht
    change 1 ≤ |t| at ht
    rcases (le_total 0 t) with ht0 | ht0
    · rw [abs_of_nonneg ht0] at ht
      rcases exists_positive_preimage t ht with ⟨x, hx, hy⟩
      refine ⟨x, ?_, hy.symm⟩
      rw [gap1]
      exact Or.inr hx
    · rw [abs_of_nonpos ht0] at ht
      have hneg : 1 ≤ -t := ht
      rcases exists_positive_preimage (-t) hneg with ⟨x, hx, hy⟩
      refine ⟨-x, ?_, ?_⟩
      · rw [gap1]
        exact Or.inl ⟨by linarith [hx.2], by linarith [hx.1]⟩
      · rw [y_neg, hy]
        simp

end

end ProofGap.Exercise181
