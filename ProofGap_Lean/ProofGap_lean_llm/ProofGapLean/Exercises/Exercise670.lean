import ProofGapLean.Prelude.Sequences
import ProofGapLean.Prelude.Discrete
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise670

noncomputable section

def f (x : ℝ) : ℝ := x + 0.001 * (Int.floor x : ℝ)
def IsInteger (x : ℝ) : Prop := ∃ z : ℤ, (z : ℝ) = x
def localRadius (ε x₀ : ℝ) (n : ℤ) : ℝ :=
  min (min (x₀ - n) (n + 1 - x₀)) ε

/-- Exercise 670, gap 1. -/
private theorem floor_sub_abs_le_one {x y : ℝ} (h : |y - x| < 1) :
    |(Int.floor x : ℝ) - Int.floor y| ≤ 1 := by
  have hyx : y < x + 1 := by
    have ha := (abs_lt.mp h).2
    linarith
  have hxy : x < y + 1 := by
    have ha := (abs_lt.mp h).1
    linarith
  have hfloor_y : Int.floor y ≤ Int.floor x + 1 := by
    have hm := Int.floor_mono (le_of_lt hyx)
    simpa using hm
  have hfloor_x : Int.floor x ≤ Int.floor y + 1 := by
    have hm := Int.floor_mono (le_of_lt hxy)
    simpa using hm
  rw [abs_le]
  constructor
  · have hz : -(1 : ℤ) ≤ Int.floor x - Int.floor y := by omega
    have hc :
        (↑(-(1 : ℤ)) : ℝ) ≤
          (↑(Int.floor x - Int.floor y) : ℝ) :=
      (Int.cast_le).2 hz
    simpa only [Int.cast_neg, Int.cast_one, Int.cast_sub] using hc
  · have hz : Int.floor x - Int.floor y ≤ (1 : ℤ) := by omega
    have hc :
        (↑(Int.floor x - Int.floor y) : ℝ) ≤ (↑(1 : ℤ) : ℝ) :=
      (Int.cast_le).2 hz
    simpa only [Int.cast_sub, Int.cast_one] using hc

theorem gap1 (x₁ ε x : ℝ) (hε : 0.001 < ε) (h : |x₁ - x| < 1) :
    |f x₁ - f x| =
      |x - x₁ + 0.001 * ((Int.floor x : ℝ) - Int.floor x₁)| := by
  have heq :
      f x₁ - f x =
        -(x - x₁ + 0.001 * ((Int.floor x : ℝ) - Int.floor x₁)) := by
    unfold f
    ring
  rw [heq, abs_neg]

/-- Exercise 670, gap 2; use the fact that floors differ by at most one locally. -/
theorem gap2 (x₁ ε x : ℝ) (hε : 0.001 < ε) (h : |x₁ - x| < 1) :
    |x - x₁ + 0.001 * ((Int.floor x : ℝ) - Int.floor x₁)| ≤
      |x - x₁| + 0.001 := by
  have hfloor :
      |(Int.floor x : ℝ) - Int.floor x₁| ≤ 1 :=
    floor_sub_abs_le_one h
  have hcoeff :
      |(0.001 : ℝ) * ((Int.floor x : ℝ) - Int.floor x₁)| ≤ 0.001 := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.001)]
    nlinarith
  have habs :
      |x - x₁ + 0.001 * ((Int.floor x : ℝ) - Int.floor x₁)| ≤
        |x - x₁| + |0.001 * ((Int.floor x : ℝ) - Int.floor x₁)| := by
    rw [abs_le]
    constructor
    · nlinarith [neg_le_abs (x - x₁),
        neg_le_abs (0.001 * ((Int.floor x : ℝ) - Int.floor x₁))]
    · nlinarith [le_abs_self (x - x₁),
        le_abs_self (0.001 * ((Int.floor x : ℝ) - Int.floor x₁))]
  nlinarith

/-- Exercise 670, gap 3. -/
theorem gap3 (x₁ ε x : ℝ) (hε : 0.001 < ε) (h : |x₁ - x| < 1) :
    |f x₁ - f x| ≤ |x - x₁| + 0.001 := by
  calc
    |f x₁ - f x| =
        |x - x₁ + 0.001 * ((Int.floor x : ℝ) - Int.floor x₁)| :=
      gap1 x₁ ε x hε h
    _ ≤ |x - x₁| + 0.001 := gap2 x₁ ε x hε h

/-- Exercise 670, gap 4; remove shadowed binders. -/
theorem gap4 (ε x : ℝ) (hε : 0.001 < ε) :
    ∃ δ > 0, ∀ x₁, |x - x₁| < δ → |f x - f x₁| < ε := by
  refine ⟨min 1 (ε - 0.001), lt_min (by norm_num) (sub_pos.mpr hε), ?_⟩
  intro x₁ hx₁
  have hlocal : |x₁ - x| < 1 := by
    rw [abs_sub_comm]
    exact lt_of_lt_of_le hx₁ (min_le_left _ _)
  have hsmall : |x - x₁| < ε - 0.001 :=
    lt_of_lt_of_le hx₁ (min_le_right _ _)
  calc
    |f x - f x₁| = |f x₁ - f x| := abs_sub_comm _ _
    _ ≤ |x - x₁| + 0.001 := gap3 x₁ ε x hε hlocal
    _ < ε := by linarith

/-- Exercise 670, gap 5. -/
theorem gap5 (ε x₀ : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 0.001)
    (hx₀ : ¬ IsInteger x₀) :
    ∃ n : ℤ, (n : ℝ) < x₀ ∧ x₀ < n + 1 := by
  refine ⟨Int.floor x₀, ?_, Int.lt_floor_add_one x₀⟩
  have hne : (Int.floor x₀ : ℝ) ≠ x₀ := by
    intro heq
    apply hx₀
    exact ⟨Int.floor x₀, heq⟩
  exact lt_of_le_of_ne (Int.floor_le x₀) hne

/-- Exercise 670, gap 6; bind the integer bracketing `x₀`. -/
theorem gap6 (ε x₀ : ℝ) (n : ℤ) (hε : 0 < ε)
    (hn : (n : ℝ) < x₀ ∧ x₀ < n + 1) :
    ∀ x, |x - x₀| < localRadius ε x₀ n →
      Int.floor x = Int.floor x₀ := by
  intro x hx
  have hrleft : localRadius ε x₀ n ≤ x₀ - (n : ℝ) := by
    unfold localRadius
    exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hrright : localRadius ε x₀ n ≤ (n : ℝ) + 1 - x₀ := by
    unfold localRadius
    exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hleft : |x - x₀| < x₀ - (n : ℝ) :=
    lt_of_lt_of_le hx hrleft
  have hright : |x - x₀| < (n : ℝ) + 1 - x₀ :=
    lt_of_lt_of_le hx hrright
  have hnx : (n : ℝ) < x := by
    have ha := (abs_lt.mp hleft).1
    linarith
  have hxn : x < (n : ℝ) + 1 := by
    have ha := (abs_lt.mp hright).2
    linarith
  have hfloorx : Int.floor x = n := by
    rw [Int.floor_eq_iff]
    exact ⟨le_of_lt hnx, hxn⟩
  have hfloorx₀ : Int.floor x₀ = n := by
    rw [Int.floor_eq_iff]
    exact ⟨le_of_lt hn.1, hn.2⟩
  exact hfloorx.trans hfloorx₀.symm

/-- Exercise 670, gap 7. -/
theorem gap7 (ε x₀ : ℝ) (n : ℤ) (hε : 0 < ε)
    (hn : (n : ℝ) < x₀ ∧ x₀ < n + 1) :
    ∀ x, |x - x₀| < localRadius ε x₀ n →
      |f x - f x₀| = |x - x₀| := by
  intro x hx
  have hfloor := gap6 ε x₀ n hε hn x hx
  simp only [f]
  rw [hfloor]
  congr 1
  ring

/-- Exercise 670, gap 8. -/
theorem gap8 (ε x₀ : ℝ) (n : ℤ) (x : ℝ)
    (h : |x - x₀| < localRadius ε x₀ n) :
    |x - x₀| < localRadius ε x₀ n := by
  exact h

/-- Exercise 670, gap 9. -/
theorem gap9 (ε x₀ : ℝ) (n : ℤ) :
    localRadius ε x₀ n ≤ ε := by
  unfold localRadius
  exact min_le_right _ _

/-- Exercise 670, gap 10; bind the bracketing integer. -/
theorem gap10 (ε x₀ : ℝ) (n : ℤ) (hε : 0 < ε)
    (hn : (n : ℝ) < x₀ ∧ x₀ < n + 1) :
    ∀ x, |x - x₀| < localRadius ε x₀ n →
      |f x - f x₀| < ε := by
  intro x hx
  rw [gap7 ε x₀ n hε hn x hx]
  exact lt_of_lt_of_le hx (gap9 ε x₀ n)

/-- Exercise 670, gap 11. -/
theorem gap11 (x₀ : ℝ) (hx₀ : IsInteger x₀) :
    ∀ δ > 0, ∃ x, x < x₀ ∧ x₀ - x < δ := by
  intro δ hδ
  refine ⟨x₀ - δ / 2, ?_, ?_⟩ <;> linarith

/-- Exercise 670, gap 12; include the omitted left-neighborhood conditions. -/
theorem gap12 (x₀ : ℝ) (hx₀ : IsInteger x₀) :
    ∀ δ > 0, ∃ x, x < x₀ ∧ x₀ - x < δ ∧
      |f x - f x₀| = x₀ - x + 0.001 := by
  rcases hx₀ with ⟨z, hz⟩
  intro δ hδ
  let r : ℝ := min (δ / 2) (1 / 2)
  have hrpos : 0 < r := by
    dsimp [r]
    exact lt_min (by linarith) (by norm_num)
  have hrδ : r < δ := by
    dsimp [r]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hrone : r < 1 := by
    dsimp [r]
    exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hfloorx : Int.floor (x₀ - r) = z - 1 := by
    rw [Int.floor_eq_iff]
    constructor
    · rw [← hz]
      simp only [Int.cast_sub, Int.cast_one]
      linarith
    · rw [← hz]
      simp only [Int.cast_sub, Int.cast_one]
      linarith
  have hfloorx₀ : Int.floor x₀ = z := by
    rw [← hz]
    simp
  have hdiff : f (x₀ - r) - f x₀ = -(r + 0.001) := by
    simp only [f, hfloorx, hfloorx₀, Int.cast_sub, Int.cast_one]
    ring
  have hsumpos : 0 < r + 0.001 := by
    linarith
  refine ⟨x₀ - r, by linarith, by linarith, ?_⟩
  calc
    |f (x₀ - r) - f x₀| = |-(r + 0.001)| := congrArg abs hdiff
    _ = |r + 0.001| := abs_neg _
    _ = r + 0.001 := abs_of_pos hsumpos
    _ = x₀ - (x₀ - r) + 0.001 := by ring

/-- Exercise 670, gap 13; choose a fixed positive jump witness. -/
theorem gap13 (x₀ : ℝ) (hx₀ : IsInteger x₀) :
    ∀ δ > 0, ∃ x, x < x₀ ∧ x₀ - x < δ ∧
      (0.0005 : ℝ) < x₀ - x + 0.001 := by
  intro δ hδ
  rcases gap11 x₀ hx₀ δ hδ with ⟨x, hx, hdist⟩
  refine ⟨x, hx, hdist, ?_⟩
  have hpos : 0 < x₀ - x := sub_pos.mpr hx
  linarith

/-- Exercise 670, gap 14; bind the epsilon witness. -/
theorem gap14 (x₀ : ℝ) (hx₀ : IsInteger x₀) :
    ∀ δ > 0, ∃ x, |x - x₀| < δ ∧
      (0.0005 : ℝ) < |f x - f x₀| := by
  intro δ hδ
  rcases gap12 x₀ hx₀ δ hδ with ⟨x, hx, hdist, hjump⟩
  refine ⟨x, ?_, ?_⟩
  · rw [abs_of_neg (sub_neg.mpr hx), neg_sub]
    exact hdist
  · rw [hjump]
    have hpos : 0 < x₀ - x := sub_pos.mpr hx
    linarith

/-- Exercise 670, gap 15. -/
theorem gap15 (x₀ : ℝ) (hx₀ : IsInteger x₀) :
    ¬ ContinuousAt f x₀ := by
  intro hcont
  rw [Metric.continuousAt_iff] at hcont
  rcases hcont (0.0005 : ℝ) (by norm_num) with ⟨δ, hδ, hclose⟩
  rcases gap14 x₀ hx₀ δ hδ with ⟨x, hx, hjump⟩
  have hxdist : dist x x₀ < δ := by
    simpa only [Real.dist_eq] using hx
  have hsmall := hclose hxdist
  simp only [Real.dist_eq] at hsmall
  linarith

/-- Exercise 670, gap 16. -/
theorem gap16 (n : ℤ) :
    ¬ ContinuousAt f (n : ℝ) := by
  exact gap15 (n : ℝ) ⟨n, rfl⟩

/-- Exercise 670, gap 17; separate the coarse epsilon estimate from discontinuity at integers. -/
theorem gap17 :
    (∀ x ε : ℝ, 0.001 < ε → ∃ δ > 0, ∀ x₁,
      |x₁ - x| < δ → |f x₁ - f x| < ε) ∧
    (∀ n : ℤ, ¬ ContinuousAt f (n : ℝ)) := by
  constructor
  · intro x ε hε
    rcases gap4 ε x hε with ⟨δ, hδ, hclose⟩
    refine ⟨δ, hδ, ?_⟩
    intro x₁ hx₁
    have hx₁' : |x - x₁| < δ := by
      rw [abs_sub_comm]
      exact hx₁
    have hout := hclose x₁ hx₁'
    rw [abs_sub_comm]
    exact hout
  · exact gap16

end

end ProofGap.Exercise670
