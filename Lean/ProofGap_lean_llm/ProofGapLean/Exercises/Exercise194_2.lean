import ProofGapLean.Prelude.Elementary
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise194_2

noncomputable section

def f (x : ℝ) : ℝ := Real.sin (Real.pi / x)
def domain : Set ℝ := {x | x ≠ 0}
def positiveCondition (x : ℝ) : Prop :=
  ∃ k : ℕ,
    (2 * (k : ℝ) * Real.pi < Real.pi / x ∧
      Real.pi / x < (2 * (k : ℝ) + 1) * Real.pi) ∨
    (-(2 * (k : ℝ) + 2) * Real.pi < Real.pi / x ∧
      Real.pi / x < -(2 * (k : ℝ) + 1) * Real.pi)
def negativeCondition (x : ℝ) : Prop :=
  ∃ k : ℕ,
    ((2 * (k : ℝ) + 1) * Real.pi < Real.pi / x ∧
      Real.pi / x < (2 * (k : ℝ) + 2) * Real.pi) ∨
    (-(2 * (k : ℝ) + 1) * Real.pi < Real.pi / x ∧
      Real.pi / x < -2 * (k : ℝ) * Real.pi)

/-- Source: `proof_gap/exercise_194_2/1.txt`; give an admissible root. -/
theorem gap1 : ∃ x ∈ domain, f x = 0 := by
  refine ⟨1, by norm_num [domain], ?_⟩
  simp [f]

/-- Source: `proof_gap/exercise_194_2/2.txt`; bind the root and integer coherently. -/
theorem gap2 : ∀ x ∈ domain,
    f x = 0 ↔ ∃ k : ℤ, k ≠ 0 ∧ Real.pi / x = (k : ℝ) * Real.pi := by
  intro x hx
  have hx0 : x ≠ 0 := hx
  unfold f
  rw [Real.sin_eq_zero_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_, hk.symm⟩
    intro hk0
    subst k
    norm_num at hk
    exact (div_ne_zero Real.pi_ne_zero hx0) hk.symm
  · rintro ⟨k, _, hk⟩
    exact ⟨k, hk.symm⟩

/-- Source: `proof_gap/exercise_194_2/3.txt`; the source existential had no relation to x. -/
theorem gap3 : ∃ k : ℤ, k ≠ 0 := by
  exact ⟨1, by norm_num⟩

/-- Source: `proof_gap/exercise_194_2/4.txt`. -/
theorem gap4 : ∃ k : ℤ, k ≠ 0 := by
  exact gap3

/-- Source: `proof_gap/exercise_194_2/5.txt`; use an explicit image of nonzero integers. -/
theorem gap5 :
    {x : ℝ | x ∈ domain ∧ f x = 0} =
      {x : ℝ | ∃ k : ℤ, k ≠ 0 ∧ x = 1 / (k : ℝ)} := by
  apply Set.ext
  intro x
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hx, hf⟩
    rcases (gap2 x hx).mp hf with ⟨k, hk, hquot⟩
    have hx0 : x ≠ 0 := hx
    have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    refine ⟨k, hk, ?_⟩
    have hrecip : 1 / x = (k : ℝ) := by
      apply (mul_right_cancel₀ Real.pi_ne_zero)
      calc
        (1 / x) * Real.pi = Real.pi / x := by ring
        _ = (k : ℝ) * Real.pi := hquot
    field_simp [hx0, hk0] at hrecip ⊢
    nlinarith
  · rintro ⟨k, hk, rfl⟩
    have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    have hx : (1 / (k : ℝ)) ∈ domain := by
      simpa [domain] using one_div_ne_zero hk0
    refine ⟨hx, (gap2 _ hx).mpr ⟨k, hk, ?_⟩⟩
    field_simp [hk0]

private theorem sin_pos_nonneg_iff {y : ℝ} (hy : 0 ≤ y) :
    0 < Real.sin y ↔ ∃ k : ℕ,
      2 * (k : ℝ) * Real.pi < y ∧
        y < (2 * (k : ℝ) + 1) * Real.pi := by
  constructor
  · intro hsin
    let k : ℕ := ⌊y / (2 * Real.pi)⌋₊
    have hden : 0 < 2 * Real.pi := by positivity
    have hq : 0 ≤ y / (2 * Real.pi) := div_nonneg hy hden.le
    have hk_le : (k : ℝ) ≤ y / (2 * Real.pi) := Nat.floor_le hq
    have hk_lt : y / (2 * Real.pi) < (k : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    have hleft : (k : ℝ) * (2 * Real.pi) ≤ y :=
      (le_div_iff₀ hden).mp hk_le
    have hright : y < ((k : ℝ) + 1) * (2 * Real.pi) :=
      (div_lt_iff₀ hden).mp hk_lt
    let r : ℝ := y - (k : ℝ) * (2 * Real.pi)
    have hr_nonneg : 0 ≤ r := by
      dsimp [r]
      linarith
    have hr_two_pi : r < 2 * Real.pi := by
      dsimp [r]
      nlinarith [Real.pi_pos]
    have hperiod : Real.sin r = Real.sin y := by
      dsimp [r]
      exact Real.sin_sub_nat_mul_two_pi y k
    have hsinr : 0 < Real.sin r := by
      rw [hperiod]
      exact hsin
    have hr_pos : 0 < r := by
      apply lt_of_le_of_ne hr_nonneg
      intro hr
      have hy_eq : y = (k : ℝ) * (2 * Real.pi) := by
        dsimp [r] at hr
        linarith
      have hzero : Real.sin y = 0 := by
        rw [hy_eq]
        simpa using Real.sin_nat_mul_two_pi_sub 0 k
      linarith
    have hr_pi : r < Real.pi := by
      by_contra hnot
      have hpi_le : Real.pi ≤ r := le_of_not_gt hnot
      have hr_ne_pi : r ≠ Real.pi := by
        intro hr
        have hzero : Real.sin r = 0 := by
          rw [hr]
          exact Real.sin_pi
        linarith
      have hpi_lt : Real.pi < r :=
        lt_of_le_of_ne hpi_le (Ne.symm hr_ne_pi)
      have hsneg :
          Real.sin (r - (1 : ℕ) * (2 * Real.pi)) < 0 :=
        Real.sin_neg_of_neg_of_neg_pi_lt
          (by norm_num; linarith)
          (by norm_num; linarith)
      simpa using (lt_asymm hsinr (by simpa using hsneg))
    refine ⟨k, ?_, ?_⟩
    · dsimp [r] at hr_pos
      nlinarith
    · dsimp [r] at hr_pi
      nlinarith
  · rintro ⟨k, hleft, hright⟩
    have hrpos :
        0 < y - (k : ℝ) * (2 * Real.pi) := by
      nlinarith
    have hrpi :
        y - (k : ℝ) * (2 * Real.pi) < Real.pi := by
      nlinarith
    have hsin :=
      Real.sin_pos_of_pos_of_lt_pi hrpos hrpi
    simpa using hsin

private theorem sin_neg_nonneg_iff {y : ℝ} (hy : 0 ≤ y) :
    Real.sin y < 0 ↔ ∃ k : ℕ,
      (2 * (k : ℝ) + 1) * Real.pi < y ∧
        y < (2 * (k : ℝ) + 2) * Real.pi := by
  constructor
  · intro hsin
    let k : ℕ := ⌊y / (2 * Real.pi)⌋₊
    have hden : 0 < 2 * Real.pi := by positivity
    have hq : 0 ≤ y / (2 * Real.pi) := div_nonneg hy hden.le
    have hk_le : (k : ℝ) ≤ y / (2 * Real.pi) := Nat.floor_le hq
    have hk_lt : y / (2 * Real.pi) < (k : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    have hleft : (k : ℝ) * (2 * Real.pi) ≤ y :=
      (le_div_iff₀ hden).mp hk_le
    have hright : y < ((k : ℝ) + 1) * (2 * Real.pi) :=
      (div_lt_iff₀ hden).mp hk_lt
    let r : ℝ := y - (k : ℝ) * (2 * Real.pi)
    have hr_nonneg : 0 ≤ r := by
      dsimp [r]
      linarith
    have hr_two_pi : r < 2 * Real.pi := by
      dsimp [r]
      nlinarith [Real.pi_pos]
    have hperiod : Real.sin r = Real.sin y := by
      dsimp [r]
      exact Real.sin_sub_nat_mul_two_pi y k
    have hsinr : Real.sin r < 0 := by
      rw [hperiod]
      exact hsin
    have hr_pos : 0 < r := by
      apply lt_of_le_of_ne hr_nonneg
      intro hr
      have hy_eq : y = (k : ℝ) * (2 * Real.pi) := by
        dsimp [r] at hr
        linarith
      have hzero : Real.sin y = 0 := by
        rw [hy_eq]
        simpa using Real.sin_nat_mul_two_pi_sub 0 k
      linarith
    have hr_pi : Real.pi < r := by
      by_contra hnot
      have hr_le : r ≤ Real.pi := le_of_not_gt hnot
      rcases hr_le.eq_or_lt with hr | hr
      · have hzero : Real.sin r = 0 := by
          rw [hr]
          exact Real.sin_pi
        linarith
      · have := Real.sin_pos_of_pos_of_lt_pi hr_pos hr
        linarith
    refine ⟨k, ?_, ?_⟩
    · dsimp [r] at hr_pi
      nlinarith
    · nlinarith
  · rintro ⟨k, hleft, hright⟩
    have hrneg :
        y - ((k : ℝ) + 1) * (2 * Real.pi) < 0 := by
      nlinarith
    have hrnegpi :
        -Real.pi < y - ((k : ℝ) + 1) * (2 * Real.pi) := by
      nlinarith
    have hsin :=
      Real.sin_neg_of_neg_of_neg_pi_lt hrneg hrnegpi
    calc
      Real.sin y =
          Real.sin (y - (k + 1 : ℕ) * (2 * Real.pi)) := by
        symm
        exact Real.sin_sub_nat_mul_two_pi y (k + 1)
      _ < 0 := by
        simpa only [Nat.cast_add, Nat.cast_one] using hsin

private theorem sin_pos_iff_nat_intervals (y : ℝ) :
    0 < Real.sin y ↔ ∃ k : ℕ,
      (2 * (k : ℝ) * Real.pi < y ∧
        y < (2 * (k : ℝ) + 1) * Real.pi) ∨
      (-(2 * (k : ℝ) + 2) * Real.pi < y ∧
        y < -(2 * (k : ℝ) + 1) * Real.pi) := by
  constructor
  · intro hsin
    by_cases hy : 0 ≤ y
    · rcases (sin_pos_nonneg_iff hy).mp hsin with ⟨k, hk⟩
      exact ⟨k, Or.inl hk⟩
    · have hneg : Real.sin (-y) < 0 := by
        rw [Real.sin_neg]
        linarith
      rcases (sin_neg_nonneg_iff (by linarith : 0 ≤ -y)).mp hneg with
        ⟨k, hk⟩
      exact ⟨k, Or.inr ⟨by linarith, by linarith⟩⟩
  · rintro ⟨k, hk | hk⟩
    · exact (sin_pos_nonneg_iff (by
        nlinarith [Real.pi_pos] : 0 ≤ y)).mpr ⟨k, hk⟩
    · have hneg : Real.sin (-y) < 0 :=
        (sin_neg_nonneg_iff (by
          nlinarith [Real.pi_pos] : 0 ≤ -y)).mpr
          ⟨k, ⟨by linarith, by linarith⟩⟩
      rw [Real.sin_neg] at hneg
      linarith

private theorem sin_neg_iff_nat_intervals (y : ℝ) :
    Real.sin y < 0 ↔ ∃ k : ℕ,
      ((2 * (k : ℝ) + 1) * Real.pi < y ∧
        y < (2 * (k : ℝ) + 2) * Real.pi) ∨
      (-(2 * (k : ℝ) + 1) * Real.pi < y ∧
        y < -2 * (k : ℝ) * Real.pi) := by
  constructor
  · intro hsin
    by_cases hy : 0 ≤ y
    · rcases (sin_neg_nonneg_iff hy).mp hsin with ⟨k, hk⟩
      exact ⟨k, Or.inl hk⟩
    · have hpos : 0 < Real.sin (-y) := by
        rw [Real.sin_neg]
        linarith
      rcases (sin_pos_nonneg_iff (by linarith : 0 ≤ -y)).mp hpos with
        ⟨k, hk⟩
      exact ⟨k, Or.inr ⟨by linarith, by linarith⟩⟩
  · rintro ⟨k, hk | hk⟩
    · exact (sin_neg_nonneg_iff (by
        nlinarith [Real.pi_pos] : 0 ≤ y)).mpr ⟨k, hk⟩
    · have hpos : 0 < Real.sin (-y) :=
        (sin_pos_nonneg_iff (by
          nlinarith [Real.pi_pos] : 0 ≤ -y)).mpr
          ⟨k, ⟨by linarith, by linarith⟩⟩
      rw [Real.sin_neg] at hpos
      linarith

private theorem mul_pi_lt_pi_div_iff (a x : ℝ) :
    a * Real.pi < Real.pi / x ↔ a < 1 / x := by
  rw [show Real.pi / x = (1 / x) * Real.pi by ring]
  constructor <;> intro h <;> nlinarith [Real.pi_pos]

private theorem pi_div_lt_mul_pi_iff (a x : ℝ) :
    Real.pi / x < a * Real.pi ↔ 1 / x < a := by
  rw [show Real.pi / x = (1 / x) * Real.pi by ring]
  constructor <;> intro h <;> nlinarith [Real.pi_pos]

/-- Source: `proof_gap/exercise_194_2/6.txt`; restore x≠0. -/
theorem gap6 : ∀ x ∈ domain, f x > 0 ↔ positiveCondition x := by
  intro x _
  simpa [f, positiveCondition] using
    sin_pos_iff_nat_intervals (Real.pi / x)

/-- Source: `proof_gap/exercise_194_2/7.txt`; replace reciprocal endpoint 1/0 by x>1. -/
theorem gap7 :
    {x : ℝ | x ∈ domain ∧ f x > 0} =
      {x : ℝ | 1 < x ∨
        (∃ k : ℕ, 0 < k ∧ 1 / (2 * (k : ℝ) + 1) < x ∧
          x < 1 / (2 * (k : ℝ))) ∨
        (∃ k : ℕ, -1 / (2 * (k : ℝ) + 1) < x ∧
          x < -1 / (2 * (k : ℝ) + 2))} := by
  apply Set.ext
  intro x
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hx, hf⟩
    rcases (gap6 x hx).mp hf with ⟨k, hk | hk⟩
    · have hlow :
          2 * (k : ℝ) < 1 / x :=
        (mul_pi_lt_pi_div_iff _ _).mp hk.1
      have hupp :
          1 / x < 2 * (k : ℝ) + 1 :=
        (pi_div_lt_mul_pi_iff _ _).mp hk.2
      have hinvpos : 0 < 1 / x := by
        nlinarith
      have hxpos : 0 < x := one_div_pos.mp hinvpos
      by_cases hk0 : k = 0
      · subst k
        left
        have hupp' : 1 / x < 1 := by simpa using hupp
        simpa using (one_div_lt hxpos zero_lt_one).mp hupp'
      · right
        left
        have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
        have hApos : 0 < 2 * (k : ℝ) := by positivity
        have hBpos : 0 < 2 * (k : ℝ) + 1 := by positivity
        exact ⟨k, hkpos,
          (one_div_lt hxpos hBpos).mp hupp,
          (lt_one_div hApos hxpos).mp hlow⟩
    · have hlow :
          -(2 * (k : ℝ) + 2) < 1 / x :=
        (mul_pi_lt_pi_div_iff _ _).mp hk.1
      have hupp :
          1 / x < -(2 * (k : ℝ) + 1) :=
        (pi_div_lt_mul_pi_iff _ _).mp hk.2
      have hinvneg : 1 / x < 0 := by
        nlinarith
      have hxneg : x < 0 := one_div_neg.mp hinvneg
      have hk_nonneg : 0 ≤ (k : ℝ) := by positivity
      have hCneg : -(2 * (k : ℝ) + 2) < 0 := by linarith
      have hDneg : -(2 * (k : ℝ) + 1) < 0 := by linarith
      right
      right
      refine ⟨k, ?_, ?_⟩
      · simpa only [div_eq_mul_inv, inv_neg, neg_mul, one_mul] using
          (one_div_lt_of_neg hxneg hDneg).mp hupp
      · simpa only [div_eq_mul_inv, inv_neg, neg_mul, one_mul] using
          (lt_one_div_of_neg hCneg hxneg).mp hlow
  · intro hx
    have hx0 : x ∈ domain := by
      change x ≠ 0
      rcases hx with hx | hx | hx
      · linarith
      · rcases hx with ⟨_, _, hlow, _⟩
        have : 0 < x := lt_of_lt_of_le (by positivity) hlow.le
        linarith
      · rcases hx with ⟨k, hlow, hupp⟩
        have hdenpos : 0 < 2 * (k : ℝ) + 2 := by positivity
        have hendneg : -1 / (2 * (k : ℝ) + 2) < 0 :=
          div_neg_of_neg_of_pos (by norm_num) hdenpos
        have : x < 0 := hupp.trans hendneg
        linarith
    refine ⟨hx0, (gap6 x hx0).mpr ?_⟩
    unfold positiveCondition
    rcases hx with hx | hx | hx
    · have hxpos : 0 < x := by linarith
      have hupp : 1 / x < 1 :=
        (one_div_lt hxpos zero_lt_one).mpr (by simpa using hx)
      have hlow : 0 < 1 / x := one_div_pos.mpr hxpos
      refine ⟨0, Or.inl ⟨?_, ?_⟩⟩
      · simpa using (mul_pi_lt_pi_div_iff 0 x).mpr hlow
      · simpa using (pi_div_lt_mul_pi_iff 1 x).mpr hupp
    · rcases hx with ⟨k, hkpos, hlowx, huppx⟩
      have hApos : 0 < 2 * (k : ℝ) := by positivity
      have hBpos : 0 < 2 * (k : ℝ) + 1 := by positivity
      have hxpos : 0 < x := lt_of_lt_of_le (by positivity) hlowx.le
      have hlow : 2 * (k : ℝ) < 1 / x :=
        (lt_one_div hApos hxpos).mpr huppx
      have hupp : 1 / x < 2 * (k : ℝ) + 1 :=
        (one_div_lt hxpos hBpos).mpr hlowx
      exact ⟨k, Or.inl ⟨
        (mul_pi_lt_pi_div_iff _ _).mpr hlow,
        (pi_div_lt_mul_pi_iff _ _).mpr hupp⟩⟩
    · rcases hx with ⟨k, hlowx, huppx⟩
      have hk_nonneg : 0 ≤ (k : ℝ) := by positivity
      have hCneg : -(2 * (k : ℝ) + 2) < 0 := by linarith
      have hDneg : -(2 * (k : ℝ) + 1) < 0 := by linarith
      have hdenpos : 0 < 2 * (k : ℝ) + 2 := by positivity
      have hendneg : -1 / (2 * (k : ℝ) + 2) < 0 :=
        div_neg_of_neg_of_pos (by norm_num) hdenpos
      have hxneg : x < 0 := huppx.trans hendneg
      have hlow : -(2 * (k : ℝ) + 2) < 1 / x := by
        apply (lt_one_div_of_neg hCneg hxneg).mpr
        simpa only [div_eq_mul_inv, inv_neg, neg_mul, one_mul] using huppx
      have hupp : 1 / x < -(2 * (k : ℝ) + 1) := by
        apply (one_div_lt_of_neg hxneg hDneg).mpr
        simpa only [div_eq_mul_inv, inv_neg, neg_mul, one_mul] using hlowx
      exact ⟨k, Or.inr ⟨
        (mul_pi_lt_pi_div_iff _ _).mpr hlow,
        (pi_div_lt_mul_pi_iff _ _).mpr hupp⟩⟩

/-- Source: `proof_gap/exercise_194_2/8.txt`; restore x≠0. -/
theorem gap8 : ∀ x ∈ domain, f x < 0 ↔ negativeCondition x := by
  intro x _
  simpa [f, negativeCondition] using
    sin_neg_iff_nat_intervals (Real.pi / x)

/-- Source: `proof_gap/exercise_194_2/9.txt`. -/
theorem gap9 :
    {x : ℝ | x ∈ domain ∧ f x < 0} =
      {x : ℝ |
        (∃ k : ℕ, 1 / (2 * (k : ℝ) + 2) < x ∧
          x < 1 / (2 * (k : ℝ) + 1)) ∨
        x < -1 ∨
        (∃ k : ℕ, 0 < k ∧ -1 / (2 * (k : ℝ)) < x ∧
          x < -1 / (2 * (k : ℝ) + 1))} := by
  apply Set.ext
  intro x
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hx, hf⟩
    rcases (gap8 x hx).mp hf with ⟨k, hk | hk⟩
    · have hlow :
          2 * (k : ℝ) + 1 < 1 / x :=
        (mul_pi_lt_pi_div_iff _ _).mp hk.1
      have hupp :
          1 / x < 2 * (k : ℝ) + 2 :=
        (pi_div_lt_mul_pi_iff _ _).mp hk.2
      have hxpos : 0 < x := one_div_pos.mp (by nlinarith)
      have hApos : 0 < 2 * (k : ℝ) + 1 := by positivity
      have hBpos : 0 < 2 * (k : ℝ) + 2 := by positivity
      left
      exact ⟨k,
        (one_div_lt hxpos hBpos).mp hupp,
        (lt_one_div hApos hxpos).mp hlow⟩
    · have hlow :
          -(2 * (k : ℝ) + 1) < 1 / x :=
        (mul_pi_lt_pi_div_iff _ _).mp hk.1
      have hupp :
          1 / x < -2 * (k : ℝ) :=
        (pi_div_lt_mul_pi_iff _ _).mp hk.2
      have hxneg : x < 0 := one_div_neg.mp (by nlinarith)
      by_cases hk0 : k = 0
      · subst k
        right
        left
        have hlow' : (-1 : ℝ) < 1 / x := by simpa using hlow
        have := (lt_one_div_of_neg (by norm_num : (-1 : ℝ) < 0) hxneg).mp hlow'
        norm_num at this
        exact this
      · right
        right
        have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
        have hkcast : 0 < (k : ℝ) := by exact_mod_cast hkpos
        have hCneg : -(2 * (k : ℝ) + 1) < 0 := by linarith
        have hDneg : -2 * (k : ℝ) < 0 := by linarith
        refine ⟨k, hkpos, ?_, ?_⟩
        · simpa only [div_eq_mul_inv, inv_neg, neg_mul, one_mul] using
            (one_div_lt_of_neg hxneg hDneg).mp hupp
        · simpa only [div_eq_mul_inv, inv_neg, neg_mul, one_mul] using
            (lt_one_div_of_neg hCneg hxneg).mp hlow
  · intro hx
    have hx0 : x ∈ domain := by
      change x ≠ 0
      rcases hx with hx | hx | hx
      · rcases hx with ⟨_, hlow, _⟩
        have : 0 < x := lt_of_lt_of_le (by positivity) hlow.le
        linarith
      · linarith
      · rcases hx with ⟨k, hkpos, hlow, hupp⟩
        have hdenpos : 0 < 2 * (k : ℝ) + 1 := by positivity
        have hendneg : -1 / (2 * (k : ℝ) + 1) < 0 :=
          div_neg_of_neg_of_pos (by norm_num) hdenpos
        have : x < 0 := hupp.trans hendneg
        linarith
    refine ⟨hx0, (gap8 x hx0).mpr ?_⟩
    unfold negativeCondition
    rcases hx with hx | hx | hx
    · rcases hx with ⟨k, hlowx, huppx⟩
      have hApos : 0 < 2 * (k : ℝ) + 1 := by positivity
      have hBpos : 0 < 2 * (k : ℝ) + 2 := by positivity
      have hxpos : 0 < x := lt_of_lt_of_le (by positivity) hlowx.le
      have hlow : 2 * (k : ℝ) + 1 < 1 / x :=
        (lt_one_div hApos hxpos).mpr huppx
      have hupp : 1 / x < 2 * (k : ℝ) + 2 :=
        (one_div_lt hxpos hBpos).mpr hlowx
      exact ⟨k, Or.inl ⟨
        (mul_pi_lt_pi_div_iff _ _).mpr hlow,
        (pi_div_lt_mul_pi_iff _ _).mpr hupp⟩⟩
    · have hxneg : x < 0 := by linarith
      have hlow : (-1 : ℝ) < 1 / x := by
        apply (lt_one_div_of_neg (by norm_num : (-1 : ℝ) < 0) hxneg).mpr
        norm_num
        exact hx
      have hupp : 1 / x < 0 := one_div_neg.mpr hxneg
      refine ⟨0, Or.inr ⟨?_, ?_⟩⟩
      · simpa using (mul_pi_lt_pi_div_iff (-1) x).mpr hlow
      · simpa using (pi_div_lt_mul_pi_iff 0 x).mpr hupp
    · rcases hx with ⟨k, hkpos, hlowx, huppx⟩
      have hkcast : 0 < (k : ℝ) := by exact_mod_cast hkpos
      have hCneg : -(2 * (k : ℝ) + 1) < 0 := by linarith
      have hDneg : -2 * (k : ℝ) < 0 := by linarith
      have hdenpos : 0 < 2 * (k : ℝ) + 1 := by positivity
      have hendneg : -1 / (2 * (k : ℝ) + 1) < 0 :=
        div_neg_of_neg_of_pos (by norm_num) hdenpos
      have hxneg : x < 0 := huppx.trans hendneg
      have hlow : -(2 * (k : ℝ) + 1) < 1 / x := by
        apply (lt_one_div_of_neg hCneg hxneg).mpr
        simpa only [div_eq_mul_inv, inv_neg, neg_mul, one_mul] using huppx
      have hupp : 1 / x < -2 * (k : ℝ) := by
        apply (one_div_lt_of_neg hxneg hDneg).mpr
        simpa only [div_eq_mul_inv, inv_neg, neg_mul, one_mul] using hlowx
      exact ⟨k, Or.inr ⟨
        (mul_pi_lt_pi_div_iff _ _).mpr hlow,
        (pi_div_lt_mul_pi_iff _ _).mpr hupp⟩⟩

end

end ProofGap.Exercise194_2
