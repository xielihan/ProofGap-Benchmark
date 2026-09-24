import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise157

noncomputable section

def angleCondition (x : ℝ) : Prop :=
  x ≠ 0 ∧ ∃ k : ℕ,
    (2 * (k : ℝ) * Real.pi < Real.pi / x ∧
      Real.pi / x < (2 * (k : ℝ) + 1) * Real.pi) ∨
    (-(2 * (k : ℝ) + 2) * Real.pi < Real.pi / x ∧
      Real.pi / x < -(2 * (k : ℝ) + 1) * Real.pi)

def intervalCondition (x : ℝ) : Prop :=
  ∃ k : ℕ,
    ((k = 0 ∧ 1 < x) ∨
      (0 < k ∧ 1 / (2 * (k : ℝ) + 1) < x ∧ x < 1 / (2 * (k : ℝ)))) ∨
    (-1 / (2 * (k : ℝ) + 1) < x ∧ x < -1 / (2 * (k : ℝ) + 2))

def domain : Set ℝ := {x | x ≠ 0 ∧ 0 < Real.sin (Real.pi / x)}

private lemma normalizePiInterval (a b x : ℝ) :
    (a * Real.pi < Real.pi / x ∧ Real.pi / x < b * Real.pi) ↔
      (a < 1 / x ∧ 1 / x < b) := by
  constructor <;> rintro ⟨hlo, hhi⟩
  · constructor
    · apply (mul_lt_mul_iff_left₀ Real.pi_pos).mp
      calc
        a * Real.pi < Real.pi / x := hlo
        _ = (1 / x) * Real.pi := by ring
    · apply (mul_lt_mul_iff_left₀ Real.pi_pos).mp
      calc
        (1 / x) * Real.pi = Real.pi / x := by ring
        _ < b * Real.pi := hhi
  · constructor
    · calc
        a * Real.pi < (1 / x) * Real.pi :=
          (mul_lt_mul_iff_left₀ Real.pi_pos).2 hlo
        _ = Real.pi / x := by ring
    · calc
        Real.pi / x = (1 / x) * Real.pi := by ring
        _ < b * Real.pi := (mul_lt_mul_iff_left₀ Real.pi_pos).2 hhi

private lemma positiveReciprocalInterval (a b x : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hx : 0 < x) :
    (a < 1 / x ∧ 1 / x < b) ↔ (1 / b < x ∧ x < 1 / a) := by
  constructor <;> rintro ⟨hlo, hhi⟩
  · constructor
    · apply (div_lt_iff₀ hb).2
      have h := (div_lt_iff₀ hx).1 hhi
      nlinarith
    · apply (lt_div_iff₀ ha).2
      have h := (lt_div_iff₀ hx).1 hlo
      nlinarith
  · constructor
    · apply (lt_div_iff₀ hx).2
      have h := (lt_div_iff₀ ha).1 hhi
      nlinarith
    · apply (div_lt_iff₀ hx).2
      have h := (div_lt_iff₀ hb).1 hlo
      nlinarith

/-- Source: `proof_gap/exercise_157/1.txt`; positivity is conditional on domain membership. -/
theorem gap1 : ∀ x : ℝ, x ∈ domain → 0 < Real.sin (Real.pi / x) := by
  intro x hx
  exact hx.2

/-- Source: `proof_gap/exercise_157/2.txt`; k is existential and x≠0 is explicit. -/
theorem gap2 : ∀ x : ℝ, x ∈ domain ↔ angleCondition x := by
  intro x
  constructor
  · intro hdom
    refine ⟨hdom.1, ?_⟩
    let t : ℝ := Real.pi / x
    let θ : Real.Angle := (t : Real.Angle)
    let z : ℤ := toIocDiv Real.two_pi_pos (-Real.pi) t
    have hr : θ.toReal ∈ Set.Ioo 0 Real.pi := by
      rw [Real.Angle.toReal_mem_Ioo_iff_sign_pos, Real.Angle.sign,
        sign_eq_one_iff]
      simpa [θ, t] using hdom.2
    have hdecomp : θ.toReal + (z : ℝ) * (2 * Real.pi) = t := by
      simpa [θ, z, Real.Angle.toReal_coe] using
        (toIocMod_add_toIocDiv_mul Real.two_pi_pos (-Real.pi) t)
    by_cases hz : 0 ≤ z
    · let k : ℕ := z.toNat
      have hkz : (k : ℤ) = z := Int.toNat_of_nonneg hz
      have hkzr : (k : ℝ) = (z : ℝ) := by exact_mod_cast hkz
      refine ⟨k, Or.inl ⟨?_, ?_⟩⟩
      · change 2 * (k : ℝ) * Real.pi < t
        rw [← hdecomp, ← hkzr]
        ring_nf
        linarith [hr.1]
      · change t < (2 * (k : ℝ) + 1) * Real.pi
        rw [← hdecomp, ← hkzr]
        ring_nf
        linarith [hr.2]
    · have hzneg : z < 0 := lt_of_not_ge hz
      let k : ℕ := (-z - 1).toNat
      have hmnonneg : 0 ≤ -z - 1 := by omega
      have hkz : (k : ℤ) = -z - 1 := Int.toNat_of_nonneg hmnonneg
      have hzform : z = -(k : ℤ) - 1 := by omega
      have hzformr : (z : ℝ) = -(k : ℝ) - 1 := by exact_mod_cast hzform
      refine ⟨k, Or.inr ⟨?_, ?_⟩⟩
      · change -(2 * (k : ℝ) + 2) * Real.pi < t
        rw [← hdecomp, hzformr]
        ring_nf
        linarith [hr.1]
      · change t < -(2 * (k : ℝ) + 1) * Real.pi
        rw [← hdecomp, hzformr]
        ring_nf
        linarith [hr.2]
  · intro hang
    refine ⟨hang.1, ?_⟩
    rcases hang.2 with ⟨k, hpos | hneg⟩
    · let u := Real.pi / x - (k : ℝ) * (2 * Real.pi)
      have hu0 : 0 < u := by
        dsimp [u]
        linarith
      have hupi : u < Real.pi := by
        dsimp [u]
        linarith
      have hsinu : 0 < Real.sin u := Real.sin_pos_of_pos_of_lt_pi hu0 hupi
      have hperiod := Real.sin_sub_nat_mul_two_pi (Real.pi / x) k
      dsimp [u] at hsinu
      rwa [hperiod] at hsinu
    · let u := Real.pi / x + ((k : ℝ) + 1) * (2 * Real.pi)
      have hu0 : 0 < u := by
        dsimp [u]
        linarith
      have hupi : u < Real.pi := by
        dsimp [u]
        linarith
      have hsinu : 0 < Real.sin u := Real.sin_pos_of_pos_of_lt_pi hu0 hupi
      have hperiod := Real.sin_add_nat_mul_two_pi (Real.pi / x) (k + 1)
      dsimp [u] at hsinu
      convert hsinu using 1
      simpa only [Nat.cast_add, Nat.cast_one] using hperiod.symm

/-- Source: `proof_gap/exercise_157/3.txt`; handle k=0 without the undefined endpoint 1/0. -/
theorem gap3 : ∀ x : ℝ, angleCondition x ↔ intervalCondition x := by
  intro x
  constructor
  · rintro ⟨hxne, k, hpos | hneg⟩
    · have hnorm :
          2 * (k : ℝ) < 1 / x ∧ 1 / x < 2 * (k : ℝ) + 1 :=
        (normalizePiInterval _ _ x).1 hpos
      have hxpos : 0 < x := by
        rw [← one_div_pos]
        exact lt_of_le_of_lt (by positivity) hnorm.1
      by_cases hk : k = 0
      · refine ⟨k, Or.inl (Or.inl ⟨hk, ?_⟩)⟩
        subst k
        have hmul := (div_lt_iff₀ hxpos).1 hnorm.2
        norm_num at hmul ⊢
        exact hmul
      · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
        have ha : 0 < 2 * (k : ℝ) := by positivity
        have hb : 0 < 2 * (k : ℝ) + 1 := by positivity
        have hinter := (positiveReciprocalInterval
          (2 * (k : ℝ)) (2 * (k : ℝ) + 1) x ha hb hxpos).1 hnorm
        exact ⟨k, Or.inl (Or.inr ⟨hkpos, hinter⟩)⟩
    · let y : ℝ := -x
      have hyang :
          (2 * (k : ℝ) + 1) * Real.pi < Real.pi / y ∧
            Real.pi / y < (2 * (k : ℝ) + 2) * Real.pi := by
        dsimp [y]
        rw [div_neg]
        constructor <;> linarith
      have hnorm :
          2 * (k : ℝ) + 1 < 1 / y ∧ 1 / y < 2 * (k : ℝ) + 2 :=
        (normalizePiInterval _ _ y).1 hyang
      have hypos : 0 < y := by
        rw [← one_div_pos]
        exact lt_of_lt_of_le (by positivity) hnorm.1.le
      have ha : 0 < 2 * (k : ℝ) + 1 := by positivity
      have hb : 0 < 2 * (k : ℝ) + 2 := by positivity
      have hinter := (positiveReciprocalInterval
        (2 * (k : ℝ) + 1) (2 * (k : ℝ) + 2) y ha hb hypos).1 hnorm
      refine ⟨k, Or.inr ?_⟩
      dsimp [y] at hinter
      constructor
      · simpa only [neg_div, neg_neg] using neg_lt_neg hinter.2
      · simpa only [neg_div, neg_neg] using neg_lt_neg hinter.1
  · rintro ⟨k, (hzero | hpos) | hneg⟩
    · rcases hzero with ⟨rfl, hx⟩
      have hxpos : 0 < x := lt_trans zero_lt_one hx
      have hnorm : (0 : ℝ) < 1 / x ∧ 1 / x < 1 := by
        constructor
        · positivity
        · apply (div_lt_iff₀ hxpos).2
          simpa only [one_mul] using hx
      have hang := (normalizePiInterval 0 1 x).2 hnorm
      refine ⟨ne_of_gt hxpos, 0, Or.inl ?_⟩
      norm_num at hang ⊢
      exact hang
    · rcases hpos with ⟨hk, hxlo, hxhi⟩
      have ha : 0 < 2 * (k : ℝ) := by positivity
      have hb : 0 < 2 * (k : ℝ) + 1 := by positivity
      have hxpos : 0 < x := lt_trans (by positivity) hxlo
      have hnorm := (positiveReciprocalInterval
        (2 * (k : ℝ)) (2 * (k : ℝ) + 1) x ha hb hxpos).2 ⟨hxlo, hxhi⟩
      have hang := (normalizePiInterval
        (2 * (k : ℝ)) (2 * (k : ℝ) + 1) x).2 hnorm
      exact ⟨ne_of_gt hxpos, k, Or.inl hang⟩
    · let y : ℝ := -x
      have ha : 0 < 2 * (k : ℝ) + 1 := by positivity
      have hb : 0 < 2 * (k : ℝ) + 2 := by positivity
      have hyint :
          1 / (2 * (k : ℝ) + 2) < y ∧
            y < 1 / (2 * (k : ℝ) + 1) := by
        dsimp [y]
        constructor
        · simpa only [neg_div, neg_neg] using neg_lt_neg hneg.2
        · simpa only [neg_div, neg_neg] using neg_lt_neg hneg.1
      have hypos : 0 < y := lt_trans (by positivity) hyint.1
      have hnorm := (positiveReciprocalInterval
        (2 * (k : ℝ) + 1) (2 * (k : ℝ) + 2) y ha hb hypos).2 hyint
      have hyang := (normalizePiInterval
        (2 * (k : ℝ) + 1) (2 * (k : ℝ) + 2) y).2 hnorm
      have hxneg : x < 0 := by
        dsimp [y] at hypos
        linarith
      refine ⟨ne_of_lt hxneg, k, Or.inr ?_⟩
      dsimp [y] at hyang
      rw [div_neg] at hyang
      constructor <;> linarith

/-- Source: `proof_gap/exercise_157/4.txt`. -/
theorem gap4 : domain = {x : ℝ | intervalCondition x} := by
  ext x
  exact (gap2 x).trans (gap3 x)

end

end ProofGap.Exercise157
