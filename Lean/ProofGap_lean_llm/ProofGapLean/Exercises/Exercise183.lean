import ProofGapLean.Prelude.Sequences
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Filter Topology

namespace ProofGap.Exercise183

def y (a b x : ℝ) : ℝ := a + (b - a) * x
def domain : Set ℝ := Set.Ioo 0 1
def valueSet (a b : ℝ) : Set ℝ := {t | ∃ x ∈ domain, t = y a b x}

/-- Source: `proof_gap/exercise_183/1.txt`. -/
theorem gap1 (a b : ℝ) :
    Tendsto (y a b) (𝓝[Set.Ioi 0] 0) (𝓝 a) := by
  have hc : Continuous (y a b) := by
    unfold y
    fun_prop
  have htend :
      Tendsto (y a b) (𝓝[Set.Ioi 0] 0) (𝓝 (y a b 0)) :=
    hc.continuousAt.continuousWithinAt
  convert htend using 1
  · unfold y
    ring

/-- Source: `proof_gap/exercise_183/2.txt`. -/
theorem gap2 (a b : ℝ) :
    Tendsto (y a b) (𝓝[Set.Iio 1] 1) (𝓝 b) := by
  have hc : Continuous (y a b) := by
    unfold y
    fun_prop
  have htend :
      Tendsto (y a b) (𝓝[Set.Iio 1] 1) (𝓝 (y a b 1)) :=
    hc.continuousAt.continuousWithinAt
  convert htend using 1
  · unfold y
    ring

/-- Source: `proof_gap/exercise_183/3.txt`. -/
theorem gap3 (a b : ℝ) (h : a < b) : valueSet a b = Set.Ioo a b := by
  ext t
  constructor
  · rintro ⟨x, ⟨hx0, hx1⟩, rfl⟩
    unfold y
    constructor
    · have hmul := mul_pos (sub_pos.mpr h) hx0
      linarith
    · have hmul := mul_lt_mul_of_pos_left hx1 (sub_pos.mpr h)
      linarith
  · rintro ⟨htlo, hthi⟩
    let x := (t - a) / (b - a)
    have hden : 0 < b - a := sub_pos.mpr h
    have hx0 : 0 < x := by
      dsimp [x]
      exact div_pos (sub_pos.mpr htlo) hden
    have hx1 : x < 1 := by
      dsimp [x]
      apply (div_lt_iff₀ hden).2
      linarith
    refine ⟨x, ⟨hx0, hx1⟩, ?_⟩
    unfold y
    dsimp [x]
    field_simp [ne_of_gt hden]
    ring

/-- Source: `proof_gap/exercise_183/4.txt`. -/
theorem gap4 (a b : ℝ) (h : b < a) : valueSet a b = Set.Ioo b a := by
  ext t
  constructor
  · rintro ⟨x, ⟨hx0, hx1⟩, rfl⟩
    unfold y
    constructor
    · have hmul := mul_lt_mul_of_neg_left hx1 (sub_neg.mpr h)
      linarith
    · have hmul := mul_neg_of_neg_of_pos (sub_neg.mpr h) hx0
      linarith
  · rintro ⟨htlo, hthi⟩
    let x := (t - a) / (b - a)
    have hden : b - a < 0 := sub_neg.mpr h
    have hx0 : 0 < x := by
      dsimp [x]
      exact div_pos_of_neg_of_neg (sub_neg.mpr hthi) hden
    have hx1 : x < 1 := by
      dsimp [x]
      apply (div_lt_iff_of_neg hden).2
      linarith
    refine ⟨x, ⟨hx0, hx1⟩, ?_⟩
    unfold y
    dsimp [x]
    field_simp [ne_of_lt hden]
    ring

end ProofGap.Exercise183
