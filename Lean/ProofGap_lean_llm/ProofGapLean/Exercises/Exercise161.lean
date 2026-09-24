import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise161

noncomputable section

def lg (x : ℝ) : ℝ := Real.log x / Real.log 10
def pow10 (t : ℝ) : ℝ := Real.rpow 10 t
def domain : Set ℝ := {x | 0 < x ∧ 0 < Real.cos (lg x)}

def intervalCondition (x : ℝ) : Prop :=
  ∃ k : ℤ,
    pow10 (((2 : ℝ) * k - 1 / 2) * Real.pi) < x ∧
    x < pow10 (((2 : ℝ) * k + 1 / 2) * Real.pi)

/-- Exercise 161, gap 1; positivity is conditional on the logarithm's domain. -/
theorem gap1 : ∀ x : ℝ, x ∈ domain → 0 < Real.cos (lg x) := by
  intro x hx
  exact hx.2

/-- Exercise 161, gap 2; k is existentially chosen. -/
theorem gap2 : ∀ x : ℝ, x ∈ domain ↔
    0 < x ∧ ∃ k : ℤ,
      ((2 : ℝ) * k - 1 / 2) * Real.pi < lg x ∧
      lg x < ((2 : ℝ) * k + 1 / 2) * Real.pi := by
  intro x
  constructor
  · intro hx
    refine ⟨hx.1, ?_⟩
    let t : ℝ := lg x
    let θ : Real.Angle := (t : Real.Angle)
    let k : ℤ := toIocDiv Real.two_pi_pos (-Real.pi) t
    have hrabs : |θ.toReal| < Real.pi / 2 := by
      rw [← Real.Angle.cos_pos_iff_abs_toReal_lt_pi_div_two]
      simpa [θ, t] using hx.2
    have hrlo : -(Real.pi / 2) < θ.toReal := (abs_lt.mp hrabs).1
    have hrhi : θ.toReal < Real.pi / 2 := (abs_lt.mp hrabs).2
    have hdecomp : θ.toReal + (k : ℝ) * (2 * Real.pi) = t := by
      simpa [θ, k, Real.Angle.toReal_coe] using
        (toIocMod_add_toIocDiv_mul Real.two_pi_pos (-Real.pi) t)
    refine ⟨k, ?_, ?_⟩
    · change ((2 : ℝ) * k - 1 / 2) * Real.pi < t
      rw [← hdecomp]
      ring_nf
      linarith
    · change t < ((2 : ℝ) * k + 1 / 2) * Real.pi
      rw [← hdecomp]
      ring_nf
      linarith
  · rintro ⟨hx0, k, hklo, hkhi⟩
    refine ⟨hx0, ?_⟩
    let u := lg x - (k : ℝ) * (2 * Real.pi)
    have hulo : -(Real.pi / 2) < u := by
      dsimp [u]
      ring_nf at hklo ⊢
      linarith
    have huhi : u < Real.pi / 2 := by
      dsimp [u]
      ring_nf at hkhi ⊢
      linarith
    have hcosu : 0 < Real.cos u := Real.cos_pos_of_mem_Ioo ⟨hulo, huhi⟩
    have hperiod := Real.cos_sub_int_mul_two_pi (lg x) k
    dsimp [u] at hcosu
    rwa [hperiod] at hcosu

/-- Exercise 161, gap 3. -/
theorem gap3 : ∀ x : ℝ, x ∈ domain ↔ intervalCondition x := by
  intro x
  constructor
  · intro hx
    rcases (gap2 x).1 hx with ⟨hx0, k, hklo, hkhi⟩
    have hlogpow : pow10 (lg x) = x := by
      simpa [pow10, lg, Real.logb] using
        (Real.rpow_logb (x := x) (by norm_num : (0 : ℝ) < 10)
          (by norm_num : (10 : ℝ) ≠ 1) hx0)
    refine ⟨k, ?_, ?_⟩
    · rw [← hlogpow]
      exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hklo
    · rw [← hlogpow]
      exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hkhi
  · rintro ⟨k, hklo, hkhi⟩
    have hpowpos : 0 < pow10 (((2 : ℝ) * k - 1 / 2) * Real.pi) := by
      exact Real.rpow_pos_of_pos (by norm_num) _
    have hx0 : 0 < x := lt_trans hpowpos hklo
    have hlogpow : pow10 (lg x) = x := by
      simpa [pow10, lg, Real.logb] using
        (Real.rpow_logb (x := x) (by norm_num : (0 : ℝ) < 10)
          (by norm_num : (10 : ℝ) ≠ 1) hx0)
    apply (gap2 x).2
    refine ⟨hx0, k, ?_, ?_⟩
    · have hklo' :
          pow10 (((2 : ℝ) * k - 1 / 2) * Real.pi) < pow10 (lg x) := by
        rwa [hlogpow]
      exact (Real.rpow_lt_rpow_left_iff (by norm_num : (1 : ℝ) < 10)).1
        (by simpa [pow10] using hklo')
    · have hkhi' :
          pow10 (lg x) < pow10 (((2 : ℝ) * k + 1 / 2) * Real.pi) := by
        rwa [hlogpow]
      exact (Real.rpow_lt_rpow_left_iff (by norm_num : (1 : ℝ) < 10)).1
        (by simpa [pow10] using hkhi')

/-- Exercise 161, gap 4. -/
theorem gap4 : domain = {x : ℝ | intervalCondition x} := by
  ext x
  exact gap3 x

end

end ProofGap.Exercise161
