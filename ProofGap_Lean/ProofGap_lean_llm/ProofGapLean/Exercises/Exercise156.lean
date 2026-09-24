import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise156

noncomputable section

def phaseCondition (x : ℝ) : Prop :=
  0 ≤ x ^ 2 ∧ x ^ 2 ≤ Real.pi / 2 ∨
  ∃ k : ℕ, 0 < k ∧
    (4 * (k : ℝ) - 1) * Real.pi / 2 ≤ x ^ 2 ∧
    x ^ 2 ≤ (4 * (k : ℝ) + 1) * Real.pi / 2

def radialCondition (x : ℝ) : Prop :=
  |x| ≤ Real.sqrt (Real.pi / 2) ∨
  ∃ k : ℕ, 0 < k ∧
    Real.sqrt ((4 * (k : ℝ) - 1) * Real.pi / 2) ≤ |x| ∧
    |x| ≤ Real.sqrt ((4 * (k : ℝ) + 1) * Real.pi / 2)

def domain : Set ℝ := {x | 0 ≤ Real.cos (x ^ 2)}

/-- Exercise 156, gap 1; the inequality is the domain condition. -/
theorem gap1 : ∀ x : ℝ, x ∈ domain ↔ 0 ≤ Real.cos (x ^ 2) := by
  intro x
  rfl

/-- Exercise 156, gap 2; the phase intervals are existential. -/
theorem gap2 : ∀ x : ℝ, x ∈ domain ↔ phaseCondition x := by
  intro x
  change 0 ≤ Real.cos (x ^ 2) ↔ phaseCondition x
  constructor
  · intro hcos
    let t : ℝ := x ^ 2
    let θ : Real.Angle := (t : Real.Angle)
    let z : ℤ := toIocDiv Real.two_pi_pos (-Real.pi) t
    have ht0 : 0 ≤ t := by
      dsimp [t]
      positivity
    have hrabs : |θ.toReal| ≤ Real.pi / 2 := by
      rw [← Real.Angle.cos_nonneg_iff_abs_toReal_le_pi_div_two]
      simpa [θ, t] using hcos
    have hrlo : -(Real.pi / 2) ≤ θ.toReal := (abs_le.mp hrabs).1
    have hrhi : θ.toReal ≤ Real.pi / 2 := (abs_le.mp hrabs).2
    have hdecomp : θ.toReal + (z : ℝ) * (2 * Real.pi) = t := by
      simpa [θ, z, Real.Angle.toReal_coe] using
        (toIocMod_add_toIocDiv_mul Real.two_pi_pos (-Real.pi) t)
    have hz : 0 ≤ z := by
      by_contra hn
      have hzle : z ≤ -1 := by omega
      have hzlereal : (z : ℝ) ≤ -1 := by exact_mod_cast hzle
      have hmul :
          (z : ℝ) * (2 * Real.pi) ≤ (-1 : ℝ) * (2 * Real.pi) :=
        mul_le_mul_of_nonneg_right hzlereal (by positivity)
      have hrpi := Real.Angle.toReal_le_pi θ
      linarith [Real.pi_pos]
    let k : ℕ := z.toNat
    have hkz : (k : ℤ) = z := Int.toNat_of_nonneg hz
    have hkzr : (k : ℝ) = (z : ℝ) := by exact_mod_cast hkz
    by_cases hk : k = 0
    · left
      constructor
      · exact ht0
      · change t ≤ Real.pi / 2
        have hz0 : (z : ℝ) = 0 := by simpa [hk] using hkzr.symm
        rw [← hdecomp]
        simpa [hz0] using hrhi
    · right
      refine ⟨k, Nat.pos_of_ne_zero hk, ?_, ?_⟩
      · change (4 * (k : ℝ) - 1) * Real.pi / 2 ≤ t
        rw [← hdecomp, ← hkzr]
        linarith
      · change t ≤ (4 * (k : ℝ) + 1) * Real.pi / 2
        rw [← hdecomp, ← hkzr]
        linarith
  · intro hphase
    rcases hphase with hbase | ⟨k, hk, hklo, hkhi⟩
    · exact Real.cos_nonneg_of_neg_pi_div_two_le_of_le
        (by linarith [Real.pi_pos]) hbase.2
    · let u := x ^ 2 - (k : ℝ) * (2 * Real.pi)
      have hulo : -(Real.pi / 2) ≤ u := by
        dsimp [u]
        linarith
      have huhi : u ≤ Real.pi / 2 := by
        dsimp [u]
        linarith
      have hcosu : 0 ≤ Real.cos u :=
        Real.cos_nonneg_of_neg_pi_div_two_le_of_le hulo huhi
      have hperiod := Real.cos_sub_nat_mul_two_pi (x ^ 2) k
      dsimp [u] at hcosu
      rw [hperiod] at hcosu
      exact hcosu

/-- Exercise 156, gap 3. -/
theorem gap3 : ∀ x : ℝ, phaseCondition x ↔ radialCondition x := by
  intro x
  constructor
  · intro hphase
    rcases hphase with hbase | ⟨k, hk, hklo, hkhi⟩
    · left
      rw [← Real.sqrt_sq_eq_abs x]
      exact Real.sqrt_le_sqrt hbase.2
    · right
      have hkcast : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      have hcoef : 0 ≤ 4 * (k : ℝ) - 1 := by linarith
      have hleft0 : 0 ≤ (4 * (k : ℝ) - 1) * Real.pi / 2 := by
        positivity
      have hright0 : 0 ≤ (4 * (k : ℝ) + 1) * Real.pi / 2 := by
        positivity
      refine ⟨k, hk, ?_, ?_⟩
      · rw [← Real.sqrt_sq_eq_abs x]
        exact Real.sqrt_le_sqrt hklo
      · rw [← Real.sqrt_sq_eq_abs x]
        exact Real.sqrt_le_sqrt hkhi
  · intro hradial
    rcases hradial with hbase | ⟨k, hk, hklo, hkhi⟩
    · left
      have hright0 : 0 ≤ Real.pi / 2 := by positivity
      have hsq :
          |x| ^ 2 ≤ (Real.sqrt (Real.pi / 2)) ^ 2 :=
        (sq_le_sq₀ (abs_nonneg x) (Real.sqrt_nonneg _)).2 hbase
      rw [sq_abs, Real.sq_sqrt hright0] at hsq
      exact ⟨sq_nonneg x, hsq⟩
    · right
      have hkcast : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
      have hcoef : 0 ≤ 4 * (k : ℝ) - 1 := by linarith
      have hleft0 : 0 ≤ (4 * (k : ℝ) - 1) * Real.pi / 2 := by
        positivity
      have hright0 : 0 ≤ (4 * (k : ℝ) + 1) * Real.pi / 2 := by
        positivity
      have hlo_sq :
          (Real.sqrt ((4 * (k : ℝ) - 1) * Real.pi / 2)) ^ 2 ≤ |x| ^ 2 :=
        (sq_le_sq₀ (Real.sqrt_nonneg _) (abs_nonneg x)).2 hklo
      have hhi_sq :
          |x| ^ 2 ≤
            (Real.sqrt ((4 * (k : ℝ) + 1) * Real.pi / 2)) ^ 2 :=
        (sq_le_sq₀ (abs_nonneg x) (Real.sqrt_nonneg _)).2 hkhi
      rw [Real.sq_sqrt hleft0, sq_abs] at hlo_sq
      rw [Real.sq_sqrt hright0, sq_abs] at hhi_sq
      exact ⟨k, hk, hlo_sq, hhi_sq⟩

/-- Exercise 156, gap 4. -/
theorem gap4 : domain = {x : ℝ | radialCondition x} := by
  ext x
  exact (gap2 x).trans (gap3 x)

end

end ProofGap.Exercise156
