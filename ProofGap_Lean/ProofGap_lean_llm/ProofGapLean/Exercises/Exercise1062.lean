import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise1062

noncomputable section

def intersectionXs : Set ℝ :=
  {x | ∃ k : ℤ, x = Real.pi / 4 + (k : ℝ) * Real.pi}

def paritySign (k : ℤ) : ℝ := if Even k then 1 else -1
def slope1 (k : ℤ) : ℝ := Real.cos (Real.pi / 4 + (k : ℝ) * Real.pi)
def slope2 (k : ℤ) : ℝ := -Real.sin (Real.pi / 4 + (k : ℝ) * Real.pi)
def θ : ℝ := Real.arctan (2 * Real.sqrt 2)

private theorem parity_ratio_value (k : ℤ) :
    |((paritySign k * (Real.sqrt 2 / 2) -
          (-(paritySign k)) * (Real.sqrt 2 / 2)) /
        (1 + (paritySign k * (Real.sqrt 2 / 2)) *
          ((-(paritySign k)) * (Real.sqrt 2 / 2))))| =
      |paritySign k * (Real.sqrt 2 / (1 - 1 / 2))| ∧
    |paritySign k * (Real.sqrt 2 / (1 - 1 / 2))| =
      2 * Real.sqrt 2 := by
  have hp : paritySign k * paritySign k = 1 := by
    by_cases hk : Even k
    · simp [paritySign, hk]
    · simp [paritySign, hk]
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 :=
    Real.mul_self_sqrt (by norm_num)
  have hden :
      1 + (paritySign k * (Real.sqrt 2 / 2)) *
          ((-(paritySign k)) * (Real.sqrt 2 / 2)) = (1 / 2 : ℝ) := by
    calc
      1 + (paritySign k * (Real.sqrt 2 / 2)) *
          ((-(paritySign k)) * (Real.sqrt 2 / 2)) =
          1 - (paritySign k * paritySign k) *
            (Real.sqrt 2 * Real.sqrt 2) / 4 := by ring
      _ = (1 / 2 : ℝ) := by rw [hp, hs]; norm_num
  have hinner :
      ((paritySign k * (Real.sqrt 2 / 2) -
          (-(paritySign k)) * (Real.sqrt 2 / 2)) /
        (1 + (paritySign k * (Real.sqrt 2 / 2)) *
          ((-(paritySign k)) * (Real.sqrt 2 / 2)))) =
        paritySign k * (Real.sqrt 2 / (1 - 1 / 2)) := by
    rw [hden]
    norm_num [div_eq_mul_inv] <;> ring
  constructor
  · exact congrArg abs hinner
  · rw [abs_mul, abs_div]
    have hpabs : |paritySign k| = 1 := by
      by_cases hk : Even k
      · simp [paritySign, hk]
      · simp [paritySign, hk]
    rw [hpabs, abs_of_nonneg (Real.sqrt_nonneg 2)]
    norm_num [div_eq_mul_inv] <;> ring

theorem gap1 (x : ℝ) :
    Real.sin x = Real.cos x ↔
      ∃ k : ℤ, x = Real.pi / 4 + (k : ℝ) * Real.pi := by
  constructor
  · intro h
    have hz : Real.sin (x - Real.pi / 4) = 0 := by
      rw [Real.sin_sub, Real.sin_pi_div_four, Real.cos_pi_div_four, h]
      ring
    obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp hz
    refine ⟨k, ?_⟩
    linarith
  · rintro ⟨k, hk⟩
    have hz : Real.sin (x - Real.pi / 4) = 0 := by
      apply Real.sin_eq_zero_iff.mpr
      refine ⟨k, ?_⟩
      linarith
    rw [Real.sin_sub, Real.sin_pi_div_four, Real.cos_pi_div_four] at hz
    have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    have hsne : Real.sqrt 2 / 2 ≠ 0 :=
      div_ne_zero (ne_of_gt hspos) (by norm_num)
    have hmul :
        (Real.sqrt 2 / 2) * Real.sin x =
          (Real.sqrt 2 / 2) * Real.cos x := by
      nlinarith [hz]
    exact mul_left_cancel₀ hsne hmul

theorem gap2 (x : ℝ) (hx : Real.sin x = Real.cos x) :
    ∃ k : ℤ, x = Real.pi / 4 + (k : ℝ) * Real.pi := by
  exact (gap1 x).mp hx

theorem gap3 (x : ℝ) :
    x ∈ intersectionXs ↔ Real.sin x = Real.cos x := by
  simpa [intersectionXs] using (gap1 x).symm

theorem gap4 (k : ℤ) :
    ∃ k₁ : ℝ, k₁ = Real.cos (Real.pi / 4 + (k : ℝ) * Real.pi) := by
  exact ⟨Real.cos (Real.pi / 4 + (k : ℝ) * Real.pi), rfl⟩

theorem gap5 (k : ℤ) :
    Real.cos (Real.pi / 4 + (k : ℝ) * Real.pi) =
      paritySign k * (Real.sqrt 2 / 2) := by
  rcases Int.even_or_odd k with hk | hk
  · rcases hk with ⟨j, hj⟩
    have heven : Even k := ⟨j, hj⟩
    have harg :
        Real.pi / 4 + (k : ℝ) * Real.pi =
          Real.pi / 4 + (j : ℝ) * (2 * Real.pi) := by
      norm_num [hj] <;> ring
    calc
      Real.cos (Real.pi / 4 + (k : ℝ) * Real.pi) =
          Real.cos (Real.pi / 4 + (j : ℝ) * (2 * Real.pi)) := by rw [harg]
      _ = Real.cos (Real.pi / 4) := by
        simpa using Real.cos_add_int_mul_two_pi (Real.pi / 4) j
      _ = Real.sqrt 2 / 2 := Real.cos_pi_div_four
      _ = paritySign k * (Real.sqrt 2 / 2) := by
        simp [paritySign, heven]
  · rcases hk with ⟨j, hj⟩
    have hnot : ¬ Even k := by
      intro heven
      rcases heven with ⟨m, hm⟩
      omega
    have harg :
        Real.pi / 4 + (k : ℝ) * Real.pi =
          (Real.pi / 4 + Real.pi) + (j : ℝ) * (2 * Real.pi) := by
      norm_num [hj] <;> ring
    calc
      Real.cos (Real.pi / 4 + (k : ℝ) * Real.pi) =
          Real.cos ((Real.pi / 4 + Real.pi) + (j : ℝ) * (2 * Real.pi)) := by rw [harg]
      _ = Real.cos (Real.pi / 4 + Real.pi) := by
        simpa using Real.cos_add_int_mul_two_pi (Real.pi / 4 + Real.pi) j
      _ = -Real.cos (Real.pi / 4) := Real.cos_add_pi (Real.pi / 4)
      _ = -(Real.sqrt 2 / 2) := by rw [Real.cos_pi_div_four]
      _ = paritySign k * (Real.sqrt 2 / 2) := by
        simp [paritySign, hnot]

theorem gap6 (k : ℤ) :
    ∃ k₁ : ℝ, k₁ = paritySign k * (Real.sqrt 2 / 2) := by
  exact ⟨paritySign k * (Real.sqrt 2 / 2), rfl⟩

theorem gap7 (k : ℤ) :
    ∃ k₂ : ℝ, k₂ = -Real.sin (Real.pi / 4 + (k : ℝ) * Real.pi) := by
  exact ⟨-Real.sin (Real.pi / 4 + (k : ℝ) * Real.pi), rfl⟩

theorem gap8 (k : ℤ) :
    -Real.sin (Real.pi / 4 + (k : ℝ) * Real.pi) =
      -(paritySign k) * (Real.sqrt 2 / 2) := by
  have hsc :
      Real.sin (Real.pi / 4 + (k : ℝ) * Real.pi) =
        Real.cos (Real.pi / 4 + (k : ℝ) * Real.pi) :=
    (gap1 (Real.pi / 4 + (k : ℝ) * Real.pi)).2 ⟨k, rfl⟩
  calc
    -Real.sin (Real.pi / 4 + (k : ℝ) * Real.pi) =
        -Real.cos (Real.pi / 4 + (k : ℝ) * Real.pi) :=
      congrArg (fun z : ℝ => -z) hsc
    _ = -(paritySign k * (Real.sqrt 2 / 2)) :=
      congrArg (fun z : ℝ => -z) (gap5 k)
    _ = -(paritySign k) * (Real.sqrt 2 / 2) := by ring

theorem gap9 (k : ℤ) :
    ∃ k₂ : ℝ, k₂ = -(paritySign k) * (Real.sqrt 2 / 2) := by
  exact ⟨-(paritySign k) * (Real.sqrt 2 / 2), rfl⟩

theorem gap10 : 0 ≤ θ := by
  unfold θ
  apply Real.arctan_nonneg.mpr
  nlinarith [Real.sqrt_nonneg (2 : ℝ)]
theorem gap11 : θ ≤ Real.pi / 2 := by
  unfold θ
  exact le_of_lt (Real.arctan_lt_pi_div_two (2 * Real.sqrt 2))
theorem gap12 : 0 ≤ Real.pi / 2 := by
  nlinarith [Real.pi_pos]

theorem gap13 (k : ℤ) :
    Real.tan θ =
      |(slope1 k - slope2 k) / (1 + slope1 k * slope2 k)| := by
  have htan : Real.tan θ = 2 * Real.sqrt 2 := by
    unfold θ
    rw [Real.tan_arctan]
  rw [htan]
  unfold slope1 slope2
  rw [gap5 k, gap8 k]
  exact
    ((parity_ratio_value k).1.trans (parity_ratio_value k).2).symm

theorem gap14 (k : ℤ) :
    |(slope1 k - slope2 k) / (1 + slope1 k * slope2 k)| =
      |paritySign k * (Real.sqrt 2 / (1 - 1 / 2))| := by
  unfold slope1 slope2
  rw [gap5 k, gap8 k]
  exact (parity_ratio_value k).1

theorem gap15 (k : ℤ) :
    |paritySign k * (Real.sqrt 2 / (1 - 1 / 2))| =
      2 * Real.sqrt 2 := by
  exact (parity_ratio_value k).2

theorem gap16 : Real.tan θ = 2 * Real.sqrt 2 := by
  unfold θ
  rw [Real.tan_arctan]
theorem gap17 : θ = Real.arctan (2 * Real.sqrt 2) := by
  rfl

end

end ProofGap.Exercise1062
