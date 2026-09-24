import ProofGapLean.Prelude.Elementary
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise166

noncomputable section

def domain : Set ℝ := {x | 0 ≤ 2 + x - x ^ 2}
def y (x : ℝ) : ℝ := Real.sqrt (2 + x - x ^ 2)
def valueSet : Set ℝ := {t | ∃ x ∈ domain, t = y x}

/-- Source: `proof_gap/exercise_166/1.txt`. -/
theorem gap1 : ∀ x : ℝ, 0 ≤ 2 + x - x ^ 2 → x ∈ domain := by
  intro x hx
  exact hx

/-- Source: `proof_gap/exercise_166/2.txt`. -/
theorem gap2 : domain = Set.Icc (-1) 2 := by
  ext x
  constructor
  · intro hx
    change 0 ≤ 2 + x - x ^ 2 at hx
    constructor
    · by_contra h
      have hlt : x < -1 := lt_of_not_ge h
      nlinarith [sq_nonneg (x + 1)]
    · by_contra h
      have hlt : 2 < x := lt_of_not_ge h
      nlinarith [sq_nonneg (x - 2)]
  · rintro ⟨hxlo, hxhi⟩
    change 0 ≤ 2 + x - x ^ 2
    have hprod : 0 ≤ (x + 1) * (2 - x) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith

/-- Source: `proof_gap/exercise_166/3.txt`; complete the square. -/
theorem gap3 : ∀ x : ℝ,
    y x = Real.sqrt (9 / 4 - (x - 1 / 2) ^ 2) := by
  intro x
  unfold y
  congr 1
  ring_nf

/-- Source: `proof_gap/exercise_166/4.txt`; the bound is restricted to the domain. -/
theorem gap4 : ∀ x : ℝ, x ∈ domain →
    Real.sqrt (9 / 4 - (x - 1 / 2) ^ 2) ≤ 3 / 2 := by
  intro x _
  apply Real.sqrt_le_iff.mpr
  constructor
  · norm_num
  · nlinarith [sq_nonneg (x - 1 / 2)]

/-- Source: `proof_gap/exercise_166/5.txt`. -/
theorem gap5 : ∀ x : ℝ, x ∈ domain → y x ≤ 3 / 2 := by
  intro x hx
  rw [gap3 x]
  exact gap4 x hx

/-- Source: `proof_gap/exercise_166/6.txt`; remove the shadowed existential y. -/
theorem gap6 : valueSet = Set.Icc 0 (3 / 2) := by
  ext t
  constructor
  · rintro ⟨x, hxdom, rfl⟩
    exact ⟨Real.sqrt_nonneg _, gap5 x hxdom⟩
  · rintro ⟨ht0, htmax⟩
    let s : ℝ := Real.sqrt (9 / 4 - t ^ 2)
    let x : ℝ := 1 / 2 - s
    have hrad : 0 ≤ 9 / 4 - t ^ 2 := by nlinarith
    have hs : s ^ 2 = 9 / 4 - t ^ 2 := by
      dsimp [s]
      exact Real.sq_sqrt hrad
    have hpoly : 2 + x - x ^ 2 = t ^ 2 := by
      dsimp [x]
      nlinarith
    have hxdom : x ∈ domain := gap1 x (by rw [hpoly]; positivity)
    refine ⟨x, hxdom, ?_⟩
    rw [y, hpoly, Real.sqrt_sq_eq_abs, abs_of_nonneg ht0]

end

end ProofGap.Exercise166
