import ProofGapLean.Prelude.Elementary
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise233_2

noncomputable section

def f (x : ℝ) : ℝ :=
  Real.sin x + (1 / 2 : ℝ) * Real.sin (2 * x) +
    (1 / 3 : ℝ) * Real.sin (3 * x)

def IsLeastPositivePeriod (g : ℝ → ℝ) (T : ℝ) : Prop :=
  0 < T ∧ Function.Periodic g T ∧
    ∀ T', 0 < T' → Function.Periodic g T' → T ≤ T'

/-- Exercise 233_2, gap 1. -/
private theorem f_factor (x : ℝ) :
    f x = (1 / 3 : ℝ) * Real.sin x *
      (4 * Real.cos x ^ 2 + 3 * Real.cos x + 2) := by
  unfold f
  rw [Real.sin_two_mul, Real.sin_three_mul]
  have htrig := Real.sin_sq_add_cos_sq x
  calc
    Real.sin x + (1 / 2 : ℝ) * (2 * Real.sin x * Real.cos x) +
        (1 / 3 : ℝ) * (3 * Real.sin x - 4 * Real.sin x ^ 3) =
      (1 / 3 : ℝ) * Real.sin x *
          (4 * Real.cos x ^ 2 + 3 * Real.cos x + 2) +
        (4 / 3 : ℝ) * Real.sin x *
          (1 - (Real.sin x ^ 2 + Real.cos x ^ 2)) := by
            ring
    _ = (1 / 3 : ℝ) * Real.sin x *
        (4 * Real.cos x ^ 2 + 3 * Real.cos x + 2) := by
          rw [htrig]
          ring

theorem gap1 : Function.Periodic f (2 * Real.pi) := by
  intro x
  unfold f
  have h1 : Real.sin (x + 2 * Real.pi) = Real.sin x :=
    Real.sin_add_two_pi x
  have h2 : Real.sin (2 * (x + 2 * Real.pi)) = Real.sin (2 * x) := by
    calc
      Real.sin (2 * (x + 2 * Real.pi)) =
          Real.sin ((2 * x + 2 * Real.pi) + 2 * Real.pi) := by
            congr 1 <;> ring
      _ = Real.sin (2 * x + 2 * Real.pi) := Real.sin_add_two_pi _
      _ = Real.sin (2 * x) := Real.sin_add_two_pi _
  have h3 : Real.sin (3 * (x + 2 * Real.pi)) = Real.sin (3 * x) := by
    calc
      Real.sin (3 * (x + 2 * Real.pi)) =
          Real.sin (((3 * x + 2 * Real.pi) + 2 * Real.pi) + 2 * Real.pi) := by
            congr 1 <;> ring
      _ = Real.sin ((3 * x + 2 * Real.pi) + 2 * Real.pi) :=
        Real.sin_add_two_pi _
      _ = Real.sin (3 * x + 2 * Real.pi) := Real.sin_add_two_pi _
      _ = Real.sin (3 * x) := Real.sin_add_two_pi _
  rw [h1, h2, h3]

/-- Exercise 233_2, gap 2; represent `min` by the least-positive-period predicate. -/
theorem gap2 : IsLeastPositivePeriod f (2 * Real.pi) := by
  refine ⟨?_, gap1, ?_⟩
  · nlinarith [Real.pi_pos]
  · intro T hT hper
    apply le_of_not_gt
    intro hlt
    have hzero : f T = 0 := by
      simpa [f] using hper 0
    rw [f_factor] at hzero
    have hqpos :
        0 < 4 * Real.cos T ^ 2 + 3 * Real.cos T + 2 := by
      nlinarith [sq_nonneg (8 * Real.cos T + 3)]
    have hs : Real.sin T = 0 := by
      rcases mul_eq_zero.mp hzero with hprod | hq
      · rcases mul_eq_zero.mp hprod with hthird | hsin
        · norm_num at hthird
        · exact hsin
      · exact False.elim ((ne_of_gt hqpos) hq)
    have hTpi : T = Real.pi := by
      rcases lt_trichotomy T Real.pi with hbelow | heq | habove
      · have hp := Real.sin_pos_of_pos_of_lt_pi hT hbelow
        exfalso
        rw [hs] at hp
        exact (lt_irrefl 0) hp
      · exact heq
      · have hypos : 0 < T - Real.pi := sub_pos.mpr habove
        have hylt : T - Real.pi < Real.pi := by
          linarith
        have hysin := Real.sin_pos_of_pos_of_lt_pi hypos hylt
        have hsneg : Real.sin T < 0 := by
          calc
            Real.sin T = Real.sin ((T - Real.pi) + Real.pi) := by
              congr 1 <;> ring
            _ = -Real.sin (T - Real.pi) := Real.sin_add_pi _
            _ < 0 := neg_neg_of_pos hysin
        exfalso
        rw [hs] at hsneg
        exact (lt_irrefl 0) hsneg
    have hspecial := hper (Real.pi / 2)
    rw [hTpi] at hspecial
    norm_num [f_factor, Real.sin_add_pi, Real.cos_add_pi,
      Real.sin_pi_div_two, Real.cos_pi_div_two] at hspecial

end

end ProofGap.Exercise233_2
