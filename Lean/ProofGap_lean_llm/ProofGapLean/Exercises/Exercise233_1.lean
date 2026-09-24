import ProofGapLean.Prelude.Elementary
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise233_1

noncomputable section

def f (A B lambda x : ℝ) : ℝ :=
  A * Real.cos (lambda * x) + B * Real.sin (lambda * x)

def period (lambda : ℝ) : ℝ := 2 * Real.pi / lambda

def IsLeastPositivePeriod (g : ℝ → ℝ) (T : ℝ) : Prop :=
  0 < T ∧ Function.Periodic g T ∧
    ∀ T', 0 < T' → Function.Periodic g T' → T ≤ T'

/-- Source: `proof_gap/exercise_233_1/1.txt`. -/
theorem gap1 (A B lambda : ℝ) (hlambda : 0 < lambda) : ∀ x,
    f A B lambda (x + period lambda) =
      A * Real.cos (lambda * (x + period lambda)) +
        B * Real.sin (lambda * (x + period lambda)) := by
  intro x
  rfl

/-- Source: `proof_gap/exercise_233_1/2.txt`. -/
theorem gap2 (A B lambda : ℝ) (hlambda : 0 < lambda) : ∀ x,
    A * Real.cos (lambda * (x + period lambda)) +
        B * Real.sin (lambda * (x + period lambda)) =
      A * Real.cos (lambda * x) + B * Real.sin (lambda * x) := by
  intro x
  have harg :
      lambda * (x + period lambda) = lambda * x + 2 * Real.pi := by
    unfold period
    field_simp [ne_of_gt hlambda]
  rw [harg, Real.cos_add, Real.sin_add, Real.cos_two_pi,
    Real.sin_two_pi]
  ring

/-- Source: `proof_gap/exercise_233_1/3.txt`. -/
theorem gap3 (A B lambda : ℝ) (hlambda : 0 < lambda) : ∀ x,
    A * Real.cos (lambda * x) + B * Real.sin (lambda * x) =
      f A B lambda x := by
  intro x
  rfl

/-- Source: `proof_gap/exercise_233_1/4.txt`. -/
theorem gap4 (A B lambda : ℝ) (hlambda : 0 < lambda) : ∀ x,
    f A B lambda (x + period lambda) = f A B lambda x := by
  intro x
  calc
    f A B lambda (x + period lambda) =
        A * Real.cos (lambda * (x + period lambda)) +
          B * Real.sin (lambda * (x + period lambda)) :=
      gap1 A B lambda hlambda x
    _ = A * Real.cos (lambda * x) + B * Real.sin (lambda * x) :=
      gap2 A B lambda hlambda x
    _ = f A B lambda x := gap3 A B lambda hlambda x

/-- Source: `proof_gap/exercise_233_1/5.txt`. -/
theorem gap5 (A B lambda : ℝ) (hlambda : 0 < lambda) :
    Function.Periodic (f A B lambda) (period lambda) := by
  intro x
  exact gap4 A B lambda hlambda x

/-- Source: `proof_gap/exercise_233_1/6.txt`; exclude the zero function before asserting a fundamental period. -/
theorem gap6 (A B lambda : ℝ) (hlambda : 0 < lambda)
    (hnonzero : A ≠ 0 ∨ B ≠ 0) :
    IsLeastPositivePeriod (f A B lambda) (period lambda) := by
  refine ⟨?_, gap5 A B lambda hlambda, ?_⟩
  · unfold period
    apply div_pos
    · nlinarith [Real.pi_pos]
    · exact hlambda
  · intro T hT hper
    by_contra hnot
    have hTlt : T < period lambda := lt_of_not_ge hnot
    have hTlt' : T < 2 * Real.pi / lambda := by
      simpa [period] using hTlt
    have hphase_pos : 0 < lambda * T := mul_pos hlambda hT
    have hphase_lt : lambda * T < 2 * Real.pi := by
      have hmul : T * lambda < 2 * Real.pi :=
        (lt_div_iff₀ hlambda).mp hTlt'
      nlinarith
    have h1 :
        A * Real.cos (lambda * T) + B * Real.sin (lambda * T) = A := by
      simpa [f] using hper 0
    have hq0 :
        lambda * (Real.pi / (2 * lambda)) = Real.pi / 2 := by
      field_simp [ne_of_gt hlambda]
      <;> ring
    have hqadd :
        lambda * (Real.pi / (2 * lambda) + T) =
          Real.pi / 2 + lambda * T := by
      rw [mul_add, hq0]
    have h2 :
        A * (-Real.sin (lambda * T)) + B * Real.cos (lambda * T) = B := by
      have h := hper (Real.pi / (2 * lambda))
      simp only [f] at h
      rw [hqadd, hq0, Real.cos_add, Real.sin_add,
        Real.cos_pi_div_two, Real.sin_pi_div_two] at h
      simpa using h
    have hdetA :
        A * ((Real.cos (lambda * T) - 1) ^ 2 +
          (Real.sin (lambda * T)) ^ 2) = 0 := by
      calc
        A * ((Real.cos (lambda * T) - 1) ^ 2 +
            (Real.sin (lambda * T)) ^ 2) =
            (Real.cos (lambda * T) - 1) *
                (A * Real.cos (lambda * T) +
                  B * Real.sin (lambda * T) - A) -
              Real.sin (lambda * T) *
                (A * (-Real.sin (lambda * T)) +
                  B * Real.cos (lambda * T) - B) := by ring
        _ = 0 := by rw [h1, h2]; ring
    have hdetB :
        B * ((Real.cos (lambda * T) - 1) ^ 2 +
          (Real.sin (lambda * T)) ^ 2) = 0 := by
      calc
        B * ((Real.cos (lambda * T) - 1) ^ 2 +
            (Real.sin (lambda * T)) ^ 2) =
            Real.sin (lambda * T) *
                (A * Real.cos (lambda * T) +
                  B * Real.sin (lambda * T) - A) +
              (Real.cos (lambda * T) - 1) *
                (A * (-Real.sin (lambda * T)) +
                  B * Real.cos (lambda * T) - B) := by ring
        _ = 0 := by rw [h1, h2]; ring
    have hdet :
        (Real.cos (lambda * T) - 1) ^ 2 +
          (Real.sin (lambda * T)) ^ 2 = 0 := by
      rcases hnonzero with hA | hB
      · exact (mul_eq_zero.mp hdetA).resolve_left hA
      · exact (mul_eq_zero.mp hdetB).resolve_left hB
    have hcos : Real.cos (lambda * T) = 1 := by
      nlinarith [sq_nonneg (Real.cos (lambda * T) - 1),
        sq_nonneg (Real.sin (lambda * T))]
    have hphase_neg : -(2 * Real.pi) < lambda * T := by
      nlinarith [Real.pi_pos]
    have hphase_zero : lambda * T = 0 :=
      (Real.cos_eq_one_iff_of_lt_of_lt hphase_neg hphase_lt).mp hcos
    nlinarith

end

end ProofGap.Exercise233_1
