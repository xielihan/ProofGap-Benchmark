import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1012

noncomputable section

def y (A a b c x : ℝ) : ℝ :=
  A * (x - a) * (x - b) * (x - c)

def derivativeValue (A a b c x : ℝ) : ℝ :=
  A * ((x - b) * (x - c) + (x - a) * (x - c) + (x - a) * (x - b))

def solution (a b k₁ k₂ : ℝ) : ℝ × ℝ :=
  ((k₁ + k₂) / (b - a) ^ 2, (a * k₂ + b * k₁) / (k₁ + k₂))

theorem gap1 (A a b c x : ℝ) :
    HasDerivAt (y A a b c) (derivativeValue A a b c x) x := by
  have hA : HasDerivAt (fun _ : ℝ => A) 0 x := hasDerivAt_const x A
  have ha : HasDerivAt (fun z : ℝ => z - a) 1 x :=
    (hasDerivAt_id x).sub_const a
  have hb : HasDerivAt (fun z : ℝ => z - b) 1 x :=
    (hasDerivAt_id x).sub_const b
  have hc : HasDerivAt (fun z : ℝ => z - c) 1 x :=
    (hasDerivAt_id x).sub_const c
  convert ((hA.mul ha).mul hb).mul hc using 1 <;>
    simp [y, derivativeValue] <;> ring

theorem gap2 (A a b c k₁ k₂ x : ℝ) (hx : x = a)
    (h : A * (a - b) * (a - c) = k₁ ∧
      A * (b - a) * (b - c) = k₂) :
    A * (a - b) * (a - c) = k₁ := by
  exact h.1

theorem gap3 (A a b c k₁ k₂ x : ℝ) (hx : x = b)
    (h : A * (a - b) * (a - c) = k₁ ∧
      A * (b - a) * (b - c) = k₂) :
    A * (b - a) * (b - c) = k₂ := by
  exact h.2

theorem gap4 (A a b c k₁ k₂ : ℝ) (hab : a ≠ b) (hsum : k₁ + k₂ ≠ 0) :
    (A, c) ∈ ({solution a b k₁ k₂} : Set (ℝ × ℝ)) ↔
      A * (a - b) * (a - c) = k₁ ∧
        A * (b - a) * (b - c) = k₂ := by
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have hba_sq : (b - a) ^ 2 ≠ 0 := pow_ne_zero 2 hba
  constructor
  · intro hm
    have hm' : (A, c) = solution a b k₁ k₂ := by
      simpa only [Set.mem_singleton_iff] using hm
    have hA : A = (k₁ + k₂) / (b - a) ^ 2 := by
      simpa [solution] using congrArg Prod.fst hm'
    have hc : c = (a * k₂ + b * k₁) / (k₁ + k₂) := by
      simpa [solution] using congrArg Prod.snd hm'
    constructor
    · rw [hA, hc]
      field_simp [hba, hsum] <;> ring
    · rw [hA, hc]
      field_simp [hba, hsum] <;> ring
  · rintro ⟨hk₁, hk₂⟩
    have hAeq : A * (b - a) ^ 2 = k₁ + k₂ := by
      calc
        A * (b - a) ^ 2 =
            A * (a - b) * (a - c) + A * (b - a) * (b - c) := by ring
        _ = k₁ + k₂ := by rw [hk₁, hk₂]
    have hA : A = (k₁ + k₂) / (b - a) ^ 2 :=
      (eq_div_iff hba_sq).2 hAeq
    have hcnum : (k₁ + k₂) * c = a * k₂ + b * k₁ := by
      rw [← hk₁, ← hk₂]
      ring
    have hc : c = (a * k₂ + b * k₁) / (k₁ + k₂) := by
      apply (eq_div_iff hsum).2
      calc
        c * (k₁ + k₂) = (k₁ + k₂) * c := by ring
        _ = a * k₂ + b * k₁ := hcnum
    have hp : (A, c) = solution a b k₁ k₂ := by
      simp only [solution, Prod.mk.injEq]
      exact ⟨hA, hc⟩
    simpa only [Set.mem_singleton_iff] using hp

theorem gap5 (A a b c k₁ k₂ : ℝ) (hab : a ≠ b) (hsum : k₁ + k₂ ≠ 0)
    (hsol : (A, c) ∈ ({solution a b k₁ k₂} : Set (ℝ × ℝ))) :
    A * (a - b) * (a - c) = k₁ ∧
      A * (b - a) * (b - c) = k₂ := by
  exact (gap4 A a b c k₁ k₂ hab hsum).mp hsol

end

end ProofGap.Exercise1012
