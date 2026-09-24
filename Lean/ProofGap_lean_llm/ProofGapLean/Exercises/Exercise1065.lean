import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1065

noncomputable section

def r (a m φ : ℝ) : ℝ := a * Real.exp (m * φ)
def β (a m φ : ℝ) : ℝ := Real.arctan (r a m φ / deriv (r a m) φ)

theorem gap1 (a m φ : ℝ) :
    r a m φ = a * Real.exp (m * φ) := by
  rfl

theorem gap2 (a m φ : ℝ) :
    deriv (r a m) φ = a * m * Real.exp (m * φ) := by
  unfold r
  have hinner : HasDerivAt (fun x : ℝ => m * x) m φ := by
    simpa using (hasDerivAt_id φ).const_mul m
  have h :=
    ((Real.hasDerivAt_exp (m * φ)).comp φ hinner).const_mul a
  convert h.deriv using 1 <;> ring

theorem gap3 (a m φ : ℝ) :
    Real.tan (β a m φ) = r a m φ / deriv (r a m) φ := by
  simp [β]

theorem gap4 (a m φ : ℝ) (ha : a ≠ 0) (hm : m ≠ 0) :
    r a m φ / deriv (r a m) φ = 1 / m := by
  rw [gap1, gap2]
  field_simp [ha, hm, Real.exp_ne_zero] <;> ring

theorem gap5 (a m φ : ℝ) (ha : a ≠ 0) (hm : m ≠ 0) :
    Real.tan (β a m φ) = 1 / m := by
  rw [gap3, gap4 a m φ ha hm]

theorem gap6 (a m φ : ℝ) (ha : a ≠ 0) (hm : m ≠ 0) :
    β a m φ = Real.arctan (1 / m) := by
  unfold β
  rw [gap4 a m φ ha hm]

theorem gap7 (a m : ℝ) (ha : a ≠ 0) (hm : m ≠ 0) :
    ∃ c : ℝ, ∀ φ, β a m φ = c := by
  refine ⟨Real.arctan (1 / m), ?_⟩
  intro φ
  exact gap6 a m φ ha hm

theorem gap8 (rfun : ℝ → ℝ) (angle : ℝ → ℝ) (a m : ℝ)
    (ha : a ≠ 0) (hm : m ≠ 0)
    (hr : ∀ φ, rfun φ = a * Real.exp (m * φ))
    (hangle : ∀ φ, angle φ = Real.arctan (rfun φ / deriv rfun φ)) :
    ∃ c : ℝ, ∀ φ, angle φ = c := by
  have hrf : rfun = r a m := by
    funext φ
    simpa [r] using hr φ
  refine ⟨Real.arctan (1 / m), ?_⟩
  intro φ
  rw [hangle φ, hrf, gap4 a m φ ha hm]

end

end ProofGap.Exercise1065
