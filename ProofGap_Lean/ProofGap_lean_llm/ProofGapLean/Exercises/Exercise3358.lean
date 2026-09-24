import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise3358

noncomputable section

def partialY (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => z x s) y

def SatisfiesPDE (z : ℝ → ℝ → ℝ) : Prop :=
  (∀ x, Differentiable ℝ (fun y => z x y)) ∧
    ∀ x y, partialY z x y = x ^ 2 + 2 * y

def SatisfiesBoundaryData (z : ℝ → ℝ → ℝ) : Prop :=
  ∀ x, z x (x ^ 2) = 1

def candidate (x y : ℝ) : ℝ :=
  1 + x ^ 2 * y + y ^ 2 - 2 * x ^ 4

private theorem candidate_satisfies :
    SatisfiesPDE candidate ∧ SatisfiesBoundaryData candidate := by
  have hcand : ∀ x y : ℝ,
      HasDerivAt (fun t => candidate x t) (x ^ 2 + 2 * y) y := by
    intro x y
    unfold candidate
    convert
      ((((hasDerivAt_const y (1 : ℝ)).add
        ((hasDerivAt_const y (x ^ 2)).mul (hasDerivAt_id y))).add
        ((hasDerivAt_id y).mul (hasDerivAt_id y))).sub
        (hasDerivAt_const y (2 * x ^ 4))) using 1
    · funext t
      simp <;> ring
    · simp <;> ring
  constructor
  · constructor
    · intro x y
      exact (hcand x y).differentiableAt
    · intro x y
      simpa [partialY] using (hcand x y).deriv
  · intro x
    unfold candidate
    ring

theorem gap1 (z : ℝ → ℝ → ℝ)
    (hpde : SatisfiesPDE z) (hdata : SatisfiesBoundaryData z) :
    ∃ φ : ℝ → ℝ,
      ∀ x y, z x y = x ^ 2 * y + y ^ 2 + φ x := by
  refine ⟨fun x => z x 0, ?_⟩
  intro x y
  have hz_diff : Differentiable ℝ (fun t => z x t) := hpde.1 x
  have hpoly_at : ∀ t : ℝ,
      HasDerivAt (fun s : ℝ => x ^ 2 * s + s ^ 2)
        (x ^ 2 + 2 * t) t := by
    intro t
    convert
      (((hasDerivAt_const t (x ^ 2)).mul (hasDerivAt_id t)).add
        ((hasDerivAt_id t).mul (hasDerivAt_id t))) using 1
    · funext s
      simp <;> ring
    · simp <;> ring
  have hpoly_diff :
      Differentiable ℝ (fun t : ℝ => x ^ 2 * t + t ^ 2) := by
    intro t
    exact (hpoly_at t).differentiableAt
  have hzero :
      ∀ t, deriv (fun s : ℝ => z x s - (x ^ 2 * s + s ^ 2)) t = 0 := by
    intro t
    have hz_deriv : deriv (fun s => z x s) t = x ^ 2 + 2 * t := by
      simpa [partialY] using hpde.2 x t
    have hz_at : HasDerivAt (fun s => z x s) (x ^ 2 + 2 * t) t := by
      have hz_at' := (hz_diff t).hasDerivAt
      rw [hz_deriv] at hz_at'
      exact hz_at'
    simpa using (hz_at.sub (hpoly_at t)).deriv
  have hconst :=
    is_const_of_deriv_eq_zero (hz_diff.sub hpoly_diff) hzero y 0
  have hconst' :
      z x y - (x ^ 2 * y + y ^ 2) =
        z x 0 - (x ^ 2 * 0 + 0 ^ 2) := by
    simpa using hconst
  calc
    z x y = x ^ 2 * y + y ^ 2 +
        (z x y - (x ^ 2 * y + y ^ 2)) := by ring
    _ = x ^ 2 * y + y ^ 2 +
        (z x 0 - (x ^ 2 * 0 + 0 ^ 2)) := by rw [hconst']
    _ = x ^ 2 * y + y ^ 2 + z x 0 := by ring

theorem gap2 (z : ℝ → ℝ → ℝ) (φ : ℝ → ℝ)
    (hpde : SatisfiesPDE z) (hdata : SatisfiesBoundaryData z)
    (hrepr : ∀ x y, z x y = x ^ 2 * y + y ^ 2 + φ x) :
    ∀ x, 1 = x ^ 4 + x ^ 4 + φ x := by
  intro x
  calc
    1 = z x (x ^ 2) := (hdata x).symm
    _ = x ^ 2 * (x ^ 2) + (x ^ 2) ^ 2 + φ x := hrepr x (x ^ 2)
    _ = x ^ 4 + x ^ 4 + φ x := by ring

theorem gap3 (z : ℝ → ℝ → ℝ) (φ : ℝ → ℝ)
    (hpde : SatisfiesPDE z) (hdata : SatisfiesBoundaryData z)
    (hrepr : ∀ x y, z x y = x ^ 2 * y + y ^ 2 + φ x) :
    ∀ x, φ x = 1 - 2 * x ^ 4 := by
  intro x
  have h := gap2 z φ hpde hdata hrepr x
  calc
    φ x = (x ^ 4 + x ^ 4 + φ x) - (x ^ 4 + x ^ 4) := by ring
    _ = 1 - (x ^ 4 + x ^ 4) := by rw [← h]
    _ = 1 - 2 * x ^ 4 := by ring

theorem gap4 (z : ℝ → ℝ → ℝ) :
    (SatisfiesPDE z ∧ SatisfiesBoundaryData z) ↔
      ∀ x y, z x y = candidate x y := by
  constructor
  · rintro ⟨hpde, hdata⟩
    obtain ⟨φ, hrepr⟩ := gap1 z hpde hdata
    have hphi := gap3 z φ hpde hdata hrepr
    intro x y
    rw [hrepr x y, hphi x]
    unfold candidate
    ring
  · intro hrepr
    have hz : z = candidate := by
      funext x y
      exact hrepr x y
    rw [hz]
    exact candidate_satisfies

theorem gap5 (z : ℝ → ℝ → ℝ)
    (hz : z = candidate) :
    SatisfiesPDE z ∧ SatisfiesBoundaryData z := by
  rw [hz]
  exact candidate_satisfies

end

end ProofGap.Exercise3358
