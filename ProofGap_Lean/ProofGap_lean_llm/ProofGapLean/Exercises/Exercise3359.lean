import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise3359

noncomputable section

def partialY (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => z x s) y

def partialYY (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => partialY z x s) y

def TwiceDifferentiableInY (z : ℝ → ℝ → ℝ) : Prop :=
  ∀ x,
    Differentiable ℝ (fun y => z x y) ∧
      Differentiable ℝ (fun y => partialY z x y)

def SatisfiesPDE (z : ℝ → ℝ → ℝ) : Prop :=
  TwiceDifferentiableInY z ∧ ∀ x y, partialYY z x y = 2

def SatisfiesInitialData (z : ℝ → ℝ → ℝ) : Prop :=
  (∀ x, z x 0 = 1) ∧ ∀ x, partialY z x 0 = x

def candidate (x y : ℝ) : ℝ :=
  1 + x * y + y ^ 2

private theorem candidate_satisfies :
    SatisfiesPDE candidate ∧ SatisfiesInitialData candidate := by
  have hcand (x y : ℝ) :
      HasDerivAt (fun s : ℝ => candidate x s) (x + 2 * y) y := by
    have hone : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 y :=
      hasDerivAt_const y 1
    have hlin : HasDerivAt (fun s : ℝ => x * s) x y := by
      simpa using
        (hasDerivAt_const y x).mul (hasDerivAt_id y)
    have hsq : HasDerivAt (fun s : ℝ => s ^ 2) (2 * y) y := by
      simpa [pow_two, two_mul] using
        (hasDerivAt_id y).mul (hasDerivAt_id y)
    simpa [candidate] using (hone.add hlin).add hsq
  have hpartial (x y : ℝ) :
      partialY candidate x y = x + 2 * y := by
    simpa [partialY] using (hcand x y).deriv
  constructor
  · constructor
    · intro x
      constructor
      · intro y
        exact (hcand x y).differentiableAt
      · rw [show (fun y : ℝ => partialY candidate x y) =
            (fun y : ℝ => x + 2 * y) by
          funext y
          exact hpartial x y]
        exact
          (differentiable_const (c := x)).add
            ((differentiable_const (c := (2 : ℝ))).mul differentiable_id)
    · intro x y
      unfold partialYY
      rw [show (fun s : ℝ => partialY candidate x s) =
            (fun s : ℝ => x + 2 * s) by
          funext s
          exact hpartial x s]
      have hd : HasDerivAt (fun s : ℝ => x + 2 * s) 2 y := by
        convert
          (hasDerivAt_const y x).add
            ((hasDerivAt_const y (2 : ℝ)).mul (hasDerivAt_id y)) using 1 <;>
          ring
      exact hd.deriv
  · constructor
    · intro x
      simp [candidate]
    · intro x
      simpa using hpartial x 0

theorem gap1 (z : ℝ → ℝ → ℝ)
    (hpde : SatisfiesPDE z) (hdata : SatisfiesInitialData z) :
    ∃ φ : ℝ → ℝ,
      ∀ x y, partialY z x y = 2 * y + φ x := by
  refine ⟨fun x => partialY z x 0, ?_⟩
  intro x y
  have hdiff : Differentiable ℝ
      (fun t : ℝ => partialY z x t - 2 * t) :=
    ((hpde.1 x).2).sub
      ((differentiable_const (c := (2 : ℝ))).mul differentiable_id)
  have hzero : ∀ t : ℝ,
      deriv (fun s : ℝ => partialY z x s - 2 * s) t = 0 := by
    intro t
    have hz : HasDerivAt (fun s : ℝ => partialY z x s)
        (partialYY z x t) t := by
      simpa [partialYY] using ((hpde.1 x).2 t).hasDerivAt
    have htwo : HasDerivAt (fun s : ℝ => 2 * s) 2 t := by
      convert
        (hasDerivAt_const t (2 : ℝ)).mul (hasDerivAt_id t) using 1 <;>
        ring
    calc
      deriv (fun s : ℝ => partialY z x s - 2 * s) t =
          partialYY z x t - 2 := (hz.sub htwo).deriv
      _ = 0 := by rw [hpde.2 x t]; ring
  have hc := is_const_of_deriv_eq_zero hdiff hzero y 0
  simp at hc
  linarith

theorem gap2 (z : ℝ → ℝ → ℝ) (φ : ℝ → ℝ)
    (hpde : SatisfiesPDE z) (hdata : SatisfiesInitialData z)
    (hderiv : ∀ x y, partialY z x y = 2 * y + φ x) :
    ∀ x, x = 0 + φ x := by
  intro x
  calc
    x = partialY z x 0 := (hdata.2 x).symm
    _ = 2 * 0 + φ x := hderiv x 0
    _ = 0 + φ x := by ring

theorem gap3 (z : ℝ → ℝ → ℝ) (φ : ℝ → ℝ)
    (hpde : SatisfiesPDE z) (hdata : SatisfiesInitialData z)
    (hderiv : ∀ x y, partialY z x y = 2 * y + φ x) :
    ∀ x, φ x = x := by
  intro x
  have hx := gap2 z φ hpde hdata hderiv x
  linarith

theorem gap4 (z : ℝ → ℝ → ℝ)
    (hpde : SatisfiesPDE z) (hdata : SatisfiesInitialData z) :
    ∀ x y, partialY z x y = 2 * y + x := by
  rcases gap1 z hpde hdata with ⟨φ, hφ⟩
  have hφx : ∀ x, φ x = x := gap3 z φ hpde hdata hφ
  intro x y
  rw [hφ x y, hφx x]

theorem gap5 (z : ℝ → ℝ → ℝ)
    (hpde : SatisfiesPDE z) (hdata : SatisfiesInitialData z) :
    ∃ φ : ℝ → ℝ,
      ∀ x y, z x y = y ^ 2 + x * y + φ x := by
  refine ⟨fun x => z x 0, ?_⟩
  intro x y
  have hpolyDiff : Differentiable ℝ
      (fun t : ℝ => t ^ 2 + x * t) := by
    simpa only [pow_two] using
      (differentiable_id.mul differentiable_id).add
        ((differentiable_const (c := x)).mul differentiable_id)
  have hdiff : Differentiable ℝ
      (fun t : ℝ => z x t - (t ^ 2 + x * t)) :=
    ((hpde.1 x).1).sub hpolyDiff
  have hzero : ∀ t : ℝ,
      deriv (fun s : ℝ => z x s - (s ^ 2 + x * s)) t = 0 := by
    intro t
    have hz : HasDerivAt (fun s : ℝ => z x s)
        (partialY z x t) t := by
      simpa [partialY] using ((hpde.1 x).1 t).hasDerivAt
    have hsq : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
      simpa [pow_two, two_mul] using
        (hasDerivAt_id t).mul (hasDerivAt_id t)
    have hlin : HasDerivAt (fun s : ℝ => x * s) x t := by
      simpa using
        (hasDerivAt_const t x).mul (hasDerivAt_id t)
    have hpoly : HasDerivAt (fun s : ℝ => s ^ 2 + x * s)
        (2 * t + x) t := by
      simpa using hsq.add hlin
    calc
      deriv (fun s : ℝ => z x s - (s ^ 2 + x * s)) t =
          partialY z x t - (2 * t + x) := (hz.sub hpoly).deriv
      _ = 0 := by rw [gap4 z hpde hdata x t]; ring
  have hc := is_const_of_deriv_eq_zero hdiff hzero y 0
  simp at hc
  linarith

theorem gap6 (z : ℝ → ℝ → ℝ) (φ : ℝ → ℝ)
    (hpde : SatisfiesPDE z) (hdata : SatisfiesInitialData z)
    (hrepr : ∀ x y, z x y = y ^ 2 + x * y + φ x) :
    ∀ x, 1 = 0 + 0 + φ x := by
  intro x
  calc
    1 = z x 0 := (hdata.1 x).symm
    _ = 0 ^ 2 + x * 0 + φ x := hrepr x 0
    _ = 0 + 0 + φ x := by ring

theorem gap7 (z : ℝ → ℝ → ℝ) (φ : ℝ → ℝ)
    (hpde : SatisfiesPDE z) (hdata : SatisfiesInitialData z)
    (hrepr : ∀ x y, z x y = y ^ 2 + x * y + φ x) :
    ∀ x, φ x = 1 := by
  intro x
  have hx := gap6 z φ hpde hdata hrepr x
  linarith

theorem gap8 (z : ℝ → ℝ → ℝ) :
    (SatisfiesPDE z ∧ SatisfiesInitialData z) ↔
      ∀ x y, z x y = candidate x y := by
  constructor
  · rintro ⟨hpde, hdata⟩
    rcases gap5 z hpde hdata with ⟨φ, hrepr⟩
    have hφ : ∀ x, φ x = 1 := gap7 z φ hpde hdata hrepr
    intro x y
    calc
      z x y = y ^ 2 + x * y + φ x := hrepr x y
      _ = candidate x y := by rw [hφ x]; unfold candidate; ring
  · intro h
    have hz : z = candidate := by
      funext x y
      exact h x y
    rw [hz]
    exact candidate_satisfies

theorem gap9 (z : ℝ → ℝ → ℝ)
    (hz : z = candidate) :
    SatisfiesPDE z ∧ SatisfiesInitialData z := by
  rw [hz]
  exact candidate_satisfies

end

end ProofGap.Exercise3359
