import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise4274

noncomputable section

open scoped Interval

abbrev Point := ℝ × ℝ

def P (x y : ℝ) : ℝ :=
  Real.exp x * (Real.exp y * (x - y + 2) + y)

def Q (x y : ℝ) : ℝ :=
  Real.exp x * (Real.exp y * (x - y) + 1)

def field (p : Point) : Point :=
  (P p.1 p.2, Q p.1 p.2)

def potential (p : Point) : ℝ :=
  (p.1 - p.2 + 1) * Real.exp (p.1 + p.2) +
    p.2 * Real.exp p.1

def constructedPotential (p : Point) : ℝ :=
  (∫ s in (0 : ℝ)..p.1,
      (s - p.2 + 2) * Real.exp (s + p.2) +
        p.2 * Real.exp s) +
    ∫ t in (0 : ℝ)..p.2, 1 - t * Real.exp t

def HasCoordinateGradientAt
    (U : Point → ℝ) (V : Point) (p : Point) : Prop :=
  HasDerivAt (fun x => U (x, p.2)) V.1 p.1 ∧
    HasDerivAt (fun y => U (p.1, y)) V.2 p.2

def IsSolution (z : Point → ℝ) : Prop :=
  ∀ p, HasCoordinateGradientAt z (field p) p

private theorem potential_gradient (p : Point) :
    HasCoordinateGradientAt potential (field p) p := by
  constructor
  · convert
      (((((hasDerivAt_id p.1).sub_const p.2).add_const 1).mul
          ((Real.hasDerivAt_exp (p.1 + p.2)).comp p.1
            ((hasDerivAt_id p.1).add_const p.2))).add
        ((Real.hasDerivAt_exp p.1).const_mul p.2))
      using 1 <;>
      simp [potential, field, P, Real.exp_add] <;> ring
  · convert
      ((((((hasDerivAt_const p.2 p.1).sub (hasDerivAt_id p.2)).add_const 1).mul
          ((Real.hasDerivAt_exp (p.1 + p.2)).comp p.2
            ((hasDerivAt_const p.2 p.1).add (hasDerivAt_id p.2)))).add
        ((hasDerivAt_id p.2).mul_const (Real.exp p.1))))
      using 1 <;>
      simp [potential, field, Q, Real.exp_add] <;> ring

private theorem constructed_eq_potential_sub (p : Point) :
    constructedPotential p = potential p - potential (0, 0) := by
  have hc₁ : Continuous
      (fun s : ℝ =>
        (s - p.2 + 2) * Real.exp (s + p.2) + p.2 * Real.exp s) :=
    (((continuous_id.sub continuous_const).add continuous_const).mul
      (Real.continuous_exp.comp (continuous_id.add continuous_const))).add
      (continuous_const.mul Real.continuous_exp)
  have hd₁ :
      ∀ x ∈ Set.uIcc (0 : ℝ) p.1,
        HasDerivAt
          (fun u : ℝ => potential (u, p.2))
          ((x - p.2 + 2) * Real.exp (x + p.2) + p.2 * Real.exp x) x := by
    intro x hx
    have h := (potential_gradient (x, p.2)).1
    convert h using 1 <;>
      simp [field, P, Real.exp_add] <;> ring
  have h₁ :
      (∫ s in (0 : ℝ)..p.1,
          (s - p.2 + 2) * Real.exp (s + p.2) + p.2 * Real.exp s) =
        potential (p.1, p.2) - potential (0, p.2) := by
    simpa using
      (intervalIntegral.integral_eq_sub_of_hasDerivAt hd₁
        (hc₁.intervalIntegrable 0 p.1))
  have hc₂ : Continuous (fun t : ℝ => 1 - t * Real.exp t) :=
    continuous_const.sub (continuous_id.mul Real.continuous_exp)
  have hd₂ :
      ∀ t ∈ Set.uIcc (0 : ℝ) p.2,
        HasDerivAt
          (fun v : ℝ => potential (0, v))
          (1 - t * Real.exp t) t := by
    intro t ht
    have h := (potential_gradient (0, t)).2
    convert h using 1 <;>
      simp [field, Q] <;> ring
  have h₂ :
      (∫ t in (0 : ℝ)..p.2, 1 - t * Real.exp t) =
        potential (0, p.2) - potential (0, 0) := by
    simpa using
      (intervalIntegral.integral_eq_sub_of_hasDerivAt hd₂
        (hc₂.intervalIntegrable 0 p.2))
  unfold constructedPotential
  rw [h₁, h₂]
  ring

private theorem isSolution_potential_add (C : ℝ) :
    IsSolution (fun p => potential p + C) := by
  intro p
  constructor
  · simpa using (potential_gradient p).1.add_const C
  · simpa using (potential_gradient p).2.add_const C

private theorem solution_eq_potential_add (z : Point → ℝ) (hz : IsSolution z) :
    ∃ C : ℝ, ∀ p, z p = potential p + C := by
  refine ⟨z (0, 0) - potential (0, 0), ?_⟩
  rintro ⟨x, y⟩
  have hxderiv : ∀ u : ℝ,
      HasDerivAt
        (fun u => z (u, y) - potential (u, y)) 0 u := by
    intro u
    convert ((hz (u, y)).1.sub (potential_gradient (u, y)).1) using 1 <;>
      simp
  have hxconst :
      z (x, y) - potential (x, y) =
        z (0, y) - potential (0, y) :=
    is_const_of_deriv_eq_zero
      (fun u => (hxderiv u).differentiableAt)
      (fun u => (hxderiv u).deriv) x 0
  have hyderiv : ∀ v : ℝ,
      HasDerivAt
        (fun v => z (0, v) - potential (0, v)) 0 v := by
    intro v
    convert ((hz (0, v)).2.sub (potential_gradient (0, v)).2) using 1 <;>
      simp
  have hyconst :
      z (0, y) - potential (0, y) =
        z (0, 0) - potential (0, 0) :=
    is_const_of_deriv_eq_zero
      (fun v => (hyderiv v).differentiableAt)
      (fun v => (hyderiv v).deriv) y 0
  calc
    z (x, y) = potential (x, y) +
        (z (x, y) - potential (x, y)) := by ring
    _ = potential (x, y) +
        (z (0, y) - potential (0, y)) := by rw [hxconst]
    _ = potential (x, y) +
        (z (0, 0) - potential (0, 0)) := by rw [hyconst]

theorem gap1 (z : Point → ℝ) :
    IsSolution z ↔
      ∃ C : ℝ, ∀ p, z p = constructedPotential p + C := by
  constructor
  · intro hz
    rcases solution_eq_potential_add z hz with ⟨C, hC⟩
    refine ⟨C + potential (0, 0), ?_⟩
    intro p
    rw [hC p, constructed_eq_potential_sub]
    ring
  · rintro ⟨C, hz⟩
    have hzfun :
        z = fun p => potential p + (C - potential (0, 0)) := by
      funext p
      rw [hz p, constructed_eq_potential_sub]
      ring
    rw [hzfun]
    exact isSolution_potential_add (C - potential (0, 0))

theorem gap2 (p : Point) :
    constructedPotential p = potential p - potential (0, 0) := by
  exact constructed_eq_potential_sub p

theorem gap3 (z : Point → ℝ) :
    IsSolution z ↔
      ∃ C₁ : ℝ, ∀ p, z p = potential p + C₁ := by
  constructor
  · exact solution_eq_potential_add z
  · rintro ⟨C, hz⟩
    have hzfun : z = fun p => potential p + C := by
      funext p
      exact hz p
    rw [hzfun]
    exact isSolution_potential_add C

theorem gap4 (C₁ : ℝ) :
    IsSolution (fun p => potential p + C₁) := by
  exact isSolution_potential_add C₁

end

end ProofGap.Exercise4274
