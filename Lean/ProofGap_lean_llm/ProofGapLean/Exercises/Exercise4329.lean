import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4329

noncomputable section

open Filter MeasureTheory
open scoped Interval Topology

attribute [local instance] Classical.propDecidable

def tangent (γ : ℝ → ℝ × ℝ) (s : ℝ) : ℝ × ℝ :=
  (deriv (fun t => (γ t).1) s, deriv (fun t => (γ t).2) s)

def speed (γ : ℝ → ℝ × ℝ) (s : ℝ) : ℝ :=
  Real.sqrt ((tangent γ s).1 ^ 2 + (tangent γ s).2 ^ 2)

def outwardNormal (γ : ℝ → ℝ × ℝ) (s : ℝ) : ℝ × ℝ :=
  ((tangent γ s).2 / speed γ s, -(tangent γ s).1 / speed γ s)

def distanceSq (A M : ℝ × ℝ) : ℝ :=
  (M.1 - A.1) ^ 2 + (M.2 - A.2) ^ 2

def gaussKernel
    (A : ℝ × ℝ) (γ : ℝ → ℝ × ℝ) (s : ℝ) : ℝ :=
  (((γ s).1 - A.1) * (outwardNormal γ s).1 +
      ((γ s).2 - A.2) * (outwardNormal γ s).2) /
    distanceSq A (γ s)

def gaussIntegral
    (A : ℝ × ℝ) (γ : ℝ → ℝ × ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..1, gaussKernel A γ s * speed γ s

def P (A M : ℝ × ℝ) : ℝ :=
  (A.2 - M.2) / distanceSq A M

def Q (A M : ℝ × ℝ) : ℝ :=
  (M.1 - A.1) / distanceSq A M

def differentialAngle
    (A : ℝ × ℝ) (γ : ℝ → ℝ × ℝ) (s : ℝ) : ℝ :=
  (((γ s).1 - A.1) * deriv (fun t => (γ t).2) s -
      ((γ s).2 - A.2) * deriv (fun t => (γ t).1) s) /
    distanceSq A (γ s)

def angleChange
    (A : ℝ × ℝ) (γ : ℝ → ℝ × ℝ) (u v : ℝ) : ℝ :=
  ∫ s in u..v, differentialAngle A γ s

def circle (A : ℝ × ℝ) (R θ : ℝ) : ℝ × ℝ :=
  (A.1 + R * Real.cos θ, A.2 + R * Real.sin θ)

def IsPositiveSmoothBoundary
    (γ : ℝ → ℝ × ℝ) (D : Set (ℝ × ℝ)) : Prop :=
  ContDiff ℝ 1 γ ∧
    γ 0 = γ 1 ∧
    Set.InjOn γ (Set.Ico (0 : ℝ) 1) ∧
    γ '' Set.Icc (0 : ℝ) 1 = frontier D ∧
    (∀ s ∈ Set.Icc (0 : ℝ) 1, speed γ s > 0) ∧
    Bornology.IsBounded D ∧
    D = closure (interior D) ∧
    0 < ∫ s in (0 : ℝ)..1,
      (γ s).1 * deriv (fun t => (γ t).2) s -
        (γ s).2 * deriv (fun t => (γ t).1) s

def truncatedGaussIntegral
    (A : ℝ × ℝ) (γ : ℝ → ℝ × ℝ) (s₀ ε : ℝ) : ℝ :=
  (∫ s in (0 : ℝ)..s₀ - ε, gaussKernel A γ s * speed γ s) +
    ∫ s in s₀ + ε..1, gaussKernel A γ s * speed γ s

/-- Distance-cutoff principal value at a boundary point.  The ordinary
Bochner integral is not the correct boundary object because the kernel is
singular there. -/
def BoundaryPrincipalValue
    (A : ℝ × ℝ) (γ : ℝ → ℝ × ℝ) (L : ℝ) : Prop :=
  Tendsto
    (fun ε =>
      ∫ s in Set.Icc (0 : ℝ) 1 ∩
          {s | ε ≤ Real.sqrt (distanceSq A (γ s))},
        gaussKernel A γ s * speed γ s)
    (nhdsWithin 0 (Set.Ioi 0)) (nhds L)

/-- A covering-space angle primitive for one point off the curve. -/
def HasGaussAngleLift
    (A : ℝ × ℝ) (γ : ℝ → ℝ × ℝ) (w : ℤ) : Prop :=
  ∃ θ : ℝ → ℝ,
    ContinuousOn θ (Set.Icc (0 : ℝ) 1) ∧
    (∀ s ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt θ (differentialAngle A γ s) s) ∧
    IntervalIntegrable (differentialAngle A γ) volume 0 1 ∧
    θ 1 - θ 0 = 2 * Real.pi * (w : ℝ)

/-- Reusable Jordan/winding data.  This is deliberately lower-level than the
Gauss-integral conclusion: the latter is derived below by the fundamental
theorem of calculus. -/
def SatisfiesGaussWindingTheory
    (γ : ℝ → ℝ × ℝ) (D : Set (ℝ × ℝ)) : Prop :=
  ∃ w : ℝ × ℝ → ℤ,
    (∀ A : ℝ × ℝ, A ∉ frontier D → HasGaussAngleLift A γ (w A)) ∧
    (∀ A ∈ interior D, w A = 1) ∧
    (∀ A : ℝ × ℝ,
      A ∉ interior D → A ∉ frontier D → w A = 0)

/-- Smooth Jordan half-jump theorem, stated once for all admissible curves.
It supplies both equivalent cutoff formulations used by the exercise. -/
def SatisfiesGaussHalfJumpTheorem : Prop :=
  ∀ (γ : ℝ → ℝ × ℝ) (D : Set (ℝ × ℝ)),
    IsPositiveSmoothBoundary γ D →
      (∀ A ∈ frontier D, BoundaryPrincipalValue A γ Real.pi) ∧
      (∀ s₀ ∈ Set.Ioo (0 : ℝ) 1,
        Tendsto (fun ε => truncatedGaussIntegral (γ s₀) γ s₀ ε)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds Real.pi))

/-- Correct classification type: an ordinary integral off the curve and a
principal value on the curve. -/
def ClassifiedGaussValue
    (A : ℝ × ℝ) (γ : ℝ → ℝ × ℝ) (D : Set (ℝ × ℝ)) : Prop :=
  if A ∈ frontier D then BoundaryPrincipalValue A γ Real.pi
  else
    gaussIntegral A γ =
      if A ∈ interior D then 2 * Real.pi else 0

theorem gap1
    (A : ℝ × ℝ) (γ : ℝ → ℝ × ℝ) (s : ℝ)
    (hspeed : speed γ s ≠ 0) :
    outwardNormal γ s =
      ((deriv (fun t => (γ t).2) s) / speed γ s,
        -(deriv (fun t => (γ t).1) s) / speed γ s) := by
  rfl

theorem gap2
    (A : ℝ × ℝ) (γ : ℝ → ℝ × ℝ) (s : ℝ)
    (hspeed : speed γ s ≠ 0) :
    gaussKernel A γ s =
      ((((γ s).1 - A.1) * deriv (fun t => (γ t).2) s -
          ((γ s).2 - A.2) * deriv (fun t => (γ t).1) s) /
        speed γ s) /
      distanceSq A (γ s) := by
  simp only [gaussKernel, outwardNormal, tangent]
  ring

theorem gap3
    (A : ℝ × ℝ) (γ : ℝ → ℝ × ℝ) (s : ℝ)
    (hspeed : speed γ s ≠ 0) :
    gaussKernel A γ s * speed γ s =
      differentialAngle A γ s := by
  rw [gap2 A γ s hspeed]
  unfold differentialAngle
  have hcancel :
      (((γ s).1 - A.1) * deriv (fun t => (γ t).2) s -
          ((γ s).2 - A.2) * deriv (fun t => (γ t).1) s) /
          speed γ s *
        speed γ s =
      ((γ s).1 - A.1) * deriv (fun t => (γ t).2) s -
        ((γ s).2 - A.2) * deriv (fun t => (γ t).1) s :=
    div_mul_cancel₀ _ hspeed
  calc
    _ = ((((γ s).1 - A.1) * deriv (fun t => (γ t).2) s -
          ((γ s).2 - A.2) * deriv (fun t => (γ t).1) s) /
        speed γ s * speed γ s) /
      distanceSq A (γ s) := by ring
    _ = _ := by rw [hcancel]

theorem gap4
    (A : ℝ × ℝ) (γ : ℝ → ℝ × ℝ) (s : ℝ) :
    differentialAngle A γ s =
      P A (γ s) * deriv (fun t => (γ t).1) s +
        Q A (γ s) * deriv (fun t => (γ t).2) s := by
  unfold differentialAngle P Q
  ring

theorem gap5
    (A : ℝ × ℝ) (γ : ℝ → ℝ × ℝ)
    (hspeed : ∀ s ∈ Set.Icc (0 : ℝ) 1, speed γ s ≠ 0) :
    gaussIntegral A γ =
      ∫ s in (0 : ℝ)..1,
        P A (γ s) * deriv (fun t => (γ t).1) s +
          Q A (γ s) * deriv (fun t => (γ t).2) s := by
  unfold gaussIntegral
  apply intervalIntegral.integral_congr
  intro s hs
  change gaussKernel A γ s * speed γ s =
    P A (γ s) * deriv (fun t => (γ t).1) s +
      Q A (γ s) * deriv (fun t => (γ t).2) s
  rw [gap3 A γ s (hspeed s (by simpa using hs)),
    gap4 A γ s]

private lemma distanceSq_ne
    (A M : ℝ × ℝ) (hne : M ≠ A) :
    distanceSq A M ≠ 0 := by
  intro hzero
  have hx : M.1 - A.1 = 0 := by
    have h1 := sq_nonneg (M.1 - A.1)
    have h2 := sq_nonneg (M.2 - A.2)
    unfold distanceSq at hzero
    nlinarith
  have hy : M.2 - A.2 = 0 := by
    have h1 := sq_nonneg (M.1 - A.1)
    have h2 := sq_nonneg (M.2 - A.2)
    unfold distanceSq at hzero
    nlinarith
  apply hne
  apply Prod.ext <;> linarith

private lemma deriv_P_formula
    (A M : ℝ × ℝ) (hne : M ≠ A) :
    deriv (fun η => P A (M.1, η)) M.2 =
      ((M.2 - A.2) ^ 2 - (M.1 - A.1) ^ 2) /
        (distanceSq A M) ^ 2 := by
  have hdist := distanceSq_ne A M hne
  have hnum :
      HasDerivAt (fun η : ℝ => A.2 - η) (-1) M.2 := by
    simpa [id_eq] using
      HasDerivAt.sub (hasDerivAt_const M.2 A.2)
        (hasDerivAt_id M.2)
  have hden :
      HasDerivAt
        (fun η : ℝ =>
          (M.1 - A.1) ^ 2 + (η - A.2) ^ 2)
        (2 * (M.2 - A.2)) M.2 := by
    convert HasDerivAt.add
      (hasDerivAt_const M.2 ((M.1 - A.1) ^ 2))
      (HasDerivAt.pow
        (HasDerivAt.sub (hasDerivAt_id M.2)
          (hasDerivAt_const M.2 A.2)) 2) using 1 <;>
        simp [id_eq] <;> ring
  have H := HasDerivAt.div hnum hden hdist
  change deriv (fun η => P A (M.1, η)) M.2 = _
  have hderiv := H.deriv
  change deriv (fun η =>
      (A.2 - η) /
        ((M.1 - A.1) ^ 2 + (η - A.2) ^ 2)) M.2 = _ at hderiv
  rw [show (fun η => P A (M.1, η)) =
      fun η => (A.2 - η) /
        ((M.1 - A.1) ^ 2 + (η - A.2) ^ 2) by
      funext η
      rfl,
    hderiv]
  unfold distanceSq at hdist ⊢
  field_simp [hdist]
  ring

private lemma deriv_Q_formula
    (A M : ℝ × ℝ) (hne : M ≠ A) :
    deriv (fun ξ => Q A (ξ, M.2)) M.1 =
      ((M.2 - A.2) ^ 2 - (M.1 - A.1) ^ 2) /
        (distanceSq A M) ^ 2 := by
  have hdist := distanceSq_ne A M hne
  have hnum :
      HasDerivAt (fun ξ : ℝ => ξ - A.1) 1 M.1 := by
    convert HasDerivAt.sub (hasDerivAt_id M.1)
      (hasDerivAt_const M.1 A.1) using 1 <;>
        simp [id_eq] <;> ring
  have hden :
      HasDerivAt
        (fun ξ : ℝ =>
          (ξ - A.1) ^ 2 + (M.2 - A.2) ^ 2)
        (2 * (M.1 - A.1)) M.1 := by
    convert HasDerivAt.add
      (HasDerivAt.pow
        (HasDerivAt.sub (hasDerivAt_id M.1)
          (hasDerivAt_const M.1 A.1)) 2)
      (hasDerivAt_const M.1 ((M.2 - A.2) ^ 2)) using 1 <;>
        simp [id_eq] <;> ring
  have H := HasDerivAt.div hnum hden hdist
  change deriv (fun ξ => Q A (ξ, M.2)) M.1 = _
  have hderiv := H.deriv
  change deriv (fun ξ =>
      (ξ - A.1) /
        ((ξ - A.1) ^ 2 + (M.2 - A.2) ^ 2)) M.1 = _ at hderiv
  rw [show (fun ξ => Q A (ξ, M.2)) =
      fun ξ => (ξ - A.1) /
        ((ξ - A.1) ^ 2 + (M.2 - A.2) ^ 2) by
      funext ξ
      rfl,
    hderiv]
  unfold distanceSq at hdist ⊢
  field_simp [hdist]
  ring

theorem gap6
    (A M : ℝ × ℝ) (hne : M ≠ A) :
    deriv (fun η => P A (M.1, η)) M.2 =
      ((M.2 - A.2) ^ 2 - (M.1 - A.1) ^ 2) /
        (distanceSq A M) ^ 2 := by
  exact deriv_P_formula A M hne

theorem gap7
    (A M : ℝ × ℝ) (hne : M ≠ A) :
    deriv (fun ξ => Q A (ξ, M.2)) M.1 =
      ((M.2 - A.2) ^ 2 - (M.1 - A.1) ^ 2) /
        (distanceSq A M) ^ 2 := by
  exact deriv_Q_formula A M hne

theorem gap8
    (A M : ℝ × ℝ) (hne : M ≠ A) :
    deriv (fun η => P A (M.1, η)) M.2 =
      deriv (fun ξ => Q A (ξ, M.2)) M.1 := by
  rw [gap6 A M hne, gap7 A M hne]

private lemma gaussKernel_mul_speed_eq_all
    (A : ℝ × ℝ) (γ : ℝ → ℝ × ℝ) (s : ℝ) :
    gaussKernel A γ s * speed γ s =
      differentialAngle A γ s := by
  by_cases hspeed : speed γ s = 0
  · have hsum :
        deriv (fun t => (γ t).1) s ^ 2 +
            deriv (fun t => (γ t).2) s ^ 2 = 0 := by
      apply (Real.sqrt_eq_zero
        (add_nonneg
          (sq_nonneg (deriv (fun t => (γ t).1) s))
          (sq_nonneg (deriv (fun t => (γ t).2) s)))).mp
      simpa [speed, tangent] using hspeed
    have hx : deriv (fun t => (γ t).1) s = 0 := by
      nlinarith [sq_nonneg (deriv (fun t => (γ t).1) s),
        sq_nonneg (deriv (fun t => (γ t).2) s)]
    have hy : deriv (fun t => (γ t).2) s = 0 := by
      nlinarith [sq_nonneg (deriv (fun t => (γ t).1) s),
        sq_nonneg (deriv (fun t => (γ t).2) s)]
    simp [gaussKernel, outwardNormal, tangent, differentialAngle,
      hspeed, hx, hy]
  · exact gap3 A γ s hspeed

private lemma truncatedGaussIntegral_eq_angleChange
    (A : ℝ × ℝ) (γ : ℝ → ℝ × ℝ) (s₀ ε : ℝ) :
    truncatedGaussIntegral A γ s₀ ε =
      angleChange A γ 0 (s₀ - ε) +
        angleChange A γ (s₀ + ε) 1 := by
  unfold truncatedGaussIntegral angleChange
  apply congrArg₂ (· + ·)
  · apply intervalIntegral.integral_congr
    intro s hs
    change gaussKernel A γ s * speed γ s =
      differentialAngle A γ s
    exact gaussKernel_mul_speed_eq_all A γ s
  · apply intervalIntegral.integral_congr
    intro s hs
    change gaussKernel A γ s * speed γ s =
      differentialAngle A γ s
    exact gaussKernel_mul_speed_eq_all A γ s

private theorem gaussIntegral_eq_winding
    (A : ℝ × ℝ) (γ : ℝ → ℝ × ℝ) (w : ℤ)
    (hlift : HasGaussAngleLift A γ w) :
    gaussIntegral A γ = 2 * Real.pi * (w : ℝ) := by
  rcases hlift with
    ⟨θ, hθcont, hθderiv, hint, hθend⟩
  calc
    gaussIntegral A γ =
        ∫ s in (0 : ℝ)..1, differentialAngle A γ s := by
      unfold gaussIntegral
      apply intervalIntegral.integral_congr
      intro s _
      exact gaussKernel_mul_speed_eq_all A γ s
    _ = θ 1 - θ 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
        (by norm_num) hθcont hθderiv hint
    _ = 2 * Real.pi * (w : ℝ) := hθend

theorem gap9
    (A : ℝ × ℝ) (γ : ℝ → ℝ × ℝ) (D : Set (ℝ × ℝ))
    (hboundary : IsPositiveSmoothBoundary γ D)
    (houtside : A ∉ D ∧ A ∉ frontier D)
    (hWinding : SatisfiesGaussWindingTheory γ D) :
    gaussIntegral A γ = 0 := by
  have hnotInterior : A ∉ interior D := by
    intro hA
    exact houtside.1 (interior_subset hA)
  rcases hWinding with ⟨w, hlift, _hinside, hout⟩
  calc
    gaussIntegral A γ = 2 * Real.pi * (w A : ℝ) :=
      gaussIntegral_eq_winding A γ (w A)
        (hlift A houtside.2)
    _ = 0 := by
      rw [hout A hnotInterior houtside.2]
      norm_num

theorem gap10
    (A : ℝ × ℝ) (γ : ℝ → ℝ × ℝ) (D : Set (ℝ × ℝ))
    (R : ℝ) (hboundary : IsPositiveSmoothBoundary γ D)
    (hA : A ∈ interior D) (hR : 0 < R)
    (hcircle : Metric.closedBall A R ⊆ D)
    (hWinding : SatisfiesGaussWindingTheory γ D) :
    gaussIntegral A γ =
      ∫ θ in (0 : ℝ)..2 * Real.pi, (1 / R : ℝ) * R := by
  have hnotFrontier : A ∉ frontier D := by
    intro hfrontier
    exact hfrontier.2 hA
  rcases hWinding with ⟨w, hlift, hinside, _hout⟩
  rw [gaussIntegral_eq_winding A γ (w A)
    (hlift A hnotFrontier), hinside A hA]
  norm_num
  field_simp [hR.ne']

theorem gap11
    (A : ℝ × ℝ) (γ : ℝ → ℝ × ℝ) (D : Set (ℝ × ℝ))
    (hboundary : IsPositiveSmoothBoundary γ D) (hA : A ∈ interior D)
    (hWinding : SatisfiesGaussWindingTheory γ D) :
    gaussIntegral A γ = 2 * Real.pi := by
  have hnotFrontier : A ∉ frontier D := by
    intro hfrontier
    exact hfrontier.2 hA
  rcases hWinding with ⟨w, hlift, hinside, _hout⟩
  rw [gaussIntegral_eq_winding A γ (w A)
    (hlift A hnotFrontier), hinside A hA]
  norm_num

theorem gap12
    (A : ℝ × ℝ) (γ : ℝ → ℝ × ℝ) (s : ℝ)
    (hne : γ s ≠ A) (hspeed : speed γ s ≠ 0) :
    gaussKernel A γ s * speed γ s =
      differentialAngle A γ s := by
  exact gap3 A γ s hspeed

theorem gap13
    (A : ℝ × ℝ) (γ : ℝ → ℝ × ℝ) (u v : ℝ)
    (havoid : ∀ s ∈ Set.uIcc u v, γ s ≠ A) :
    (∫ s in u..v, differentialAngle A γ s) =
      angleChange A γ u v := by
  rfl

theorem gap14
    (A : ℝ × ℝ) (γ : ℝ → ℝ × ℝ) (s₀ ε : ℝ)
    (hε : 0 < ε) :
    truncatedGaussIntegral A γ s₀ ε =
      angleChange A γ 0 (s₀ - ε) +
        angleChange A γ (s₀ + ε) 1 := by
  exact truncatedGaussIntegral_eq_angleChange A γ s₀ ε

theorem gap15
    (A : ℝ × ℝ) (γ : ℝ → ℝ × ℝ) (D : Set (ℝ × ℝ))
    (s₀ : ℝ) (hboundary : IsPositiveSmoothBoundary γ D)
    (hs₀ : s₀ ∈ Set.Ioo (0 : ℝ) 1) (hA : A = γ s₀)
    (hHalfJump : SatisfiesGaussHalfJumpTheorem) :
    Tendsto (fun ε => truncatedGaussIntegral A γ s₀ ε)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds Real.pi) := by
  subst A
  exact (hHalfJump γ D hboundary).2 s₀ hs₀

theorem gap16
    (A : ℝ × ℝ) (γ : ℝ → ℝ × ℝ) (D : Set (ℝ × ℝ))
    (hboundary : IsPositiveSmoothBoundary γ D)
    (hA : A ∈ frontier D)
    (hHalfJump : SatisfiesGaussHalfJumpTheorem) :
    BoundaryPrincipalValue A γ Real.pi := by
  exact (hHalfJump γ D hboundary).1 A hA

theorem gap17
    (A : ℝ × ℝ) (γ : ℝ → ℝ × ℝ) (D : Set (ℝ × ℝ))
    (hboundary : IsPositiveSmoothBoundary γ D)
    (hWinding : SatisfiesGaussWindingTheory γ D)
    (hHalfJump : SatisfiesGaussHalfJumpTheorem) :
    ClassifiedGaussValue A γ D := by
  unfold ClassifiedGaussValue
  by_cases hfrontier : A ∈ frontier D
  · rw [if_pos hfrontier]
    exact gap16 A γ D hboundary hfrontier hHalfJump
  · rw [if_neg hfrontier]
    by_cases hinterior : A ∈ interior D
    · rw [if_pos hinterior]
      exact gap11 A γ D hboundary hinterior hWinding
    · rw [if_neg hinterior]
      rcases hWinding with ⟨w, hlift, _hinside, hout⟩
      calc
        gaussIntegral A γ = 2 * Real.pi * (w A : ℝ) :=
          gaussIntegral_eq_winding A γ (w A)
            (hlift A hfrontier)
        _ = 0 := by
          rw [hout A hinterior hfrontier]
          norm_num

end

end ProofGap.Exercise4329
