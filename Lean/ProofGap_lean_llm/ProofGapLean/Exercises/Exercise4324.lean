import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Add

namespace ProofGap.Exercise4324

noncomputable section

open MeasureTheory
open scoped Interval

def tangent (γ : ℝ → ℝ × ℝ) (s : ℝ) : ℝ × ℝ :=
  (deriv (fun t => (γ t).1) s, deriv (fun t => (γ t).2) s)

def outwardNormal (γ : ℝ → ℝ × ℝ) (s : ℝ) : ℝ × ℝ :=
  ((tangent γ s).2, -(tangent γ s).1)

def speed (γ : ℝ → ℝ × ℝ) (s : ℝ) : ℝ :=
  Real.sqrt ((tangent γ s).1 ^ 2 + (tangent γ s).2 ^ 2)

def IsUnitSpeed (γ : ℝ → ℝ × ℝ) (c d : ℝ) : Prop :=
  ∀ s ∈ Set.uIcc c d, speed γ s = 1

def boundaryFlux (γ : ℝ → ℝ × ℝ) (c d : ℝ) : ℝ :=
  ∫ s in c..d,
    (γ s).1 * (outwardNormal γ s).1 +
      (γ s).2 * (outwardNormal γ s).2

def wedgeIntegral (γ : ℝ → ℝ × ℝ) (c d : ℝ) : ℝ :=
  ∫ s in c..d,
    (γ s).1 * deriv (fun t => (γ t).2) s -
      (γ s).2 * deriv (fun t => (γ t).1) s

def regionArea (D : Set (ℝ × ℝ)) : ℝ :=
  ∫ _z in D, (1 : ℝ)

def IsPositiveAreaBoundary
    (γ : ℝ → ℝ × ℝ) (c d : ℝ) (D : Set (ℝ × ℝ)) : Prop :=
  c < d ∧
    γ c = γ d ∧
    IsUnitSpeed γ c d ∧
    γ '' Set.uIcc c d = frontier D ∧
    Bornology.IsBounded D ∧
    D = closure (interior D) ∧
    0 < wedgeIntegral γ c d

def greenLineIntegral
    (γ : ℝ → ℝ × ℝ) (c d : ℝ)
    (P Q : ℝ → ℝ → ℝ) : ℝ :=
  ∫ s in c..d,
    P (γ s).1 (γ s).2 * deriv (fun t => (γ t).1) s +
      Q (γ s).1 (γ s).2 * deriv (fun t => (γ t).2) s

def greenCurlIntegral
    (D : Set (ℝ × ℝ)) (P Q : ℝ → ℝ → ℝ) : ℝ :=
  ∫ z in D,
    deriv (fun x => Q x z.2) z.1 -
      deriv (fun y => P z.1 y) z.2

def SatisfiesGreenTheorem
    (γ : ℝ → ℝ × ℝ) (c d : ℝ)
    (D : Set (ℝ × ℝ)) : Prop :=
  ∀ P Q : ℝ → ℝ → ℝ,
    ContDiff ℝ 1 (fun z : ℝ × ℝ => P z.1 z.2) →
    ContDiff ℝ 1 (fun z : ℝ × ℝ => Q z.1 z.2) →
    greenLineIntegral γ c d P Q = greenCurlIntegral D P Q

theorem gap1 (γ : ℝ → ℝ × ℝ) (s : ℝ) :
    (outwardNormal γ s).1 = (tangent γ s).2 := by
  rfl

theorem gap2 (γ : ℝ → ℝ × ℝ) (s : ℝ) :
    (tangent γ s).2 = deriv (fun t => (γ t).2) s := by
  rfl

theorem gap3 (γ : ℝ → ℝ × ℝ) (s : ℝ) :
    (outwardNormal γ s).1 = deriv (fun t => (γ t).2) s := by
  rw [gap1, gap2]

theorem gap4 (γ : ℝ → ℝ × ℝ) (s : ℝ) :
    (γ s).1 * (outwardNormal γ s).1 =
      (γ s).1 * deriv (fun t => (γ t).2) s := by
  rw [gap3]

theorem gap5 (γ : ℝ → ℝ × ℝ) (s : ℝ) :
    (outwardNormal γ s).2 = -(tangent γ s).1 := by
  rfl

theorem gap6 (γ : ℝ → ℝ × ℝ) (s : ℝ) :
    (tangent γ s).1 = deriv (fun t => (γ t).1) s := by
  rfl

theorem gap7 (γ : ℝ → ℝ × ℝ) (s : ℝ) :
    (outwardNormal γ s).2 = -(tangent γ s).1 := by
  exact gap5 γ s

theorem gap8 (γ : ℝ → ℝ × ℝ) (s : ℝ) :
    (outwardNormal γ s).2 =
      -deriv (fun t => (γ t).1) s := by
  rw [gap5, gap6]

theorem gap9 (γ : ℝ → ℝ × ℝ) (s : ℝ) :
    -(tangent γ s).1 =
      -deriv (fun t => (γ t).1) s := by
  rw [gap6]

theorem gap10 (γ : ℝ → ℝ × ℝ) (s : ℝ) :
    (γ s).2 * (outwardNormal γ s).2 =
      -(γ s).2 * deriv (fun t => (γ t).1) s := by
  rw [gap8]
  ring

theorem gap11
    (γ : ℝ → ℝ × ℝ) (c d : ℝ)
    (hunit : IsUnitSpeed γ c d) :
    boundaryFlux γ c d = wedgeIntegral γ c d := by
  unfold boundaryFlux wedgeIntegral
  apply intervalIntegral.integral_congr
  intro s hs
  change
    (γ s).1 * (outwardNormal γ s).1 +
        (γ s).2 * (outwardNormal γ s).2 =
      (γ s).1 * deriv (fun t => (γ t).2) s -
        (γ s).2 * deriv (fun t => (γ t).1) s
  rw [gap3, gap8]
  ring

theorem gap12 (γ : ℝ → ℝ × ℝ) (c d : ℝ) :
    wedgeIntegral γ c d =
      2 * ((1 / 2 : ℝ) * wedgeIntegral γ c d) := by
  ring

theorem gap13
    (γ : ℝ → ℝ × ℝ) (c d : ℝ) (D : Set (ℝ × ℝ))
    (hboundary : IsPositiveAreaBoundary γ c d D)
    (hgreen : SatisfiesGreenTheorem γ c d D) :
    2 * ((1 / 2 : ℝ) * wedgeIntegral γ c d) =
      2 * regionArea D := by
  have hP : ContDiff ℝ 1 (fun z : ℝ × ℝ => -z.2) := by
    simpa using
      (-(ContinuousLinearMap.snd ℝ ℝ ℝ)).contDiff
  have hQ : ContDiff ℝ 1 (fun z : ℝ × ℝ => z.1) := by
    simpa using
      (ContinuousLinearMap.fst ℝ ℝ ℝ).contDiff
  have hgreen' :
      greenLineIntegral γ c d (fun _ y => -y) (fun x _ => x) =
        greenCurlIntegral D (fun _ y => -y) (fun x _ => x) :=
    hgreen (fun _ y => -y) (fun x _ => x) hP hQ
  have hline :
      greenLineIntegral γ c d (fun _ y => -y) (fun x _ => x) =
        wedgeIntegral γ c d := by
    unfold greenLineIntegral wedgeIntegral
    apply intervalIntegral.integral_congr
    intro s hs
    ring
  have hcurl :
      greenCurlIntegral D (fun _ y => -y) (fun x _ => x) =
        2 * regionArea D := by
    unfold greenCurlIntegral regionArea
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    exact Filter.Eventually.of_forall (fun z => by
      have hx : deriv (fun x : ℝ => x) z.1 = 1 :=
        (hasDerivAt_id z.1).deriv
      have hzero :
          HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 z.2 :=
        hasDerivAt_const z.2 0
      have hone :
          HasDerivAt (fun y : ℝ => y) 1 z.2 :=
        hasDerivAt_id z.2
      have hneg :
          HasDerivAt (fun y : ℝ => (0 : ℝ) - y) (0 - 1) z.2 :=
        hzero.sub hone
      have hy : deriv (fun y : ℝ => -y) z.2 = -1 := by
        simpa only [zero_sub] using hneg.deriv
      change
        deriv (fun x : ℝ => x) z.1 -
            deriv (fun y : ℝ => -y) z.2 =
          2 * 1
      rw [hx, hy]
      ring)
  calc
    2 * ((1 / 2 : ℝ) * wedgeIntegral γ c d) = wedgeIntegral γ c d :=
      (gap12 γ c d).symm
    _ = greenLineIntegral γ c d (fun _ y => -y) (fun x _ => x) := hline.symm
    _ = greenCurlIntegral D (fun _ y => -y) (fun x _ => x) := hgreen'
    _ = 2 * regionArea D := hcurl

theorem gap14
    (γ : ℝ → ℝ × ℝ) (c d : ℝ) (D : Set (ℝ × ℝ))
    (hboundary : IsPositiveAreaBoundary γ c d D)
    (hgreen : SatisfiesGreenTheorem γ c d D) :
    boundaryFlux γ c d = 2 * regionArea D := by
  calc
    boundaryFlux γ c d = wedgeIntegral γ c d :=
      gap11 γ c d hboundary.2.2.1
    _ = 2 * ((1 / 2 : ℝ) * wedgeIntegral γ c d) :=
      gap12 γ c d
    _ = 2 * regionArea D :=
      gap13 γ c d D hboundary hgreen

end

end ProofGap.Exercise4324
