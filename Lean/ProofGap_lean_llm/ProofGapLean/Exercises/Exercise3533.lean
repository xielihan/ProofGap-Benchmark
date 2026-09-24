import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3533

noncomputable section

abbrev Point3 := ℝ × (ℝ × ℝ)

def curve (t : ℝ) : Point3 := (t, (t ^ 2, t ^ 3))

def tangent (t : ℝ) : Point3 :=
  (deriv (fun s => (curve s).1) t,
    (deriv (fun s => (curve s).2.1) t,
      deriv (fun s => (curve s).2.2) t))

def planeNormal : Point3 := (1, (2, 1))

def dot (U V : Point3) : ℝ :=
  U.1 * V.1 + U.2.1 * V.2.1 + U.2.2 * V.2.2

def IsParallelToPlaneAt (t : ℝ) : Prop :=
  dot (tangent t) planeNormal = 0

def candidateParameters : Set ℝ := {-1, -(1 : ℝ) / 3}

def candidatePoints : Set Point3 :=
  {(-1, (1, -1)), (-(1 : ℝ) / 3, ((1 : ℝ) / 9, -(1 : ℝ) / 27))}

theorem gap1 :
    ∀ t, tangent t = (1, (2 * t, 3 * t ^ 2)) := by
  intro t
  have h1 : deriv (fun s : ℝ => s) t = 1 :=
    (hasDerivAt_id t).deriv
  have hsq : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
    simpa [pow_two, two_mul] using
      ((hasDerivAt_id t).mul (hasDerivAt_id t))
  have h2 : deriv (fun s : ℝ => s ^ 2) t = 2 * t :=
    hsq.deriv
  have hprod :
      HasDerivAt (fun s : ℝ => s ^ 2 * s) (2 * t * t + t ^ 2) t := by
    simpa using hsq.mul (hasDerivAt_id t)
  have h3 : deriv (fun s : ℝ => s ^ 3) t = 3 * t ^ 2 := by
    rw [show (fun s : ℝ => s ^ 3) = (fun s : ℝ => s ^ 2 * s) by
      funext s
      ring]
    calc
      deriv (fun s : ℝ => s ^ 2 * s) t = 2 * t * t + t ^ 2 := hprod.deriv
      _ = 3 * t ^ 2 := by ring
  change
    (deriv (fun s : ℝ => s) t,
      (deriv (fun s : ℝ => s ^ 2) t, deriv (fun s : ℝ => s ^ 3) t)) =
      (1, (2 * t, 3 * t ^ 2))
  rw [h1, h2, h3]

theorem gap2 :
    planeNormal = (1, (2, 1)) := by
  rfl

theorem gap3 :
    ∀ t, dot (tangent t) planeNormal = 1 + 4 * t + 3 * t ^ 2 := by
  intro t
  rw [gap1 t]
  dsimp [dot, planeNormal]
  ring

theorem gap4 (t : ℝ) (hParallel : IsParallelToPlaneAt t) :
    1 + 4 * t + 3 * t ^ 2 = 0 := by
  unfold IsParallelToPlaneAt at hParallel
  rw [gap3 t] at hParallel
  exact hParallel

theorem gap5 (t : ℝ) (hRoot : 1 + 4 * t + 3 * t ^ 2 = 0) :
    dot (tangent t) planeNormal = 0 := by
  rw [gap3 t]
  exact hRoot

theorem gap6 :
    ∀ t, t ∈ candidateParameters ↔ 1 + 4 * t + 3 * t ^ 2 = 0 := by
  intro t
  constructor
  · intro ht
    simp only [candidateParameters, Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with ht | ht
    · rw [ht]
      norm_num
    · rw [ht]
      norm_num
  · intro hRoot
    simp only [candidateParameters, Set.mem_insert_iff, Set.mem_singleton_iff]
    have hFactor : (t + 1) * (3 * t + 1) = 0 := by
      nlinarith [hRoot]
    rcases mul_eq_zero.mp hFactor with hLeft | hRight
    · left
      linarith
    · right
      linarith

theorem gap7 (M : Point3)
    (hM : ∃ t, IsParallelToPlaneAt t ∧ M = curve t) :
    M ∈ candidatePoints := by
  rcases hM with ⟨t, hParallel, hM⟩
  have hRoot : 1 + 4 * t + 3 * t ^ 2 = 0 := gap4 t hParallel
  have ht : t ∈ candidateParameters := (gap6 t).2 hRoot
  rw [hM]
  simp only [candidateParameters, Set.mem_insert_iff, Set.mem_singleton_iff] at ht
  rcases ht with ht | ht
  · rw [ht]
    norm_num [curve, candidatePoints]
  · rw [ht]
    norm_num [curve, candidatePoints]

end

end ProofGap.Exercise3533
