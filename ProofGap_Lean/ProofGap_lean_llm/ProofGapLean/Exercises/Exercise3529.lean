import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ProofGap.Exercise3529

noncomputable section

abbrev Point3 := ℝ × (ℝ × ℝ)

def curve (a b c t : ℝ) : Point3 :=
  (a * Real.sin t ^ 2, (b * Real.sin t * Real.cos t, c * Real.cos t ^ 2))

def tangent (a b c t : ℝ) : Point3 :=
  (deriv (fun s => (curve a b c s).1) t,
    (deriv (fun s => (curve a b c s).2.1) t,
      deriv (fun s => (curve a b c s).2.2) t))

def basePoint (a b c : ℝ) : Point3 := (a / 2, (b / 2, c / 2))

def tangentDirection (a c : ℝ) : Point3 := (a, (0, -c))

def linePoint (P V : Point3) (s : ℝ) : Point3 :=
  (P.1 + s * V.1, (P.2.1 + s * V.2.1, P.2.2 + s * V.2.2))

def OnTangentLine (P V Q : Point3) : Prop :=
  ∃ s : ℝ, Q = linePoint P V s

def OnNormalPlane (P V Q : Point3) : Prop :=
  V.1 * (Q.1 - P.1) + V.2.1 * (Q.2.1 - P.2.1) +
    V.2.2 * (Q.2.2 - P.2.2) = 0

theorem gap1 (a b c : ℝ) :
    (curve a b c (Real.pi / 4)).1 = a * Real.sin (Real.pi / 4) ^ 2 := by
  rfl

theorem gap2 (a : ℝ) :
    a * Real.sin (Real.pi / 4) ^ 2 = a / 2 := by
  rw [Real.sin_pi_div_four]
  calc
    a * (Real.sqrt 2 / 2) ^ 2 = a * (Real.sqrt 2) ^ 2 / 4 := by ring
    _ = a / 2 := by
      rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      ring

theorem gap3 (a b c : ℝ) :
    (curve a b c (Real.pi / 4)).1 = a / 2 := by
  calc
    (curve a b c (Real.pi / 4)).1 = a * Real.sin (Real.pi / 4) ^ 2 := gap1 a b c
    _ = a / 2 := gap2 a

theorem gap4 (a b c : ℝ) :
    (curve a b c (Real.pi / 4)).2.1 = b / 2 := by
  change b * Real.sin (Real.pi / 4) * Real.cos (Real.pi / 4) = b / 2
  rw [Real.sin_pi_div_four, Real.cos_pi_div_four]
  calc
    b * (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) = b * (Real.sqrt 2) ^ 2 / 4 := by ring
    _ = b / 2 := by
      rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      ring

theorem gap5 (a b c : ℝ) :
    (curve a b c (Real.pi / 4)).2.2 = c / 2 := by
  change c * Real.cos (Real.pi / 4) ^ 2 = c / 2
  rw [Real.cos_pi_div_four]
  calc
    c * (Real.sqrt 2 / 2) ^ 2 = c * (Real.sqrt 2) ^ 2 / 4 := by ring
    _ = c / 2 := by
      rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      ring

theorem gap6 (a b c : ℝ) :
    tangent a b c (Real.pi / 4) = tangentDirection a c := by
  have hx :
      deriv (fun s : ℝ => a * Real.sin s ^ 2) (Real.pi / 4) = a := by
    convert (((Real.hasDerivAt_sin (Real.pi / 4)).pow 2).const_mul a).deriv using 1
    rw [Real.sin_pi_div_four, Real.cos_pi_div_four]
    ring_nf
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  have hy :
      deriv (fun s : ℝ => b * Real.sin s * Real.cos s) (Real.pi / 4) = 0 := by
    convert ((((Real.hasDerivAt_sin (Real.pi / 4)).const_mul b).mul
      (Real.hasDerivAt_cos (Real.pi / 4))).deriv) using 1
    rw [Real.sin_pi_div_four, Real.cos_pi_div_four]
    ring
  have hz :
      deriv (fun s : ℝ => c * Real.cos s ^ 2) (Real.pi / 4) = -c := by
    convert (((Real.hasDerivAt_cos (Real.pi / 4)).pow 2).const_mul c).deriv using 1
    rw [Real.sin_pi_div_four, Real.cos_pi_div_four]
    ring_nf
    rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  change
    (deriv (fun s : ℝ => a * Real.sin s ^ 2) (Real.pi / 4),
      (deriv (fun s : ℝ => b * Real.sin s * Real.cos s) (Real.pi / 4),
        deriv (fun s : ℝ => c * Real.cos s ^ 2) (Real.pi / 4))) =
      (a, (0, -c))
  rw [hx, hy, hz]

theorem gap7 (a b c : ℝ) (Q : Point3)
    (hLine : OnTangentLine (basePoint a b c) (tangentDirection a c) Q) :
    (Q.1 - a / 2) * (-c) = (Q.2.2 - c / 2) * a := by
  rcases hLine with ⟨s, rfl⟩
  dsimp [linePoint, basePoint, tangentDirection]
  ring

theorem gap8 (a b c : ℝ) (Q : Point3)
    (hLine : OnTangentLine (basePoint a b c) (tangentDirection a c) Q) :
    Q.2.1 = b / 2 := by
  rcases hLine with ⟨s, rfl⟩
  simp [linePoint, basePoint, tangentDirection]

theorem gap9 (a b c : ℝ) (Q : Point3)
    (ha : a ≠ 0) (hc : c ≠ 0)
    (hLine : OnTangentLine (basePoint a b c) (tangentDirection a c) Q) :
    Q.1 / a + Q.2.2 / c = 1 := by
  rcases hLine with ⟨s, rfl⟩
  dsimp [linePoint, basePoint, tangentDirection]
  field_simp [ha, hc] <;> ring

theorem gap10 (a b c : ℝ) (Q : Point3)
    (hLine : OnTangentLine (basePoint a b c) (tangentDirection a c) Q) :
    Q.2.1 = b / 2 := by
  exact gap8 a b c Q hLine

theorem gap11 (a b c : ℝ) (Q : Point3)
    (hPlane : OnNormalPlane (basePoint a b c) (tangentDirection a c) Q) :
    a * (Q.1 - a / 2) - c * (Q.2.2 - c / 2) = 0 := by
  simpa [OnNormalPlane, basePoint, tangentDirection] using hPlane

theorem gap12 (a b c : ℝ) (Q : Point3)
    (hPlane : OnNormalPlane (basePoint a b c) (tangentDirection a c) Q) :
    a * Q.1 - c * Q.2.2 = (1 : ℝ) / 2 * (a ^ 2 - c ^ 2) := by
  have h := gap11 a b c Q hPlane
  calc
    a * Q.1 - c * Q.2.2 =
        (a * (Q.1 - a / 2) - c * (Q.2.2 - c / 2)) +
          (1 : ℝ) / 2 * (a ^ 2 - c ^ 2) := by ring
    _ = (1 : ℝ) / 2 * (a ^ 2 - c ^ 2) := by rw [h]; ring

end

end ProofGap.Exercise3529
