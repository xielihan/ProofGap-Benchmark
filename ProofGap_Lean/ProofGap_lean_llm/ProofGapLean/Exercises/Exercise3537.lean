import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Prod

namespace ProofGap.Exercise3537

noncomputable section

abbrev Point3 := ℝ × (ℝ × ℝ)

def partialX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => f s y) x

def partialY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => f x s) y

def phi (x0 y0 α x : ℝ) : ℝ :=
  y0 + (x - x0) * Real.tan α

def psi (f : ℝ → ℝ → ℝ) (x0 y0 α x : ℝ) : ℝ :=
  f x (phi x0 y0 α x)

def rawTangent (f : ℝ → ℝ → ℝ) (x0 y0 α : ℝ) : Point3 :=
  (1,
    (deriv (phi x0 y0 α) x0,
      deriv (psi f x0 y0 α) x0))

def explicitXDirection (f : ℝ → ℝ → ℝ) (x0 y0 α : ℝ) : Point3 :=
  (1,
    (Real.tan α,
      partialX f x0 y0 + Real.tan α * partialY f x0 y0))

def inclinationSlopeX (f : ℝ → ℝ → ℝ) (x0 y0 α : ℝ) : ℝ :=
  (rawTangent f x0 y0 α).2.2 /
    Real.sqrt (1 + (rawTangent f x0 y0 α).2.1 ^ 2)

def directionalSlope (f : ℝ → ℝ → ℝ) (x0 y0 α : ℝ) : ℝ :=
  partialX f x0 y0 * Real.cos α + partialY f x0 y0 * Real.sin α

def unitDirection (f : ℝ → ℝ → ℝ) (x0 y0 α : ℝ) : Point3 :=
  (Real.cos α, (Real.sin α, directionalSlope f x0 y0 α))

def surfacePoint (f : ℝ → ℝ → ℝ) (x0 y0 : ℝ) : Point3 :=
  (x0, (y0, f x0 y0))

def linePoint (P V : Point3) (s : ℝ) : Point3 :=
  (P.1 + s * V.1, (P.2.1 + s * V.2.1, P.2.2 + s * V.2.2))

def OnTangentLine (P V Q : Point3) : Prop :=
  ∃ s : ℝ, Q = linePoint P V s

def unitInclinationSlope (f : ℝ → ℝ → ℝ) (x0 y0 α : ℝ) : ℝ :=
  directionalSlope f x0 y0 α /
    Real.sqrt (Real.cos α ^ 2 + Real.sin α ^ 2)

def C1At (f : ℝ → ℝ → ℝ) (x0 y0 : ℝ) : Prop :=
  DifferentiableAt ℝ (Function.uncurry f) (x0, y0)

theorem gap1 (f : ℝ → ℝ → ℝ) (x0 y0 α : ℝ) :
    rawTangent f x0 y0 α =
      (1,
        (deriv (phi x0 y0 α) x0,
          deriv (psi f x0 y0 α) x0)) := by
  rfl

theorem gap2 (f : ℝ → ℝ → ℝ) (x0 y0 α : ℝ)
    (hC1 : C1At f x0 y0) :
    (1,
        (deriv (phi x0 y0 α) x0,
          deriv (psi f x0 y0 α) x0)) =
      explicitXDirection f x0 y0 α := by
  unfold C1At at hC1
  have hphi : HasDerivAt (phi x0 y0 α) (Real.tan α) x0 := by
    simpa [phi] using
      (hasDerivAt_const x0 y0).add
        (((hasDerivAt_id x0).sub_const x0).mul_const (Real.tan α))
  have hxPath :=
    (hasDerivAt_id x0).hasFDerivAt.prodMk
      (hasDerivAt_const x0 y0).hasFDerivAt
  have hxcomp := hC1.hasFDerivAt.comp x0 hxPath
  have hdx :
      partialX f x0 y0 =
        fderiv ℝ (Function.uncurry f) (x0, y0) (1, 0) := by
    simpa [partialX, Function.comp_def] using hxcomp.hasDerivAt.deriv
  have hyPath :=
    (hasDerivAt_const y0 x0).hasFDerivAt.prodMk
      (hasDerivAt_id y0).hasFDerivAt
  have hycomp := hC1.hasFDerivAt.comp y0 hyPath
  have hdy :
      partialY f x0 y0 =
        fderiv ℝ (Function.uncurry f) (x0, y0) (0, 1) := by
    simpa [partialY, Function.comp_def] using hycomp.hasDerivAt.deriv
  have hC1phi :
      DifferentiableAt ℝ (Function.uncurry f) (x0, phi x0 y0 α x0) := by
    simpa [phi] using hC1
  have hInclinedPath :=
    (hasDerivAt_id x0).hasFDerivAt.prodMk hphi.hasFDerivAt
  have hpcomp := hC1phi.hasFDerivAt.comp x0 hInclinedPath
  have hp :
      deriv (psi f x0 y0 α) x0 =
        fderiv ℝ (Function.uncurry f) (x0, y0) (1, Real.tan α) := by
    simpa [psi, phi, Function.comp_def] using hpcomp.hasDerivAt.deriv
  have hv :
      ((1, Real.tan α) : ℝ × ℝ) =
        (1, 0) + Real.tan α • (0, 1) := by
    ext <;> simp
  have hlin :
      fderiv ℝ (Function.uncurry f) (x0, y0) (1, Real.tan α) =
        fderiv ℝ (Function.uncurry f) (x0, y0) (1, 0) +
          Real.tan α *
            fderiv ℝ (Function.uncurry f) (x0, y0) (0, 1) := by
    rw [hv, map_add, map_smul] <;> simp
  have hpsi :
      deriv (psi f x0 y0 α) x0 =
        partialX f x0 y0 + Real.tan α * partialY f x0 y0 := by
    calc
      deriv (psi f x0 y0 α) x0 =
          fderiv ℝ (Function.uncurry f) (x0, y0) (1, Real.tan α) := hp
      _ = fderiv ℝ (Function.uncurry f) (x0, y0) (1, 0) +
          Real.tan α *
            fderiv ℝ (Function.uncurry f) (x0, y0) (0, 1) := hlin
      _ = partialX f x0 y0 + Real.tan α * partialY f x0 y0 := by
        rw [← hdx, ← hdy]
  unfold explicitXDirection
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · exact hphi.deriv
    · exact hpsi

theorem gap3 (f : ℝ → ℝ → ℝ) (x0 y0 α : ℝ)
    (hC1 : C1At f x0 y0) :
    rawTangent f x0 y0 α = explicitXDirection f x0 y0 α := by
  exact (gap1 f x0 y0 α).trans (gap2 f x0 y0 α hC1)

theorem gap4 (f : ℝ → ℝ → ℝ) (x0 y0 α : ℝ) :
    inclinationSlopeX f x0 y0 α =
      deriv (psi f x0 y0 α) x0 /
        Real.sqrt (1 + (deriv (phi x0 y0 α) x0) ^ 2) := by
  rfl

theorem gap5 (f : ℝ → ℝ → ℝ) (x0 y0 α : ℝ)
    (hC1 : C1At f x0 y0) :
    inclinationSlopeX f x0 y0 α =
      (partialX f x0 y0 + Real.tan α * partialY f x0 y0) /
        Real.sqrt (1 + Real.tan α ^ 2) := by
  simpa [inclinationSlopeX, explicitXDirection] using
    congrArg
      (fun V : Point3 => V.2.2 / Real.sqrt (1 + V.2.1 ^ 2))
      (gap3 f x0 y0 α hC1)

theorem gap6 (f : ℝ → ℝ → ℝ) (x0 y0 α : ℝ)
    (hC1 : C1At f x0 y0) (hcos : 0 < Real.cos α) :
    (partialX f x0 y0 + Real.tan α * partialY f x0 y0) /
        Real.sqrt (1 + Real.tan α ^ 2) =
      directionalSlope f x0 y0 α := by
  have hcne : Real.cos α ≠ 0 := ne_of_gt hcos
  have hden :
      1 + Real.tan α ^ 2 = (1 / Real.cos α) ^ 2 := by
    rw [Real.tan_eq_sin_div_cos]
    field_simp [hcne]
    nlinarith [Real.sin_sq_add_cos_sq α]
  have hinvpos : 0 < 1 / Real.cos α := one_div_pos.mpr hcos
  have hroot :
      Real.sqrt (1 + Real.tan α ^ 2) = 1 / Real.cos α := by
    rw [hden, Real.sqrt_sq_eq_abs, abs_of_pos hinvpos]
  unfold directionalSlope
  rw [hroot, Real.tan_eq_sin_div_cos]
  field_simp [hcne] <;> ring

theorem gap7 (f : ℝ → ℝ → ℝ) (x0 y0 α : ℝ)
    (hC1 : C1At f x0 y0) (hcos : 0 < Real.cos α) :
    inclinationSlopeX f x0 y0 α = directionalSlope f x0 y0 α := by
  exact
    (gap5 f x0 y0 α hC1).trans
      (gap6 f x0 y0 α hC1 hcos)

theorem gap8 (f : ℝ → ℝ → ℝ) (x0 y0 α : ℝ) (Q : Point3)
    (hC1 : C1At f x0 y0)
    (hLine :
      OnTangentLine (surfacePoint f x0 y0) (unitDirection f x0 y0 α) Q) :
    (Q.1 - x0) * Real.sin α = (Q.2.1 - y0) * Real.cos α := by
  rcases hLine with ⟨s, rfl⟩
  dsimp [linePoint, surfacePoint, unitDirection]
  ring

theorem gap9 (f : ℝ → ℝ → ℝ) (x0 y0 α : ℝ) (Q : Point3)
    (hC1 : C1At f x0 y0)
    (hLine :
      OnTangentLine (surfacePoint f x0 y0) (unitDirection f x0 y0 α) Q) :
    (Q.2.1 - y0) * directionalSlope f x0 y0 α =
      (Q.2.2 - f x0 y0) * Real.sin α := by
  rcases hLine with ⟨s, rfl⟩
  dsimp [linePoint, surfacePoint, unitDirection]
  ring

theorem gap10 (f : ℝ → ℝ → ℝ) (x0 y0 α : ℝ) (Q : Point3)
    (hC1 : C1At f x0 y0)
    (hLine :
      OnTangentLine (surfacePoint f x0 y0) (unitDirection f x0 y0 α) Q) :
    (Q.1 - x0) * directionalSlope f x0 y0 α =
      (Q.2.2 - f x0 y0) * Real.cos α := by
  rcases hLine with ⟨s, rfl⟩
  dsimp [linePoint, surfacePoint, unitDirection]
  ring

theorem gap11 (f : ℝ → ℝ → ℝ) (x0 y0 α : ℝ)
    (hC1 : C1At f x0 y0) :
    unitInclinationSlope f x0 y0 α =
      directionalSlope f x0 y0 α /
        Real.sqrt (Real.cos α ^ 2 + Real.sin α ^ 2) := by
  rfl

theorem gap12 (f : ℝ → ℝ → ℝ) (x0 y0 α : ℝ)
    (hC1 : C1At f x0 y0) :
    directionalSlope f x0 y0 α /
        Real.sqrt (Real.cos α ^ 2 + Real.sin α ^ 2) =
      directionalSlope f x0 y0 α := by
  have hunit : Real.cos α ^ 2 + Real.sin α ^ 2 = 1 := by
    simpa [add_comm] using Real.sin_sq_add_cos_sq α
  rw [hunit]
  simp

theorem gap13 (f : ℝ → ℝ → ℝ) (x0 y0 α : ℝ)
    (hC1 : C1At f x0 y0) :
    unitInclinationSlope f x0 y0 α =
      directionalSlope f x0 y0 α := by
  exact
    (gap11 f x0 y0 α hC1).trans
      (gap12 f x0 y0 α hC1)

end

end ProofGap.Exercise3537
