import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise3613

noncomputable section

def F (x y : ℝ) : ℝ :=
  y ^ 2 - 1 + Real.exp (-(x ^ 2))

def partialX (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun u => g u y) x

def partialY (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun v => g x v) y

def partialXX (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun u => partialX g u y) x

def partialXY (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun v => partialX g x v) y

def partialYY (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun v => partialY g x v) y

def singularPoints : Set (ℝ × ℝ) :=
  {p | F p.1 p.2 = 0 ∧ partialX F p.1 p.2 = 0 ∧
    partialY F p.1 p.2 = 0}

def singularPoint : ℝ × ℝ :=
  (0, 0)

def hessianA : ℝ :=
  partialXX F singularPoint.1 singularPoint.2

def hessianB : ℝ :=
  partialXY F singularPoint.1 singularPoint.2

def hessianC : ℝ :=
  partialYY F singularPoint.1 singularPoint.2

def hessianDiscriminant : ℝ :=
  hessianA * hessianC - hessianB ^ 2

inductive SingularPointType
  | ordinaryDoublePoint
  | other
  deriving DecidableEq

def singularPointType : SingularPointType :=
  if hessianDiscriminant < 0 then
    SingularPointType.ordinaryDoublePoint
  else
    SingularPointType.other

theorem gap1 (x y : ℝ)
    (hCurve : y ^ 2 = 1 - Real.exp (-(x ^ 2))) :
    F x y = 0 := by
  unfold F
  rw [hCurve]
  ring

theorem gap2 :
    ∀ x y : ℝ,
      partialX F x y = -2 * x * Real.exp (-(x ^ 2)) := by
  intro x y
  have hsq : HasDerivAt (fun u : ℝ => u ^ 2) (2 * x) x := by
    simpa [pow_two, two_mul] using
      (hasDerivAt_id x).mul (hasDerivAt_id x)
  have hinner :
      HasDerivAt (fun u : ℝ => -(u ^ 2)) (-2 * x) x := by
    convert hsq.neg using 1 <;> ring
  have hexp :
      HasDerivAt (fun u : ℝ => Real.exp (-(u ^ 2)))
        (Real.exp (-(x ^ 2)) * (-2 * x)) x := by
    simpa only [Function.comp_apply] using
      ((Real.hasDerivAt_exp (-(x ^ 2))).comp x hinner)
  have htotal :
      HasDerivAt (fun u : ℝ => y ^ 2 - 1 + Real.exp (-(u ^ 2)))
        (-2 * x * Real.exp (-(x ^ 2))) x := by
    convert (hasDerivAt_const (x := x) (y ^ 2 - 1)).add hexp using 1 <;> ring
  change deriv (fun u : ℝ => y ^ 2 - 1 + Real.exp (-(u ^ 2))) x =
    -2 * x * Real.exp (-(x ^ 2))
  exact htotal.deriv

theorem gap3 (p : ℝ × ℝ) (hp : p ∈ singularPoints) :
    -2 * p.1 * Real.exp (-(p.1 ^ 2)) = 0 := by
  have hx := hp.2.1
  rw [gap2] at hx
  exact hx

theorem gap4 :
    ∀ x y : ℝ, partialY F x y = 2 * y := by
  intro x y
  have hsq : HasDerivAt (fun v : ℝ => v ^ 2) (2 * y) y := by
    simpa [pow_two, two_mul] using
      (hasDerivAt_id y).mul (hasDerivAt_id y)
  have h :
      HasDerivAt (fun v : ℝ => v ^ 2 - 1 + Real.exp (-(x ^ 2)))
        (2 * y) y := by
    convert (hsq.sub (hasDerivAt_const (x := y) (1 : ℝ))).add
      (hasDerivAt_const (x := y) (Real.exp (-(x ^ 2)))) using 1 <;> ring
  change deriv (fun v : ℝ => v ^ 2 - 1 + Real.exp (-(x ^ 2))) y = 2 * y
  exact h.deriv

theorem gap5 (p : ℝ × ℝ) (hp : p ∈ singularPoints) :
    2 * p.2 = 0 := by
  have hy := hp.2.2
  rw [gap4] at hy
  exact hy

theorem gap6 (p : ℝ × ℝ) (hp : p ∈ singularPoints) :
    p.1 = 0 := by
  have hx := gap3 p hp
  rcases mul_eq_zero.mp hx with hx | hexp
  · rcases mul_eq_zero.mp hx with htwo | hp1
    · norm_num at htwo
    · exact hp1
  · exact (Real.exp_ne_zero _ hexp).elim

theorem gap7 (p : ℝ × ℝ) (hp : p ∈ singularPoints) :
    p.2 = 0 := by
  have hy := gap5 p hp
  rcases mul_eq_zero.mp hy with htwo | hp2
  · norm_num at htwo
  · exact hp2

theorem gap8 :
    singularPoints = {singularPoint} := by
  ext p
  constructor
  · intro hp
    apply Set.mem_singleton_iff.mpr
    apply Prod.ext
    · simpa [singularPoint] using gap6 p hp
    · simpa [singularPoint] using gap7 p hp
  · intro hp
    have hp' : p = singularPoint := by
      simpa using hp
    subst p
    change F 0 0 = 0 ∧ partialX F 0 0 = 0 ∧ partialY F 0 0 = 0
    norm_num [F, gap2, gap4]

theorem gap9 :
    hessianA = partialXX F singularPoint.1 singularPoint.2 := by
  rfl

theorem gap10 :
    partialXX F 0 0 = -2 := by
  have hlin : HasDerivAt (fun u : ℝ => -2 * u) (-2) 0 := by
    convert (hasDerivAt_const (x := (0 : ℝ)) (-2 : ℝ)).mul
      (hasDerivAt_id (0 : ℝ)) using 1 <;> norm_num
  have hsq : HasDerivAt (fun u : ℝ => u ^ 2) 0 0 := by
    simpa [pow_two] using
      (hasDerivAt_id (0 : ℝ)).mul (hasDerivAt_id (0 : ℝ))
  have hinner : HasDerivAt (fun u : ℝ => -(u ^ 2)) 0 0 := by
    convert hsq.neg using 1 <;> norm_num
  have hexp :
      HasDerivAt (fun u : ℝ => Real.exp (-(u ^ 2))) 0 0 := by
    simpa [Function.comp_apply] using
      ((Real.hasDerivAt_exp (-(0 ^ 2))).comp 0 hinner)
  have h :
      HasDerivAt (fun u : ℝ => -2 * u * Real.exp (-(u ^ 2))) (-2) 0 := by
    convert hlin.mul hexp using 1 <;> norm_num
  simpa only [partialXX, gap2] using h.deriv

theorem gap11 :
    ∃ A : ℝ, A = hessianA ∧ A = -2 := by
  have hA : hessianA = -2 := by
    simpa [hessianA, singularPoint] using gap10
  exact ⟨-2, hA.symm, rfl⟩

theorem gap12 :
    hessianB = partialXY F singularPoint.1 singularPoint.2 := by
  rfl

theorem gap13 :
    partialXY F 0 0 = 0 := by
  simp [partialXY, gap2]

theorem gap14 :
    ∃ B : ℝ, B = hessianB ∧ B = 0 := by
  have hB : hessianB = 0 := by
    simpa [hessianB, singularPoint] using gap13
  exact ⟨0, hB.symm, rfl⟩

theorem gap15 :
    hessianC = partialYY F singularPoint.1 singularPoint.2 := by
  rfl

theorem gap16 :
    partialYY F 0 0 = 2 := by
  have h : HasDerivAt (fun v : ℝ => 2 * v) 2 0 := by
    convert (hasDerivAt_const (x := (0 : ℝ)) (2 : ℝ)).mul
      (hasDerivAt_id (0 : ℝ)) using 1 <;> norm_num
  simpa only [partialYY, gap4] using h.deriv

theorem gap17 :
    ∃ C : ℝ, C = hessianC ∧ C = 2 := by
  have hC : hessianC = 2 := by
    simpa [hessianC, singularPoint] using gap16
  exact ⟨2, hC.symm, rfl⟩

theorem gap18 :
    hessianDiscriminant = -4 := by
  have hA : hessianA = -2 := by
    simpa [hessianA, singularPoint] using gap10
  have hB : hessianB = 0 := by
    simpa [hessianB, singularPoint] using gap13
  have hC : hessianC = 2 := by
    simpa [hessianC, singularPoint] using gap16
  norm_num [hessianDiscriminant, hA, hB, hC]

theorem gap19 :
    (-4 : ℝ) < 0 := by
  norm_num

theorem gap20 :
    hessianDiscriminant < 0 := by
  rw [gap18]
  exact gap19

theorem gap21 :
    singularPointType = SingularPointType.ordinaryDoublePoint := by
  simp [singularPointType, gap20]

end

end ProofGap.Exercise3613
