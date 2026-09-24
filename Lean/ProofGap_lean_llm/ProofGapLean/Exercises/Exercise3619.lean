import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3619

noncomputable section

def F (x y : ℝ) : ℝ :=
  y ^ 2 - Real.sin (x ^ 2)

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
    (hCurve : y ^ 2 = Real.sin (x ^ 2)) :
    F x y = 0 := by
  unfold F
  rw [hCurve]
  exact sub_self _

theorem gap2 :
    ∀ x y : ℝ,
      partialX F x y = -2 * x * Real.cos (x ^ 2) := by
  intro x y
  have hpow : HasDerivAt (fun u : ℝ => u ^ 2) (2 * x) x := by
    convert (hasDerivAt_id x).pow 2 using 1 <;> simp [id] <;> ring
  have hsin :
      HasDerivAt (fun u : ℝ => Real.sin (u ^ 2))
        (2 * x * Real.cos (x ^ 2)) x := by
    convert (Real.hasDerivAt_sin (x ^ 2)).comp x hpow using 1 <;> ring
  have hconst : HasDerivAt (fun _ : ℝ => y ^ 2) 0 x :=
    hasDerivAt_const x _
  unfold partialX
  change deriv (fun u : ℝ => y ^ 2 - Real.sin (u ^ 2)) x =
    -2 * x * Real.cos (x ^ 2)
  convert (hconst.sub hsin).deriv using 1 <;> ring

theorem gap3 (p : ℝ × ℝ) (hp : p ∈ singularPoints) :
    -2 * p.1 * Real.cos (p.1 ^ 2) = 0 := by
  change F p.1 p.2 = 0 ∧ partialX F p.1 p.2 = 0 ∧
    partialY F p.1 p.2 = 0 at hp
  have hx := hp.2.1
  rw [gap2] at hx
  exact hx

theorem gap4 :
    ∀ x y : ℝ, partialY F x y = 2 * y := by
  intro x y
  have hpow : HasDerivAt (fun v : ℝ => v ^ 2) (2 * y) y := by
    convert (hasDerivAt_id y).pow 2 using 1 <;> simp [id] <;> ring
  have hconst : HasDerivAt (fun _ : ℝ => Real.sin (x ^ 2)) 0 y :=
    hasDerivAt_const y _
  unfold partialY
  change deriv (fun v : ℝ => v ^ 2 - Real.sin (x ^ 2)) y = 2 * y
  convert (hpow.sub hconst).deriv using 1 <;> ring

theorem gap5 (p : ℝ × ℝ) (hp : p ∈ singularPoints) :
    2 * p.2 = 0 := by
  change F p.1 p.2 = 0 ∧ partialX F p.1 p.2 = 0 ∧
    partialY F p.1 p.2 = 0 at hp
  have hy := hp.2.2
  rw [gap4] at hy
  exact hy

theorem gap6 (p : ℝ × ℝ) (hp : p ∈ singularPoints) :
    p.1 = 0 := by
  have hy : p.2 = 0 := by
    have h := gap5 p hp
    linarith
  have hsin : Real.sin (p.1 ^ 2) = 0 := by
    have hf := hp
    change F p.1 p.2 = 0 ∧ partialX F p.1 p.2 = 0 ∧
      partialY F p.1 p.2 = 0 at hf
    simpa [F, hy] using hf.1
  have hprod : p.1 * Real.cos (p.1 ^ 2) = 0 := by
    have h := gap3 p hp
    linarith
  rcases mul_eq_zero.mp hprod with hx | hcos
  · exact hx
  · have htrig := Real.sin_sq_add_cos_sq (p.1 ^ 2)
    rw [hsin, hcos] at htrig
    norm_num at htrig

theorem gap7 (p : ℝ × ℝ) (hp : p ∈ singularPoints) :
    p.2 = 0 := by
  have h := gap5 p hp
  linarith

theorem gap8 :
    singularPoints = {singularPoint} := by
  ext p
  constructor
  · intro hp
    have heq : p = singularPoint := by
      apply Prod.ext
      · simpa [singularPoint] using gap6 p hp
      · simpa [singularPoint] using gap7 p hp
    simpa [heq]
  · intro hp
    have heq : p = singularPoint := by
      simpa using hp
    subst p
    change F 0 0 = 0 ∧ partialX F 0 0 = 0 ∧ partialY F 0 0 = 0
    rw [gap2, gap4]
    norm_num [F]

theorem gap9 :
    hessianA = partialXX F singularPoint.1 singularPoint.2 := by
  rfl

theorem gap10 :
    partialXX F 0 0 = -2 := by
  unfold partialXX
  have hfun :
      (fun u : ℝ => partialX F u 0) =
        (fun u : ℝ => -2 * u * Real.cos (u ^ 2)) := by
    funext u
    exact gap2 u 0
  rw [hfun]
  have hlin : HasDerivAt (fun u : ℝ => -2 * u) (-2) 0 := by
    convert
      (hasDerivAt_const (0 : ℝ) (-2)).mul (hasDerivAt_id (0 : ℝ))
      using 1 <;> norm_num
  have hpow : HasDerivAt (fun u : ℝ => u ^ 2) 0 0 := by
    convert (hasDerivAt_id (0 : ℝ)).pow 2 using 1 <;> norm_num
  have hcos : HasDerivAt (fun u : ℝ => Real.cos (u ^ 2)) 0 0 := by
    convert (Real.hasDerivAt_cos (0 ^ 2)).comp 0 hpow using 1 <;> norm_num
  convert (hlin.mul hcos).deriv using 1 <;> norm_num

theorem gap11 :
    ∃ A : ℝ, A = hessianA ∧ A = -2 := by
  refine ⟨-2, ?_, rfl⟩
  simpa [hessianA, singularPoint] using gap10.symm

theorem gap12 :
    hessianB = partialXY F singularPoint.1 singularPoint.2 := by
  rfl

theorem gap13 :
    partialXY F 0 0 = 0 := by
  unfold partialXY
  have hfun :
      (fun v : ℝ => partialX F 0 v) = (fun _ : ℝ => 0) := by
    funext v
    rw [gap2]
    norm_num
  rw [hfun]
  simpa using (hasDerivAt_const (0 : ℝ) (0 : ℝ)).deriv

theorem gap14 :
    ∃ B : ℝ, B = hessianB ∧ B = 0 := by
  refine ⟨0, ?_, rfl⟩
  simpa [hessianB, singularPoint] using gap13.symm

theorem gap15 :
    hessianC = partialYY F singularPoint.1 singularPoint.2 := by
  rfl

theorem gap16 :
    partialYY F 0 0 = 2 := by
  unfold partialYY
  have hfun :
      (fun v : ℝ => partialY F 0 v) = (fun v : ℝ => 2 * v) := by
    funext v
    exact gap4 0 v
  rw [hfun]
  have hlin : HasDerivAt (fun v : ℝ => 2 * v) 2 0 := by
    convert
      (hasDerivAt_const (0 : ℝ) 2).mul (hasDerivAt_id (0 : ℝ))
      using 1 <;> norm_num
  exact hlin.deriv

theorem gap17 :
    ∃ C : ℝ, C = hessianC ∧ C = 2 := by
  refine ⟨2, ?_, rfl⟩
  simpa [hessianC, singularPoint] using gap16.symm

theorem gap18 :
    hessianDiscriminant = -4 := by
  have hA : hessianA = -2 := by
    simpa [hessianA, singularPoint] using gap10
  have hB : hessianB = 0 := by
    simpa [hessianB, singularPoint] using gap13
  have hC : hessianC = 2 := by
    simpa [hessianC, singularPoint] using gap16
  unfold hessianDiscriminant
  rw [hA, hB, hC]
  norm_num

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

end ProofGap.Exercise3619
