import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ProofGap.Exercise3521

noncomputable section

def partialX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f t y) x

def partialY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f x t) y

def partialXY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialX f x t) y

def C2 (f : ℝ → ℝ → ℝ) : Prop :=
  Differentiable ℝ (Function.uncurry f) ∧
    Differentiable ℝ (Function.uncurry (partialX f)) ∧
    Differentiable ℝ (Function.uncurry (partialY f))

def gauge (u : ℝ → ℝ → ℝ) (α β x y : ℝ) : ℝ :=
  u x y * Real.exp (α * x + β * y)

def selectedGauge (u : ℝ → ℝ → ℝ) (a b x y : ℝ) : ℝ :=
  u x y * Real.exp (-(b * x + a * y))

def originalExpression (z : ℝ → ℝ → ℝ) (a b c x y : ℝ) : ℝ :=
  partialXY z x y + a * partialX z x y + b * partialY z x y + c * z x y

def reducedExpression (u : ℝ → ℝ → ℝ) (c1 x y : ℝ) : ℝ :=
  partialXY u x y + c1 * u x y

private theorem firstSliceDifferentiableAt
    (f : ℝ → ℝ → ℝ)
    (hf : Differentiable ℝ (Function.uncurry f))
    (x y : ℝ) :
    DifferentiableAt ℝ (fun t : ℝ => f t y) x := by
  have hp : DifferentiableAt ℝ (fun t : ℝ => (t, y)) x :=
    differentiableAt_id.prodMk (differentiableAt_const (c := y))
  simpa [Function.comp_def, Function.uncurry] using
    hf.differentiableAt.comp x hp

private theorem secondSliceDifferentiableAt
    (f : ℝ → ℝ → ℝ)
    (hf : Differentiable ℝ (Function.uncurry f))
    (x y : ℝ) :
    DifferentiableAt ℝ (fun t : ℝ => f x t) y := by
  have hp : DifferentiableAt ℝ (fun t : ℝ => (x, t)) y :=
    (differentiableAt_const (c := x)).prodMk differentiableAt_id
  simpa [Function.comp_def, Function.uncurry] using
    hf.differentiableAt.comp y hp

theorem gap1 (u : ℝ → ℝ → ℝ) (α β : ℝ)
    (hu : C2 u) :
    ∀ x y,
      partialX (fun a b => gauge u α β a b) x y =
        Real.exp (α * x + β * y) * (α * u x y + partialX u x y) := by
  intro x y
  have hux := firstSliceDifferentiableAt u hu.1 x y
  have hlin : HasDerivAt (fun t : ℝ => α * t + β * y) α x := by
    convert ((hasDerivAt_id x).const_mul α).add_const (β * y) using 1 <;> ring
  have he : HasDerivAt Real.exp (Real.exp (α * x + β * y))
      (α * x + β * y) := Real.hasDerivAt_exp _
  have hexp0 := he.comp x hlin
  have hexp : HasDerivAt (fun t : ℝ => Real.exp (α * t + β * y))
      (Real.exp (α * x + β * y) * α) x := by
    simpa only [Function.comp_apply] using hexp0
  have hprod := hux.hasDerivAt.mul hexp
  unfold partialX gauge
  convert hprod.deriv using 1 <;> ring

theorem gap2 (u : ℝ → ℝ → ℝ) (α β : ℝ)
    (hu : C2 u) :
    ∀ x y,
      partialY (fun a b => gauge u α β a b) x y =
        Real.exp (α * x + β * y) * (β * u x y + partialY u x y) := by
  intro x y
  have huy := secondSliceDifferentiableAt u hu.1 x y
  have hlin : HasDerivAt (fun t : ℝ => α * x + β * t) β y := by
    convert ((hasDerivAt_id y).const_mul β).const_add (α * x) using 1 <;> ring
  have he : HasDerivAt Real.exp (Real.exp (α * x + β * y))
      (α * x + β * y) := Real.hasDerivAt_exp _
  have hexp0 := he.comp y hlin
  have hexp : HasDerivAt (fun t : ℝ => Real.exp (α * x + β * t))
      (Real.exp (α * x + β * y) * β) y := by
    simpa only [Function.comp_apply] using hexp0
  have hprod := huy.hasDerivAt.mul hexp
  unfold partialY gauge
  convert hprod.deriv using 1 <;> ring

theorem gap3 (u : ℝ → ℝ → ℝ) (α β : ℝ)
    (hu : C2 u) :
    ∀ x y,
      partialXY (fun a b => gauge u α β a b) x y =
        Real.exp (α * x + β * y) *
          (α * β * u x y + β * partialX u x y + α * partialY u x y +
            partialXY u x y) := by
  intro x y
  unfold partialXY
  rw [show
    (fun t => partialX (fun a b => gauge u α β a b) x t) =
      (fun t => Real.exp (α * x + β * t) *
        (α * u x t + partialX u x t)) by
      funext t
      exact gap1 u α β hu x t]
  have huy := secondSliceDifferentiableAt u hu.1 x y
  have hpx := secondSliceDifferentiableAt (partialX u) hu.2.1 x y
  have hlin : HasDerivAt (fun t : ℝ => α * x + β * t) β y := by
    convert ((hasDerivAt_id y).const_mul β).const_add (α * x) using 1 <;> ring
  have he : HasDerivAt Real.exp (Real.exp (α * x + β * y))
      (α * x + β * y) := Real.hasDerivAt_exp _
  have hexp0 := he.comp y hlin
  have hexp : HasDerivAt (fun t : ℝ => Real.exp (α * x + β * t))
      (Real.exp (α * x + β * y) * β) y := by
    simpa only [Function.comp_apply] using hexp0
  have hsum0 := (huy.hasDerivAt.const_mul α).add hpx.hasDerivAt
  have hsum : HasDerivAt
      (fun t : ℝ => α * u x t + partialX u x t)
      (α * partialY u x y + partialXY u x y) y := by
    unfold partialY partialXY
    simpa only [Pi.add_apply] using hsum0
  have hprod := hexp.mul hsum
  convert hprod.deriv using 1 <;> (simp only [partialXY] <;> ring)

theorem gap4 (u : ℝ → ℝ → ℝ) (a b c α β : ℝ)
    (hu : C2 u)
    (hPDE : ∀ x y,
      originalExpression (fun s t => gauge u α β s t) a b c x y = 0) :
    ∀ x y,
      partialXY u x y + (β + a) * partialX u x y +
          (α + b) * partialY u x y +
          (α * β + α * a + b * β + c) * u x y = 0 := by
  intro x y
  have hpde := hPDE x y
  unfold originalExpression at hpde
  rw [gap3 u α β hu x y, gap1 u α β hu x y,
    gap2 u α β hu x y] at hpde
  unfold gauge at hpde
  have hfactor :
      Real.exp (α * x + β * y) *
        (partialXY u x y + (β + a) * partialX u x y +
          (α + b) * partialY u x y +
          (α * β + α * a + b * β + c) * u x y) = 0 := by
    calc
      Real.exp (α * x + β * y) *
          (partialXY u x y + (β + a) * partialX u x y +
            (α + b) * partialY u x y +
            (α * β + α * a + b * β + c) * u x y) =
        Real.exp (α * x + β * y) *
            (α * β * u x y + β * partialX u x y +
              α * partialY u x y + partialXY u x y) +
          a * (Real.exp (α * x + β * y) *
            (α * u x y + partialX u x y)) +
          b * (Real.exp (α * x + β * y) *
            (β * u x y + partialY u x y)) +
          c * (u x y * Real.exp (α * x + β * y)) := by ring
      _ = 0 := hpde
  exact (mul_eq_zero.mp hfactor).resolve_left (Real.exp_ne_zero _)

theorem gap5 (u : ℝ → ℝ → ℝ) (a b c α β : ℝ)
    (hβ : β + a = 0) (hα : α + b = 0)
    (hTransformed : ∀ x y,
      partialXY u x y + (β + a) * partialX u x y +
          (α + b) * partialY u x y +
          (α * β + α * a + b * β + c) * u x y = 0) :
    ∀ x y,
      reducedExpression u (α * β + α * a + b * β + c) x y = 0 := by
  intro x y
  unfold reducedExpression
  simpa [hβ, hα] using hTransformed x y

theorem gap6 (u : ℝ → ℝ → ℝ) (a b c α β c1 : ℝ)
    (hβ : β + a = 0) (hα : α + b = 0)
    (hc1 : c1 = α * β + α * a + b * β + c)
    (hTransformed : ∀ x y,
      partialXY u x y + (β + a) * partialX u x y +
          (α + b) * partialY u x y +
          (α * β + α * a + b * β + c) * u x y = 0) :
    ∀ x y, reducedExpression u c1 x y = 0 := by
  rw [hc1]
  exact gap5 u a b c α β hβ hα hTransformed

theorem gap7 (a : ℝ) :
    ∃ β : ℝ, β = -a := by
  exact ⟨-a, rfl⟩

theorem gap8 (b : ℝ) :
    ∃ α : ℝ, α = -b := by
  exact ⟨-b, rfl⟩

theorem gap9 (u : ℝ → ℝ → ℝ) (a b : ℝ) :
    ∀ x y,
      selectedGauge u a b x y = u x y * Real.exp (-(b * x + a * y)) := by
  intro x y
  rfl

theorem gap10 (u : ℝ → ℝ → ℝ) (a b c : ℝ)
    (hu : C2 u)
    (hPDE : ∀ x y,
      originalExpression (fun s t => selectedGauge u a b s t) a b c x y = 0) :
    ∃ c1 : ℝ, ∀ x y, reducedExpression u c1 x y = 0 := by
  have hsame :
      (fun s t => selectedGauge u a b s t) =
        (fun s t => gauge u (-b) (-a) s t) := by
    funext s t
    unfold selectedGauge gauge
    have hexponent : -(b * s + a * t) = (-b) * s + (-a) * t := by ring
    rw [hexponent]
  have hpde := hPDE
  rw [hsame] at hpde
  have htransformed := gap4 u a b c (-b) (-a) hu hpde
  refine ⟨(-b) * (-a) + (-b) * a + b * (-a) + c, ?_⟩
  exact gap5 u a b c (-b) (-a) (by ring) (by ring) htransformed

theorem gap11 (u : ℝ → ℝ → ℝ) (a b c : ℝ)
    (hu : C2 u) :
    ∃ α β c1 : ℝ,
      α = -b ∧ β = -a ∧ c1 = c - a * b ∧
      (∀ x y,
        originalExpression (fun s t => gauge u α β s t) a b c x y = 0 →
          reducedExpression u c1 x y = 0) := by
  refine ⟨-b, -a, c - a * b, rfl, rfl, by ring, ?_⟩
  intro x y hpde
  unfold originalExpression at hpde
  rw [gap3 u (-b) (-a) hu x y, gap1 u (-b) (-a) hu x y,
    gap2 u (-b) (-a) hu x y] at hpde
  unfold gauge at hpde
  have hfactor :
      Real.exp ((-b) * x + (-a) * y) *
        (partialXY u x y + (c - a * b) * u x y) = 0 := by
    calc
      Real.exp ((-b) * x + (-a) * y) *
          (partialXY u x y + (c - a * b) * u x y) =
        Real.exp ((-b) * x + (-a) * y) *
            ((-b) * (-a) * u x y + (-a) * partialX u x y +
              (-b) * partialY u x y + partialXY u x y) +
          a * (Real.exp ((-b) * x + (-a) * y) *
            ((-b) * u x y + partialX u x y)) +
          b * (Real.exp ((-b) * x + (-a) * y) *
            ((-a) * u x y + partialY u x y)) +
          c * (u x y * Real.exp ((-b) * x + (-a) * y)) := by ring
      _ = 0 := hpde
  unfold reducedExpression
  exact (mul_eq_zero.mp hfactor).resolve_left (Real.exp_ne_zero _)

end

end ProofGap.Exercise3521
