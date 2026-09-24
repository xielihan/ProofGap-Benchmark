import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.FunProp

namespace ProofGap.Exercise3524

noncomputable section

def partial1 (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => f t y z) x

def partial2 (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => f x t z) y

def partial3 (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => f x y t) z

def partial11 (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => partial1 f t y z) x

def partial22 (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => partial2 f x t z) y

def partial33 (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => partial3 f x y t) z

def C2 (f : ℝ → ℝ → ℝ → ℝ) : Prop :=
  Differentiable ℝ (fun p : ℝ × (ℝ × ℝ) => f p.1 p.2.1 p.2.2) ∧
    Differentiable ℝ (fun p : ℝ × (ℝ × ℝ) => partial1 f p.1 p.2.1 p.2.2) ∧
    Differentiable ℝ (fun p : ℝ × (ℝ × ℝ) => partial2 f p.1 p.2.1 p.2.2) ∧
    Differentiable ℝ (fun p : ℝ × (ℝ × ℝ) => partial3 f p.1 p.2.1 p.2.2)

def coordX (ξ η ζ : ℝ) : ℝ := Real.exp ξ

def coordY (ξ η ζ : ℝ) : ℝ := Real.exp η

def coordZ (ξ η ζ : ℝ) : ℝ := Real.exp ζ

def physicalPDE (u : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : Prop :=
  x ^ 2 * partial11 u x y z + y ^ 2 * partial22 u x y z +
      z ^ 2 * partial33 u x y z =
    (x * partial1 u x y z) ^ 2 + (y * partial2 u x y z) ^ 2 +
      (z * partial3 u x y z) ^ 2

def transformedEquation (w : ℝ → ℝ → ℝ → ℝ) (ξ η ζ : ℝ) : Prop :=
  partial11 w ξ η ζ + partial22 w ξ η ζ + partial33 w ξ η ζ =
    (Real.exp (w ξ η ζ) - 1) *
        (partial1 w ξ η ζ ^ 2 + partial2 w ξ η ζ ^ 2 +
          partial3 w ξ η ζ ^ 2) +
      partial1 w ξ η ζ + partial2 w ξ η ζ + partial3 w ξ η ζ

private theorem exp_change_deriv_identities
    (f g : ℝ → ℝ) (a : ℝ)
    (hf : Differentiable ℝ f)
    (hdf : Differentiable ℝ (fun x => deriv f x))
    (hg : Differentiable ℝ g)
    (hdg : Differentiable ℝ (fun x => deriv g x))
    (hcomp : ∀ t, f (Real.exp t) = Real.exp (g t)) :
    Real.exp a * deriv f (Real.exp a) =
        Real.exp (g a) * deriv g a ∧
      Real.exp a ^ 2 * deriv (fun x => deriv f x) (Real.exp a) =
        Real.exp (g a) * deriv g a ^ 2 +
          Real.exp (g a) * deriv (fun x => deriv g x) a -
          Real.exp (g a) * deriv g a := by
  have hfirst : ∀ t,
      Real.exp t * deriv f (Real.exp t) =
        Real.exp (g t) * deriv g t := by
    intro t
    have hleft :
        HasDerivAt (fun s => f (Real.exp s))
          (deriv f (Real.exp t) * Real.exp t) t :=
      ((hf (Real.exp t)).hasDerivAt).comp t (Real.hasDerivAt_exp t)
    have hright :
        HasDerivAt (fun s => Real.exp (g s))
          (Real.exp (g t) * deriv g t) t :=
      (Real.hasDerivAt_exp (g t)).comp t ((hg t).hasDerivAt)
    calc
      Real.exp t * deriv f (Real.exp t) =
          deriv f (Real.exp t) * Real.exp t := by ac_rfl
      _ = deriv (fun s => f (Real.exp s)) t := hleft.deriv.symm
      _ = deriv (fun s => Real.exp (g s)) t := by
        exact congrArg (fun q : ℝ → ℝ => deriv q t) (funext hcomp)
      _ = Real.exp (g t) * deriv g t := hright.deriv
  have hleft2 :
      HasDerivAt (fun t => Real.exp t * deriv f (Real.exp t))
        (Real.exp a * deriv f (Real.exp a) +
          Real.exp a *
            (deriv (fun x => deriv f x) (Real.exp a) * Real.exp a)) a :=
    (Real.hasDerivAt_exp a).mul
      (((hdf (Real.exp a)).hasDerivAt).comp a (Real.hasDerivAt_exp a))
  have hright2 :
      HasDerivAt (fun t => Real.exp (g t) * deriv g t)
        ((Real.exp (g a) * deriv g a) * deriv g a +
          Real.exp (g a) * deriv (fun x => deriv g x) a) a :=
    ((Real.hasDerivAt_exp (g a)).comp a ((hg a).hasDerivAt)).mul
      ((hdg a).hasDerivAt)
  have hd :
      Real.exp a * deriv f (Real.exp a) +
          Real.exp a *
            (deriv (fun x => deriv f x) (Real.exp a) * Real.exp a) =
        (Real.exp (g a) * deriv g a) * deriv g a +
          Real.exp (g a) * deriv (fun x => deriv g x) a := by
    calc
      _ = deriv (fun t => Real.exp t * deriv f (Real.exp t)) a :=
        hleft2.deriv.symm
      _ = deriv (fun t => Real.exp (g t) * deriv g t) a := by
        exact congrArg (fun q : ℝ → ℝ => deriv q a) (funext hfirst)
      _ = _ := hright2.deriv
  constructor
  · exact hfirst a
  · nlinarith [hd, hfirst a]

private theorem slice_differentiableAt_prod
    {F G : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : ℝ → F} {g : ℝ → G} {x : ℝ}
    (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    DifferentiableAt ℝ (fun t => (f t, g t)) x := by
  fun_prop

theorem gap1 (u w : ℝ → ℝ → ℝ → ℝ) (ξ η ζ : ℝ)
    (hu : C2 u) (hw : C2 w)
    (hComp : ∀ a b c,
      u (coordX a b c) (coordY a b c) (coordZ a b c) = Real.exp (w a b c)) :
    partial1 u (coordX ξ η ζ) (coordY ξ η ζ) (coordZ ξ η ζ) =
      deriv Real.exp (w ξ η ζ) * partial1 w ξ η ζ * (1 / coordX ξ η ζ) := by
  have hmapU : Differentiable ℝ
      (fun x : ℝ => (x, (coordY ξ η ζ, coordZ ξ η ζ))) := by
    intro x
    have hx : DifferentiableAt ℝ (fun t : ℝ => t) x := differentiableAt_id
    have hy : DifferentiableAt ℝ (fun _ : ℝ => coordY ξ η ζ) x :=
      differentiableAt_const (c := coordY ξ η ζ)
    have hz : DifferentiableAt ℝ (fun _ : ℝ => coordZ ξ η ζ) x :=
      differentiableAt_const (c := coordZ ξ η ζ)
    exact slice_differentiableAt_prod hx
      (slice_differentiableAt_prod hy hz)
  have hfu : Differentiable ℝ
      (fun x : ℝ => u x (coordY ξ η ζ) (coordZ ξ η ζ)) := by
    intro x
    simpa [Function.comp_def] using
      (hu.1 (x, (coordY ξ η ζ, coordZ ξ η ζ))).comp x (hmapU x)
  have hdfu : Differentiable ℝ
      (fun x : ℝ => deriv (fun t => u t (coordY ξ η ζ) (coordZ ξ η ζ)) x) := by
    intro x
    simpa [Function.comp_def, partial1] using
      (hu.2.1 (x, (coordY ξ η ζ, coordZ ξ η ζ))).comp x (hmapU x)
  have hmapW : Differentiable ℝ (fun a : ℝ => (a, (η, ζ))) := by
    intro a
    have ha : DifferentiableAt ℝ (fun t : ℝ => t) a := differentiableAt_id
    have hb : DifferentiableAt ℝ (fun _ : ℝ => η) a :=
      differentiableAt_const (c := η)
    have hc : DifferentiableAt ℝ (fun _ : ℝ => ζ) a :=
      differentiableAt_const (c := ζ)
    exact slice_differentiableAt_prod ha
      (slice_differentiableAt_prod hb hc)
  have hfw : Differentiable ℝ (fun a : ℝ => w a η ζ) := by
    intro a
    simpa [Function.comp_def] using
      (hw.1 (a, (η, ζ))).comp a (hmapW a)
  have hdfw : Differentiable ℝ
      (fun a : ℝ => deriv (fun t => w t η ζ) a) := by
    intro a
    simpa [Function.comp_def, partial1] using
      (hw.2.1 (a, (η, ζ))).comp a (hmapW a)
  have h := exp_change_deriv_identities
    (f := fun x : ℝ => u x (coordY ξ η ζ) (coordZ ξ η ζ))
    (g := fun a : ℝ => w a η ζ) (a := ξ)
    hfu hdfu hfw hdfw (by
      intro a
      simpa [coordX, coordY, coordZ] using hComp a η ζ)
  have hfirst :
      coordX ξ η ζ *
          partial1 u (coordX ξ η ζ) (coordY ξ η ζ) (coordZ ξ η ζ) =
        Real.exp (w ξ η ζ) * partial1 w ξ η ζ := by
    simpa [coordX, partial1] using h.1
  rw [Real.deriv_exp, ← hfirst]
  field_simp [coordX, Real.exp_ne_zero]

theorem gap2 (w : ℝ → ℝ → ℝ → ℝ) (ξ η ζ : ℝ) :
    deriv Real.exp (w ξ η ζ) * partial1 w ξ η ζ * (1 / coordX ξ η ζ) =
      Real.exp (w ξ η ζ) / coordX ξ η ζ * partial1 w ξ η ζ := by
  rw [Real.deriv_exp]
  simp only [div_eq_mul_inv, one_div]
  ac_rfl

theorem gap3 (u w : ℝ → ℝ → ℝ → ℝ) (ξ η ζ : ℝ)
    (hu : C2 u) (hw : C2 w)
    (hComp : ∀ a b c,
      u (coordX a b c) (coordY a b c) (coordZ a b c) = Real.exp (w a b c)) :
    partial1 u (coordX ξ η ζ) (coordY ξ η ζ) (coordZ ξ η ζ) =
      Real.exp (w ξ η ζ) / coordX ξ η ζ * partial1 w ξ η ζ := by
  calc
    partial1 u (coordX ξ η ζ) (coordY ξ η ζ) (coordZ ξ η ζ) =
        deriv Real.exp (w ξ η ζ) * partial1 w ξ η ζ *
          (1 / coordX ξ η ζ) := gap1 u w ξ η ζ hu hw hComp
    _ = Real.exp (w ξ η ζ) / coordX ξ η ζ * partial1 w ξ η ζ :=
      gap2 w ξ η ζ

theorem gap4 (u w : ℝ → ℝ → ℝ → ℝ) (ξ η ζ : ℝ)
    (hu : C2 u) (hw : C2 w)
    (hComp : ∀ a b c,
      u (coordX a b c) (coordY a b c) (coordZ a b c) = Real.exp (w a b c)) :
    coordX ξ η ζ *
        partial1 u (coordX ξ η ζ) (coordY ξ η ζ) (coordZ ξ η ζ) =
      Real.exp (w ξ η ζ) * partial1 w ξ η ζ := by
  calc
    coordX ξ η ζ *
        partial1 u (coordX ξ η ζ) (coordY ξ η ζ) (coordZ ξ η ζ) =
      coordX ξ η ζ *
        (Real.exp (w ξ η ζ) / coordX ξ η ζ * partial1 w ξ η ζ) := by
          rw [gap3 u w ξ η ζ hu hw hComp]
    _ = Real.exp (w ξ η ζ) * partial1 w ξ η ζ := by
      field_simp [coordX, Real.exp_ne_zero]

theorem gap5 (u w : ℝ → ℝ → ℝ → ℝ) (ξ η ζ : ℝ)
    (hu : C2 u) (hw : C2 w)
    (hComp : ∀ a b c,
      u (coordX a b c) (coordY a b c) (coordZ a b c) = Real.exp (w a b c)) :
    coordY ξ η ζ *
        partial2 u (coordX ξ η ζ) (coordY ξ η ζ) (coordZ ξ η ζ) =
      Real.exp (w ξ η ζ) * partial2 w ξ η ζ := by
  have hmapU : Differentiable ℝ
      (fun y : ℝ => (coordX ξ η ζ, (y, coordZ ξ η ζ))) := by
    intro y
    have hx : DifferentiableAt ℝ (fun _ : ℝ => coordX ξ η ζ) y :=
      differentiableAt_const (c := coordX ξ η ζ)
    have hy : DifferentiableAt ℝ (fun t : ℝ => t) y := differentiableAt_id
    have hz : DifferentiableAt ℝ (fun _ : ℝ => coordZ ξ η ζ) y :=
      differentiableAt_const (c := coordZ ξ η ζ)
    exact slice_differentiableAt_prod hx
      (slice_differentiableAt_prod hy hz)
  have hfu : Differentiable ℝ
      (fun y : ℝ => u (coordX ξ η ζ) y (coordZ ξ η ζ)) := by
    intro y
    simpa [Function.comp_def] using
      (hu.1 (coordX ξ η ζ, (y, coordZ ξ η ζ))).comp y (hmapU y)
  have hdfu : Differentiable ℝ
      (fun y : ℝ => deriv (fun t => u (coordX ξ η ζ) t (coordZ ξ η ζ)) y) := by
    intro y
    simpa [Function.comp_def, partial2] using
      (hu.2.2.1 (coordX ξ η ζ, (y, coordZ ξ η ζ))).comp y (hmapU y)
  have hmapW : Differentiable ℝ (fun b : ℝ => (ξ, (b, ζ))) := by
    intro b
    have ha : DifferentiableAt ℝ (fun _ : ℝ => ξ) b :=
      differentiableAt_const (c := ξ)
    have hb : DifferentiableAt ℝ (fun t : ℝ => t) b := differentiableAt_id
    have hc : DifferentiableAt ℝ (fun _ : ℝ => ζ) b :=
      differentiableAt_const (c := ζ)
    exact slice_differentiableAt_prod ha
      (slice_differentiableAt_prod hb hc)
  have hfw : Differentiable ℝ (fun b : ℝ => w ξ b ζ) := by
    intro b
    simpa [Function.comp_def] using
      (hw.1 (ξ, (b, ζ))).comp b (hmapW b)
  have hdfw : Differentiable ℝ
      (fun b : ℝ => deriv (fun t => w ξ t ζ) b) := by
    intro b
    simpa [Function.comp_def, partial2] using
      (hw.2.2.1 (ξ, (b, ζ))).comp b (hmapW b)
  have h := exp_change_deriv_identities
    (f := fun y : ℝ => u (coordX ξ η ζ) y (coordZ ξ η ζ))
    (g := fun b : ℝ => w ξ b ζ) (a := η)
    hfu hdfu hfw hdfw (by
      intro b
      simpa [coordX, coordY, coordZ] using hComp ξ b ζ)
  simpa [coordY, partial2] using h.1

theorem gap6 (u w : ℝ → ℝ → ℝ → ℝ) (ξ η ζ : ℝ)
    (hu : C2 u) (hw : C2 w)
    (hComp : ∀ a b c,
      u (coordX a b c) (coordY a b c) (coordZ a b c) = Real.exp (w a b c)) :
    coordZ ξ η ζ *
        partial3 u (coordX ξ η ζ) (coordY ξ η ζ) (coordZ ξ η ζ) =
      Real.exp (w ξ η ζ) * partial3 w ξ η ζ := by
  have hmapU : Differentiable ℝ
      (fun z : ℝ => (coordX ξ η ζ, (coordY ξ η ζ, z))) := by
    intro z
    have hx : DifferentiableAt ℝ (fun _ : ℝ => coordX ξ η ζ) z :=
      differentiableAt_const (c := coordX ξ η ζ)
    have hy : DifferentiableAt ℝ (fun _ : ℝ => coordY ξ η ζ) z :=
      differentiableAt_const (c := coordY ξ η ζ)
    have hz : DifferentiableAt ℝ (fun t : ℝ => t) z := differentiableAt_id
    exact slice_differentiableAt_prod hx
      (slice_differentiableAt_prod hy hz)
  have hfu : Differentiable ℝ
      (fun z : ℝ => u (coordX ξ η ζ) (coordY ξ η ζ) z) := by
    intro z
    simpa [Function.comp_def] using
      (hu.1 (coordX ξ η ζ, (coordY ξ η ζ, z))).comp z (hmapU z)
  have hdfu : Differentiable ℝ
      (fun z : ℝ => deriv (fun t => u (coordX ξ η ζ) (coordY ξ η ζ) t) z) := by
    intro z
    simpa [Function.comp_def, partial3] using
      (hu.2.2.2 (coordX ξ η ζ, (coordY ξ η ζ, z))).comp z (hmapU z)
  have hmapW : Differentiable ℝ (fun c : ℝ => (ξ, (η, c))) := by
    intro c
    have ha : DifferentiableAt ℝ (fun _ : ℝ => ξ) c :=
      differentiableAt_const (c := ξ)
    have hb : DifferentiableAt ℝ (fun _ : ℝ => η) c :=
      differentiableAt_const (c := η)
    have hc : DifferentiableAt ℝ (fun t : ℝ => t) c := differentiableAt_id
    exact slice_differentiableAt_prod ha
      (slice_differentiableAt_prod hb hc)
  have hfw : Differentiable ℝ (fun c : ℝ => w ξ η c) := by
    intro c
    simpa [Function.comp_def] using
      (hw.1 (ξ, (η, c))).comp c (hmapW c)
  have hdfw : Differentiable ℝ
      (fun c : ℝ => deriv (fun t => w ξ η t) c) := by
    intro c
    simpa [Function.comp_def, partial3] using
      (hw.2.2.2 (ξ, (η, c))).comp c (hmapW c)
  have h := exp_change_deriv_identities
    (f := fun z : ℝ => u (coordX ξ η ζ) (coordY ξ η ζ) z)
    (g := fun c : ℝ => w ξ η c) (a := ζ)
    hfu hdfu hfw hdfw (by
      intro c
      simpa [coordX, coordY, coordZ] using hComp ξ η c)
  simpa [coordZ, partial3] using h.1

theorem gap7 (u w : ℝ → ℝ → ℝ → ℝ) (ξ η ζ : ℝ)
    (hu : C2 u) (hw : C2 w)
    (hComp : ∀ a b c,
      u (coordX a b c) (coordY a b c) (coordZ a b c) = Real.exp (w a b c)) :
    coordX ξ η ζ ^ 2 *
        partial11 u (coordX ξ η ζ) (coordY ξ η ζ) (coordZ ξ η ζ) =
      Real.exp (w ξ η ζ) * partial1 w ξ η ζ ^ 2 +
        Real.exp (w ξ η ζ) * partial11 w ξ η ζ -
        Real.exp (w ξ η ζ) * partial1 w ξ η ζ := by
  have hmapU : Differentiable ℝ
      (fun x : ℝ => (x, (coordY ξ η ζ, coordZ ξ η ζ))) := by
    intro x
    have hx : DifferentiableAt ℝ (fun t : ℝ => t) x := differentiableAt_id
    have hy : DifferentiableAt ℝ (fun _ : ℝ => coordY ξ η ζ) x :=
      differentiableAt_const (c := coordY ξ η ζ)
    have hz : DifferentiableAt ℝ (fun _ : ℝ => coordZ ξ η ζ) x :=
      differentiableAt_const (c := coordZ ξ η ζ)
    exact slice_differentiableAt_prod hx
      (slice_differentiableAt_prod hy hz)
  have hfu : Differentiable ℝ
      (fun x : ℝ => u x (coordY ξ η ζ) (coordZ ξ η ζ)) := by
    intro x
    simpa [Function.comp_def] using
      (hu.1 (x, (coordY ξ η ζ, coordZ ξ η ζ))).comp x (hmapU x)
  have hdfu : Differentiable ℝ
      (fun x : ℝ => deriv (fun t => u t (coordY ξ η ζ) (coordZ ξ η ζ)) x) := by
    intro x
    simpa [Function.comp_def, partial1] using
      (hu.2.1 (x, (coordY ξ η ζ, coordZ ξ η ζ))).comp x (hmapU x)
  have hmapW : Differentiable ℝ (fun a : ℝ => (a, (η, ζ))) := by
    intro a
    have ha : DifferentiableAt ℝ (fun t : ℝ => t) a := differentiableAt_id
    have hb : DifferentiableAt ℝ (fun _ : ℝ => η) a :=
      differentiableAt_const (c := η)
    have hc : DifferentiableAt ℝ (fun _ : ℝ => ζ) a :=
      differentiableAt_const (c := ζ)
    exact slice_differentiableAt_prod ha
      (slice_differentiableAt_prod hb hc)
  have hfw : Differentiable ℝ (fun a : ℝ => w a η ζ) := by
    intro a
    simpa [Function.comp_def] using
      (hw.1 (a, (η, ζ))).comp a (hmapW a)
  have hdfw : Differentiable ℝ
      (fun a : ℝ => deriv (fun t => w t η ζ) a) := by
    intro a
    simpa [Function.comp_def, partial1] using
      (hw.2.1 (a, (η, ζ))).comp a (hmapW a)
  have h := exp_change_deriv_identities
    (f := fun x : ℝ => u x (coordY ξ η ζ) (coordZ ξ η ζ))
    (g := fun a : ℝ => w a η ζ) (a := ξ)
    hfu hdfu hfw hdfw (by
      intro a
      simpa [coordX, coordY, coordZ] using hComp a η ζ)
  simpa [coordX, partial1, partial11] using h.2

theorem gap8 (u w : ℝ → ℝ → ℝ → ℝ) (ξ η ζ : ℝ)
    (hu : C2 u) (hw : C2 w)
    (hComp : ∀ a b c,
      u (coordX a b c) (coordY a b c) (coordZ a b c) = Real.exp (w a b c)) :
    coordY ξ η ζ ^ 2 *
        partial22 u (coordX ξ η ζ) (coordY ξ η ζ) (coordZ ξ η ζ) =
      Real.exp (w ξ η ζ) * partial2 w ξ η ζ ^ 2 +
        Real.exp (w ξ η ζ) * partial22 w ξ η ζ -
        Real.exp (w ξ η ζ) * partial2 w ξ η ζ := by
  have hmapU : Differentiable ℝ
      (fun y : ℝ => (coordX ξ η ζ, (y, coordZ ξ η ζ))) := by
    intro y
    have hx : DifferentiableAt ℝ (fun _ : ℝ => coordX ξ η ζ) y :=
      differentiableAt_const (c := coordX ξ η ζ)
    have hy : DifferentiableAt ℝ (fun t : ℝ => t) y := differentiableAt_id
    have hz : DifferentiableAt ℝ (fun _ : ℝ => coordZ ξ η ζ) y :=
      differentiableAt_const (c := coordZ ξ η ζ)
    exact slice_differentiableAt_prod hx
      (slice_differentiableAt_prod hy hz)
  have hfu : Differentiable ℝ
      (fun y : ℝ => u (coordX ξ η ζ) y (coordZ ξ η ζ)) := by
    intro y
    simpa [Function.comp_def] using
      (hu.1 (coordX ξ η ζ, (y, coordZ ξ η ζ))).comp y (hmapU y)
  have hdfu : Differentiable ℝ
      (fun y : ℝ => deriv (fun t => u (coordX ξ η ζ) t (coordZ ξ η ζ)) y) := by
    intro y
    simpa [Function.comp_def, partial2] using
      (hu.2.2.1 (coordX ξ η ζ, (y, coordZ ξ η ζ))).comp y (hmapU y)
  have hmapW : Differentiable ℝ (fun b : ℝ => (ξ, (b, ζ))) := by
    intro b
    have ha : DifferentiableAt ℝ (fun _ : ℝ => ξ) b :=
      differentiableAt_const (c := ξ)
    have hb : DifferentiableAt ℝ (fun t : ℝ => t) b := differentiableAt_id
    have hc : DifferentiableAt ℝ (fun _ : ℝ => ζ) b :=
      differentiableAt_const (c := ζ)
    exact slice_differentiableAt_prod ha
      (slice_differentiableAt_prod hb hc)
  have hfw : Differentiable ℝ (fun b : ℝ => w ξ b ζ) := by
    intro b
    simpa [Function.comp_def] using
      (hw.1 (ξ, (b, ζ))).comp b (hmapW b)
  have hdfw : Differentiable ℝ
      (fun b : ℝ => deriv (fun t => w ξ t ζ) b) := by
    intro b
    simpa [Function.comp_def, partial2] using
      (hw.2.2.1 (ξ, (b, ζ))).comp b (hmapW b)
  have h := exp_change_deriv_identities
    (f := fun y : ℝ => u (coordX ξ η ζ) y (coordZ ξ η ζ))
    (g := fun b : ℝ => w ξ b ζ) (a := η)
    hfu hdfu hfw hdfw (by
      intro b
      simpa [coordX, coordY, coordZ] using hComp ξ b ζ)
  simpa [coordY, partial2, partial22] using h.2

theorem gap9 (u w : ℝ → ℝ → ℝ → ℝ) (ξ η ζ : ℝ)
    (hu : C2 u) (hw : C2 w)
    (hComp : ∀ a b c,
      u (coordX a b c) (coordY a b c) (coordZ a b c) = Real.exp (w a b c)) :
    coordZ ξ η ζ ^ 2 *
        partial33 u (coordX ξ η ζ) (coordY ξ η ζ) (coordZ ξ η ζ) =
      Real.exp (w ξ η ζ) * partial3 w ξ η ζ ^ 2 +
        Real.exp (w ξ η ζ) * partial33 w ξ η ζ -
        Real.exp (w ξ η ζ) * partial3 w ξ η ζ := by
  have hmapU : Differentiable ℝ
      (fun z : ℝ => (coordX ξ η ζ, (coordY ξ η ζ, z))) := by
    intro z
    have hx : DifferentiableAt ℝ (fun _ : ℝ => coordX ξ η ζ) z :=
      differentiableAt_const (c := coordX ξ η ζ)
    have hy : DifferentiableAt ℝ (fun _ : ℝ => coordY ξ η ζ) z :=
      differentiableAt_const (c := coordY ξ η ζ)
    have hz : DifferentiableAt ℝ (fun t : ℝ => t) z := differentiableAt_id
    exact slice_differentiableAt_prod hx
      (slice_differentiableAt_prod hy hz)
  have hfu : Differentiable ℝ
      (fun z : ℝ => u (coordX ξ η ζ) (coordY ξ η ζ) z) := by
    intro z
    simpa [Function.comp_def] using
      (hu.1 (coordX ξ η ζ, (coordY ξ η ζ, z))).comp z (hmapU z)
  have hdfu : Differentiable ℝ
      (fun z : ℝ => deriv (fun t => u (coordX ξ η ζ) (coordY ξ η ζ) t) z) := by
    intro z
    simpa [Function.comp_def, partial3] using
      (hu.2.2.2 (coordX ξ η ζ, (coordY ξ η ζ, z))).comp z (hmapU z)
  have hmapW : Differentiable ℝ (fun c : ℝ => (ξ, (η, c))) := by
    intro c
    have ha : DifferentiableAt ℝ (fun _ : ℝ => ξ) c :=
      differentiableAt_const (c := ξ)
    have hb : DifferentiableAt ℝ (fun _ : ℝ => η) c :=
      differentiableAt_const (c := η)
    have hc : DifferentiableAt ℝ (fun t : ℝ => t) c := differentiableAt_id
    exact slice_differentiableAt_prod ha
      (slice_differentiableAt_prod hb hc)
  have hfw : Differentiable ℝ (fun c : ℝ => w ξ η c) := by
    intro c
    simpa [Function.comp_def] using
      (hw.1 (ξ, (η, c))).comp c (hmapW c)
  have hdfw : Differentiable ℝ
      (fun c : ℝ => deriv (fun t => w ξ η t) c) := by
    intro c
    simpa [Function.comp_def, partial3] using
      (hw.2.2.2 (ξ, (η, c))).comp c (hmapW c)
  have h := exp_change_deriv_identities
    (f := fun z : ℝ => u (coordX ξ η ζ) (coordY ξ η ζ) z)
    (g := fun c : ℝ => w ξ η c) (a := ζ)
    hfu hdfu hfw hdfw (by
      intro c
      simpa [coordX, coordY, coordZ] using hComp ξ η c)
  simpa [coordZ, partial3, partial33] using h.2

theorem gap10 (u w : ℝ → ℝ → ℝ → ℝ) (ξ η ζ : ℝ)
    (hu : C2 u) (hw : C2 w)
    (hComp : ∀ a b c,
      u (coordX a b c) (coordY a b c) (coordZ a b c) = Real.exp (w a b c))
    (hPDE : ∀ x y z, physicalPDE u x y z) :
    transformedEquation w ξ η ζ := by
  have hp := hPDE (coordX ξ η ζ) (coordY ξ η ζ) (coordZ ξ η ζ)
  simp only [physicalPDE] at hp
  rw [gap7 u w ξ η ζ hu hw hComp,
      gap8 u w ξ η ζ hu hw hComp,
      gap9 u w ξ η ζ hu hw hComp,
      gap4 u w ξ η ζ hu hw hComp,
      gap5 u w ξ η ζ hu hw hComp,
      gap6 u w ξ η ζ hu hw hComp] at hp
  have hE : Real.exp (w ξ η ζ) ≠ 0 := Real.exp_ne_zero _
  have hc :
      partial11 w ξ η ζ + partial22 w ξ η ζ + partial33 w ξ η ζ -
          partial1 w ξ η ζ - partial2 w ξ η ζ - partial3 w ξ η ζ =
        (Real.exp (w ξ η ζ) - 1) *
          (partial1 w ξ η ζ ^ 2 + partial2 w ξ η ζ ^ 2 +
            partial3 w ξ η ζ ^ 2) := by
    apply mul_left_cancel₀ hE
    nlinarith [hp]
  unfold transformedEquation
  nlinarith [hc]

end

end ProofGap.Exercise3524
