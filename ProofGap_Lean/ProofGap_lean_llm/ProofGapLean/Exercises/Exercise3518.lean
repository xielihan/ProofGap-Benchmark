import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Prod

namespace ProofGap.Exercise3518

noncomputable section

def partialX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f t y) x

def partialY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f x t) y

def partialXX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialX f t y) x

def partialYY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialY f x t) y

def C2 (f : ℝ → ℝ → ℝ) : Prop :=
  Differentiable ℝ (Function.uncurry f) ∧
    Differentiable ℝ (Function.uncurry (partialX f)) ∧
    Differentiable ℝ (Function.uncurry (partialY f))

def coordX (u v : ℝ) : ℝ := Real.sin u

def coordY (u v : ℝ) : ℝ := Real.sin v

def physicalPDE (z : ℝ → ℝ → ℝ) (x y : ℝ) : Prop :=
  (1 - x ^ 2) * partialXX z x y + (1 - y ^ 2) * partialYY z x y =
    x * partialX z x y + y * partialY z x y

def transformedPDE (w : ℝ → ℝ → ℝ) (u v : ℝ) : Prop :=
  partialXX w u v + partialYY w u v +
    partialX w u v ^ 2 + partialY w u v ^ 2 = 0

private theorem sectionX_differentiableAt
    (f : ℝ → ℝ → ℝ)
    (hf : Differentiable ℝ (Function.uncurry f))
    (x y : ℝ) :
    DifferentiableAt ℝ (fun t : ℝ => f t y) x := by
  have hid : DifferentiableAt ℝ (fun t : ℝ => t) x :=
    differentiableAt_id
  have hconst : DifferentiableAt ℝ (fun _ : ℝ => y) x :=
    differentiableAt_const (c := y)
  rcases hid with ⟨fid, hfid⟩
  rcases hconst with ⟨fconst, hfconst⟩
  have hpair : DifferentiableAt ℝ (fun t : ℝ => (t, y)) x :=
    (hfid.prodMk hfconst).differentiableAt
  simpa [Function.uncurry, Function.comp_def] using
    hf.differentiableAt.comp x hpair

private theorem sectionY_differentiableAt
    (f : ℝ → ℝ → ℝ)
    (hf : Differentiable ℝ (Function.uncurry f))
    (x y : ℝ) :
    DifferentiableAt ℝ (fun t : ℝ => f x t) y := by
  have hconst : DifferentiableAt ℝ (fun _ : ℝ => x) y :=
    differentiableAt_const (c := x)
  have hid : DifferentiableAt ℝ (fun t : ℝ => t) y :=
    differentiableAt_id
  rcases hconst with ⟨fconst, hfconst⟩
  rcases hid with ⟨fid, hfid⟩
  have hpair : DifferentiableAt ℝ (fun t : ℝ => (x, t)) y :=
    (hfconst.prodMk hfid).differentiableAt
  simpa [Function.uncurry, Function.comp_def] using
    hf.differentiableAt.comp y hpair

private theorem chainX_raw
    (z w : ℝ → ℝ → ℝ) (u v : ℝ)
    (hz : C2 z) (hw : C2 w)
    (hComp : ∀ a b,
      z (coordX a b) (coordY a b) = Real.exp (w a b)) :
    partialX z (coordX u v) (coordY u v) * Real.cos u =
      Real.exp (w u v) * partialX w u v := by
  have hz_at :=
    sectionX_differentiableAt z hz.1 (coordX u v) (coordY u v)
  have hleft :
      HasDerivAt
        (fun a : ℝ => z (coordX a v) (coordY a v))
        (partialX z (coordX u v) (coordY u v) * Real.cos u) u := by
    simpa [partialX, coordX, coordY, Function.comp_def] using
      hz_at.hasDerivAt.comp u (Real.hasDerivAt_sin u)
  have hw_at := sectionX_differentiableAt w hw.1 u v
  have hright :
      HasDerivAt (fun a : ℝ => Real.exp (w a v))
        (Real.exp (w u v) * partialX w u v) u := by
    simpa [partialX, Function.comp_def] using
      (Real.hasDerivAt_exp (w u v)).comp u hw_at.hasDerivAt
  calc
    _ = deriv (fun a : ℝ => z (coordX a v) (coordY a v)) u :=
      hleft.deriv.symm
    _ = deriv (fun a : ℝ => Real.exp (w a v)) u := by
      exact congrArg (fun f : ℝ → ℝ => deriv f u)
        (funext fun a => hComp a v)
    _ = _ := hright.deriv

private theorem chainY_raw
    (z w : ℝ → ℝ → ℝ) (u v : ℝ)
    (hz : C2 z) (hw : C2 w)
    (hComp : ∀ a b,
      z (coordX a b) (coordY a b) = Real.exp (w a b)) :
    partialY z (coordX u v) (coordY u v) * Real.cos v =
      Real.exp (w u v) * partialY w u v := by
  have hz_at :=
    sectionY_differentiableAt z hz.1 (coordX u v) (coordY u v)
  have hleft :
      HasDerivAt
        (fun b : ℝ => z (coordX u b) (coordY u b))
        (partialY z (coordX u v) (coordY u v) * Real.cos v) v := by
    simpa [partialY, coordX, coordY, Function.comp_def] using
      hz_at.hasDerivAt.comp v (Real.hasDerivAt_sin v)
  have hw_at := sectionY_differentiableAt w hw.1 u v
  have hright :
      HasDerivAt (fun b : ℝ => Real.exp (w u b))
        (Real.exp (w u v) * partialY w u v) v := by
    simpa [partialY, Function.comp_def] using
      (Real.hasDerivAt_exp (w u v)).comp v hw_at.hasDerivAt
  calc
    _ = deriv (fun b : ℝ => z (coordX u b) (coordY u b)) v :=
      hleft.deriv.symm
    _ = deriv (fun b : ℝ => Real.exp (w u b)) v := by
      exact congrArg (fun f : ℝ → ℝ => deriv f v)
        (funext fun b => hComp u b)
    _ = _ := hright.deriv

theorem gap1 (z w : ℝ → ℝ → ℝ) (u v : ℝ)
    (hcu : Real.cos u ≠ 0)
    (hz : C2 z) (hw : C2 w)
    (hComp : ∀ a b,
      z (coordX a b) (coordY a b) = Real.exp (w a b)) :
    partialX z (coordX u v) (coordY u v) =
      deriv Real.exp (w u v) * partialX w u v * (1 / Real.cos u) := by
  have hraw := chainX_raw z w u v hz hw hComp
  rw [(Real.hasDerivAt_exp (w u v)).deriv]
  field_simp [hcu] <;> nlinarith [hraw]

theorem gap2 (w : ℝ → ℝ → ℝ) (u v : ℝ)
    (hcu : Real.cos u ≠ 0) :
    deriv Real.exp (w u v) * partialX w u v * (1 / Real.cos u) =
      Real.exp (w u v) / Real.cos u * partialX w u v := by
  rw [(Real.hasDerivAt_exp (w u v)).deriv]
  ring

theorem gap3 (z w : ℝ → ℝ → ℝ) (u v : ℝ)
    (hcu : Real.cos u ≠ 0)
    (hz : C2 z) (hw : C2 w)
    (hComp : ∀ a b,
      z (coordX a b) (coordY a b) = Real.exp (w a b)) :
    partialX z (coordX u v) (coordY u v) =
      Real.exp (w u v) / Real.cos u * partialX w u v := by
  calc
    partialX z (coordX u v) (coordY u v) =
        deriv Real.exp (w u v) * partialX w u v *
          (1 / Real.cos u) := gap1 z w u v hcu hz hw hComp
    _ = Real.exp (w u v) / Real.cos u * partialX w u v :=
      gap2 w u v hcu

theorem gap4 (z w : ℝ → ℝ → ℝ) (u v : ℝ)
    (hcv : Real.cos v ≠ 0)
    (hz : C2 z) (hw : C2 w)
    (hComp : ∀ a b,
      z (coordX a b) (coordY a b) = Real.exp (w a b)) :
    partialY z (coordX u v) (coordY u v) =
      Real.exp (w u v) / Real.cos v * partialY w u v := by
  have hraw := chainY_raw z w u v hz hw hComp
  field_simp [hcv] <;> nlinarith [hraw]

theorem gap5 (z w : ℝ → ℝ → ℝ) (u v : ℝ)
    (hcu : Real.cos u ≠ 0)
    (hz : C2 z) (hw : C2 w)
    (hComp : ∀ a b,
      z (coordX a b) (coordY a b) = Real.exp (w a b)) :
    partialXX z (coordX u v) (coordY u v) =
      Real.exp (w u v) / Real.cos u ^ 2 *
        (partialX w u v ^ 2 + partialXX w u v +
          Real.tan u * partialX w u v) := by
  have hzpx :=
    sectionX_differentiableAt (partialX z) hz.2.1
      (coordX u v) (coordY u v)
  have hA :
      HasDerivAt
        (fun a : ℝ => partialX z (coordX a v) (coordY a v))
        (partialXX z (coordX u v) (coordY u v) * Real.cos u) u := by
    simpa [partialXX, coordX, coordY, Function.comp_def] using
      hzpx.hasDerivAt.comp u (Real.hasDerivAt_sin u)
  have hleft :
      HasDerivAt
        (fun a : ℝ =>
          partialX z (coordX a v) (coordY a v) * Real.cos a)
        ((partialXX z (coordX u v) (coordY u v) * Real.cos u) *
            Real.cos u +
          partialX z (coordX u v) (coordY u v) * (-Real.sin u)) u := by
    simpa [coordX, coordY] using hA.mul (Real.hasDerivAt_cos u)
  have hwx := sectionX_differentiableAt w hw.1 u v
  have hexp :
      HasDerivAt (fun a : ℝ => Real.exp (w a v))
        (Real.exp (w u v) * partialX w u v) u := by
    simpa [partialX, Function.comp_def] using
      (Real.hasDerivAt_exp (w u v)).comp u hwx.hasDerivAt
  have hwpx := sectionX_differentiableAt (partialX w) hw.2.1 u v
  have hB :
      HasDerivAt (fun a : ℝ => partialX w a v) (partialXX w u v) u := by
    simpa [partialXX] using hwpx.hasDerivAt
  have hright :
      HasDerivAt
        (fun a : ℝ => Real.exp (w a v) * partialX w a v)
        ((Real.exp (w u v) * partialX w u v) * partialX w u v +
          Real.exp (w u v) * partialXX w u v) u :=
    hexp.mul hB
  have hsecond :
      (partialXX z (coordX u v) (coordY u v) * Real.cos u) *
            Real.cos u +
          partialX z (coordX u v) (coordY u v) * (-Real.sin u) =
        (Real.exp (w u v) * partialX w u v) * partialX w u v +
          Real.exp (w u v) * partialXX w u v := by
    calc
      _ = deriv
          (fun a : ℝ =>
            partialX z (coordX a v) (coordY a v) * Real.cos a) u :=
        hleft.deriv.symm
      _ = deriv
          (fun a : ℝ => Real.exp (w a v) * partialX w a v) u := by
        apply congrArg (fun f : ℝ → ℝ => deriv f u)
        funext a
        exact chainX_raw z w a v hz hw hComp
      _ = _ := hright.deriv
  have hfirst := gap3 z w u v hcu hz hw hComp
  rw [hfirst] at hsecond
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff (pow_ne_zero 2 hcu)).2
  rw [Real.tan_eq_sin_div_cos]
  field_simp [hcu] at hsecond ⊢
  nlinarith [hsecond]

theorem gap6 (z w : ℝ → ℝ → ℝ) (u v : ℝ)
    (hcv : Real.cos v ≠ 0)
    (hz : C2 z) (hw : C2 w)
    (hComp : ∀ a b,
      z (coordX a b) (coordY a b) = Real.exp (w a b)) :
    partialYY z (coordX u v) (coordY u v) =
      Real.exp (w u v) / Real.cos v ^ 2 *
        (partialY w u v ^ 2 + partialYY w u v +
          Real.tan v * partialY w u v) := by
  have hzpy :=
    sectionY_differentiableAt (partialY z) hz.2.2
      (coordX u v) (coordY u v)
  have hA :
      HasDerivAt
        (fun b : ℝ => partialY z (coordX u b) (coordY u b))
        (partialYY z (coordX u v) (coordY u v) * Real.cos v) v := by
    simpa [partialYY, coordX, coordY, Function.comp_def] using
      hzpy.hasDerivAt.comp v (Real.hasDerivAt_sin v)
  have hleft :
      HasDerivAt
        (fun b : ℝ =>
          partialY z (coordX u b) (coordY u b) * Real.cos b)
        ((partialYY z (coordX u v) (coordY u v) * Real.cos v) *
            Real.cos v +
          partialY z (coordX u v) (coordY u v) * (-Real.sin v)) v := by
    simpa [coordX, coordY] using hA.mul (Real.hasDerivAt_cos v)
  have hwy := sectionY_differentiableAt w hw.1 u v
  have hexp :
      HasDerivAt (fun b : ℝ => Real.exp (w u b))
        (Real.exp (w u v) * partialY w u v) v := by
    simpa [partialY, Function.comp_def] using
      (Real.hasDerivAt_exp (w u v)).comp v hwy.hasDerivAt
  have hwpy := sectionY_differentiableAt (partialY w) hw.2.2 u v
  have hB :
      HasDerivAt (fun b : ℝ => partialY w u b) (partialYY w u v) v := by
    simpa [partialYY] using hwpy.hasDerivAt
  have hright :
      HasDerivAt
        (fun b : ℝ => Real.exp (w u b) * partialY w u b)
        ((Real.exp (w u v) * partialY w u v) * partialY w u v +
          Real.exp (w u v) * partialYY w u v) v :=
    hexp.mul hB
  have hsecond :
      (partialYY z (coordX u v) (coordY u v) * Real.cos v) *
            Real.cos v +
          partialY z (coordX u v) (coordY u v) * (-Real.sin v) =
        (Real.exp (w u v) * partialY w u v) * partialY w u v +
          Real.exp (w u v) * partialYY w u v := by
    calc
      _ = deriv
          (fun b : ℝ =>
            partialY z (coordX u b) (coordY u b) * Real.cos b) v :=
        hleft.deriv.symm
      _ = deriv
          (fun b : ℝ => Real.exp (w u b) * partialY w u b) v := by
        apply congrArg (fun f : ℝ → ℝ => deriv f v)
        funext b
        exact chainY_raw z w u b hz hw hComp
      _ = _ := hright.deriv
  have hfirst := gap4 z w u v hcv hz hw hComp
  rw [hfirst] at hsecond
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff (pow_ne_zero 2 hcv)).2
  rw [Real.tan_eq_sin_div_cos]
  field_simp [hcv] at hsecond ⊢
  nlinarith [hsecond]

theorem gap7 :
    ∀ u v, 1 - coordX u v ^ 2 = Real.cos u ^ 2 := by
  intro u v
  simp only [coordX]
  nlinarith [Real.sin_sq_add_cos_sq u]

theorem gap8 :
    ∀ u v, 1 - coordY u v ^ 2 = Real.cos v ^ 2 := by
  intro u v
  simp only [coordY]
  nlinarith [Real.sin_sq_add_cos_sq v]

theorem gap9 (z : ℝ → ℝ → ℝ)
    (hPDE : ∀ x y, physicalPDE z x y) :
    ∀ u v,
      (1 - coordX u v ^ 2) *
          partialXX z (coordX u v) (coordY u v) +
        (1 - coordY u v ^ 2) *
          partialYY z (coordX u v) (coordY u v) =
        coordX u v * partialX z (coordX u v) (coordY u v) +
          coordY u v * partialY z (coordX u v) (coordY u v) := by
  intro u v
  exact hPDE (coordX u v) (coordY u v)

theorem gap10 (z w : ℝ → ℝ → ℝ) (u v : ℝ)
    (hcu : Real.cos u ≠ 0) (hcv : Real.cos v ≠ 0)
    (hz : C2 z) (hw : C2 w)
    (hComp : ∀ a b,
      z (coordX a b) (coordY a b) = Real.exp (w a b))
    (hPDE : ∀ x y, physicalPDE z x y) :
    transformedPDE w u v := by
  have hp := gap9 z hPDE u v
  rw [gap7 u v, gap8 u v,
      gap5 z w u v hcu hz hw hComp,
      gap6 z w u v hcv hz hw hComp,
      gap3 z w u v hcu hz hw hComp,
      gap4 z w u v hcv hz hw hComp] at hp
  simp only [coordX, coordY] at hp
  have hp' :
      Real.exp (w u v) *
          (partialX w u v ^ 2 + partialXX w u v +
            Real.tan u * partialX w u v) +
        Real.exp (w u v) *
          (partialY w u v ^ 2 + partialYY w u v +
            Real.tan v * partialY w u v) =
        Real.sin u *
            (Real.exp (w u v) / Real.cos u * partialX w u v) +
          Real.sin v *
            (Real.exp (w u v) / Real.cos v * partialY w u v) := by
    calc
      _ = Real.cos u ^ 2 *
              (Real.exp (w u v) / Real.cos u ^ 2 *
                (partialX w u v ^ 2 + partialXX w u v +
                  Real.tan u * partialX w u v)) +
            Real.cos v ^ 2 *
              (Real.exp (w u v) / Real.cos v ^ 2 *
                (partialY w u v ^ 2 + partialYY w u v +
                  Real.tan v * partialY w u v)) := by
          field_simp [hcu, hcv] <;> ring
      _ = _ := hp
  have hpTrig :
      Real.exp (w u v) *
          (partialX w u v ^ 2 + partialXX w u v +
            Real.sin u / Real.cos u * partialX w u v) +
        Real.exp (w u v) *
          (partialY w u v ^ 2 + partialYY w u v +
            Real.sin v / Real.cos v * partialY w u v) =
        Real.sin u *
            (Real.exp (w u v) / Real.cos u * partialX w u v) +
          Real.sin v *
            (Real.exp (w u v) / Real.cos v * partialY w u v) := by
    simpa only [Real.tan_eq_sin_div_cos] using hp'
  have hzero :
      Real.exp (w u v) *
        (partialX w u v ^ 2 + partialXX w u v +
          partialY w u v ^ 2 + partialYY w u v) = 0 := by
    calc
      _ =
          (Real.exp (w u v) *
              (partialX w u v ^ 2 + partialXX w u v +
                Real.sin u / Real.cos u * partialX w u v) +
            Real.exp (w u v) *
              (partialY w u v ^ 2 + partialYY w u v +
                Real.sin v / Real.cos v * partialY w u v)) -
            (Real.sin u *
                (Real.exp (w u v) / Real.cos u * partialX w u v) +
              Real.sin v *
                (Real.exp (w u v) / Real.cos v * partialY w u v)) := by
          ring
      _ = 0 := sub_eq_zero.mpr hpTrig
  have hsum :
      partialX w u v ^ 2 + partialXX w u v +
          partialY w u v ^ 2 + partialYY w u v = 0 :=
    (mul_eq_zero.mp hzero).resolve_left (ne_of_gt (Real.exp_pos (w u v)))
  unfold transformedPDE
  nlinarith [hsum]

end

end ProofGap.Exercise3518
