import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3285

noncomputable section

def partial1 (f : ℝ → ℝ → ℝ → ℝ) (a b c : ℝ) : ℝ :=
  deriv (fun t => f t b c) a

def partial2 (f : ℝ → ℝ → ℝ → ℝ) (a b c : ℝ) : ℝ :=
  deriv (fun t => f a t c) b

def partial3 (f : ℝ → ℝ → ℝ → ℝ) (a b c : ℝ) : ℝ :=
  deriv (fun t => f a b t) c

def partial11 (f : ℝ → ℝ → ℝ → ℝ) (a b c : ℝ) : ℝ :=
  (deriv^[2]) (fun t => f t b c) a

def partial12 (f : ℝ → ℝ → ℝ → ℝ) (a b c : ℝ) : ℝ :=
  deriv (fun t => partial1 f a t c) b

def partial13 (f : ℝ → ℝ → ℝ → ℝ) (a b c : ℝ) : ℝ :=
  deriv (fun t => partial1 f a b t) c

def partial21 (f : ℝ → ℝ → ℝ → ℝ) (a b c : ℝ) : ℝ :=
  deriv (fun t => partial2 f t b c) a

def partial22 (f : ℝ → ℝ → ℝ → ℝ) (a b c : ℝ) : ℝ :=
  (deriv^[2]) (fun t => f a t c) b

def partial23 (f : ℝ → ℝ → ℝ → ℝ) (a b c : ℝ) : ℝ :=
  deriv (fun t => partial2 f a b t) c

def partial31 (f : ℝ → ℝ → ℝ → ℝ) (a b c : ℝ) : ℝ :=
  deriv (fun t => partial3 f t b c) a

def partial32 (f : ℝ → ℝ → ℝ → ℝ) (a b c : ℝ) : ℝ :=
  deriv (fun t => partial3 f a t c) b

def partial33 (f : ℝ → ℝ → ℝ → ℝ) (a b c : ℝ) : ℝ :=
  (deriv^[2]) (fun t => f a b t) c

def transformed (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  f x (x * y) (x * y * z)

def uncurry₃ (f : ℝ → ℝ → ℝ → ℝ) : ℝ × ℝ × ℝ → ℝ :=
  fun p => f p.1 p.2.1 p.2.2

def partialX (g : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => g t y z) x

def partialY (g : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => g x t z) y

def partialZ (g : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => g x y t) z

def partialXX (g : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  (deriv^[2]) (fun t => g t y z) x

def partialYY (g : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  (deriv^[2]) (fun t => g x t z) y

def partialZZ (g : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  (deriv^[2]) (fun t => g x y t) z

def partialXY (g : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => partialX g x t z) y

def partialXZ (g : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => partialX g x y t) z

def partialYZ (g : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => partialY g x y t) z

def firstXFormula (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  partial1 f x (x * y) (x * y * z) +
    y * partial2 f x (x * y) (x * y * z) +
    y * z * partial3 f x (x * y) (x * y * z)

def secondXRaw (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  partial11 f x (x * y) (x * y * z) +
    y * partial12 f x (x * y) (x * y * z) +
    y * z * partial13 f x (x * y) (x * y * z) +
    y * (partial21 f x (x * y) (x * y * z) +
      y * partial22 f x (x * y) (x * y * z) +
      y * z * partial23 f x (x * y) (x * y * z)) +
    y * z * (partial31 f x (x * y) (x * y * z) +
      y * partial32 f x (x * y) (x * y * z) +
      y * z * partial33 f x (x * y) (x * y * z))

def secondXClosed (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  partial11 f x (x * y) (x * y * z) +
    y ^ 2 * partial22 f x (x * y) (x * y * z) +
    y ^ 2 * z ^ 2 * partial33 f x (x * y) (x * y * z) +
    2 * y * partial12 f x (x * y) (x * y * z) +
    2 * y * z * partial13 f x (x * y) (x * y * z) +
    2 * y ^ 2 * z * partial23 f x (x * y) (x * y * z)

def secondYRaw (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  x ^ 2 * partial22 f x (x * y) (x * y * z) +
    x ^ 2 * z * partial23 f x (x * y) (x * y * z) +
    x ^ 2 * z * partial32 f x (x * y) (x * y * z) +
    x ^ 2 * z ^ 2 * partial33 f x (x * y) (x * y * z)

def secondYClosed (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  x ^ 2 * partial22 f x (x * y) (x * y * z) +
    2 * x ^ 2 * z * partial23 f x (x * y) (x * y * z) +
    x ^ 2 * z ^ 2 * partial33 f x (x * y) (x * y * z)

def mixedXYRaw (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  x * partial12 f x (x * y) (x * y * z) +
    x * z * partial13 f x (x * y) (x * y * z) +
    partial2 f x (x * y) (x * y * z) +
    x * y * partial22 f x (x * y) (x * y * z) +
    x * y * z * partial23 f x (x * y) (x * y * z) +
    z * partial3 f x (x * y) (x * y * z) +
    x * y * z * partial32 f x (x * y) (x * y * z) +
    x * y * z ^ 2 * partial33 f x (x * y) (x * y * z)

def mixedXYClosed (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  x * y * partial22 f x (x * y) (x * y * z) +
    x * y * z ^ 2 * partial33 f x (x * y) (x * y * z) +
    x * partial12 f x (x * y) (x * y * z) +
    x * z * partial13 f x (x * y) (x * y * z) +
    2 * x * y * z * partial23 f x (x * y) (x * y * z) +
    partial2 f x (x * y) (x * y * z) +
    z * partial3 f x (x * y) (x * y * z)

private theorem hasDerivAt_prod3
    {u v w : ℝ → ℝ} {du dv dw x : ℝ}
    (hu : HasDerivAt u du x) (hv : HasDerivAt v dv x)
    (hw : HasDerivAt w dw x) :
    HasDerivAt (fun t => (u t, (v t, w t))) (du, (dv, dw)) x := by
  simpa using
    (hu.hasFDerivAt.prodMk
      (hv.hasFDerivAt.prodMk hw.hasFDerivAt)).hasDerivAt

private theorem partial1_eq_fderiv (f : ℝ → ℝ → ℝ → ℝ)
    (hF : Differentiable ℝ (uncurry₃ f)) (a b c : ℝ) :
    partial1 f a b c =
      fderiv ℝ (uncurry₃ f) (a, (b, c)) (1, (0, 0)) := by
  have hp : HasDerivAt (fun t : ℝ => (t, (b, c))) (1, (0, 0)) a := by
    simpa using hasDerivAt_prod3
      (hasDerivAt_id a) (hasDerivAt_const a b) (hasDerivAt_const a c)
  have hcomp := hF.differentiableAt.hasFDerivAt.comp a hp.hasFDerivAt
  simpa [partial1, uncurry₃, Function.comp_def] using hcomp.hasDerivAt.deriv

private theorem partial2_eq_fderiv (f : ℝ → ℝ → ℝ → ℝ)
    (hF : Differentiable ℝ (uncurry₃ f)) (a b c : ℝ) :
    partial2 f a b c =
      fderiv ℝ (uncurry₃ f) (a, (b, c)) (0, (1, 0)) := by
  have hp : HasDerivAt (fun t : ℝ => (a, (t, c))) (0, (1, 0)) b := by
    simpa using hasDerivAt_prod3
      (hasDerivAt_const b a) (hasDerivAt_id b) (hasDerivAt_const b c)
  have hcomp := hF.differentiableAt.hasFDerivAt.comp b hp.hasFDerivAt
  simpa [partial2, uncurry₃, Function.comp_def] using hcomp.hasDerivAt.deriv

private theorem partial3_eq_fderiv (f : ℝ → ℝ → ℝ → ℝ)
    (hF : Differentiable ℝ (uncurry₃ f)) (a b c : ℝ) :
    partial3 f a b c =
      fderiv ℝ (uncurry₃ f) (a, (b, c)) (0, (0, 1)) := by
  have hp : HasDerivAt (fun t : ℝ => (a, (b, t))) (0, (0, 1)) c := by
    simpa using hasDerivAt_prod3
      (hasDerivAt_const c a) (hasDerivAt_const c b) (hasDerivAt_id c)
  have hcomp := hF.differentiableAt.hasFDerivAt.comp c hp.hasFDerivAt
  simpa [partial3, uncurry₃, Function.comp_def] using hcomp.hasDerivAt.deriv

private theorem hasDerivAt_transformedX (f : ℝ → ℝ → ℝ → ℝ)
    (hF : Differentiable ℝ (uncurry₃ f)) (x y z : ℝ) :
    HasDerivAt (fun t => transformed f t y z) (firstXFormula f x y z) x := by
  have hp : HasDerivAt (fun t : ℝ => (t, (t * y, t * y * z)))
      (1, (y, y * z)) x := by
    simpa using hasDerivAt_prod3 (hasDerivAt_id x)
      ((hasDerivAt_id x).mul_const y)
      (((hasDerivAt_id x).mul_const y).mul_const z)
  have hcomp := hF.differentiableAt.hasFDerivAt.comp x hp.hasFDerivAt
  have hraw : HasDerivAt (fun t => transformed f t y z)
      (fderiv ℝ (uncurry₃ f) (x, (x * y, x * y * z)) (1, (y, y * z))) x := by
    simpa [transformed, uncurry₃, Function.comp_def] using hcomp.hasDerivAt
  convert hraw using 1
  unfold firstXFormula
  rw [partial1_eq_fderiv f hF, partial2_eq_fderiv f hF,
    partial3_eq_fderiv f hF]
  have hv : (1, (y, y * z)) =
      ((1, (0, 0)) : ℝ × ℝ × ℝ) +
        y • ((0, (1, 0)) : ℝ × ℝ × ℝ) +
        (y * z) • ((0, (0, 1)) : ℝ × ℝ × ℝ) := by
    ext <;> simp
  rw [hv, map_add, map_add, map_smul, map_smul]
  simp [smul_eq_mul]

private theorem hasDerivAt_transformedY (f : ℝ → ℝ → ℝ → ℝ)
    (hF : Differentiable ℝ (uncurry₃ f)) (x y z : ℝ) :
    HasDerivAt (fun t => transformed f x t z)
      (x * partial2 f x (x * y) (x * y * z) +
        x * z * partial3 f x (x * y) (x * y * z)) y := by
  have hp : HasDerivAt (fun t : ℝ => (x, (x * t, x * t * z)))
      (0, (x, x * z)) y := by
    simpa using hasDerivAt_prod3 (hasDerivAt_const y x)
      ((hasDerivAt_id y).const_mul x)
      (((hasDerivAt_id y).const_mul x).mul_const z)
  have hcomp := hF.differentiableAt.hasFDerivAt.comp y hp.hasFDerivAt
  have hraw : HasDerivAt (fun t => transformed f x t z)
      (fderiv ℝ (uncurry₃ f) (x, (x * y, x * y * z)) (0, (x, x * z))) y := by
    simpa [transformed, uncurry₃, Function.comp_def] using hcomp.hasDerivAt
  convert hraw using 1
  rw [partial2_eq_fderiv f hF, partial3_eq_fderiv f hF]
  have hv : (0, (x, x * z)) =
      x • ((0, (1, 0)) : ℝ × ℝ × ℝ) +
        (x * z) • ((0, (0, 1)) : ℝ × ℝ × ℝ) := by
    ext <;> simp
  rw [hv, map_add, map_smul, map_smul]
  simp [smul_eq_mul]

private theorem hasDerivAt_transformedZ (f : ℝ → ℝ → ℝ → ℝ)
    (hF : Differentiable ℝ (uncurry₃ f)) (x y z : ℝ) :
    HasDerivAt (fun t => transformed f x y t)
      (x * y * partial3 f x (x * y) (x * y * z)) z := by
  have hp : HasDerivAt (fun t : ℝ => (x, (x * y, x * y * t)))
      (0, (0, x * y)) z := by
    simpa using hasDerivAt_prod3 (hasDerivAt_const z x)
      (hasDerivAt_const z (x * y))
      ((hasDerivAt_id z).const_mul (x * y))
  have hcomp := hF.differentiableAt.hasFDerivAt.comp z hp.hasFDerivAt
  have hraw : HasDerivAt (fun t => transformed f x y t)
      (fderiv ℝ (uncurry₃ f) (x, (x * y, x * y * z)) (0, (0, x * y))) z := by
    simpa [transformed, uncurry₃, Function.comp_def] using hcomp.hasDerivAt
  convert hraw using 1
  rw [partial3_eq_fderiv f hF]
  have hv : (0, (0, x * y)) =
      (x * y) • ((0, (0, 1)) : ℝ × ℝ × ℝ) := by
    ext <;> simp
  rw [hv, map_smul]
  simp [smul_eq_mul]

private theorem differentiable_fderiv_of_contDiff_two
    (F : (ℝ × ℝ × ℝ) → ℝ) (hF : ContDiff ℝ 2 F) :
    Differentiable ℝ (fderiv ℝ F) := by
  let E := ℝ × ℝ × ℝ
  have hFam : ContDiff ℝ 2
      (Function.uncurry (fun _ : E => F)) := by
    simpa [E, Function.uncurry] using hF.comp contDiff_snd
  have hFD : ContDiff ℝ 1 (fun x : E => fderiv ℝ F x) := by
    simpa [E] using ContDiff.fderiv hFam contDiff_id (by norm_num)
  exact hFD.differentiable (by norm_num)

private theorem differentiable_uncurry_partial1 (f : ℝ → ℝ → ℝ → ℝ)
    (hf : ContDiff ℝ 2 (uncurry₃ f)) :
    Differentiable ℝ (uncurry₃ (partial1 f)) := by
  have hF : Differentiable ℝ (uncurry₃ f) := hf.differentiable (by decide)
  have hFD : Differentiable ℝ (fderiv ℝ (uncurry₃ f)) :=
    differentiable_fderiv_of_contDiff_two (uncurry₃ f) hf
  have heq : uncurry₃ (partial1 f) =
      fun p => fderiv ℝ (uncurry₃ f) p (1, (0, 0)) := by
    funext p
    simpa [uncurry₃] using partial1_eq_fderiv f hF p.1 p.2.1 p.2.2
  rw [heq]
  exact hFD.clm_apply (differentiable_const _)

private theorem differentiable_uncurry_partial2 (f : ℝ → ℝ → ℝ → ℝ)
    (hf : ContDiff ℝ 2 (uncurry₃ f)) :
    Differentiable ℝ (uncurry₃ (partial2 f)) := by
  have hF : Differentiable ℝ (uncurry₃ f) := hf.differentiable (by decide)
  have hFD : Differentiable ℝ (fderiv ℝ (uncurry₃ f)) :=
    differentiable_fderiv_of_contDiff_two (uncurry₃ f) hf
  have heq : uncurry₃ (partial2 f) =
      fun p => fderiv ℝ (uncurry₃ f) p (0, (1, 0)) := by
    funext p
    simpa [uncurry₃] using partial2_eq_fderiv f hF p.1 p.2.1 p.2.2
  rw [heq]
  exact hFD.clm_apply (differentiable_const _)

private theorem differentiable_uncurry_partial3 (f : ℝ → ℝ → ℝ → ℝ)
    (hf : ContDiff ℝ 2 (uncurry₃ f)) :
    Differentiable ℝ (uncurry₃ (partial3 f)) := by
  have hF : Differentiable ℝ (uncurry₃ f) := hf.differentiable (by decide)
  have hFD : Differentiable ℝ (fderiv ℝ (uncurry₃ f)) :=
    differentiable_fderiv_of_contDiff_two (uncurry₃ f) hf
  have heq : uncurry₃ (partial3 f) =
      fun p => fderiv ℝ (uncurry₃ f) p (0, (0, 1)) := by
    funext p
    simpa [uncurry₃] using partial3_eq_fderiv f hF p.1 p.2.1 p.2.2
  rw [heq]
  exact hFD.clm_apply (differentiable_const _)

private theorem deriv_fderiv_apply_along
    (F : (ℝ × ℝ × ℝ) → ℝ)
    (hFD : Differentiable ℝ (fderiv ℝ F))
    (p : ℝ → (ℝ × ℝ × ℝ)) (x : ℝ) (v : ℝ × ℝ × ℝ)
    (hp : HasDerivAt p v x) (w : ℝ × ℝ × ℝ) :
    deriv (fun t => fderiv ℝ F (p t) w) x =
      fderiv ℝ (fderiv ℝ F) (p x) v w := by
  have hcomp := hFD.differentiableAt.hasFDerivAt.comp x hp.hasFDerivAt
  have happ := hcomp.clm_apply (hasDerivAt_const x w).hasFDerivAt
  simpa [Function.comp_def] using happ.hasDerivAt.deriv

private theorem partial2_partial1_eq (f : ℝ → ℝ → ℝ → ℝ)
    (a b c : ℝ) : partial2 (partial1 f) a b c = partial12 f a b c := by
  rfl

private theorem partial3_partial1_eq (f : ℝ → ℝ → ℝ → ℝ)
    (a b c : ℝ) : partial3 (partial1 f) a b c = partial13 f a b c := by
  rfl

private theorem partial2_partial2_eq (f : ℝ → ℝ → ℝ → ℝ)
    (a b c : ℝ) : partial2 (partial2 f) a b c = partial22 f a b c := by
  rfl

private theorem partial3_partial2_eq (f : ℝ → ℝ → ℝ → ℝ)
    (a b c : ℝ) : partial3 (partial2 f) a b c = partial23 f a b c := by
  rfl

private theorem partial2_partial3_eq (f : ℝ → ℝ → ℝ → ℝ)
    (a b c : ℝ) : partial2 (partial3 f) a b c = partial32 f a b c := by
  rfl

private theorem partial3_partial3_eq (f : ℝ → ℝ → ℝ → ℝ)
    (a b c : ℝ) : partial3 (partial3 f) a b c = partial33 f a b c := by
  rfl

theorem gap1 (f : ℝ → ℝ → ℝ → ℝ)
    (hf : ContDiff ℝ 1 (uncurry₃ f)) (x y z : ℝ) :
    partialX (transformed f) x y z = firstXFormula f x y z := by
  exact (hasDerivAt_transformedX f (hf.differentiable (by norm_num)) x y z).deriv

theorem gap2 (f : ℝ → ℝ → ℝ → ℝ)
    (hf : ContDiff ℝ 1 (uncurry₃ f)) (x y z : ℝ) :
    partialX (transformed f) x y z =
      partial1 f x (x * y) (x * y * z) +
        y * partial2 f x (x * y) (x * y * z) +
        y * z * partial3 f x (x * y) (x * y * z) := by
  simpa [firstXFormula] using gap1 f hf x y z

theorem gap3 (f : ℝ → ℝ → ℝ → ℝ)
    (hf : ContDiff ℝ 1 (uncurry₃ f)) (x y z : ℝ) :
    partialY (transformed f) x y z =
      x * partial2 f x (x * y) (x * y * z) +
        x * z * partial3 f x (x * y) (x * y * z) := by
  exact (hasDerivAt_transformedY f (hf.differentiable (by norm_num)) x y z).deriv

theorem gap4 (f : ℝ → ℝ → ℝ → ℝ)
    (hf : ContDiff ℝ 1 (uncurry₃ f)) (x y z : ℝ) :
    partialZ (transformed f) x y z =
      x * y * partial3 f x (x * y) (x * y * z) := by
  exact (hasDerivAt_transformedZ f (hf.differentiable (by norm_num)) x y z).deriv

theorem gap5 (f : ℝ → ℝ → ℝ → ℝ)
    (hf : ContDiff ℝ 2 (uncurry₃ f)) (x y z : ℝ) :
    partialXX (transformed f) x y z = secondXRaw f x y z := by
  change deriv (fun t => partialX (transformed f) t y z) x = _
  rw [show (fun t => partialX (transformed f) t y z) =
      (fun t => firstXFormula f t y z) by
    funext t
    exact gap1 f (hf.of_le (by norm_num)) t y z]
  have h1 := hasDerivAt_transformedX (partial1 f)
    (differentiable_uncurry_partial1 f hf) x y z
  have h2 := hasDerivAt_transformedX (partial2 f)
    (differentiable_uncurry_partial2 f hf) x y z
  have h3 := hasDerivAt_transformedX (partial3 f)
    (differentiable_uncurry_partial3 f hf) x y z
  have hsum := (h1.add (h2.const_mul y)).add (h3.const_mul (y * z))
  simpa [firstXFormula, secondXRaw, transformed] using hsum.deriv

theorem gap6 (f : ℝ → ℝ → ℝ → ℝ)
    (hf : ContDiff ℝ 2 (uncurry₃ f)) (a b c : ℝ) :
    partial12 f a b c = partial21 f a b c := by
  let F := uncurry₃ f
  let p : ℝ × ℝ × ℝ := (a, (b, c))
  let e1 : ℝ × ℝ × ℝ := (1, (0, 0))
  let e2 : ℝ × ℝ × ℝ := (0, (1, 0))
  have hF : Differentiable ℝ F := hf.differentiable (by decide)
  have hFD : Differentiable ℝ (fderiv ℝ F) :=
    differentiable_fderiv_of_contDiff_two F hf
  have h12 : partial12 f a b c = fderiv ℝ (fderiv ℝ F) p e2 e1 := by
    unfold partial12
    rw [show (fun t => partial1 f a t c) =
        (fun t => fderiv ℝ F (a, (t, c)) e1) by
      funext t
      simpa [F, e1] using partial1_eq_fderiv f hF a t c]
    have hp : HasDerivAt (fun t : ℝ => (a, (t, c))) e2 b := by
      simpa [e2] using hasDerivAt_prod3
        (hasDerivAt_const b a) (hasDerivAt_id b) (hasDerivAt_const b c)
    simpa [p] using deriv_fderiv_apply_along F hFD
      (fun t : ℝ => (a, (t, c))) b e2 hp e1
  have h21 : partial21 f a b c = fderiv ℝ (fderiv ℝ F) p e1 e2 := by
    unfold partial21
    rw [show (fun t => partial2 f t b c) =
        (fun t => fderiv ℝ F (t, (b, c)) e2) by
      funext t
      simpa [F, e2] using partial2_eq_fderiv f hF t b c]
    have hp : HasDerivAt (fun t : ℝ => (t, (b, c))) e1 a := by
      simpa [e1] using hasDerivAt_prod3
        (hasDerivAt_id a) (hasDerivAt_const a b) (hasDerivAt_const a c)
    simpa [p] using deriv_fderiv_apply_along F hFD
      (fun t : ℝ => (t, (b, c))) a e1 hp e2
  rw [h12, h21]
  exact
    (show ContDiffAt ℝ 2 F p from hf.contDiffAt).isSymmSndFDerivAt
      (by norm_num) e2 e1

theorem gap7 (f : ℝ → ℝ → ℝ → ℝ)
    (hf : ContDiff ℝ 2 (uncurry₃ f)) (a b c : ℝ) :
    partial13 f a b c = partial31 f a b c := by
  let F := uncurry₃ f
  let p : ℝ × ℝ × ℝ := (a, (b, c))
  let e1 : ℝ × ℝ × ℝ := (1, (0, 0))
  let e3 : ℝ × ℝ × ℝ := (0, (0, 1))
  have hF : Differentiable ℝ F := hf.differentiable (by decide)
  have hFD : Differentiable ℝ (fderiv ℝ F) :=
    differentiable_fderiv_of_contDiff_two F hf
  have h13 : partial13 f a b c = fderiv ℝ (fderiv ℝ F) p e3 e1 := by
    unfold partial13
    rw [show (fun t => partial1 f a b t) =
        (fun t => fderiv ℝ F (a, (b, t)) e1) by
      funext t
      simpa [F, e1] using partial1_eq_fderiv f hF a b t]
    have hp : HasDerivAt (fun t : ℝ => (a, (b, t))) e3 c := by
      simpa [e3] using hasDerivAt_prod3
        (hasDerivAt_const c a) (hasDerivAt_const c b) (hasDerivAt_id c)
    simpa [p] using deriv_fderiv_apply_along F hFD
      (fun t : ℝ => (a, (b, t))) c e3 hp e1
  have h31 : partial31 f a b c = fderiv ℝ (fderiv ℝ F) p e1 e3 := by
    unfold partial31
    rw [show (fun t => partial3 f t b c) =
        (fun t => fderiv ℝ F (t, (b, c)) e3) by
      funext t
      simpa [F, e3] using partial3_eq_fderiv f hF t b c]
    have hp : HasDerivAt (fun t : ℝ => (t, (b, c))) e1 a := by
      simpa [e1] using hasDerivAt_prod3
        (hasDerivAt_id a) (hasDerivAt_const a b) (hasDerivAt_const a c)
    simpa [p] using deriv_fderiv_apply_along F hFD
      (fun t : ℝ => (t, (b, c))) a e1 hp e3
  rw [h13, h31]
  exact
    (show ContDiffAt ℝ 2 F p from hf.contDiffAt).isSymmSndFDerivAt
      (by norm_num) e3 e1

theorem gap8 (f : ℝ → ℝ → ℝ → ℝ)
    (hf : ContDiff ℝ 2 (uncurry₃ f)) (a b c : ℝ) :
    partial23 f a b c = partial32 f a b c := by
  let F := uncurry₃ f
  let p : ℝ × ℝ × ℝ := (a, (b, c))
  let e2 : ℝ × ℝ × ℝ := (0, (1, 0))
  let e3 : ℝ × ℝ × ℝ := (0, (0, 1))
  have hF : Differentiable ℝ F := hf.differentiable (by decide)
  have hFD : Differentiable ℝ (fderiv ℝ F) :=
    differentiable_fderiv_of_contDiff_two F hf
  have h23 : partial23 f a b c = fderiv ℝ (fderiv ℝ F) p e3 e2 := by
    unfold partial23
    rw [show (fun t => partial2 f a b t) =
        (fun t => fderiv ℝ F (a, (b, t)) e2) by
      funext t
      simpa [F, e2] using partial2_eq_fderiv f hF a b t]
    have hp : HasDerivAt (fun t : ℝ => (a, (b, t))) e3 c := by
      simpa [e3] using hasDerivAt_prod3
        (hasDerivAt_const c a) (hasDerivAt_const c b) (hasDerivAt_id c)
    simpa [p] using deriv_fderiv_apply_along F hFD
      (fun t : ℝ => (a, (b, t))) c e3 hp e2
  have h32 : partial32 f a b c = fderiv ℝ (fderiv ℝ F) p e2 e3 := by
    unfold partial32
    rw [show (fun t => partial3 f a t c) =
        (fun t => fderiv ℝ F (a, (t, c)) e3) by
      funext t
      simpa [F, e3] using partial3_eq_fderiv f hF a t c]
    have hp : HasDerivAt (fun t : ℝ => (a, (t, c))) e2 b := by
      simpa [e2] using hasDerivAt_prod3
        (hasDerivAt_const b a) (hasDerivAt_id b) (hasDerivAt_const b c)
    simpa [p] using deriv_fderiv_apply_along F hFD
      (fun t : ℝ => (a, (t, c))) b e2 hp e3
  rw [h23, h32]
  exact
    (show ContDiffAt ℝ 2 F p from hf.contDiffAt).isSymmSndFDerivAt
      (by norm_num) e3 e2

theorem gap9 (f : ℝ → ℝ → ℝ → ℝ)
    (hf : ContDiff ℝ 2 (uncurry₃ f)) (x y z : ℝ) :
    partialXX (transformed f) x y z = secondXClosed f x y z := by
  rw [gap5 f hf x y z]
  unfold secondXRaw secondXClosed
  rw [← gap6 f hf x (x * y) (x * y * z)]
  rw [← gap7 f hf x (x * y) (x * y * z)]
  rw [← gap8 f hf x (x * y) (x * y * z)]
  ring

theorem gap10 (f : ℝ → ℝ → ℝ → ℝ)
    (hf : ContDiff ℝ 2 (uncurry₃ f)) (x y z : ℝ) :
    partialYY (transformed f) x y z = secondYRaw f x y z := by
  change deriv (fun t => partialY (transformed f) x t z) y = _
  rw [show (fun t => partialY (transformed f) x t z) =
      (fun t => x * transformed (partial2 f) x t z +
        x * z * transformed (partial3 f) x t z) by
    funext t
    simpa [transformed] using gap3 f (hf.of_le (by norm_num)) x t z]
  have h2 := hasDerivAt_transformedY (partial2 f)
    (differentiable_uncurry_partial2 f hf) x y z
  have h3 := hasDerivAt_transformedY (partial3 f)
    (differentiable_uncurry_partial3 f hf) x y z
  have hsum := (h2.const_mul x).add (h3.const_mul (x * z))
  have hd := hsum.deriv
  unfold secondYRaw
  convert hd using 1
  simp only [partial2_partial2_eq, partial3_partial2_eq,
    partial2_partial3_eq, partial3_partial3_eq]
  ring

theorem gap11 (f : ℝ → ℝ → ℝ → ℝ)
    (hf : ContDiff ℝ 2 (uncurry₃ f)) (x y z : ℝ) :
    secondYRaw f x y z = secondYClosed f x y z := by
  unfold secondYRaw secondYClosed
  rw [← gap8 f hf x (x * y) (x * y * z)]
  ring

theorem gap12 (f : ℝ → ℝ → ℝ → ℝ)
    (hf : ContDiff ℝ 2 (uncurry₃ f)) (x y z : ℝ) :
    partialYY (transformed f) x y z = secondYClosed f x y z := by
  rw [gap10 f hf x y z]
  exact gap11 f hf x y z

theorem gap13 (f : ℝ → ℝ → ℝ → ℝ)
    (hf : ContDiff ℝ 2 (uncurry₃ f)) (x y z : ℝ) :
    partialZZ (transformed f) x y z =
      x ^ 2 * y ^ 2 * partial33 f x (x * y) (x * y * z) := by
  change deriv (fun t => partialZ (transformed f) x y t) z = _
  rw [show (fun t => partialZ (transformed f) x y t) =
      (fun t => x * y * transformed (partial3 f) x y t) by
    funext t
    simpa [transformed] using gap4 f (hf.of_le (by norm_num)) x y t]
  have h3 := hasDerivAt_transformedZ (partial3 f)
    (differentiable_uncurry_partial3 f hf) x y z
  have hd := (h3.const_mul (x * y)).deriv
  convert hd using 1
  rw [partial3_partial3_eq]
  ring

theorem gap14 (f : ℝ → ℝ → ℝ → ℝ)
    (hf : ContDiff ℝ 2 (uncurry₃ f)) (x y z : ℝ) :
    partialXY (transformed f) x y z = mixedXYRaw f x y z := by
  change deriv (fun t => partialX (transformed f) x t z) y = _
  rw [show (fun t => partialX (transformed f) x t z) =
      (fun t => firstXFormula f x t z) by
    funext t
    exact gap1 f (hf.of_le (by norm_num)) x t z]
  have h1 := hasDerivAt_transformedY (partial1 f)
    (differentiable_uncurry_partial1 f hf) x y z
  have h2 := hasDerivAt_transformedY (partial2 f)
    (differentiable_uncurry_partial2 f hf) x y z
  have h3 := hasDerivAt_transformedY (partial3 f)
    (differentiable_uncurry_partial3 f hf) x y z
  have hterm2 := (hasDerivAt_id y).mul h2
  have hterm3 := ((hasDerivAt_id y).mul_const z).mul h3
  have hsum := (h1.add hterm2).add hterm3
  have hd := hsum.deriv
  unfold mixedXYRaw
  convert hd using 1
  simp only [partial2_partial1_eq, partial3_partial1_eq,
    partial2_partial2_eq, partial3_partial2_eq,
    partial2_partial3_eq, partial3_partial3_eq]
  simp [firstXFormula, transformed]
  ring

theorem gap15 (f : ℝ → ℝ → ℝ → ℝ)
    (hf : ContDiff ℝ 2 (uncurry₃ f)) (x y z : ℝ) :
    partialXY (transformed f) x y z = mixedXYClosed f x y z := by
  rw [gap14 f hf x y z]
  unfold mixedXYRaw mixedXYClosed
  rw [← gap8 f hf x (x * y) (x * y * z)]
  ring

theorem gap16 (f : ℝ → ℝ → ℝ → ℝ)
    (hf : ContDiff ℝ 2 (uncurry₃ f)) (x y z : ℝ) :
    partialXZ (transformed f) x y z =
      x * y * partial13 f x (x * y) (x * y * z) +
        x * y ^ 2 * partial23 f x (x * y) (x * y * z) +
        x * y ^ 2 * z * partial33 f x (x * y) (x * y * z) +
        y * partial3 f x (x * y) (x * y * z) := by
  change deriv (fun t => partialX (transformed f) x y t) z = _
  rw [show (fun t => partialX (transformed f) x y t) =
      (fun t => firstXFormula f x y t) by
    funext t
    exact gap1 f (hf.of_le (by norm_num)) x y t]
  have h1 := hasDerivAt_transformedZ (partial1 f)
    (differentiable_uncurry_partial1 f hf) x y z
  have h2 := hasDerivAt_transformedZ (partial2 f)
    (differentiable_uncurry_partial2 f hf) x y z
  have h3 := hasDerivAt_transformedZ (partial3 f)
    (differentiable_uncurry_partial3 f hf) x y z
  have hterm2 := h2.const_mul y
  have hterm3 := ((hasDerivAt_id z).const_mul y).mul h3
  have hsum := (h1.add hterm2).add hterm3
  have hd := hsum.deriv
  convert hd using 1
  simp only [partial3_partial1_eq, partial3_partial2_eq,
    partial3_partial3_eq]
  simp [firstXFormula, transformed]
  ring

theorem gap17 (f : ℝ → ℝ → ℝ → ℝ)
    (hf : ContDiff ℝ 2 (uncurry₃ f)) (x y z : ℝ) :
    partialYZ (transformed f) x y z =
      x ^ 2 * y * partial23 f x (x * y) (x * y * z) +
        x ^ 2 * y * z * partial33 f x (x * y) (x * y * z) +
        x * partial3 f x (x * y) (x * y * z) := by
  change deriv (fun t => partialY (transformed f) x y t) z = _
  rw [show (fun t => partialY (transformed f) x y t) =
      (fun t => x * transformed (partial2 f) x y t +
        x * t * transformed (partial3 f) x y t) by
    funext t
    simpa [transformed] using gap3 f (hf.of_le (by norm_num)) x y t]
  have h2 := hasDerivAt_transformedZ (partial2 f)
    (differentiable_uncurry_partial2 f hf) x y z
  have h3 := hasDerivAt_transformedZ (partial3 f)
    (differentiable_uncurry_partial3 f hf) x y z
  have hterm2 := h2.const_mul x
  have hterm3 := ((hasDerivAt_id z).const_mul x).mul h3
  have hsum := hterm2.add hterm3
  have hd := hsum.deriv
  convert hd using 1
  simp only [partial3_partial2_eq, partial3_partial3_eq]
  simp [transformed]
  ring

end

end ProofGap.Exercise3285
