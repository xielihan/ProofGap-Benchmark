import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3325

noncomputable section

def partialX (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => g s y) x

def partialY (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => g x s) y

def partialFirst (g : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun s => g s y z) x

def partialSecond (g : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun s => g x s z) y

def partialThird (g : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun s => g x y s) z

def u (φ : ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  x * y / z * Real.log x + x * φ (y / x) (z / x)

private theorem hasDerivAt_phi_comp
    (φ : ℝ → ℝ → ℝ)
    (hφ : ContDiff ℝ 1 (Function.uncurry φ))
    {a b : ℝ → ℝ} {da db t : ℝ}
    (ha : HasDerivAt a da t) (hb : HasDerivAt b db t) :
    HasDerivAt (fun s => φ (a s) (b s))
      (da * partialX φ (a t) (b t) + db * partialY φ (a t) (b t)) t := by
  let D := fderiv ℝ (Function.uncurry φ) (a t, b t)
  have hF : HasFDerivAt (Function.uncurry φ) D (a t, b t) := by
    simpa [D] using
      ((hφ.differentiable (by simp)).differentiableAt.hasFDerivAt)
  have hX :
      HasDerivAt (fun s : ℝ => φ s (b t)) (D (1, 0)) (a t) := by
    have hp : HasFDerivAt (fun s : ℝ => (s, b t))
        ((1 : ℝ →L[ℝ] ℝ).prod (0 : ℝ →L[ℝ] ℝ)) (a t) := by
      simpa only [id_eq] using
        ((hasFDerivAt_id (a t)).prodMk
          (hasFDerivAt_const (b t) (a t)))
    simpa [Function.uncurry] using (hF.comp (a t) hp).hasDerivAt
  have hY :
      HasDerivAt (fun s : ℝ => φ (a t) s) (D (0, 1)) (b t) := by
    have hp : HasFDerivAt (fun s : ℝ => (a t, s))
        ((0 : ℝ →L[ℝ] ℝ).prod (1 : ℝ →L[ℝ] ℝ)) (b t) := by
      simpa only [id_eq] using
        ((hasFDerivAt_const (a t) (b t)).prodMk
          (hasFDerivAt_id (b t)))
    simpa [Function.uncurry] using (hF.comp (b t) hp).hasDerivAt
  have hxval : partialX φ (a t) (b t) = D (1, 0) := by
    unfold partialX
    exact hX.deriv
  have hyval : partialY φ (a t) (b t) = D (0, 1) := by
    unfold partialY
    exact hY.deriv
  have hp :
      (da, db) = da • ((1 : ℝ), (0 : ℝ)) + db • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  have hlin :
      D (da, db) = da * D (1, 0) + db * D (0, 1) := by
    calc
      D (da, db) =
          D (da • ((1 : ℝ), (0 : ℝ)) + db • ((0 : ℝ), (1 : ℝ))) := by
            rw [hp]
      _ = da • D (1, 0) + db • D (0, 1) := by
            rw [map_add, map_smul, map_smul]
      _ = da * D (1, 0) + db * D (0, 1) := by
            simp [smul_eq_mul]
  have heq :
      D (da, db) =
        da * partialX φ (a t) (b t) + db * partialY φ (a t) (b t) := by
    rw [hxval, hyval]
    exact hlin
  rw [← heq]
  have hp := ha.hasFDerivAt.prodMk hb.hasFDerivAt
  simpa [Function.uncurry] using (hF.comp t hp).hasDerivAt

theorem gap1 (φ : ℝ → ℝ → ℝ)
    (hφ : ContDiff ℝ 1 (Function.uncurry φ)) :
    ∀ x y z, 0 < x → z ≠ 0 →
      x * partialFirst (u φ) x y z =
        x * y / z * Real.log x + x * y / z +
          x * φ (y / x) (z / x) -
          y * partialX φ (y / x) (z / x) -
          z * partialY φ (y / x) (z / x) := by
  intro x y z hx hz
  have hx0 : x ≠ 0 := ne_of_gt hx
  have ha : HasDerivAt (fun s : ℝ => y / s) (-y / x ^ 2) x := by
    convert (hasDerivAt_const x y).div (hasDerivAt_id x) hx0 using 1 <;>
      simp only [id_eq] <;>
      field_simp [hx0] <;> ring
  have hb : HasDerivAt (fun s : ℝ => z / s) (-z / x ^ 2) x := by
    convert (hasDerivAt_const x z).div (hasDerivAt_id x) hx0 using 1 <;>
      simp only [id_eq] <;>
      field_simp [hx0] <;> ring
  have hcomp := hasDerivAt_phi_comp φ hφ ha hb
  have hxy :
      HasDerivAt (fun s : ℝ => s * y / z) (y / z) x := by
    simpa only [id_eq, one_mul] using
      (((hasDerivAt_id x).mul_const y).div_const z)
  have hfirst :
      HasDerivAt (fun s : ℝ => s * y / z * Real.log s)
        (y / z * Real.log x + y / z) x := by
    convert hxy.mul (Real.hasDerivAt_log hx0) using 1 <;>
      field_simp [hx0, hz] <;> ring
  have hsecond :
      HasDerivAt (fun s : ℝ => s * φ (y / s) (z / s))
        (φ (y / x) (z / x) +
          x * ((-y / x ^ 2) * partialX φ (y / x) (z / x) +
            (-z / x ^ 2) * partialY φ (y / x) (z / x))) x := by
    convert (hasDerivAt_id x).mul hcomp using 1 <;>
      simp only [id_eq] <;> ring
  have hpartial :
      partialFirst (u φ) x y z =
        y / z * Real.log x + y / z +
          (φ (y / x) (z / x) +
            x * ((-y / x ^ 2) * partialX φ (y / x) (z / x) +
              (-z / x ^ 2) * partialY φ (y / x) (z / x))) := by
    unfold partialFirst
    simpa [u] using (hfirst.add hsecond).deriv
  rw [hpartial]
  field_simp [hx0, hz] <;> ring

theorem gap2 (φ : ℝ → ℝ → ℝ)
    (hφ : ContDiff ℝ 1 (Function.uncurry φ)) :
    ∀ y x z, 0 < x → z ≠ 0 →
      y * partialSecond (u φ) x y z =
        x * y / z * Real.log x +
          y * partialX φ (y / x) (z / x) := by
  intro y x z hx hz
  have hx0 : x ≠ 0 := ne_of_gt hx
  have ha : HasDerivAt (fun s : ℝ => s / x) (1 / x) y := by
    convert (hasDerivAt_id y).div_const x using 1 <;>
      simp only [id_eq] <;> ring
  have hb : HasDerivAt (fun _ : ℝ => z / x) 0 y :=
    hasDerivAt_const y (z / x)
  have hcomp := hasDerivAt_phi_comp φ hφ ha hb
  have hfirst :
      HasDerivAt (fun s : ℝ => x * s / z * Real.log x)
        (x / z * Real.log x) y := by
    convert ((((hasDerivAt_const y x).mul (hasDerivAt_id y)).div_const z).mul
      (hasDerivAt_const y (Real.log x))) using 1 <;>
      simp only [id_eq] <;> ring
  have hsecond :
      HasDerivAt (fun s : ℝ => x * φ (s / x) (z / x))
        (partialX φ (y / x) (z / x)) y := by
    convert (hasDerivAt_const y x).mul hcomp using 1 <;>
      field_simp [hx0] <;> ring
  have hpartial :
      partialSecond (u φ) x y z =
        x / z * Real.log x + partialX φ (y / x) (z / x) := by
    unfold partialSecond
    simpa [u] using (hfirst.add hsecond).deriv
  rw [hpartial]
  ring

theorem gap3 (φ : ℝ → ℝ → ℝ)
    (hφ : ContDiff ℝ 1 (Function.uncurry φ)) :
    ∀ z x y, 0 < x → z ≠ 0 →
      z * partialThird (u φ) x y z =
        -(x * y / z * Real.log x) +
          z * partialY φ (y / x) (z / x) := by
  intro z x y hx hz
  have hx0 : x ≠ 0 := ne_of_gt hx
  have ha : HasDerivAt (fun _ : ℝ => y / x) 0 z :=
    hasDerivAt_const z (y / x)
  have hb : HasDerivAt (fun s : ℝ => s / x) (1 / x) z := by
    convert (hasDerivAt_id z).div_const x using 1 <;>
      simp only [id_eq] <;> ring
  have hcomp := hasDerivAt_phi_comp φ hφ ha hb
  have hfirst :
      HasDerivAt (fun s : ℝ => x * y / s * Real.log x)
        (-(x * y / z ^ 2 * Real.log x)) z := by
    convert (((hasDerivAt_const z (x * y)).div (hasDerivAt_id z) hz).mul
      (hasDerivAt_const z (Real.log x))) using 1 <;>
      simp only [id_eq] <;>
      field_simp [hz] <;> ring
  have hsecond :
      HasDerivAt (fun s : ℝ => x * φ (y / x) (s / x))
        (partialY φ (y / x) (z / x)) z := by
    convert (hasDerivAt_const z x).mul hcomp using 1 <;>
      field_simp [hx0] <;> ring
  have hpartial :
      partialThird (u φ) x y z =
        -(x * y / z ^ 2 * Real.log x) + partialY φ (y / x) (z / x) := by
    unfold partialThird
    simpa [u] using (hfirst.add hsecond).deriv
  rw [hpartial]
  field_simp [hz] <;> ring

theorem gap4 (φ : ℝ → ℝ → ℝ)
    (hφ : ContDiff ℝ 1 (Function.uncurry φ)) :
    ∀ x y z, 0 < x → z ≠ 0 →
      x * partialFirst (u φ) x y z +
          y * partialSecond (u φ) x y z +
          z * partialThird (u φ) x y z =
        u φ x y z + x * y / z := by
  intro x y z hx hz
  rw [gap1 φ hφ x y z hx hz,
    gap2 φ hφ y x z hx hz,
    gap3 φ hφ z x y hx hz]
  unfold u
  ring

theorem gap5 (φ : ℝ → ℝ → ℝ)
    (hφ : ContDiff ℝ 1 (Function.uncurry φ)) :
    ∀ x y z, 0 < x → z ≠ 0 →
      x * partialFirst (u φ) x y z +
          y * partialSecond (u φ) x y z +
          z * partialThird (u φ) x y z =
        u φ x y z + x * y / z := by
  exact gap4 φ hφ

end

end ProofGap.Exercise3325
