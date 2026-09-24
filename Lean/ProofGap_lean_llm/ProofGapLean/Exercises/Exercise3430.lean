import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3430

noncomputable section

def px (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => z s y) x

def py (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => z x s) y

def pxx (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  px (px z) x y

def pxy (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  py (px z) x y

def pyy (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  py (py z) x y

def A (φ ψ : ℝ → ℝ) (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  x * deriv φ (z x y) + deriv ψ (z x y)

def B (φ ψ : ℝ → ℝ) (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  x * deriv (deriv φ) (z x y) + deriv (deriv ψ) (z x y)

def borderedDet (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  (py z x y) ^ 2 * pxx z x y -
    2 * px z x y * py z x y * pxy z x y +
    (px z x y) ^ 2 * pyy z x y

private theorem xSlice_contDiff {n : WithTop ℕ∞}
    (z : ℝ → ℝ → ℝ) (hz : ContDiff ℝ n (Function.uncurry z))
    (y : ℝ) :
    ContDiff ℝ n (fun s => z s y) := by
  have hp : ContDiff ℝ n (fun s : ℝ => (s, y)) := by fun_prop
  simpa [Function.uncurry] using hz.comp hp

private theorem ySlice_contDiff {n : WithTop ℕ∞}
    (z : ℝ → ℝ → ℝ) (hz : ContDiff ℝ n (Function.uncurry z))
    (x : ℝ) :
    ContDiff ℝ n (fun s => z x s) := by
  have hp : ContDiff ℝ n (fun s : ℝ => (x, s)) := by fun_prop
  simpa [Function.uncurry] using hz.comp hp

private theorem hasDerivAt_px_x (z : ℝ → ℝ → ℝ)
    (hz : ContDiff ℝ 1 (Function.uncurry z)) (x y : ℝ) :
    HasDerivAt (fun s => z s y) (px z x y) x := by
  apply DifferentiableAt.hasDerivAt
  exact (xSlice_contDiff z hz y).differentiable (by decide) x

private theorem hasDerivAt_py_y (z : ℝ → ℝ → ℝ)
    (hz : ContDiff ℝ 1 (Function.uncurry z)) (x y : ℝ) :
    HasDerivAt (fun s => z x s) (py z x y) y := by
  apply DifferentiableAt.hasDerivAt
  exact (ySlice_contDiff z hz x).differentiable (by decide) y

private theorem px_eq_fderiv (z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hz : DifferentiableAt ℝ (Function.uncurry z) (x, y)) :
    px z x y =
      fderiv ℝ (Function.uncurry z) (x, y) (1, 0) := by
  unfold px
  have hp : HasDerivAt (fun t : ℝ => (t, y)) (1, 0) x :=
    (hasDerivAt_id x).prodMk (hasDerivAt_const x y)
  have h := (hz.hasFDerivAt.comp x hp.hasFDerivAt).hasDerivAt.deriv
  simpa [Function.uncurry] using h

private theorem px_uncurry_differentiable (z : ℝ → ℝ → ℝ)
    (hz : ContDiff ℝ 2 (Function.uncurry z)) :
    Differentiable ℝ (Function.uncurry (px z)) := by
  let G := Function.uncurry z
  have hDf : Differentiable ℝ (fderiv ℝ G) :=
    (hz.fderiv_right (m := 1) (by norm_num)).differentiable (by decide)
  have hzDiff : Differentiable ℝ G :=
    hz.differentiable (by decide)
  have heq :
      Function.uncurry (px z) =
        fun p : ℝ × ℝ => fderiv ℝ G p (1, 0) := by
    funext p
    exact px_eq_fderiv z p.1 p.2 hzDiff.differentiableAt
  rw [heq]
  fun_prop

private theorem hasDerivAt_pxx (z : ℝ → ℝ → ℝ)
    (hz : ContDiff ℝ 2 (Function.uncurry z)) (x y : ℝ) :
    HasDerivAt (fun s => px z s y) (pxx z x y) x := by
  change HasDerivAt (deriv (fun s => z s y))
    (deriv (deriv (fun s => z s y)) x) x
  exact (xSlice_contDiff z hz y).differentiable_deriv_two
    |>.differentiableAt.hasDerivAt

private theorem hasDerivAt_pxy (z : ℝ → ℝ → ℝ)
    (hz : ContDiff ℝ 2 (Function.uncurry z)) (x y : ℝ) :
    HasDerivAt (fun s => px z x s) (pxy z x y) y := by
  change HasDerivAt (fun s => px z x s)
    (deriv (fun s => px z x s) y) y
  apply DifferentiableAt.hasDerivAt
  have hp : DifferentiableAt ℝ (fun s : ℝ => (x, s)) y := by
    fun_prop
  exact (px_uncurry_differentiable z hz).differentiableAt.comp y hp

private theorem hasDerivAt_pyy (z : ℝ → ℝ → ℝ)
    (hz : ContDiff ℝ 2 (Function.uncurry z)) (x y : ℝ) :
    HasDerivAt (fun s => py z x s) (pyy z x y) y := by
  change HasDerivAt (deriv (fun s => z x s))
    (deriv (deriv (fun s => z x s)) y) y
  exact (ySlice_contDiff z hz x).differentiable_deriv_two
    |>.differentiableAt.hasDerivAt

theorem gap1 (φ ψ : ℝ → ℝ) (z : ℝ → ℝ → ℝ)
    (hImplicit : ∀ x y, y = x * φ (z x y) + ψ (z x y))
    (hφ : ContDiff ℝ 1 φ)
    (hψ : ContDiff ℝ 1 ψ)
    (hz : ContDiff ℝ 1 (Function.uncurry z)) :
    ∀ x y, φ (z x y) + A φ ψ z x y * px z x y = 0 := by
  intro x y
  have hzX := hasDerivAt_px_x z hz x y
  have hφAt : HasDerivAt φ (deriv φ (z x y)) (z x y) :=
    (hφ.differentiable (by decide)).differentiableAt.hasDerivAt
  have hψAt : HasDerivAt ψ (deriv ψ (z x y)) (z x y) :=
    (hψ.differentiable (by decide)).differentiableAt.hasDerivAt
  have hφz := hφAt.comp x hzX
  have hψz := hψAt.comp x hzX
  have hright :
      HasDerivAt (fun s => s * φ (z s y) + ψ (z s y))
        (φ (z x y) + A φ ψ z x y * px z x y) x := by
    convert ((hasDerivAt_id x).mul hφz).add hψz using 1 <;>
      simp [A] <;> ring
  have heq :
      (fun _ : ℝ => y) =
        fun s => s * φ (z s y) + ψ (z s y) := by
    funext s
    exact hImplicit s y
  have hd := congrArg (fun f : ℝ → ℝ => deriv f x) heq
  change deriv (fun _ : ℝ => y) x =
    deriv (fun s => s * φ (z s y) + ψ (z s y)) x at hd
  rw [deriv_const, hright.deriv] at hd
  exact hd.symm

theorem gap2 (φ ψ : ℝ → ℝ) (z : ℝ → ℝ → ℝ)
    (hImplicit : ∀ x y, y = x * φ (z x y) + ψ (z x y))
    (hφ : ContDiff ℝ 1 φ)
    (hψ : ContDiff ℝ 1 ψ)
    (hz : ContDiff ℝ 1 (Function.uncurry z)) :
    ∀ x y, A φ ψ z x y * py z x y = 1 := by
  intro x y
  have hzY := hasDerivAt_py_y z hz x y
  have hφAt : HasDerivAt φ (deriv φ (z x y)) (z x y) :=
    (hφ.differentiable (by decide)).differentiableAt.hasDerivAt
  have hψAt : HasDerivAt ψ (deriv ψ (z x y)) (z x y) :=
    (hψ.differentiable (by decide)).differentiableAt.hasDerivAt
  have hright :
      HasDerivAt (fun s => x * φ (z x s) + ψ (z x s))
        (A φ ψ z x y * py z x y) y := by
    convert (hφAt.comp y hzY).const_mul x |>.add (hψAt.comp y hzY)
      using 1 <;> simp [A] <;> ring
  have heq :
      (fun s : ℝ => s) =
        fun s => x * φ (z x s) + ψ (z x s) := by
    funext s
    exact hImplicit x s
  have hd := congrArg (fun f : ℝ → ℝ => deriv f y) heq
  change deriv (fun s : ℝ => s) y =
    deriv (fun s => x * φ (z x s) + ψ (z x s)) y at hd
  rw [show deriv (fun s : ℝ => s) y = 1 from (hasDerivAt_id y).deriv,
    hright.deriv] at hd
  exact hd.symm

theorem gap3 (φ ψ : ℝ → ℝ) (z : ℝ → ℝ → ℝ)
    (hImplicit : ∀ x y, y = x * φ (z x y) + ψ (z x y))
    (hφ : ContDiff ℝ 2 φ)
    (hψ : ContDiff ℝ 2 ψ)
    (hz : ContDiff ℝ 2 (Function.uncurry z)) :
    ∀ x y,
      2 * deriv φ (z x y) * px z x y +
          B φ ψ z x y * (px z x y) ^ 2 +
          A φ ψ z x y * pxx z x y =
        0 := by
  intro x y
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by norm_num)
  have hz1 : ContDiff ℝ 1 (Function.uncurry z) := hz.of_le (by norm_num)
  have hzX := hasDerivAt_px_x z hz1 x y
  have hpxX := hasDerivAt_pxx z hz x y
  have hφAt : HasDerivAt φ (deriv φ (z x y)) (z x y) :=
    hφ1.differentiable (by decide) (z x y) |>.hasDerivAt
  have hφ'At :
      HasDerivAt (deriv φ) (deriv (deriv φ) (z x y)) (z x y) :=
    hφ.differentiable_deriv_two (z x y) |>.hasDerivAt
  have hψ'At :
      HasDerivAt (deriv ψ) (deriv (deriv ψ) (z x y)) (z x y) :=
    hψ.differentiable_deriv_two (z x y) |>.hasDerivAt
  have hAz :
      HasDerivAt (fun s => A φ ψ z s y)
        (deriv φ (z x y) + B φ ψ z x y * px z x y) x := by
    convert
      ((hasDerivAt_id x).mul (hφ'At.comp x hzX)).add
        (hψ'At.comp x hzX) using 1 <;>
      simp [A, B] <;> ring
  have hleft :
      HasDerivAt
        (fun s => φ (z s y) + A φ ψ z s y * px z s y)
        (2 * deriv φ (z x y) * px z x y +
          B φ ψ z x y * (px z x y) ^ 2 +
          A φ ψ z x y * pxx z x y) x := by
    convert (hφAt.comp x hzX).add (hAz.mul hpxX) using 1 <;> ring
  have heq :
      (fun s => φ (z s y) + A φ ψ z s y * px z s y) =
        fun _ : ℝ => 0 := by
    funext s
    exact gap1 φ ψ z hImplicit hφ1 hψ1 hz1 s y
  have hd := congrArg (fun f : ℝ → ℝ => deriv f x) heq
  change
    deriv (fun s => φ (z s y) + A φ ψ z s y * px z s y) x =
      deriv (fun _ : ℝ => 0) x at hd
  rw [hleft.deriv, deriv_const] at hd
  exact hd

theorem gap4 (φ ψ : ℝ → ℝ) (z : ℝ → ℝ → ℝ)
    (hImplicit : ∀ x y, y = x * φ (z x y) + ψ (z x y))
    (hφ : ContDiff ℝ 2 φ)
    (hψ : ContDiff ℝ 2 ψ)
    (hz : ContDiff ℝ 2 (Function.uncurry z)) :
    ∀ x y,
      deriv φ (z x y) * py z x y +
          B φ ψ z x y * px z x y * py z x y +
          A φ ψ z x y * pxy z x y =
        0 := by
  intro x y
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by norm_num)
  have hz1 : ContDiff ℝ 1 (Function.uncurry z) := hz.of_le (by norm_num)
  have hzY := hasDerivAt_py_y z hz1 x y
  have hpxY := hasDerivAt_pxy z hz x y
  have hφAt : HasDerivAt φ (deriv φ (z x y)) (z x y) :=
    hφ1.differentiable (by decide) (z x y) |>.hasDerivAt
  have hφ'At :
      HasDerivAt (deriv φ) (deriv (deriv φ) (z x y)) (z x y) :=
    hφ.differentiable_deriv_two (z x y) |>.hasDerivAt
  have hψ'At :
      HasDerivAt (deriv ψ) (deriv (deriv ψ) (z x y)) (z x y) :=
    hψ.differentiable_deriv_two (z x y) |>.hasDerivAt
  have hAz :
      HasDerivAt (fun s => A φ ψ z x s)
        (B φ ψ z x y * py z x y) y := by
    convert
      (hφ'At.comp y hzY).const_mul x |>.add
        (hψ'At.comp y hzY) using 1 <;>
      simp [A, B] <;> ring
  have hleft :
      HasDerivAt
        (fun s => φ (z x s) + A φ ψ z x s * px z x s)
        (deriv φ (z x y) * py z x y +
          B φ ψ z x y * px z x y * py z x y +
          A φ ψ z x y * pxy z x y) y := by
    convert (hφAt.comp y hzY).add (hAz.mul hpxY) using 1 <;> ring
  have heq :
      (fun s => φ (z x s) + A φ ψ z x s * px z x s) =
        fun _ : ℝ => 0 := by
    funext s
    exact gap1 φ ψ z hImplicit hφ1 hψ1 hz1 x s
  have hd := congrArg (fun f : ℝ → ℝ => deriv f y) heq
  change
    deriv (fun s => φ (z x s) + A φ ψ z x s * px z x s) y =
      deriv (fun _ : ℝ => 0) y at hd
  rw [hleft.deriv, deriv_const] at hd
  exact hd

theorem gap5 (φ ψ : ℝ → ℝ) (z : ℝ → ℝ → ℝ)
    (hImplicit : ∀ x y, y = x * φ (z x y) + ψ (z x y))
    (hφ : ContDiff ℝ 2 φ)
    (hψ : ContDiff ℝ 2 ψ)
    (hz : ContDiff ℝ 2 (Function.uncurry z)) :
    ∀ x y,
      B φ ψ z x y * (py z x y) ^ 2 +
          A φ ψ z x y * pyy z x y =
        0 := by
  intro x y
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by norm_num)
  have hz1 : ContDiff ℝ 1 (Function.uncurry z) := hz.of_le (by norm_num)
  have hzY := hasDerivAt_py_y z hz1 x y
  have hpyY := hasDerivAt_pyy z hz x y
  have hφ'At :
      HasDerivAt (deriv φ) (deriv (deriv φ) (z x y)) (z x y) :=
    hφ.differentiable_deriv_two (z x y) |>.hasDerivAt
  have hψ'At :
      HasDerivAt (deriv ψ) (deriv (deriv ψ) (z x y)) (z x y) :=
    hψ.differentiable_deriv_two (z x y) |>.hasDerivAt
  have hAz :
      HasDerivAt (fun s => A φ ψ z x s)
        (B φ ψ z x y * py z x y) y := by
    convert
      (hφ'At.comp y hzY).const_mul x |>.add
        (hψ'At.comp y hzY) using 1 <;>
      simp [A, B] <;> ring
  have hleft :
      HasDerivAt (fun s => A φ ψ z x s * py z x s)
        (B φ ψ z x y * (py z x y) ^ 2 +
          A φ ψ z x y * pyy z x y) y := by
    convert hAz.mul hpyY using 1 <;> ring
  have heq :
      (fun s => A φ ψ z x s * py z x s) =
        fun _ : ℝ => 1 := by
    funext s
    exact gap2 φ ψ z hImplicit hφ1 hψ1 hz1 x s
  have hd := congrArg (fun f : ℝ → ℝ => deriv f y) heq
  change deriv (fun s => A φ ψ z x s * py z x s) y =
    deriv (fun _ : ℝ => 1) y at hd
  rw [hleft.deriv, deriv_const] at hd
  exact hd

theorem gap6 (φ ψ : ℝ → ℝ) (z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hY : A φ ψ z x y * py z x y = 1)
    (hXX :
      2 * deriv φ (z x y) * px z x y +
          B φ ψ z x y * (px z x y) ^ 2 +
          A φ ψ z x y * pxx z x y =
        0)
    (hXY :
      deriv φ (z x y) * py z x y +
          B φ ψ z x y * px z x y * py z x y +
          A φ ψ z x y * pxy z x y =
        0)
    (hYY :
      B φ ψ z x y * (py z x y) ^ 2 +
          A φ ψ z x y * pyy z x y =
        0) :
    borderedDet z x y = 0 := by
  have hA : A φ ψ z x y ≠ 0 := by
    intro h
    rw [h] at hY
    norm_num at hY
  have e1 := congrArg (fun q : ℝ => (py z x y) ^ 2 * q) hXX
  have e2 :=
    congrArg (fun q : ℝ => (-2 * px z x y * py z x y) * q) hXY
  have e3 := congrArg (fun q : ℝ => (px z x y) ^ 2 * q) hYY
  have hmul :
      A φ ψ z x y * borderedDet z x y = 0 := by
    unfold borderedDet
    nlinarith [e1, e2, e3]
  exact (mul_eq_zero.mp hmul).resolve_left hA

theorem gap7 (z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hDefinitions :
      (py z x y) ^ 2 * pxx z x y -
          2 * px z x y * py z x y * pxy z x y +
          (px z x y) ^ 2 * pyy z x y =
        0) :
    borderedDet z x y = 0 := by
  exact hDefinitions

theorem gap8 (z : ℝ → ℝ → ℝ)
    (hResult : ∀ x y, borderedDet z x y = 0) :
    ∀ x y, borderedDet z x y = 0 := by
  exact hResult

end

end ProofGap.Exercise3430
