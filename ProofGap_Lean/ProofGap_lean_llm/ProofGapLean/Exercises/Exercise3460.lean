import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3460

noncomputable section

def px (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => f s y) x

def py (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun s => f x s) y

def differential (f : ℝ → ℝ → ℝ)
    (x y dx dy : ℝ) : ℝ :=
  px f x y * dx + py f x y * dy

def denom (b : ℝ) (Z : ℝ → ℝ → ℝ)
    (ξ η : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  1 + b * py Z (ξ x y) (η x y)

private theorem hasDerivAt_px
    (f : ℝ → ℝ → ℝ) (x y : ℝ)
    (hf : DifferentiableAt ℝ (Function.uncurry f) (x, y)) :
    HasDerivAt (fun t : ℝ => f t y) (px f x y) x := by
  have hp : DifferentiableAt ℝ (fun t : ℝ => (t, y)) x := by fun_prop
  have hc : DifferentiableAt ℝ (fun t : ℝ => f t y) x := by
    simpa [Function.uncurry, Function.comp_def] using hf.comp x hp
  simpa [px] using hc.hasDerivAt

private theorem hasDerivAt_py
    (f : ℝ → ℝ → ℝ) (x y : ℝ)
    (hf : DifferentiableAt ℝ (Function.uncurry f) (x, y)) :
    HasDerivAt (fun t : ℝ => f x t) (py f x y) y := by
  have hp : DifferentiableAt ℝ (fun t : ℝ => (x, t)) y := by fun_prop
  have hc : DifferentiableAt ℝ (fun t : ℝ => f x t) y := by
    simpa [Function.uncurry, Function.comp_def] using hf.comp y hp
  simpa [py] using hc.hasDerivAt

private theorem hasDerivAt_comp₂
    (F : ℝ → ℝ → ℝ) (g h : ℝ → ℝ) {x dg dh : ℝ}
    (hF : DifferentiableAt ℝ (Function.uncurry F) (g x, h x))
    (hg : HasDerivAt g dg x) (hh : HasDerivAt h dh x) :
    HasDerivAt (fun t => F (g t) (h t))
      (dg * px F (g x) (h x) + dh * py F (g x) (h x)) x := by
  let D := fderiv ℝ (Function.uncurry F) (g x, h x)
  have hc := hF.hasFDerivAt.comp x
    (hg.hasFDerivAt.prodMk hh.hasFDerivAt)
  have hc' : HasDerivAt (fun t => F (g t) (h t)) (D (dg, dh)) x := by
    simpa [D, Function.comp_def, Function.uncurry] using hc.hasDerivAt
  have hdx0 : HasDerivAt (fun t : ℝ => F t (h x))
      (D (1, 0)) (g x) := by
    have hx := hF.hasFDerivAt.comp (g x)
      ((hasDerivAt_id (g x)).hasFDerivAt.prodMk
        (hasDerivAt_const (g x) (h x)).hasFDerivAt)
    simpa [D, Function.comp_def, Function.uncurry] using hx.hasDerivAt
  have hdx : px F (g x) (h x) = D (1, 0) := by
    change deriv (fun t : ℝ => F t (h x)) (g x) = D (1, 0)
    exact hdx0.deriv
  have hdy0 : HasDerivAt (fun t : ℝ => F (g x) t)
      (D (0, 1)) (h x) := by
    have hy := hF.hasFDerivAt.comp (h x)
      ((hasDerivAt_const (h x) (g x)).hasFDerivAt.prodMk
        (hasDerivAt_id (h x)).hasFDerivAt)
    simpa [D, Function.comp_def, Function.uncurry] using hy.hasDerivAt
  have hdy : py F (g x) (h x) = D (0, 1) := by
    change deriv (fun t : ℝ => F (g x) t) (h x) = D (0, 1)
    exact hdy0.deriv
  have hlin : D (dg, dh) = dg * D (1, 0) + dh * D (0, 1) := by
    calc
      D (dg, dh) = D (dg • (1, 0) + dh • (0, 1)) := by
        congr 1
        ext <;> simp
      _ = dg • D (1, 0) + dh • D (0, 1) := by
        rw [map_add, map_smul, map_smul]
      _ = dg * D (1, 0) + dh * D (0, 1) := by simp
  convert hc' using 1
  simpa [hdx, hdy] using hlin.symm

theorem gap1 (ξ : ℝ → ℝ → ℝ)
    (hξ : ∀ x y, ξ x y = x) :
    ∀ x y dx dy,
      differential ξ x y dx dy = dx := by
  intro x y dx dy
  have hx : px ξ x y = 1 := by
    have hfun : (fun s : ℝ => ξ s y) = fun s : ℝ => s := by
      funext s
      exact hξ s y
    unfold px
    rw [hfun]
    exact (hasDerivAt_id x).deriv
  have hy : py ξ x y = 0 := by
    have hfun : (fun s : ℝ => ξ x s) = fun _ : ℝ => x := by
      funext s
      exact hξ x s
    unfold py
    rw [hfun]
    exact (hasDerivAt_const y x).deriv
  unfold differential
  rw [hx, hy]
  ring

-- Statement correction: require differentiability of z so deriv distributes
-- through the identity-minus-multiple formula for η.
theorem gap2 (b : ℝ) (z η : ℝ → ℝ → ℝ)
    (hz : Differentiable ℝ (Function.uncurry z))
    (hη : ∀ x y, η x y = y - b * z x y) :
    ∀ x y dx dy,
      differential η x y dx dy =
        dy - b * differential z x y dx dy := by
  intro x y dx dy
  have hzx := hasDerivAt_px z x y (hz (x, y))
  have hzy := hasDerivAt_py z x y (hz (x, y))
  have hηx : px η x y = -(b * px z x y) := by
    have hfun : (fun s : ℝ => η s y) =
        fun s : ℝ => y - b * z s y := by
      funext s
      exact hη s y
    unfold px
    rw [hfun]
    simpa using ((hasDerivAt_const x y).sub (hzx.const_mul b)).deriv
  have hηy : py η x y = 1 - b * py z x y := by
    have hfun : (fun s : ℝ => η x s) =
        fun s : ℝ => s - b * z x s := by
      funext s
      exact hη x s
    unfold py
    rw [hfun]
    simpa using ((hasDerivAt_id y).sub (hzy.const_mul b)).deriv
  unfold differential
  rw [hηx, hηy]
  ring

theorem gap3 (z Z ξ η : ℝ → ℝ → ℝ)
    (hCompose : ∀ x y, z x y = Z (ξ x y) (η x y))
    (hZ : ContDiff ℝ 1 (Function.uncurry Z))
    (hξ : ContDiff ℝ 1 (Function.uncurry ξ))
    (hη : ContDiff ℝ 1 (Function.uncurry η)) :
    ∀ x y dx dy,
      differential z x y dx dy =
        px Z (ξ x y) (η x y) * differential ξ x y dx dy +
          py Z (ξ x y) (η x y) * differential η x y dx dy := by
  intro x y dx dy
  have hZd : Differentiable ℝ (Function.uncurry Z) :=
    hZ.differentiable (by decide)
  have hξd : Differentiable ℝ (Function.uncurry ξ) :=
    hξ.differentiable (by decide)
  have hηd : Differentiable ℝ (Function.uncurry η) :=
    hη.differentiable (by decide)
  have hξx := hasDerivAt_px ξ x y (hξd (x, y))
  have hηx := hasDerivAt_px η x y (hηd (x, y))
  have hξy := hasDerivAt_py ξ x y (hξd (x, y))
  have hηy := hasDerivAt_py η x y (hηd (x, y))
  have hzx :
      px z x y =
        px Z (ξ x y) (η x y) * px ξ x y +
          py Z (ξ x y) (η x y) * px η x y := by
    have hfun : (fun t : ℝ => z t y) =
        fun t : ℝ => Z (ξ t y) (η t y) := by
      funext t
      exact hCompose t y
    unfold px
    rw [hfun]
    convert (hasDerivAt_comp₂ Z (fun t => ξ t y) (fun t => η t y)
      (hZd (ξ x y, η x y)) hξx hηx).deriv using 1 <;>
      simp only [px, py] <;> ring
  have hzy :
      py z x y =
        px Z (ξ x y) (η x y) * py ξ x y +
          py Z (ξ x y) (η x y) * py η x y := by
    have hfun : (fun t : ℝ => z x t) =
        fun t : ℝ => Z (ξ x t) (η x t) := by
      funext t
      exact hCompose x t
    unfold py
    rw [hfun]
    convert (hasDerivAt_comp₂ Z (fun t => ξ x t) (fun t => η x t)
      (hZd (ξ x y, η x y)) hξy hηy).deriv using 1 <;>
      simp only [px, py] <;> ring
  unfold differential
  rw [hzx, hzy]
  ring

theorem gap4 (b : ℝ) (z Z ξ η : ℝ → ℝ → ℝ)
    (hξ :
      ∀ x y dx dy,
        differential ξ x y dx dy = dx)
    (hη :
      ∀ x y dx dy,
        differential η x y dx dy =
          dy - b * differential z x y dx dy) :
    ∀ x y dx dy,
      px Z (ξ x y) (η x y) * differential ξ x y dx dy +
          py Z (ξ x y) (η x y) * differential η x y dx dy =
        px Z (ξ x y) (η x y) * dx +
          py Z (ξ x y) (η x y) *
            (dy - b * differential z x y dx dy) := by
  intro x y dx dy
  rw [hξ, hη]

theorem gap5 (b : ℝ) (z Z ξ η : ℝ → ℝ → ℝ)
    (hChain :
      ∀ x y dx dy,
        differential z x y dx dy =
          px Z (ξ x y) (η x y) * differential ξ x y dx dy +
            py Z (ξ x y) (η x y) * differential η x y dx dy)
    (hSubstitute :
      ∀ x y dx dy,
        px Z (ξ x y) (η x y) * differential ξ x y dx dy +
            py Z (ξ x y) (η x y) * differential η x y dx dy =
          px Z (ξ x y) (η x y) * dx +
            py Z (ξ x y) (η x y) *
              (dy - b * differential z x y dx dy)) :
    ∀ x y dx dy,
      differential z x y dx dy =
        px Z (ξ x y) (η x y) * dx +
          py Z (ξ x y) (η x y) *
            (dy - b * differential z x y dx dy) := by
  intro x y dx dy
  exact (hChain x y dx dy).trans (hSubstitute x y dx dy)

theorem gap6 (b : ℝ) (z Z ξ η : ℝ → ℝ → ℝ)
    (hImplicit :
      ∀ x y dx dy,
        differential z x y dx dy =
          px Z (ξ x y) (η x y) * dx +
            py Z (ξ x y) (η x y) *
              (dy - b * differential z x y dx dy)) :
    ∀ x y dx dy,
      denom b Z ξ η x y * differential z x y dx dy =
        px Z (ξ x y) (η x y) * dx +
          py Z (ξ x y) (η x y) * dy := by
  intro x y dx dy
  have h := hImplicit x y dx dy
  unfold denom
  linarith

theorem gap7 (b : ℝ) (z Z ξ η : ℝ → ℝ → ℝ)
    (hCollect :
      ∀ x y dx dy,
        denom b Z ξ η x y * differential z x y dx dy =
          px Z (ξ x y) (η x y) * dx +
            py Z (ξ x y) (η x y) * dy)
    (hNonzero : ∀ x y, denom b Z ξ η x y ≠ 0) :
    ∀ x y dx dy,
      differential z x y dx dy =
        px Z (ξ x y) (η x y) / denom b Z ξ η x y * dx +
          py Z (ξ x y) (η x y) / denom b Z ξ η x y * dy := by
  intro x y dx dy
  have h := hCollect x y dx dy
  field_simp [hNonzero x y]
  linarith

theorem gap8 (b : ℝ) (z Z ξ η : ℝ → ℝ → ℝ)
    (hDifferential :
      ∀ x y dx dy,
        differential z x y dx dy =
          px Z (ξ x y) (η x y) / denom b Z ξ η x y * dx +
            py Z (ξ x y) (η x y) / denom b Z ξ η x y * dy) :
    ∀ x y,
      px z x y =
        px Z (ξ x y) (η x y) / denom b Z ξ η x y := by
  intro x y
  have h := hDifferential x y 1 0
  unfold differential at h
  simpa using h

theorem gap9 (b : ℝ) (z Z ξ η : ℝ → ℝ → ℝ)
    (hDifferential :
      ∀ x y dx dy,
        differential z x y dx dy =
          px Z (ξ x y) (η x y) / denom b Z ξ η x y * dx +
            py Z (ξ x y) (η x y) / denom b Z ξ η x y * dy) :
    ∀ x y,
      py z x y =
        py Z (ξ x y) (η x y) / denom b Z ξ η x y := by
  intro x y
  have h := hDifferential x y 0 1
  unfold differential at h
  simpa using h

theorem gap10 (a b : ℝ) (z Z ξ η : ℝ → ℝ → ℝ)
    (hPDE : ∀ x y, a * px z x y + b * py z x y = 1)
    (hX :
      ∀ x y,
        px z x y =
          px Z (ξ x y) (η x y) / denom b Z ξ η x y)
    (hY :
      ∀ x y,
        py z x y =
          py Z (ξ x y) (η x y) / denom b Z ξ η x y)
    (hNonzero : ∀ x y, denom b Z ξ η x y ≠ 0) :
    ∀ x y,
      a * px Z (ξ x y) (η x y) +
          b * py Z (ξ x y) (η x y) =
        1 + b * py Z (ξ x y) (η x y) := by
  intro x y
  have h := hPDE x y
  rw [hX x y, hY x y] at h
  have hd : 1 + b * py Z (ξ x y) (η x y) ≠ 0 := by
    simpa [denom] using hNonzero x y
  unfold denom at h
  field_simp [hd] at h
  linarith

theorem gap11 (a b : ℝ) (Z ξ η : ℝ → ℝ → ℝ)
    (ha : a ≠ 0)
    (hEquation :
      ∀ x y,
        a * px Z (ξ x y) (η x y) +
            b * py Z (ξ x y) (η x y) =
          1 + b * py Z (ξ x y) (η x y)) :
    ∀ x y,
      px Z (ξ x y) (η x y) = 1 / a := by
  intro x y
  have h := hEquation x y
  field_simp [ha]
  linarith

theorem gap12 (a : ℝ) (z Z ξ η : ℝ → ℝ → ℝ)
    (ha : a ≠ 0)
    (hCompose : ∀ x y, z x y = Z (ξ x y) (η x y))
    (hXiDerivative :
      ∀ x y,
        px Z (ξ x y) (η x y) = 1 / a)
    (hSurjective :
      Function.Surjective
        (fun p : ℝ × ℝ => (ξ p.1 p.2, η p.1 p.2)))
    (hZ : Differentiable ℝ (Function.uncurry Z)) :
    ∃ φ : ℝ → ℝ, ∀ x y,
      z x y = ξ x y / a + φ (η x y) := by
  have hpx : ∀ u v : ℝ, px Z u v = 1 / a := by
    intro u v
    obtain ⟨p, hp⟩ := hSurjective (u, v)
    rcases p with ⟨x, y⟩
    have h := hXiDerivative x y
    have hp' : (ξ x y, η x y) = (u, v) := by simpa using hp
    have hcoords : ξ x y = u ∧ η x y = v := Prod.mk.inj hp'
    simpa [hcoords.1, hcoords.2] using h
  refine ⟨fun v => Z 0 v, ?_⟩
  intro x y
  have hdiff : Differentiable ℝ
      (fun t : ℝ => Z t (η x y) - t / a) := by
    have hzslice : Differentiable ℝ (fun t : ℝ => Z t (η x y)) := by
      intro t
      exact (hasDerivAt_px Z t (η x y) (hZ (t, η x y))).differentiableAt
    fun_prop
  have hzero : ∀ t : ℝ,
      deriv (fun s : ℝ => Z s (η x y) - s / a) t = 0 := by
    intro t
    have hzder := hasDerivAt_px Z t (η x y) (hZ (t, η x y))
    have hl : HasDerivAt (fun s : ℝ => s / a) (1 / a) t := by
      simpa using (hasDerivAt_id t).div_const a
    have hd := (hzder.sub hl).deriv
    rw [hpx t (η x y)] at hd
    simpa using hd
  have hc := is_const_of_deriv_eq_zero hdiff hzero (ξ x y) 0
  rw [hCompose x y]
  dsimp at hc ⊢
  calc
    Z (ξ x y) (η x y) =
        (Z (ξ x y) (η x y) - ξ x y / a) + ξ x y / a := by ring
    _ = (Z 0 (η x y) - 0 / a) + ξ x y / a := by rw [hc]
    _ = ξ x y / a + Z 0 (η x y) := by ring

theorem gap13 (a b : ℝ) (z ξ η : ℝ → ℝ → ℝ)
    (hξ : ∀ x y, ξ x y = x)
    (hη : ∀ x y, η x y = y - b * z x y)
    (hForm :
      ∃ φ : ℝ → ℝ, ∀ x y,
        z x y = ξ x y / a + φ (η x y)) :
    ∃ φ : ℝ → ℝ, ∀ x y,
      ξ x y / a + φ (η x y) =
        x / a + φ (y - b * z x y) := by
  rcases hForm with ⟨φ, hφ⟩
  refine ⟨φ, ?_⟩
  intro x y
  rw [hξ x y, hη x y]

theorem gap14 (a b : ℝ) (z ξ η : ℝ → ℝ → ℝ)
    (hξ : ∀ x y, ξ x y = x)
    (hη : ∀ x y, η x y = y - b * z x y)
    (hForm :
      ∃ φ : ℝ → ℝ, ∀ x y,
        z x y = ξ x y / a + φ (η x y)) :
    ∃ φ : ℝ → ℝ, ∀ x y,
      z x y = x / a + φ (y - b * z x y) := by
  rcases hForm with ⟨φ, hφ⟩
  refine ⟨φ, ?_⟩
  intro x y
  simpa [hξ x y, hη x y] using hφ x y

end

end ProofGap.Exercise3460
