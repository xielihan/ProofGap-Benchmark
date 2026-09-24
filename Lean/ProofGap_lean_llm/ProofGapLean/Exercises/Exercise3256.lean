import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3256

noncomputable section

def u (x y : ℝ) : ℝ :=
  x - y + x ^ 2 + 2 * x * y + y ^ 2 +
    x ^ 3 - 3 * x ^ 2 * y - y ^ 3 +
    x ^ 4 - 4 * x ^ 2 * y ^ 2 + y ^ 4

def partialXOrder (n : ℕ) (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  (deriv^[n]) (fun t => g t y) x

def partialYOrder (n : ℕ) (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  (deriv^[n]) (fun t => g x t) y

def mixedX3Y (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialXOrder 3 g x t) y

def mixedX2Y2 (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => deriv (fun s => partialXOrder 2 g x s) t) y

private theorem u_first_deriv (x y : ℝ) :
    deriv (fun t : ℝ => u t y) x =
      1 + 2 * x + 2 * y + 3 * x ^ 2 - 6 * x * y +
        4 * x ^ 3 - 8 * x * y ^ 2 := by
  have hx : HasDerivAt (fun t : ℝ => t) 1 x := by
    simpa using (hasDerivAt_id x)
  have hx2 := hx.mul hx
  have hx3 := hx2.mul hx
  have hx4 := hx2.mul hx2
  have h1 := hx.sub_const y
  have h2 := h1.add hx2
  have h3 := h2.add ((hx.const_mul 2).mul_const y)
  have h4 := h3.add (hasDerivAt_const x (y ^ 2))
  have h5 := h4.add hx3
  have h6 := h5.sub ((hx2.const_mul 3).mul_const y)
  have h7 := h6.sub (hasDerivAt_const x (y ^ 3))
  have h8 := h7.add hx4
  have h9 := h8.sub ((hx2.const_mul 4).mul_const (y ^ 2))
  have h10 := h9.add (hasDerivAt_const x (y ^ 4))
  unfold u
  convert h10.deriv using 1
  all_goals
    try
      apply congrArg (fun f : ℝ → ℝ => deriv f x)
      funext t
    simp [u] <;> ring

private theorem u_second_deriv (x y : ℝ) :
    deriv (fun t : ℝ =>
      1 + 2 * t + 2 * y + 3 * t ^ 2 - 6 * t * y +
        4 * t ^ 3 - 8 * t * y ^ 2) x =
      2 + 6 * x - 6 * y + 12 * x ^ 2 - 8 * y ^ 2 := by
  have hx : HasDerivAt (fun t : ℝ => t) 1 x := by
    simpa using (hasDerivAt_id x)
  have hx2 := hx.mul hx
  have hx3 := hx2.mul hx
  have h1 := (hasDerivAt_const x (1 : ℝ)).add (hx.const_mul 2)
  have h2 := h1.add (hasDerivAt_const x (2 * y))
  have h3 := h2.add (hx2.const_mul 3)
  have h4 := h3.sub ((hx.const_mul 6).mul_const y)
  have h5 := h4.add (hx3.const_mul 4)
  have h6 := h5.sub ((hx.const_mul 8).mul_const (y ^ 2))
  convert h6.deriv using 1
  all_goals
    try
      apply congrArg (fun f : ℝ → ℝ => deriv f x)
      funext t
    simp <;> ring

private theorem u_third_deriv (x y : ℝ) :
    deriv (fun t : ℝ =>
      2 + 6 * t - 6 * y + 12 * t ^ 2 - 8 * y ^ 2) x =
      6 + 24 * x := by
  have hx : HasDerivAt (fun t : ℝ => t) 1 x := by
    simpa using (hasDerivAt_id x)
  have hx2 := hx.mul hx
  have h1 := (hasDerivAt_const x (2 : ℝ)).add (hx.const_mul 6)
  have h2 := h1.sub (hasDerivAt_const x (6 * y))
  have h3 := h2.add (hx2.const_mul 12)
  have h4 := h3.sub (hasDerivAt_const x (8 * y ^ 2))
  convert h4.deriv using 1
  all_goals
    try
      apply congrArg (fun f : ℝ → ℝ => deriv f x)
      funext t
    simp <;> ring

private theorem u_fourth_deriv (x : ℝ) :
    deriv (fun t : ℝ => 6 + 24 * t) x = 24 := by
  have hx : HasDerivAt (fun t : ℝ => t) 1 x := by
    simpa using (hasDerivAt_id x)
  have h := (hasDerivAt_const x (6 : ℝ)).add (hx.const_mul 24)
  convert h.deriv using 1
  all_goals
    try
      apply congrArg (fun f : ℝ → ℝ => deriv f x)
      funext t
    simp <;> ring

private theorem u_second_partial_y_first (x y : ℝ) :
    deriv (fun s : ℝ =>
      2 + 6 * x - 6 * s + 12 * x ^ 2 - 8 * s ^ 2) y =
      -6 - 16 * y := by
  have hy : HasDerivAt (fun s : ℝ => s) 1 y := by
    simpa using (hasDerivAt_id y)
  have hy2 := hy.mul hy
  have h1 := (hasDerivAt_const y (2 + 6 * x)).sub (hy.const_mul 6)
  have h2 := h1.add (hasDerivAt_const y (12 * x ^ 2))
  have h3 := h2.sub (hy2.const_mul 8)
  convert h3.deriv using 1
  all_goals
    try
      apply congrArg (fun f : ℝ → ℝ => deriv f y)
      funext s
    simp <;> ring

private theorem u_second_partial_y_second (y : ℝ) :
    deriv (fun s : ℝ => -6 - 16 * s) y = -16 := by
  have hy : HasDerivAt (fun s : ℝ => s) 1 y := by
    simpa using (hasDerivAt_id y)
  have h := (hasDerivAt_const y (-6 : ℝ)).sub (hy.const_mul 16)
  convert h.deriv using 1
  all_goals
    try
      apply congrArg (fun f : ℝ → ℝ => deriv f y)
      funext s
    simp <;> ring

theorem gap1 :
    ∀ x y, partialXOrder 2 u x y =
      2 + 6 * x - 6 * y + 12 * x ^ 2 - 8 * y ^ 2 := by
  intro x y
  change deriv (deriv (fun t : ℝ => u t y)) x = _
  rw [show deriv (fun t : ℝ => u t y) =
      fun t => 1 + 2 * t + 2 * y + 3 * t ^ 2 - 6 * t * y +
        4 * t ^ 3 - 8 * t * y ^ 2 from
    funext fun t => u_first_deriv t y]
  exact u_second_deriv x y

theorem gap2 :
    ∀ x y, partialXOrder 3 u x y = 6 + 24 * x := by
  intro x y
  change deriv (deriv (deriv (fun t : ℝ => u t y))) x = _
  rw [show deriv (fun t : ℝ => u t y) =
      fun t => 1 + 2 * t + 2 * y + 3 * t ^ 2 - 6 * t * y +
        4 * t ^ 3 - 8 * t * y ^ 2 from
    funext fun t => u_first_deriv t y]
  rw [show deriv (fun t : ℝ =>
      1 + 2 * t + 2 * y + 3 * t ^ 2 - 6 * t * y +
        4 * t ^ 3 - 8 * t * y ^ 2) =
      fun t => 2 + 6 * t - 6 * y + 12 * t ^ 2 - 8 * y ^ 2 from
    funext fun t => u_second_deriv t y]
  exact u_third_deriv x y

theorem gap3 :
    ∀ x y, partialXOrder 4 u x y = 24 := by
  intro x y
  change deriv (deriv (deriv (deriv (fun t : ℝ => u t y)))) x = _
  rw [show deriv (fun t : ℝ => u t y) =
      fun t => 1 + 2 * t + 2 * y + 3 * t ^ 2 - 6 * t * y +
        4 * t ^ 3 - 8 * t * y ^ 2 from
    funext fun t => u_first_deriv t y]
  rw [show deriv (fun t : ℝ =>
      1 + 2 * t + 2 * y + 3 * t ^ 2 - 6 * t * y +
        4 * t ^ 3 - 8 * t * y ^ 2) =
      fun t => 2 + 6 * t - 6 * y + 12 * t ^ 2 - 8 * y ^ 2 from
    funext fun t => u_second_deriv t y]
  rw [show deriv (fun t : ℝ =>
      2 + 6 * t - 6 * y + 12 * t ^ 2 - 8 * y ^ 2) =
      fun t => 6 + 24 * t from
    funext fun t => u_third_deriv t y]
  exact u_fourth_deriv x

theorem gap4 :
    ∀ x y, mixedX3Y u x y = 0 := by
  intro x y
  unfold mixedX3Y
  rw [show (fun t : ℝ => partialXOrder 3 u x t) =
      fun _ : ℝ => 6 + 24 * x from
    funext fun t => gap2 x t]
  exact (hasDerivAt_const y (6 + 24 * x)).deriv

theorem gap5 :
    ∀ x y, mixedX2Y2 u x y = -16 := by
  intro x y
  unfold mixedX2Y2
  rw [show (fun s : ℝ => partialXOrder 2 u x s) =
      fun s => 2 + 6 * x - 6 * s + 12 * x ^ 2 - 8 * s ^ 2 from
    funext fun s => gap1 x s]
  rw [show deriv (fun s : ℝ =>
      2 + 6 * x - 6 * s + 12 * x ^ 2 - 8 * s ^ 2) =
      fun s => -6 - 16 * s from
    funext fun s => u_second_partial_y_first x s]
  exact u_second_partial_y_second y

end

end ProofGap.Exercise3256
