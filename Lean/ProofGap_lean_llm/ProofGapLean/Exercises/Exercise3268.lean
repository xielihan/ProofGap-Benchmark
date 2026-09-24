import ProofGapLean.Prelude.Discrete
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3268

noncomputable section

def u (x y : ℝ) : ℝ :=
  x ^ 4 - 2 * x ^ 3 * y - 2 * x * y ^ 3 + y ^ 4 +
    x ^ 3 - 3 * x ^ 2 * y - 3 * x * y ^ 2 + y ^ 3 +
    2 * x ^ 2 - x * y + 2 * y ^ 2 + x + y + 1

def iterDeriv (n : ℕ) (g : ℝ → ℝ) : ℝ → ℝ :=
  (deriv^[n]) g

def partialXOrder (m : ℕ) (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  iterDeriv m (fun t => g t y) x

def partialYOrder (n : ℕ) (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  iterDeriv n (fun t => g x t) y

def mixedOrder (m n : ℕ) (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  partialYOrder n (fun a b => partialXOrder m g a b) x y

def fourthDirectional (x y dx dy : ℝ) : ℝ :=
  iterDeriv 4 (fun s => u (x + s * dx) (y + s * dy)) 0

def rawFourth (dx dy : ℝ) : ℝ :=
  24 * dx ^ 4 -
    2 * (Nat.choose 4 1 : ℝ) * (6 * dx ^ 3) * dy -
    2 * (Nat.choose 4 1 : ℝ) * dx * (6 * dy ^ 3) +
    24 * dy ^ 4

def simplifiedFourth (dx dy : ℝ) : ℝ :=
  24 * (dx ^ 4 - 2 * dx ^ 3 * dy - 2 * dx * dy ^ 3 + dy ^ 4)

private def quartic (a0 a1 a2 a3 a4 : ℝ) (t : ℝ) : ℝ :=
  a0 + a1 * t + a2 * (t * t) + a3 * ((t * t) * t) +
    a4 * (((t * t) * t) * t)

private theorem deriv_quartic (a0 a1 a2 a3 a4 : ℝ) :
    deriv (quartic a0 a1 a2 a3 a4) =
      quartic a1 (2 * a2) (3 * a3) (4 * a4) 0 := by
  funext t
  unfold quartic
  have h2 := (hasDerivAt_id t).mul (hasDerivAt_id t)
  have h3 := h2.mul (hasDerivAt_id t)
  have h4 := h3.mul (hasDerivAt_id t)
  have h :=
    ((((hasDerivAt_const t a0).add
      ((hasDerivAt_const t a1).mul (hasDerivAt_id t))).add
      ((hasDerivAt_const t a2).mul h2)).add
      ((hasDerivAt_const t a3).mul h3)).add
      ((hasDerivAt_const t a4).mul h4)
  convert h.deriv using 1 <;> simp [id] <;> ring

private theorem u_in_first (y : ℝ) :
    (fun x : ℝ => u x y) =
      quartic
        (y ^ 4 + y ^ 3 + 2 * y ^ 2 + y + 1)
        (-2 * y ^ 3 - 3 * y ^ 2 - y + 1)
        (-3 * y + 2) (-2 * y + 1) 1 := by
  funext x
  unfold u quartic
  ring

private theorem u_in_second (x : ℝ) :
    (fun y : ℝ => u x y) =
      quartic
        (x ^ 4 + x ^ 3 + 2 * x ^ 2 + x + 1)
        (-2 * x ^ 3 - 3 * x ^ 2 - x + 1)
        (-3 * x + 2) (-2 * x + 1) 1 := by
  funext y
  unfold u quartic
  ring

theorem gap1 (x y dx dy : ℝ) :
    fourthDirectional x y dx dy = rawFourth dx dy := by
  let q : ℝ := dx ^ 4 - 2 * dx ^ 3 * dy - 2 * dx * dy ^ 3 + dy ^ 4
  let f0 : ℝ := u x y
  let fp : ℝ := u (x + dx) (y + dy)
  let fm : ℝ := u (x - dx) (y - dy)
  let f2 : ℝ := u (x + 2 * dx) (y + 2 * dy)
  let a2 : ℝ := (fp + fm) / 2 - f0 - q
  let a3 : ℝ := (f2 - f0 - 4 * a2 - 16 * q - (fp - fm)) / 6
  let a1 : ℝ := (fp - fm) / 2 - a3
  have hline :
      (fun s : ℝ => u (x + s * dx) (y + s * dy)) =
        quartic f0 a1 a2 a3 q := by
    funext s
    dsimp [f0, fp, fm, f2, a1, a2, a3, q]
    unfold u quartic
    ring
  unfold fourthDirectional iterDeriv
  change deriv (deriv (deriv (deriv (fun s : ℝ =>
    u (x + s * dx) (y + s * dy))))) 0 = rawFourth dx dy
  rw [hline, deriv_quartic, deriv_quartic, deriv_quartic, deriv_quartic]
  norm_num [quartic, rawFourth, q] <;> ring

theorem gap2 (dx dy : ℝ) :
    rawFourth dx dy = simplifiedFourth dx dy := by
  norm_num [rawFourth, simplifiedFourth]
  <;> ring

theorem gap3 (x y dx dy : ℝ) :
    fourthDirectional x y dx dy = simplifiedFourth dx dy := by
  rw [gap1, gap2]

theorem gap4 :
    ∀ x y, partialXOrder 4 u x y = 24 := by
  intro x y
  unfold partialXOrder iterDeriv
  change deriv (deriv (deriv (deriv (fun t : ℝ => u t y)))) x = 24
  rw [u_in_first y, deriv_quartic, deriv_quartic, deriv_quartic,
    deriv_quartic]
  norm_num [quartic]

theorem gap5 :
    ∀ x y, mixedOrder 3 1 u x y = -12 := by
  intro x y
  unfold mixedOrder partialYOrder partialXOrder iterDeriv
  change deriv (fun t : ℝ =>
    deriv (deriv (deriv (fun z : ℝ => u z t))) x) y = -12
  have h :
      (fun t : ℝ => deriv (deriv (deriv (fun z : ℝ => u z t))) x) =
        quartic (6 + 24 * x) (-12) 0 0 0 := by
    funext t
    rw [u_in_first t, deriv_quartic, deriv_quartic, deriv_quartic]
    unfold quartic
    ring
  rw [h, deriv_quartic]
  norm_num [quartic]

theorem gap6 :
    ∀ x y, mixedOrder 2 2 u x y = 0 := by
  intro x y
  unfold mixedOrder partialYOrder partialXOrder iterDeriv
  change deriv (deriv (fun t : ℝ =>
    deriv (deriv (fun z : ℝ => u z t)) x)) y = 0
  have h :
      (fun t : ℝ => deriv (deriv (fun z : ℝ => u z t)) x) =
        quartic (4 + 6 * x + 12 * x ^ 2) (-6 - 12 * x) 0 0 0 := by
    funext t
    rw [u_in_first t, deriv_quartic, deriv_quartic]
    unfold quartic
    ring
  rw [h, deriv_quartic, deriv_quartic]
  norm_num [quartic]

theorem gap7 :
    ∀ x y, mixedOrder 1 3 u x y = -12 := by
  intro x y
  unfold mixedOrder partialYOrder partialXOrder iterDeriv
  change deriv (deriv (deriv (fun t : ℝ =>
    deriv (fun z : ℝ => u z t) x))) y = -12
  have h :
      (fun t : ℝ => deriv (fun z : ℝ => u z t) x) =
        quartic
          (1 + 4 * x + 3 * x ^ 2 + 4 * x ^ 3)
          (-1 - 6 * x - 6 * x ^ 2) (-3) (-2) 0 := by
    funext t
    rw [u_in_first t, deriv_quartic]
    unfold quartic
    ring
  rw [h, deriv_quartic, deriv_quartic, deriv_quartic]
  norm_num [quartic]

theorem gap8 :
    ∀ x y, partialYOrder 4 u x y = 24 := by
  intro x y
  unfold partialYOrder iterDeriv
  change deriv (deriv (deriv (deriv (fun t : ℝ => u x t)))) y = 24
  rw [u_in_second x, deriv_quartic, deriv_quartic, deriv_quartic,
    deriv_quartic]
  norm_num [quartic]

end

end ProofGap.Exercise3268
