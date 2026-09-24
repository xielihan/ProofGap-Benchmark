import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1173

noncomputable section

def nthDeriv : ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0, f => f
  | n + 1, f => deriv (nthDeriv n f)

def y (x : ℝ) : ℝ := x * Real.cos (2 * x)
def differential (n : ℕ) (f : ℝ → ℝ) (x dx : ℝ) : ℝ :=
  nthDeriv n f x * dx ^ n

def phased10 (x : ℝ) : ℝ :=
  2 ^ 10 * x * Real.cos (2 * x + (10 : ℝ) * Real.pi / 2) +
    10 * 2 ^ 9 * Real.cos (2 * x + (9 / 2 : ℝ) * Real.pi)

private theorem tenth_derivative_y (x : ℝ) :
    nthDeriv 10 y x =
      -1024 * (x * Real.cos (2 * x) + 5 * Real.sin (2 * x)) := by
  have hcos (z : ℝ) :
      HasDerivAt (fun t : ℝ => Real.cos (2 * t))
        (-2 * Real.sin (2 * z)) z := by
    convert
      ((Real.hasDerivAt_cos (2 * z)).comp z
        ((hasDerivAt_id z).const_mul 2)) using 1 <;>
      (try funext t) <;> ring
  have hsin (z : ℝ) :
      HasDerivAt (fun t : ℝ => Real.sin (2 * t))
        (2 * Real.cos (2 * z)) z := by
    convert
      ((Real.hasDerivAt_sin (2 * z)).comp z
        ((hasDerivAt_id z).const_mul 2)) using 1 <;>
      (try funext t) <;> ring
  have hxcos (z : ℝ) :
      HasDerivAt (fun t : ℝ => t * Real.cos (2 * t))
        (Real.cos (2 * z) - 2 * z * Real.sin (2 * z)) z := by
    convert ((hasDerivAt_id z).mul (hcos z)) using 1 <;>
      (try simp only [id_eq]) <;> (try funext t) <;> ring_nf
  have hxsin (z : ℝ) :
      HasDerivAt (fun t : ℝ => t * Real.sin (2 * t))
        (Real.sin (2 * z) + 2 * z * Real.cos (2 * z)) z := by
    convert ((hasDerivAt_id z).mul (hsin z)) using 1 <;>
      (try simp only [id_eq]) <;> (try funext t) <;> ring_nf
  have h1 :
      nthDeriv 1 y =
        fun t : ℝ => Real.cos (2 * t) - 2 * t * Real.sin (2 * t) := by
    funext z
    change deriv (fun t : ℝ => t * Real.cos (2 * t)) z = _
    exact (hxcos z).deriv
  have h2 :
      nthDeriv 2 y =
        fun t : ℝ => -4 * Real.sin (2 * t) - 4 * t * Real.cos (2 * t) := by
    funext z
    change deriv (nthDeriv 1 y) z = _
    rw [h1]
    have hd :
        HasDerivAt
          (fun t : ℝ => Real.cos (2 * t) - 2 * t * Real.sin (2 * t))
          (-4 * Real.sin (2 * z) - 4 * z * Real.cos (2 * z)) z := by
      convert
        ((hcos z).sub ((hxsin z).const_mul 2)) using 1 <;>
        (try funext t) <;>
        (try simp only [Pi.sub_apply, Pi.add_apply]) <;> ring_nf
    exact hd.deriv
  have h3 :
      nthDeriv 3 y =
        fun t : ℝ => -12 * Real.cos (2 * t) + 8 * t * Real.sin (2 * t) := by
    funext z
    change deriv (nthDeriv 2 y) z = _
    rw [h2]
    have hd :
        HasDerivAt
          (fun t : ℝ => -4 * Real.sin (2 * t) - 4 * t * Real.cos (2 * t))
          (-12 * Real.cos (2 * z) + 8 * z * Real.sin (2 * z)) z := by
      convert
        (((hsin z).const_mul (-4)).sub ((hxcos z).const_mul 4)) using 1 <;>
        (try funext t) <;>
        (try simp only [Pi.sub_apply, Pi.add_apply]) <;> ring_nf
    exact hd.deriv
  have h4 :
      nthDeriv 4 y =
        fun t : ℝ => 32 * Real.sin (2 * t) + 16 * t * Real.cos (2 * t) := by
    funext z
    change deriv (nthDeriv 3 y) z = _
    rw [h3]
    have hd :
        HasDerivAt
          (fun t : ℝ => -12 * Real.cos (2 * t) + 8 * t * Real.sin (2 * t))
          (32 * Real.sin (2 * z) + 16 * z * Real.cos (2 * z)) z := by
      convert
        (((hcos z).const_mul (-12)).add ((hxsin z).const_mul 8)) using 1 <;>
        (try funext t) <;>
        (try simp only [Pi.sub_apply, Pi.add_apply]) <;> ring_nf
    exact hd.deriv
  have h5 :
      nthDeriv 5 y =
        fun t : ℝ => 80 * Real.cos (2 * t) - 32 * t * Real.sin (2 * t) := by
    funext z
    change deriv (nthDeriv 4 y) z = _
    rw [h4]
    have hd :
        HasDerivAt
          (fun t : ℝ => 32 * Real.sin (2 * t) + 16 * t * Real.cos (2 * t))
          (80 * Real.cos (2 * z) - 32 * z * Real.sin (2 * z)) z := by
      convert
        (((hsin z).const_mul 32).add ((hxcos z).const_mul 16)) using 1 <;>
        (try funext t) <;>
        (try simp only [Pi.sub_apply, Pi.add_apply]) <;> ring_nf
    exact hd.deriv
  have h6 :
      nthDeriv 6 y =
        fun t : ℝ => -192 * Real.sin (2 * t) - 64 * t * Real.cos (2 * t) := by
    funext z
    change deriv (nthDeriv 5 y) z = _
    rw [h5]
    have hd :
        HasDerivAt
          (fun t : ℝ => 80 * Real.cos (2 * t) - 32 * t * Real.sin (2 * t))
          (-192 * Real.sin (2 * z) - 64 * z * Real.cos (2 * z)) z := by
      convert
        (((hcos z).const_mul 80).sub ((hxsin z).const_mul 32)) using 1 <;>
        (try funext t) <;>
        (try simp only [Pi.sub_apply, Pi.add_apply]) <;> ring_nf
    exact hd.deriv
  have h7 :
      nthDeriv 7 y =
        fun t : ℝ => -448 * Real.cos (2 * t) + 128 * t * Real.sin (2 * t) := by
    funext z
    change deriv (nthDeriv 6 y) z = _
    rw [h6]
    have hd :
        HasDerivAt
          (fun t : ℝ => -192 * Real.sin (2 * t) - 64 * t * Real.cos (2 * t))
          (-448 * Real.cos (2 * z) + 128 * z * Real.sin (2 * z)) z := by
      convert
        (((hsin z).const_mul (-192)).sub ((hxcos z).const_mul 64)) using 1 <;>
        (try funext t) <;>
        (try simp only [Pi.sub_apply, Pi.add_apply]) <;> ring_nf
    exact hd.deriv
  have h8 :
      nthDeriv 8 y =
        fun t : ℝ => 1024 * Real.sin (2 * t) + 256 * t * Real.cos (2 * t) := by
    funext z
    change deriv (nthDeriv 7 y) z = _
    rw [h7]
    have hd :
        HasDerivAt
          (fun t : ℝ => -448 * Real.cos (2 * t) + 128 * t * Real.sin (2 * t))
          (1024 * Real.sin (2 * z) + 256 * z * Real.cos (2 * z)) z := by
      convert
        (((hcos z).const_mul (-448)).add ((hxsin z).const_mul 128)) using 1 <;>
        (try funext t) <;>
        (try simp only [Pi.sub_apply, Pi.add_apply]) <;> ring_nf
    exact hd.deriv
  have h9 :
      nthDeriv 9 y =
        fun t : ℝ => 2304 * Real.cos (2 * t) - 512 * t * Real.sin (2 * t) := by
    funext z
    change deriv (nthDeriv 8 y) z = _
    rw [h8]
    have hd :
        HasDerivAt
          (fun t : ℝ => 1024 * Real.sin (2 * t) + 256 * t * Real.cos (2 * t))
          (2304 * Real.cos (2 * z) - 512 * z * Real.sin (2 * z)) z := by
      convert
        (((hsin z).const_mul 1024).add ((hxcos z).const_mul 256)) using 1 <;>
        (try funext t) <;>
        (try simp only [Pi.sub_apply, Pi.add_apply]) <;> ring_nf
    exact hd.deriv
  have h10 :
      nthDeriv 10 y =
        fun t : ℝ =>
          -1024 * (t * Real.cos (2 * t) + 5 * Real.sin (2 * t)) := by
    funext z
    change deriv (nthDeriv 9 y) z = _
    rw [h9]
    have hd :
        HasDerivAt
          (fun t : ℝ => 2304 * Real.cos (2 * t) - 512 * t * Real.sin (2 * t))
          (-1024 * (z * Real.cos (2 * z) + 5 * Real.sin (2 * z))) z := by
      convert
        (((hcos z).const_mul 2304).sub ((hxsin z).const_mul 512)) using 1 <;>
        (try funext t) <;>
        (try simp only [Pi.sub_apply, Pi.add_apply]) <;> ring_nf
    exact hd.deriv
  exact congrFun h10 x

theorem gap1 (x dx : ℝ) :
    differential 10 y x dx = nthDeriv 10 y x * dx ^ 10 := by
  rfl

theorem gap2 (x dx : ℝ) :
    nthDeriv 10 y x * dx ^ 10 =
      phased10 x * dx ^ 10 := by
  have hphase :
      phased10 x =
        -1024 * (x * Real.cos (2 * x) + 5 * Real.sin (2 * x)) := by
    unfold phased10
    have h10 :
        (10 : ℝ) * Real.pi / 2 =
          Real.pi + Real.pi + Real.pi + Real.pi + Real.pi := by
      ring
    have h9 :
        (9 / 2 : ℝ) * Real.pi =
          Real.pi + Real.pi + Real.pi + Real.pi + Real.pi / 2 := by
      ring
    rw [h10, h9]
    simp [Real.cos_add, Real.sin_add] <;> ring
  rw [tenth_derivative_y, hphase]

theorem gap3 (x dx : ℝ) :
    differential 10 y x dx = phased10 x * dx ^ 10 := by
  calc
    differential 10 y x dx = nthDeriv 10 y x * dx ^ 10 := gap1 x dx
    _ = phased10 x * dx ^ 10 := gap2 x dx

theorem gap4 (x dx : ℝ) :
    differential 10 y x dx =
      -1024 * (x * Real.cos (2 * x) + 5 * Real.sin (2 * x)) *
        dx ^ 10 := by
  rw [gap1, tenth_derivative_y]

end

end ProofGap.Exercise1173
