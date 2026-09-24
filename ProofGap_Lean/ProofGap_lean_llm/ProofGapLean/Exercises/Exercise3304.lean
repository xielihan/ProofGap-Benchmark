import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Shift

namespace ProofGap.Exercise3304

noncomputable section

abbrev RealFunction3 := ℝ → ℝ → ℝ → ℝ

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  (deriv^[n]) f

def nthDifferential (n : ℕ) (u : RealFunction3)
    (x y z dx dy dz : ℝ) : ℝ :=
  iterDeriv n
    (fun s => u (x + s * dx) (y + s * dy) (z + s * dz)) 0

def directionalOperator (dξ dη dζ : ℝ)
    (g : RealFunction3) : RealFunction3 :=
  fun ξ η ζ =>
    deriv (fun s => g (ξ + s * dξ) (η + s * dη) (ζ + s * dζ)) 0

def operatorPower (n : ℕ)
    (T : RealFunction3 → RealFunction3) (f : RealFunction3) : RealFunction3 :=
  (T^[n]) f

def uncurry₃ (f : RealFunction3) : ℝ × ℝ × ℝ → ℝ :=
  fun p => f p.1 p.2.1 p.2.2

private theorem deriv_line_eq_directional_line
    (g : RealFunction3) (x y z dx dy dz t : ℝ) :
    deriv (fun s => g (x + s * dx) (y + s * dy) (z + s * dz)) t =
      directionalOperator dx dy dz g
        (x + t * dx) (y + t * dy) (z + t * dz) := by
  unfold directionalOperator
  let h : ℝ → ℝ :=
    fun s => g (x + s * dx) (y + s * dy) (z + s * dz)
  have heq :
      (fun s =>
        g (x + t * dx + s * dx)
          (y + t * dy + s * dy)
          (z + t * dz + s * dz)) =
        fun s => h (t + s) := by
    funext s
    dsimp [h]
    congr 1 <;> ring
  rw [heq, deriv_comp_const_add]
  simp [h]

private theorem iterDeriv_line_eq_operatorPower
    (n : ℕ) (g : RealFunction3)
    (x y z dx dy dz : ℝ) :
    iterDeriv n
        (fun s => g (x + s * dx) (y + s * dy) (z + s * dz)) 0 =
      operatorPower n (directionalOperator dx dy dz) g x y z := by
  induction n generalizing g with
  | zero =>
      simp [iterDeriv, operatorPower]
  | succ n ih =>
      calc
        iterDeriv (n + 1)
            (fun s => g (x + s * dx) (y + s * dy) (z + s * dz)) 0 =
            iterDeriv n
              (deriv
                (fun s => g (x + s * dx) (y + s * dy) (z + s * dz))) 0 := by
              simp [iterDeriv, Function.iterate_succ_apply]
        _ = iterDeriv n
              (fun t =>
                directionalOperator dx dy dz g
                  (x + t * dx) (y + t * dy) (z + t * dz)) 0 := by
              congr 2
              funext t
              exact deriv_line_eq_directional_line g x y z dx dy dz t
        _ = operatorPower n (directionalOperator dx dy dz)
              (directionalOperator dx dy dz g) x y z :=
              ih (directionalOperator dx dy dz g)
        _ = operatorPower (n + 1) (directionalOperator dx dy dz) g x y z := by
              simp [operatorPower, Function.iterate_succ_apply]

theorem gap1 (u f ξ η ζ : RealFunction3)
    (a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ : ℝ)
    (hu : ∀ x y z, u x y z = f (ξ x y z) (η x y z) (ζ x y z))
    (hξ : ∀ x y z, ξ x y z = a₁ * x + b₁ * y + c₁ * z)
    (hη : ∀ x y z, η x y z = a₂ * x + b₂ * y + c₂ * z)
    (hζ : ∀ x y z, ζ x y z = a₃ * x + b₃ * y + c₃ * z)
    (n : ℕ) (hf : ContDiff ℝ n (uncurry₃ f))
    (x y z dx dy dz : ℝ) :
    nthDifferential n u x y z dx dy dz =
      operatorPower n
        (directionalOperator
          (a₁ * dx + b₁ * dy + c₁ * dz)
          (a₂ * dx + b₂ * dy + c₂ * dz)
          (a₃ * dx + b₃ * dy + c₃ * dz)) f
        (ξ x y z) (η x y z) (ζ x y z) := by
  unfold nthDifferential
  have hpath :
      (fun s => u (x + s * dx) (y + s * dy) (z + s * dz)) =
        fun s =>
          f
            (a₁ * x + b₁ * y + c₁ * z +
              s * (a₁ * dx + b₁ * dy + c₁ * dz))
            (a₂ * x + b₂ * y + c₂ * z +
              s * (a₂ * dx + b₂ * dy + c₂ * dz))
            (a₃ * x + b₃ * y + c₃ * z +
              s * (a₃ * dx + b₃ * dy + c₃ * dz)) := by
    funext s
    rw [hu, hξ, hη, hζ]
    congr 1 <;> ring
  rw [hpath, hξ, hη, hζ]
  exact iterDeriv_line_eq_operatorPower n f
    (a₁ * x + b₁ * y + c₁ * z)
    (a₂ * x + b₂ * y + c₂ * z)
    (a₃ * x + b₃ * y + c₃ * z)
    (a₁ * dx + b₁ * dy + c₁ * dz)
    (a₂ * dx + b₂ * dy + c₂ * dz)
    (a₃ * dx + b₃ * dy + c₃ * dz)

theorem gap2 (u f ξ η ζ : RealFunction3)
    (a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃ : ℝ)
    (hu : ∀ x y z, u x y z = f (ξ x y z) (η x y z) (ζ x y z))
    (hξ : ∀ x y z, ξ x y z = a₁ * x + b₁ * y + c₁ * z)
    (hη : ∀ x y z, η x y z = a₂ * x + b₂ * y + c₂ * z)
    (hζ : ∀ x y z, ζ x y z = a₃ * x + b₃ * y + c₃ * z)
    (n : ℕ) (hf : ContDiff ℝ n (uncurry₃ f))
    (x y z dx dy dz : ℝ) :
    nthDifferential n u x y z dx dy dz =
      operatorPower n
        (directionalOperator
          (dx * a₁ + dy * b₁ + dz * c₁)
          (dx * a₂ + dy * b₂ + dz * c₂)
          (dx * a₃ + dy * b₃ + dz * c₃)) f
        (ξ x y z) (η x y z) (ζ x y z) := by
  simpa [mul_comm] using
    gap1 u f ξ η ζ
      a₁ b₁ c₁ a₂ b₂ c₂ a₃ b₃ c₃
      hu hξ hη hζ n hf x y z dx dy dz

end

end ProofGap.Exercise3304
