import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise3388_2

noncomputable section

def surface (x y z : ℝ) : ℝ :=
  x ^ 2 + y ^ 2 + z ^ 2 - 3 * x * y * z

def objective (x y z : ℝ) : ℝ :=
  x * y ^ 2 * z ^ 3

def partialX₂ (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => g t y) x

def partialX₃ (g : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => g t y z) x

def partialY₃ (g : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => g x t z) y

def restrictedByY (y : ℝ → ℝ → ℝ) (x z : ℝ) : ℝ :=
  objective x (y x z) z

private theorem surface_partials_at_one :
    partialX₃ surface 1 1 1 = (-1 : ℝ) ∧
      partialY₃ surface 1 1 1 = (-1 : ℝ) := by
  constructor
  · have h : HasDerivAt (fun t : ℝ => surface t 1 1) (-1) 1 := by
      have hId := hasDerivAt_id (1 : ℝ)
      have hIdSq := hId.mul hId
      have hOne := hasDerivAt_const (1 : ℝ) (1 : ℝ)
      have hThree := hasDerivAt_const (1 : ℝ) (3 : ℝ)
      have hProduct := (((hThree.mul hId).mul hOne).mul hOne)
      have hRaw := ((hIdSq.add hOne).add hOne).sub hProduct
      convert hRaw using 1
      · funext t
        simp [surface] <;> ring
      · norm_num
    change deriv (fun t : ℝ => surface t 1 1) 1 = -1
    exact h.deriv
  · have h : HasDerivAt (fun t : ℝ => surface 1 t 1) (-1) 1 := by
      have hId := hasDerivAt_id (1 : ℝ)
      have hIdSq := hId.mul hId
      have hOne := hasDerivAt_const (1 : ℝ) (1 : ℝ)
      have hThree := hasDerivAt_const (1 : ℝ) (3 : ℝ)
      have hProduct := (((hThree.mul hOne).mul hId).mul hOne)
      have hRaw := ((hOne.add hIdSq).add hOne).sub hProduct
      convert hRaw using 1
      · funext t
        simp [surface] <;> ring
      · norm_num
    change deriv (fun t : ℝ => surface 1 t 1) 1 = -1
    exact h.deriv

theorem gap1 (y : ℝ → ℝ → ℝ)
    (hyDiff : DifferentiableAt ℝ (fun t => y t 1) 1)
    (hyValue : y 1 1 = 1)
    (hSurface :
      ∀ᶠ t in nhds (1 : ℝ), surface t (y t 1) 1 = 0) :
    partialX₂ y 1 1 =
      -partialX₃ surface 1 1 1 / partialY₃ surface 1 1 1 := by
  have hyDeriv :
      HasDerivAt (fun t => y t 1) (partialX₂ y 1 1) 1 := by
    simpa [partialX₂] using hyDiff.hasDerivAt
  have hsDeriv :
      HasDerivAt (fun t => surface t (y t 1) 1)
        (-1 - partialX₂ y 1 1) 1 := by
    have hId := hasDerivAt_id (1 : ℝ)
    have hX := hId.mul hId
    have hY := hyDeriv.mul hyDeriv
    have hOne := hasDerivAt_const (1 : ℝ) (1 : ℝ)
    have hThree := hasDerivAt_const (1 : ℝ) (3 : ℝ)
    have hProduct := (((hThree.mul hId).mul hyDeriv).mul hOne)
    have hRaw := ((hX.add hY).add hOne).sub hProduct
    convert hRaw using 1
    · funext t
      simp [surface] <;> ring
    · simp [hyValue] <;> ring
  have hsZero :
      HasDerivAt (fun t => surface t (y t 1) 1) 0 1 := by
    exact
      (hasDerivAt_const (1 : ℝ) (0 : ℝ)).congr_of_eventuallyEq hSurface
  have hySlope : partialX₂ y 1 1 = -1 := by
    linarith [hsDeriv.unique hsZero]
  rw [hySlope, surface_partials_at_one.1, surface_partials_at_one.2]
  norm_num

theorem gap2 :
    -partialX₃ surface 1 1 1 / partialY₃ surface 1 1 1 =
      (-1 : ℝ) := by
  rw [surface_partials_at_one.1, surface_partials_at_one.2]
  norm_num

theorem gap3 (y : ℝ → ℝ → ℝ)
    (hFormula :
      partialX₂ y 1 1 =
        -partialX₃ surface 1 1 1 / partialY₃ surface 1 1 1)
    (hValue :
      -partialX₃ surface 1 1 1 / partialY₃ surface 1 1 1 =
        (-1 : ℝ)) :
    partialX₂ y 1 1 = -1 := by
  exact hFormula.trans hValue

theorem gap4 (y : ℝ → ℝ → ℝ)
    (hyDeriv : HasDerivAt (fun t => y t 1) (-1) 1)
    (hyValue : y 1 1 = 1) :
    partialX₂ (restrictedByY y) 1 1 = 1 + 2 * (-1 : ℝ) := by
  have hX := hasDerivAt_id (1 : ℝ)
  have hY := hyDeriv.mul hyDeriv
  have hRaw := hX.mul hY
  have h :
      HasDerivAt (fun t => restrictedByY y t 1)
        (1 + 2 * (-1 : ℝ)) 1 := by
    convert hRaw using 1
    · funext t
      change
        t * (y t 1) ^ 2 * (1 : ℝ) ^ 3 =
          t * (y t 1 * y t 1)
      simp only [pow_two, one_pow, mul_one]
    · simp [hyValue] <;> ring
  simpa [partialX₂] using h.deriv

theorem gap5 :
    (1 : ℝ) + 2 * (-1) = -1 := by
  norm_num

theorem gap6 (y : ℝ → ℝ → ℝ)
    (hChain :
      partialX₂ (restrictedByY y) 1 1 = 1 + 2 * (-1 : ℝ))
    (hArithmetic : (1 : ℝ) + 2 * (-1) = -1) :
    partialX₂ (restrictedByY y) 1 1 = -1 := by
  exact hChain.trans hArithmetic

end

end ProofGap.Exercise3388_2
