import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3270

noncomputable section

def u (x y : ℝ) : ℝ :=
  Real.sin (x ^ 2 + y ^ 2)

def iterDeriv (n : ℕ) (g : ℝ → ℝ) : ℝ → ℝ :=
  (deriv^[n]) g

def directional (n : ℕ) (x y dx dy : ℝ) : ℝ :=
  iterDeriv n (fun s => u (x + s * dx) (y + s * dy)) 0

def radialDifferential (x y dx dy : ℝ) : ℝ :=
  x * dx + y * dy

def squaredIncrement (dx dy : ℝ) : ℝ :=
  dx ^ 2 + dy ^ 2

def firstExpanded (x y dx dy : ℝ) : ℝ :=
  2 * x * Real.cos (x ^ 2 + y ^ 2) * dx +
    2 * y * Real.cos (x ^ 2 + y ^ 2) * dy

def firstFactored (x y dx dy : ℝ) : ℝ :=
  2 * radialDifferential x y dx dy * Real.cos (x ^ 2 + y ^ 2)

def secondForm (x y dx dy : ℝ) : ℝ :=
  -4 * Real.sin (x ^ 2 + y ^ 2) *
      radialDifferential x y dx dy ^ 2 +
    2 * Real.cos (x ^ 2 + y ^ 2) * squaredIncrement dx dy

def thirdRaw (x y dx dy : ℝ) : ℝ :=
  -8 * Real.cos (x ^ 2 + y ^ 2) *
      radialDifferential x y dx dy ^ 3 -
    8 * Real.sin (x ^ 2 + y ^ 2) *
      radialDifferential x y dx dy * squaredIncrement dx dy -
    4 * Real.sin (x ^ 2 + y ^ 2) *
      radialDifferential x y dx dy * squaredIncrement dx dy

def thirdCombined (x y dx dy : ℝ) : ℝ :=
  -8 * Real.cos (x ^ 2 + y ^ 2) *
      radialDifferential x y dx dy ^ 3 -
    12 * Real.sin (x ^ 2 + y ^ 2) *
      radialDifferential x y dx dy * squaredIncrement dx dy

private theorem derivativeForms (x y dx dy : ℝ) :
    directional 1 x y dx dy = firstFactored x y dx dy ∧
      directional 2 x y dx dy = secondForm x y dx dy ∧
      directional 3 x y dx dy = thirdCombined x y dx dy := by
  let q : ℝ → ℝ := fun s => (x + s * dx) ^ 2 + (y + s * dy) ^ 2
  let a : ℝ → ℝ := fun s =>
    radialDifferential x y dx dy + s * squaredIncrement dx dy
  let f : ℝ → ℝ := fun s => u (x + s * dx) (y + s * dy)
  let d1 : ℝ → ℝ := fun s =>
    2 * a s * Real.cos (q s)
  let d2 : ℝ → ℝ := fun s =>
    -4 * Real.sin (q s) * a s ^ 2 +
      2 * Real.cos (q s) * squaredIncrement dx dy
  let d3 : ℝ → ℝ := fun s =>
    -8 * Real.cos (q s) * a s ^ 3 -
      12 * Real.sin (q s) * a s * squaredIncrement dx dy
  have hx (s : ℝ) :
      HasDerivAt (fun t : ℝ => x + t * dx) dx s := by
    simpa [id] using
      (((hasDerivAt_id s).mul_const dx).const_add x)
  have hy (s : ℝ) :
      HasDerivAt (fun t : ℝ => y + t * dy) dy s := by
    simpa [id] using
      (((hasDerivAt_id s).mul_const dy).const_add y)
  have ha (s : ℝ) :
      HasDerivAt a (squaredIncrement dx dy) s := by
    change HasDerivAt
      (fun t : ℝ => radialDifferential x y dx dy +
        t * squaredIncrement dx dy)
      (squaredIncrement dx dy) s
    simpa [id] using
      (((hasDerivAt_id s).mul_const (squaredIncrement dx dy)).const_add
        (radialDifferential x y dx dy))
  have hq (s : ℝ) : HasDerivAt q (2 * a s) s := by
    convert ((hx s).pow 2).add ((hy s).pow 2) using 1 <;>
      simp [a, radialDifferential, squaredIncrement] <;> ring
  have h1 (s : ℝ) : HasDerivAt f (d1 s) s := by
    convert (Real.hasDerivAt_sin (q s)).comp s (hq s) using 1 <;>
      simp [f, d1, q, u] <;> ring
  have h2 (s : ℝ) : HasDerivAt d1 (d2 s) s := by
    convert
      ((ha s).const_mul 2).mul
        ((Real.hasDerivAt_cos (q s)).comp s (hq s))
      using 1 <;> simp [d1, d2] <;> ring
  have h3 (s : ℝ) : HasDerivAt d2 (d3 s) s := by
    convert
      (((((Real.hasDerivAt_sin (q s)).comp s (hq s)).const_mul (-4)).mul
          ((ha s).pow 2)).add
        ((((Real.hasDerivAt_cos (q s)).comp s (hq s)).const_mul 2).mul_const
          (squaredIncrement dx dy)))
      using 1 <;> simp [d2, d3] <;> ring
  have hf1 : deriv f = d1 := funext fun s => (h1 s).deriv
  have hf2 : deriv d1 = d2 := funext fun s => (h2 s).deriv
  have e1 : directional 1 x y dx dy = d1 0 := by
    change deriv f 0 = d1 0
    exact (h1 0).deriv
  have e2 : directional 2 x y dx dy = d2 0 := by
    change deriv (deriv f) 0 = d2 0
    rw [hf1]
    exact (h2 0).deriv
  have e3 : directional 3 x y dx dy = d3 0 := by
    change deriv (deriv (deriv f)) 0 = d3 0
    rw [hf1, hf2]
    exact (h3 0).deriv
  constructor
  · calc
      directional 1 x y dx dy = d1 0 := e1
      _ = firstFactored x y dx dy := by
        simp [d1, a, q, firstFactored]
  constructor
  · calc
      directional 2 x y dx dy = d2 0 := e2
      _ = secondForm x y dx dy := by
        simp [d2, a, q, secondForm]
  · calc
      directional 3 x y dx dy = d3 0 := e3
      _ = thirdCombined x y dx dy := by
        simp [d3, a, q, thirdCombined]

theorem gap1 (x y dx dy : ℝ) :
    directional 1 x y dx dy = firstExpanded x y dx dy := by
  calc
    directional 1 x y dx dy = firstFactored x y dx dy :=
      (derivativeForms x y dx dy).1
    _ = firstExpanded x y dx dy := by
      unfold firstFactored firstExpanded radialDifferential
      ring

theorem gap2 (x y dx dy : ℝ) :
    firstExpanded x y dx dy = firstFactored x y dx dy := by
  unfold firstExpanded firstFactored radialDifferential
  ring

theorem gap3 (x y dx dy : ℝ) :
    directional 1 x y dx dy = firstFactored x y dx dy := by
  rw [gap1 x y dx dy, gap2 x y dx dy]

theorem gap4 (x y dx dy : ℝ) :
    directional 2 x y dx dy = secondForm x y dx dy := by
  exact (derivativeForms x y dx dy).2.1

theorem gap5 (x y dx dy : ℝ) :
    directional 3 x y dx dy = thirdRaw x y dx dy := by
  calc
    directional 3 x y dx dy = thirdCombined x y dx dy :=
      (derivativeForms x y dx dy).2.2
    _ = thirdRaw x y dx dy := by
      unfold thirdCombined thirdRaw
      ring

theorem gap6 (x y dx dy : ℝ) :
    directional 3 x y dx dy = thirdCombined x y dx dy := by
  exact (derivativeForms x y dx dy).2.2

end

end ProofGap.Exercise3270
