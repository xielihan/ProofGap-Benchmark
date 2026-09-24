import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3388_1

noncomputable section

def surface (x y z : ℝ) : ℝ :=
  x ^ 2 + y ^ 2 + z ^ 2 - 3 * x * y * z

def objective (x y z : ℝ) : ℝ :=
  x * y ^ 2 * z ^ 3

def partialX₂ (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => g t y) x

def partialX₃ (g : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => g t y z) x

def partialZ₃ (g : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => g x y t) z

def restrictedByZ (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  objective x y (z x y)

private theorem surface_partials_at_unit :
    partialX₃ surface 1 1 1 = (-1 : ℝ) ∧
      partialZ₃ surface 1 1 1 = (-1 : ℝ) := by
  have hid : HasDerivAt (fun t : ℝ => t) 1 1 := by
    simpa using hasDerivAt_id (1 : ℝ)
  have hsquare : HasDerivAt (fun t : ℝ => t * t) 2 1 := by
    convert hid.mul hid using 1 <;>
      norm_num
  have hpoly :
      HasDerivAt (fun t : ℝ => t ^ 2 + 2 - 3 * t) (-1) 1 := by
    convert (hsquare.add_const 2).sub (hid.const_mul 3) using 1 <;>
      norm_num [pow_two]
    funext t
    rfl
  have hx : HasDerivAt (fun t => surface t 1 1) (-1) 1 := by
    convert hpoly using 1 <;>
      norm_num [surface, pow_two] <;>
      ring_nf
  have hz : HasDerivAt (fun t => surface 1 1 t) (-1) 1 := by
    convert hpoly using 1 <;>
      norm_num [surface, pow_two] <;>
      ring_nf
  constructor
  · simpa [partialX₃] using hx.deriv
  · simpa [partialZ₃] using hz.deriv

theorem gap1 (z : ℝ → ℝ → ℝ)
    (hzDiff : DifferentiableAt ℝ (fun t => z t 1) 1)
    (hzValue : z 1 1 = 1)
    (hSurface :
      ∀ᶠ t in nhds (1 : ℝ), surface t 1 (z t 1) = 0) :
    partialX₂ z 1 1 =
      -partialX₃ surface 1 1 1 / partialZ₃ surface 1 1 1 := by
  have hzDeriv :
      HasDerivAt (fun t => z t 1) (partialX₂ z 1 1) 1 := by
    simpa [partialX₂] using hzDiff.hasDerivAt
  have hid : HasDerivAt (fun t : ℝ => t) 1 1 := by
    simpa using hasDerivAt_id (1 : ℝ)
  have hxx : HasDerivAt (fun t : ℝ => t * t) 2 1 := by
    convert hid.mul hid using 1 <;>
      norm_num
  have hzz :
      HasDerivAt (fun t => z t 1 * z t 1)
        (2 * partialX₂ z 1 1) 1 := by
    convert hzDeriv.mul hzDeriv using 1 <;>
      simp [hzValue] <;>
      ring
  have hxz :
      HasDerivAt (fun t => t * z t 1)
        (1 + partialX₂ z 1 1) 1 := by
    convert hid.mul hzDeriv using 1 <;>
      simp [hzValue] <;>
      ring
  have hcalc :
      HasDerivAt (fun t => surface t 1 (z t 1))
        (-1 - partialX₂ z 1 1) 1 := by
    convert
      ((hxx.add_const 1).add hzz).sub (hxz.const_mul 3)
      using 1 <;>
      (try funext t) <;>
      (try simp [surface, pow_two]) <;>
      ring
  have hSurfaceZero :
      (fun _ : ℝ => (0 : ℝ)) =ᶠ[nhds (1 : ℝ)]
        (fun t => surface t 1 (z t 1)) := by
    filter_upwards [hSurface] with t ht
    exact ht.symm
  have hconst :
      HasDerivAt (fun _ : ℝ => (0 : ℝ))
        (-1 - partialX₂ z 1 1) 1 :=
    hcalc.congr_of_eventuallyEq hSurfaceZero
  have hu : -1 - partialX₂ z 1 1 = 0 :=
    hconst.unique (hasDerivAt_const (x := (1 : ℝ)) (c := (0 : ℝ)))
  have hd : partialX₂ z 1 1 = -1 := by
    linarith
  rcases surface_partials_at_unit with ⟨hx, hz⟩
  rw [hd, hx, hz]
  norm_num

theorem gap2 :
    -partialX₃ surface 1 1 1 / partialZ₃ surface 1 1 1 =
      (-1 : ℝ) := by
  rcases surface_partials_at_unit with ⟨hx, hz⟩
  rw [hx, hz]
  norm_num

theorem gap3 (z : ℝ → ℝ → ℝ)
    (hFormula :
      partialX₂ z 1 1 =
        -partialX₃ surface 1 1 1 / partialZ₃ surface 1 1 1)
    (hValue :
      -partialX₃ surface 1 1 1 / partialZ₃ surface 1 1 1 =
        (-1 : ℝ)) :
    partialX₂ z 1 1 = -1 := by
  exact hFormula.trans hValue

theorem gap4 (z : ℝ → ℝ → ℝ)
    (hzDeriv : HasDerivAt (fun t => z t 1) (-1) 1)
    (hzValue : z 1 1 = 1) :
    partialX₂ (restrictedByZ z) 1 1 = 1 + 3 * (-1 : ℝ) := by
  have hid : HasDerivAt (fun t : ℝ => t) 1 1 := by
    simpa using hasDerivAt_id (1 : ℝ)
  have hzSquare :
      HasDerivAt (fun t => z t 1 * z t 1) (-2) 1 := by
    convert hzDeriv.mul hzDeriv using 1 <;>
      norm_num [hzValue]
  have hzCube :
      HasDerivAt (fun t => (z t 1 * z t 1) * z t 1) (-3) 1 := by
    convert hzSquare.mul hzDeriv using 1 <;>
      norm_num [hzValue]
  have hproduct :
      HasDerivAt (fun t => t * ((z t 1 * z t 1) * z t 1)) (-2) 1 := by
    convert hid.mul hzCube using 1 <;>
      norm_num [hzValue]
  have hrestricted :
      HasDerivAt (fun t => restrictedByZ z t 1) (-2) 1 := by
    convert hproduct using 1 <;>
      simp [restrictedByZ, objective, pow_succ] <;>
      ring
  unfold partialX₂
  calc
    deriv (fun t => restrictedByZ z t 1) 1 = -2 := hrestricted.deriv
    _ = 1 + 3 * (-1 : ℝ) := by norm_num

theorem gap5 :
    (1 : ℝ) + 3 * (-1) = -2 := by
  norm_num

theorem gap6 (z : ℝ → ℝ → ℝ)
    (hChain :
      partialX₂ (restrictedByZ z) 1 1 = 1 + 3 * (-1 : ℝ))
    (hArithmetic : (1 : ℝ) + 3 * (-1) = -2) :
    partialX₂ (restrictedByZ z) 1 1 = -2 := by
  exact hChain.trans hArithmetic

end

end ProofGap.Exercise3388_1
