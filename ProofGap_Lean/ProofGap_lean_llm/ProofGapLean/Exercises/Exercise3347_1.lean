import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

namespace ProofGap.Exercise3347_1

noncomputable section

abbrev Vec3 := ℝ × ℝ × ℝ

def vec3 (x y z : ℝ) : Vec3 :=
  (x, y, z)

def dot (p q : Vec3) : ℝ :=
  p.1 * q.1 + p.2.1 * q.2.1 + p.2.2 * q.2.2

def norm (p : Vec3) : ℝ :=
  Real.sqrt (dot p p)

def angle (p q : Vec3) : ℝ :=
  Real.arccos (dot p q / (norm p * norm q))

def u (x y z : ℝ) : ℝ :=
  x ^ 2 + y ^ 2 - z ^ 2

def partialX (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun s => f s y z) x

def partialY (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun s => f x s z) y

def partialZ (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun s => f x y s) z

def grad (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : Vec3 :=
  vec3 (partialX f x y z) (partialY f x y z) (partialZ f x y z)

def A (ε : ℝ) : Vec3 :=
  vec3 ε 0 0

def B (ε : ℝ) : Vec3 :=
  vec3 0 ε 0

def gradAt (f : ℝ → ℝ → ℝ → ℝ) (p : Vec3) : Vec3 :=
  grad f p.1 p.2.1 p.2.2

theorem gap1 :
    ∀ x y z,
      grad u x y z =
        vec3 (partialX u x y z) (partialY u x y z) (partialZ u x y z) := by
  intro x y z
  rfl

theorem gap2 :
    ∀ x y z, grad u x y z = vec3 (2 * x) (2 * y) (-2 * z) := by
  intro x y z
  have hx : HasDerivAt (fun s : ℝ => u s y z) (2 * x) x := by
    convert
      (((hasDerivAt_id x).mul (hasDerivAt_id x)).add
        (hasDerivAt_const x (y ^ 2))).sub
        (hasDerivAt_const x (z ^ 2)) using 1 <;>
      simp [u, pow_two, two_mul]
    funext s
    rfl
  have hy : HasDerivAt (fun s : ℝ => u x s z) (2 * y) y := by
    convert
      (((hasDerivAt_const y (x ^ 2)).add
        ((hasDerivAt_id y).mul (hasDerivAt_id y))).sub
        (hasDerivAt_const y (z ^ 2))) using 1 <;>
      simp [u, pow_two, two_mul]
    funext s
    rfl
  have hz : HasDerivAt (fun s : ℝ => u x y s) (-2 * z) z := by
    convert
      (((hasDerivAt_const z (x ^ 2)).add
        (hasDerivAt_const z (y ^ 2))).sub
        ((hasDerivAt_id z).mul (hasDerivAt_id z))) using 1 <;>
      simp [u, pow_two, two_mul]
    funext s
    rfl
  change
    vec3 (deriv (fun s => u s y z) x)
      (deriv (fun s => u x s z) y)
      (deriv (fun s => u x y s) z) =
      vec3 (2 * x) (2 * y) (-2 * z)
  rw [hx.deriv, hy.deriv, hz.deriv]

theorem gap3 :
    (fun p : Vec3 => gradAt u p) =
      fun p => vec3 (2 * p.1) (2 * p.2.1) (-2 * p.2.2) := by
  funext p
  simpa [gradAt] using (gap2 p.1 p.2.1 p.2.2)

theorem gap4 (ε : ℝ) :
    gradAt u (A ε) = vec3 (2 * ε) 0 0 := by
  simpa [gradAt, A, vec3] using (gap2 ε 0 0)

theorem gap5 (ε : ℝ) :
    gradAt u (B ε) = vec3 0 (2 * ε) 0 := by
  simpa [gradAt, B, vec3] using (gap2 0 ε 0)

theorem gap6 (ε : ℝ) :
    dot (gradAt u (A ε)) (gradAt u (B ε)) =
      2 * ε * 0 + 0 * (2 * ε) + 0 * 0 := by
  rw [gap4, gap5]
  rfl

theorem gap7 (ε : ℝ) :
    2 * ε * 0 + 0 * (2 * ε) + 0 * 0 = 0 := by
  simp

theorem gap8 (ε : ℝ) :
    dot (gradAt u (A ε)) (gradAt u (B ε)) = 0 := by
  calc
    dot (gradAt u (A ε)) (gradAt u (B ε)) =
        2 * ε * 0 + 0 * (2 * ε) + 0 * 0 := gap6 ε
    _ = 0 := gap7 ε

theorem gap9 (ε : ℝ) :
    dot (gradAt u (A ε)) (gradAt u (B ε)) = 0 := by
  exact gap8 ε

theorem gap10 (ε : ℝ) (hε : ε ≠ 0) :
    angle (gradAt u (A ε)) (gradAt u (B ε)) = Real.pi / 2 := by
  simpa [angle, gap9] using Real.arccos_zero

end

end ProofGap.Exercise3347_1
