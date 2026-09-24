import ProofGapLean.Prelude.Discrete
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

namespace ProofGap.Exercise3273

noncomputable section

def u (x y z : ℝ) : ℝ := x * y * z

def coordX (x y z : ℝ) : ℝ := x
def coordY (x y z : ℝ) : ℝ := y
def coordZ (x y z : ℝ) : ℝ := z

def iterDeriv (n : ℕ) (g : ℝ → ℝ) : ℝ → ℝ :=
  (deriv^[n]) g

def directional (n : ℕ) (g : ℝ → ℝ → ℝ → ℝ)
    (x y z dx dy dz : ℝ) : ℝ :=
  iterDeriv n
    (fun s => g (x + s * dx) (y + s * dy) (z + s * dz)) 0

def yzSecondDirectional (y z dy dz : ℝ) : ℝ :=
  iterDeriv 2 (fun s => (y + s * dy) * (z + s * dz)) 0

def firstLeibnizStage (dx y z dy dz : ℝ) : ℝ :=
  (Nat.choose 3 1 : ℝ) * dx * yzSecondDirectional y z dy dz

def secondLeibnizStage (dx dy dz : ℝ) : ℝ :=
  3 * dx * (Nat.choose 2 1 : ℝ) * dy * dz

def finalForm (dx dy dz : ℝ) : ℝ :=
  6 * dx * dy * dz

private lemma deriv_affine (a b s : ℝ) :
    deriv (fun t : ℝ => a + b * t) s = b := by
  convert ((hasDerivAt_const (x := s) a).add
    ((hasDerivAt_id s).const_mul b)).deriv using 1 <;> ring

private lemma deriv_quadratic (a b c s : ℝ) :
    deriv (fun t : ℝ => a + b * t + c * t ^ 2) s =
      b + 2 * c * s := by
  convert (((hasDerivAt_const (x := s) a).add
    ((hasDerivAt_id s).const_mul b)).add
    (((hasDerivAt_id s).mul (hasDerivAt_id s)).const_mul c)).deriv using 1
  all_goals
    first
    | (apply congrArg (fun f : ℝ → ℝ => deriv f s); funext t; simp; ring)
    | (simp; ring)
  all_goals simp

private lemma deriv_cubic (a b c d s : ℝ) :
    deriv (fun t : ℝ => a + b * t + c * t ^ 2 + d * t ^ 3) s =
      b + 2 * c * s + 3 * d * s ^ 2 := by
  convert ((((hasDerivAt_const (x := s) a).add
    ((hasDerivAt_id s).const_mul b)).add
    (((hasDerivAt_id s).mul (hasDerivAt_id s)).const_mul c)).add
    ((((hasDerivAt_id s).mul (hasDerivAt_id s)).mul
      (hasDerivAt_id s)).const_mul d)).deriv using 1
  all_goals
    first
    | (apply congrArg (fun f : ℝ → ℝ => deriv f s); funext t; simp; ring)
    | (simp; ring)

private lemma iterDeriv_two_quadratic (a b c : ℝ) :
    iterDeriv 2 (fun s : ℝ => a + b * s + c * s ^ 2) 0 = 2 * c := by
  have h1 :
      deriv (fun s : ℝ => a + b * s + c * s ^ 2) =
        fun s : ℝ => b + 2 * c * s := by
    funext s
    exact deriv_quadratic a b c s
  have h2 :
      deriv (fun s : ℝ => b + 2 * c * s) = fun _ : ℝ => 2 * c := by
    funext s
    exact deriv_affine b (2 * c) s
  change deriv (deriv (fun s : ℝ => a + b * s + c * s ^ 2)) 0 = 2 * c
  rw [h1, h2]

private lemma iterDeriv_three_cubic (a b c d : ℝ) :
    iterDeriv 3 (fun s : ℝ => a + b * s + c * s ^ 2 + d * s ^ 3) 0 = 6 * d := by
  have h1 :
      deriv (fun s : ℝ => a + b * s + c * s ^ 2 + d * s ^ 3) =
        fun s : ℝ => b + 2 * c * s + 3 * d * s ^ 2 := by
    funext s
    exact deriv_cubic a b c d s
  have h2 :
      deriv (fun s : ℝ => b + 2 * c * s + 3 * d * s ^ 2) =
        fun s : ℝ => 2 * c + 6 * d * s := by
    funext s
    convert deriv_quadratic b (2 * c) (3 * d) s using 1 <;> ring
  have h3 :
      deriv (fun s : ℝ => 2 * c + 6 * d * s) = fun _ : ℝ => 6 * d := by
    funext s
    exact deriv_affine (2 * c) (6 * d) s
  change deriv (deriv (deriv
    (fun s : ℝ => a + b * s + c * s ^ 2 + d * s ^ 3))) 0 = 6 * d
  rw [h1, h2, h3]

private lemma iterDeriv_two_affine (a b : ℝ) :
    iterDeriv 2 (fun s : ℝ => a + s * b) 0 = 0 := by
  have hf :
      (fun s : ℝ => a + s * b) =
        fun s : ℝ => a + b * s + 0 * s ^ 2 := by
    funext s
    ring
  rw [hf, iterDeriv_two_quadratic]
  ring

private lemma yzSecondDirectional_eq (y z dy dz : ℝ) :
    yzSecondDirectional y z dy dz = 2 * dy * dz := by
  unfold yzSecondDirectional
  have hf :
      (fun s : ℝ => (y + s * dy) * (z + s * dz)) =
        fun s : ℝ => y * z + (dy * z + y * dz) * s + (dy * dz) * s ^ 2 := by
    funext s
    ring
  rw [hf, iterDeriv_two_quadratic]
  ring

private lemma directional_product (x y z dx dy dz : ℝ) :
    directional 3 (fun a b c => a * b * c) x y z dx dy dz =
      6 * dx * dy * dz := by
  unfold directional
  have hf :
      (fun s : ℝ =>
        (x + s * dx) * (y + s * dy) * (z + s * dz)) =
      (fun s : ℝ =>
        x * y * z +
          (dx * y * z + x * dy * z + x * y * dz) * s +
          (dx * dy * z + dx * y * dz + x * dy * dz) * s ^ 2 +
          (dx * dy * dz) * s ^ 3) := by
    funext s
    ring
  rw [hf, iterDeriv_three_cubic]
  ring

theorem gap1 (x y z dx dy dz : ℝ) :
    directional 2 coordX x y z dx dy dz =
      directional 2 coordY x y z dx dy dz := by
  calc
    directional 2 coordX x y z dx dy dz = 0 := by
      simpa [directional, coordX] using iterDeriv_two_affine x dx
    _ = directional 2 coordY x y z dx dy dz := by
      symm
      simpa [directional, coordY] using iterDeriv_two_affine y dy

theorem gap2 (x y z dx dy dz : ℝ) :
    directional 2 coordY x y z dx dy dz =
      directional 2 coordZ x y z dx dy dz := by
  calc
    directional 2 coordY x y z dx dy dz = 0 := by
      simpa [directional, coordY] using iterDeriv_two_affine y dy
    _ = directional 2 coordZ x y z dx dy dz := by
      symm
      simpa [directional, coordZ] using iterDeriv_two_affine z dz

theorem gap3 (x y z dx dy dz : ℝ) :
    directional 2 coordZ x y z dx dy dz = 0 := by
  simpa [directional, coordZ] using iterDeriv_two_affine z dz

theorem gap4 (x y z dx dy dz : ℝ) :
    directional 2 coordX x y z dx dy dz = 0 := by
  calc
    directional 2 coordX x y z dx dy dz =
        directional 2 coordY x y z dx dy dz := gap1 x y z dx dy dz
    _ = directional 2 coordZ x y z dx dy dz := gap2 x y z dx dy dz
    _ = 0 := gap3 x y z dx dy dz

theorem gap5 (x y z dx dy dz : ℝ) :
    directional 3 u x y z dx dy dz =
      directional 3 (fun a b c => a * b * c) x y z dx dy dz := by
  rfl

theorem gap6 (x y z dx dy dz : ℝ) :
    directional 3 (fun a b c => a * b * c) x y z dx dy dz =
      firstLeibnizStage dx y z dy dz := by
  unfold firstLeibnizStage
  rw [directional_product, yzSecondDirectional_eq]
  norm_num [Nat.choose] <;> ring

theorem gap7 (y z dx dy dz : ℝ) :
    firstLeibnizStage dx y z dy dz =
      secondLeibnizStage dx dy dz := by
  unfold firstLeibnizStage secondLeibnizStage
  rw [yzSecondDirectional_eq]
  norm_num [Nat.choose] <;> ring

theorem gap8 (dx dy dz : ℝ) :
    secondLeibnizStage dx dy dz = finalForm dx dy dz := by
  have hchoose : (Nat.choose 2 1 : ℝ) = 2 := by
    norm_num [Nat.choose]
  rw [secondLeibnizStage, finalForm, hchoose]
  ring

theorem gap9 (x y z dx dy dz : ℝ) :
    directional 3 u x y z dx dy dz = finalForm dx dy dz := by
  calc
    directional 3 u x y z dx dy dz =
        directional 3 (fun a b c => a * b * c) x y z dx dy dz :=
      gap5 x y z dx dy dz
    _ = firstLeibnizStage dx y z dy dz := gap6 x y z dx dy dz
    _ = secondLeibnizStage dx dy dz := gap7 y z dx dy dz
    _ = finalForm dx dy dz := gap8 dx dy dz

end

end ProofGap.Exercise3273
