import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise3347_2

noncomputable section

abbrev Vec3 := ℝ × ℝ × ℝ

def vec3 (x y z : ℝ) : Vec3 :=
  (x, y, z)

def dot (p q : Vec3) : ℝ :=
  p.1 * q.1 + p.2.1 * q.2.1 + p.2.2 * q.2.2

def norm (p : Vec3) : ℝ :=
  Real.sqrt (dot p p)

def ApproxWithin (ε x y : ℝ) : Prop :=
  |x - y| ≤ ε

def radius (x y z : ℝ) : ℝ :=
  Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2)

def u (x y z : ℝ) : ℝ :=
  x + y + z

def v (x y z : ℝ) : ℝ :=
  x + y + z +
    (0.001 : ℝ) * Real.sin ((10 : ℝ) ^ 6 * Real.pi * radius x y z)

def partialX (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun s => f s y z) x

def partialY (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun s => f x s z) y

def partialZ (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun s => f x y s) z

def grad (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : Vec3 :=
  vec3 (partialX f x y z) (partialY f x y z) (partialZ f x y z)

def M : Vec3 :=
  vec3 1 2 2

def gradAt (f : ℝ → ℝ → ℝ → ℝ) (p : Vec3) : Vec3 :=
  grad f p.1 p.2.1 p.2.2

private theorem partialVFirst (x y z : ℝ) (hr : radius x y z ≠ 0) :
    deriv (fun s => v s y z) x =
      1 + 1000 * Real.pi * (x / radius x y z) *
        Real.cos ((10 : ℝ) ^ 6 * Real.pi * radius x y z) := by
  have hr' : Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2) ≠ 0 := by
    simpa [radius] using hr
  have hs : x ^ 2 + y ^ 2 + z ^ 2 ≠ 0 := by
    intro h
    apply hr'
    simp [h]
  have hpoly :
      HasDerivAt (fun s : ℝ => s ^ 2 + y ^ 2 + z ^ 2) (2 * x) x := by
    convert
      ((((hasDerivAt_id x).pow 2).add
        (hasDerivAt_const (x := x) (c := y ^ 2))).add
        (hasDerivAt_const (x := x) (c := z ^ 2))) using 1 <;>
      norm_num <;> ring
  have hroot :
      HasDerivAt (fun s : ℝ => radius s y z) (x / radius x y z) x := by
    unfold radius
    convert (Real.hasDerivAt_sqrt hs).comp x hpoly using 1 <;>
      field_simp [hr'] <;> ring
  have harg :
      HasDerivAt
        (fun s : ℝ => (10 : ℝ) ^ 6 * Real.pi * radius s y z)
        ((10 : ℝ) ^ 6 * Real.pi * (x / radius x y z)) x := by
    exact hroot.const_mul ((10 : ℝ) ^ 6 * Real.pi)
  have hsin :
      HasDerivAt
        (fun s : ℝ => Real.sin ((10 : ℝ) ^ 6 * Real.pi * radius s y z))
        (Real.cos ((10 : ℝ) ^ 6 * Real.pi * radius x y z) *
          ((10 : ℝ) ^ 6 * Real.pi * (x / radius x y z))) x := by
    exact (Real.hasDerivAt_sin _).comp x harg
  have hlin : HasDerivAt (fun s : ℝ => s + y + z) 1 x := by
    convert
      (((hasDerivAt_id x).add
        (hasDerivAt_const (x := x) (c := y))).add
        (hasDerivAt_const (x := x) (c := z))) using 1 <;>
      norm_num <;> ring
  convert (hlin.add (hsin.const_mul (0.001 : ℝ))).deriv using 1 <;>
    norm_num [v] <;> ring

theorem gap1 :
    ∀ x y z, grad u x y z = vec3 1 1 1 := by
  intro x y z
  have hx : deriv (fun s : ℝ => s + y + z) x = 1 := by
    convert
      ((((hasDerivAt_id x).add
        (hasDerivAt_const (x := x) (c := y))).add
        (hasDerivAt_const (x := x) (c := z))).deriv) using 1 <;>
      norm_num
  have hy : deriv (fun s : ℝ => x + s + z) y = 1 := by
    convert
      ((((hasDerivAt_const (x := y) (c := x)).add
        (hasDerivAt_id y)).add
        (hasDerivAt_const (x := y) (c := z))).deriv) using 1 <;>
      norm_num
  have hz : deriv (fun s : ℝ => x + y + s) z = 1 := by
    convert
      ((((hasDerivAt_const (x := z) (c := x)).add
        (hasDerivAt_const (x := z) (c := y))).add
        (hasDerivAt_id z)).deriv) using 1 <;>
      norm_num
  simp [grad, vec3, partialX, partialY, partialZ, u, hx, hy, hz]

theorem gap2 :
    ∀ x y z, norm (grad u x y z) = Real.sqrt 3 := by
  intro x y z
  rw [gap1 x y z]
  norm_num [norm, dot, vec3]

theorem gap3 :
    ∀ x y z, radius x y z ≠ 0 →
      partialX v x y z =
        1 + 1000 * Real.pi * (x / radius x y z) *
          Real.cos ((10 : ℝ) ^ 6 * Real.pi * radius x y z) := by
  intro x y z hr
  simpa [partialX] using partialVFirst x y z hr

theorem gap4 :
    ∀ x y z, radius x y z ≠ 0 →
      partialY v x y z =
        1 + 1000 * Real.pi * (y / radius x y z) *
          Real.cos ((10 : ℝ) ^ 6 * Real.pi * radius x y z) := by
  intro x y z hr
  have hr' : radius y x z ≠ 0 := by
    simpa [radius, add_comm, add_left_comm, add_assoc] using hr
  simpa [partialY, v, radius, add_comm, add_left_comm, add_assoc] using
    partialVFirst y x z hr'

theorem gap5 :
    ∀ x y z, radius x y z ≠ 0 →
      partialZ v x y z =
        1 + 1000 * Real.pi * (z / radius x y z) *
          Real.cos ((10 : ℝ) ^ 6 * Real.pi * radius x y z) := by
  intro x y z hr
  have hr' : radius z y x ≠ 0 := by
    simpa [radius, add_comm, add_left_comm, add_assoc] using hr
  simpa [partialZ, v, radius, add_comm, add_left_comm, add_assoc] using
    partialVFirst z y x hr'

theorem gap6 :
    partialX v M.1 M.2.1 M.2.2 = 1000 * Real.pi / 3 + 1 := by
  change partialX v 1 2 2 = 1000 * Real.pi / 3 + 1
  have hr : radius 1 2 2 ≠ 0 := by
    norm_num [radius]
  have hrad : radius 1 2 2 = 3 := by
    unfold radius
    convert Real.sqrt_sq (show (0 : ℝ) ≤ 3 by norm_num) using 1 <;>
      norm_num
  rw [gap3 1 2 2 hr, hrad]
  have hcos : Real.cos ((10 : ℝ) ^ 6 * Real.pi * 3) = 1 := by
    convert Real.cos_nat_mul_two_pi 1500000 using 1 <;> norm_num <;> ring
  rw [hcos]
  ring

theorem gap7 :
    ApproxWithin 1 (1000 * Real.pi / 3 + 1) (1000 * Real.pi / 3) := by
  unfold ApproxWithin
  rw [show (1000 * Real.pi / 3 + 1) - 1000 * Real.pi / 3 = 1 by ring]
  norm_num

theorem gap8 :
    ApproxWithin 1 (partialX v M.1 M.2.1 M.2.2) (1000 * Real.pi / 3) := by
  rw [gap6]
  exact gap7

theorem gap9 :
    partialY v M.1 M.2.1 M.2.2 = 2000 * Real.pi / 3 + 1 := by
  change partialY v 1 2 2 = 2000 * Real.pi / 3 + 1
  have hr : radius 1 2 2 ≠ 0 := by
    norm_num [radius]
  have hrad : radius 1 2 2 = 3 := by
    unfold radius
    convert Real.sqrt_sq (show (0 : ℝ) ≤ 3 by norm_num) using 1 <;>
      norm_num
  rw [gap4 1 2 2 hr, hrad]
  have hcos : Real.cos ((10 : ℝ) ^ 6 * Real.pi * 3) = 1 := by
    convert Real.cos_nat_mul_two_pi 1500000 using 1 <;> norm_num <;> ring
  rw [hcos]
  ring

theorem gap10 :
    ApproxWithin 1 (2000 * Real.pi / 3 + 1) (2000 * Real.pi / 3) := by
  unfold ApproxWithin
  rw [show (2000 * Real.pi / 3 + 1) - 2000 * Real.pi / 3 = 1 by ring]
  norm_num

theorem gap11 :
    ApproxWithin 1 (partialY v M.1 M.2.1 M.2.2) (2000 * Real.pi / 3) := by
  rw [gap9]
  exact gap10

theorem gap12 :
    partialZ v M.1 M.2.1 M.2.2 = 2000 * Real.pi / 3 + 1 := by
  change partialZ v 1 2 2 = 2000 * Real.pi / 3 + 1
  have hr : radius 1 2 2 ≠ 0 := by
    norm_num [radius]
  have hrad : radius 1 2 2 = 3 := by
    unfold radius
    convert Real.sqrt_sq (show (0 : ℝ) ≤ 3 by norm_num) using 1 <;>
      norm_num
  rw [gap5 1 2 2 hr, hrad]
  have hcos : Real.cos ((10 : ℝ) ^ 6 * Real.pi * 3) = 1 := by
    convert Real.cos_nat_mul_two_pi 1500000 using 1 <;> norm_num <;> ring
  rw [hcos]
  ring

theorem gap13 :
    ApproxWithin 1 (2000 * Real.pi / 3 + 1) (2000 * Real.pi / 3) := by
  unfold ApproxWithin
  rw [show (2000 * Real.pi / 3 + 1) - 2000 * Real.pi / 3 = 1 by ring]
  norm_num

theorem gap14 :
    ApproxWithin 1 (partialZ v M.1 M.2.1 M.2.2) (2000 * Real.pi / 3) := by
  rw [gap12]
  exact gap13

theorem gap15 :
    ApproxWithin (Real.sqrt 3) (norm (gradAt v M))
      (1000 * Real.pi *
        Real.sqrt ((1 / 3 : ℝ) ^ 2 + (2 / 3 : ℝ) ^ 2 + (2 / 3 : ℝ) ^ 2)) := by
  have hx : partialX v 1 2 2 = 1000 * Real.pi / 3 + 1 := by
    simpa [M, vec3] using gap6
  have hy : partialY v 1 2 2 = 2000 * Real.pi / 3 + 1 := by
    simpa [M, vec3] using gap9
  have hz : partialZ v 1 2 2 = 2000 * Real.pi / 3 + 1 := by
    simpa [M, vec3] using gap12
  have hw :
      Real.sqrt ((1 / 3 : ℝ) ^ 2 + (2 / 3 : ℝ) ^ 2 + (2 / 3 : ℝ) ^ 2) = 1 := by
    norm_num
  change
    |Real.sqrt
        (partialX v 1 2 2 * partialX v 1 2 2 +
          partialY v 1 2 2 * partialY v 1 2 2 +
          partialZ v 1 2 2 * partialZ v 1 2 2) -
      1000 * Real.pi *
        Real.sqrt ((1 / 3 : ℝ) ^ 2 + (2 / 3 : ℝ) ^ 2 + (2 / 3 : ℝ) ^ 2)| ≤
      Real.sqrt 3
  rw [hx, hy, hz, hw]
  simp only [mul_one]
  let a : ℝ := 1000 * Real.pi
  have htwo : 2000 * Real.pi = 2 * a := by
    dsimp [a]
    ring
  rw [htwo]
  let R : ℝ :=
    (a / 3 + 1) * (a / 3 + 1) +
      (2 * a / 3 + 1) * (2 * a / 3 + 1) +
      (2 * a / 3 + 1) * (2 * a / 3 + 1)
  let q : ℝ := Real.sqrt R
  change |q - a| ≤ Real.sqrt 3
  have ha : 0 ≤ a := by
    dsimp [a]
    positivity
  have hR : 0 ≤ R := by
    dsimp [R]
    positivity
  have hq : 0 ≤ q := by
    dsimp [q]
    positivity
  have hq2 : q ^ 2 = R := by
    dsimp [q]
    exact Real.sq_sqrt hR
  dsimp [R] at hq2
  have hthree : (Real.sqrt 3) ^ 2 = 3 :=
    Real.sq_sqrt (by norm_num)
  have hsnonneg : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hsbound : (5 / 3 : ℝ) ≤ Real.sqrt 3 := by
    nlinarith
  have hmul : 0 ≤ a * (Real.sqrt 3 - 5 / 3) :=
    mul_nonneg ha (sub_nonneg.mpr hsbound)
  have hlower : a ≤ q := by
    nlinarith [hq2]
  have hupper : q ≤ a + Real.sqrt 3 := by
    nlinarith [hq2, hthree, hmul]
  rw [abs_of_nonneg (sub_nonneg.mpr hlower)]
  linarith

theorem gap16 :
    1000 * Real.pi *
        Real.sqrt ((1 / 3 : ℝ) ^ 2 + (2 / 3 : ℝ) ^ 2 + (2 / 3 : ℝ) ^ 2) =
      1000 * Real.pi := by
  norm_num

theorem gap17 :
    ApproxWithin (Real.sqrt 3) (norm (gradAt v M)) (1000 * Real.pi) := by
  rw [← gap16]
  exact gap15

theorem gap18 :
    ApproxWithin (Real.sqrt 3)
      (norm (gradAt v M) - norm (gradAt u M))
      (1000 * Real.pi - Real.sqrt 3) := by
  have hu : norm (gradAt u M) = Real.sqrt 3 := by
    change norm (grad u M.1 M.2.1 M.2.2) = Real.sqrt 3
    exact gap2 M.1 M.2.1 M.2.2
  have h := gap17
  unfold ApproxWithin at h ⊢
  rw [hu]
  convert h using 1 <;> ring

theorem gap19 :
    ApproxWithin 1 (1000 * Real.pi - Real.sqrt 3) 3140 := by
  unfold ApproxWithin
  have hsnonneg : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hsquare : (Real.sqrt 3) ^ 2 = 3 :=
    Real.sq_sqrt (by norm_num)
  have hslo : 1 ≤ Real.sqrt 3 := by
    nlinarith
  have hshi : Real.sqrt 3 ≤ 2 := by
    nlinarith
  have hpilo : (3141 / 1000 : ℝ) < Real.pi := by
    nlinarith [Real.pi_gt_d20]
  have hpihi : Real.pi < (3142 / 1000 : ℝ) := by
    nlinarith [Real.pi_lt_d20]
  rw [abs_le]
  constructor <;> nlinarith

theorem gap20 :
    ApproxWithin 3 (norm (gradAt v M) - norm (gradAt u M)) 3140 := by
  have h₁ := gap18
  have h₂ := gap19
  unfold ApproxWithin at h₁ h₂ ⊢
  have hsnonneg : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have hsquare : (Real.sqrt 3) ^ 2 = 3 :=
    Real.sq_sqrt (by norm_num)
  have hsqrt : Real.sqrt 3 ≤ 2 := by
    nlinarith
  calc
    |norm (gradAt v M) - norm (gradAt u M) - 3140| =
        |(norm (gradAt v M) - norm (gradAt u M) -
            (1000 * Real.pi - Real.sqrt 3)) +
          ((1000 * Real.pi - Real.sqrt 3) - 3140)| := by
            congr 1
            ring
    _ ≤
        |norm (gradAt v M) - norm (gradAt u M) -
            (1000 * Real.pi - Real.sqrt 3)| +
          |(1000 * Real.pi - Real.sqrt 3) - 3140| := abs_add_le _ _
    _ ≤ Real.sqrt 3 + 1 := add_le_add h₁ h₂
    _ ≤ 3 := by linarith

end

end ProofGap.Exercise3347_2
