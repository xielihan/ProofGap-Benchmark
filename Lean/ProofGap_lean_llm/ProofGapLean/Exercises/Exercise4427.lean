import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4427

noncomputable section

abbrev Vec3 := ℝ × ℝ × ℝ

def radius (p : Vec3) : ℝ :=
  Real.sqrt (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2)

def scaleVec (c : ℝ) (p : Vec3) : Vec3 :=
  (c * p.1, c * p.2.1, c * p.2.2)

def partialX (u : Vec3 → ℝ) (p : Vec3) : ℝ :=
  deriv (fun x => u (x, p.2.1, p.2.2)) p.1

def partialY (u : Vec3 → ℝ) (p : Vec3) : ℝ :=
  deriv (fun y => u (p.1, y, p.2.2)) p.2.1

def partialZ (u : Vec3 → ℝ) (p : Vec3) : ℝ :=
  deriv (fun z => u (p.1, p.2.1, z)) p.2.2

def divergence (F : Vec3 → Vec3) (p : Vec3) : ℝ :=
  partialX (fun q => (F q).1) p +
    partialY (fun q => (F q).2.1) p +
      partialZ (fun q => (F q).2.2) p

def identityField (p : Vec3) : Vec3 :=
  p

def identityDerivativeSum (p : Vec3) : ℝ :=
  partialX (fun q => (identityField q).1) p +
    partialY (fun q => (identityField q).2.1) p +
      partialZ (fun q => (identityField q).2.2) p

def identityDivergence (p : Vec3) : ℝ :=
  divergence identityField p

def radialUnitField (p : Vec3) : Vec3 :=
  scaleVec (1 / radius p) p

def radialPartialSum (p : Vec3) : ℝ :=
  partialX (fun q => (radialUnitField q).1) p +
    partialY (fun q => (radialUnitField q).2.1) p +
      partialZ (fun q => (radialUnitField q).2.2) p

def radialDivergence (p : Vec3) : ℝ :=
  divergence radialUnitField p

private theorem sum_sq_pos (p : Vec3) (hp : p ≠ (0, 0, 0)) :
    0 < p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 := by
  rcases p with ⟨x, y, z⟩
  by_contra hn
  have hle : x ^ 2 + y ^ 2 + z ^ 2 ≤ 0 := le_of_not_gt hn
  have hx2 : x ^ 2 = 0 := by
    nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
  have hy2 : y ^ 2 = 0 := by
    nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
  have hz2 : z ^ 2 = 0 := by
    nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
  have hx : x = 0 := sq_eq_zero_iff.mp hx2
  have hy : y = 0 := sq_eq_zero_iff.mp hy2
  have hz : z = 0 := sq_eq_zero_iff.mp hz2
  apply hp
  simp [hx, hy, hz]

private theorem radial_component_deriv
    (g : ℝ → ℝ) (x s : ℝ)
    (hg : HasDerivAt g (2 * x) x)
    (hgs : g x = s) (hs : 0 < s) :
    deriv (fun t => (1 / Real.sqrt (g t)) * t) x =
      1 / Real.sqrt s - x ^ 2 / Real.sqrt s ^ 3 := by
  have hg0 : g x ≠ 0 := by
    rw [hgs]
    exact ne_of_gt hs
  have hroot : Real.sqrt (g x) ≠ 0 := by
    rw [hgs]
    exact ne_of_gt (Real.sqrt_pos.2 hs)
  have hsqrt0 : Real.sqrt s ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hs)
  have hsqrtd := (Real.hasDerivAt_sqrt hg0).comp x hg
  have hinv := hsqrtd.inv hroot
  have hprod := hinv.mul (hasDerivAt_id x)
  simp only [one_div]
  change deriv (((fun u : ℝ => Real.sqrt u) ∘ g)⁻¹ * id) x =
    (Real.sqrt s)⁻¹ - x ^ 2 / Real.sqrt s ^ 3
  rw [hprod.deriv]
  change
    -(1 / (2 * Real.sqrt (g x)) * (2 * x)) /
          Real.sqrt (g x) ^ 2 * x +
        (Real.sqrt (g x))⁻¹ * 1 =
      (Real.sqrt s)⁻¹ - x ^ 2 / Real.sqrt s ^ 3
  rw [hgs]
  field_simp [hsqrt0] <;> ring

theorem gap1 (p : Vec3) :
    identityDivergence p = identityDerivativeSum p := by
  rfl

theorem gap2 (p : Vec3) :
    identityDerivativeSum p = 3 := by
  have hx : deriv (fun x : ℝ => x) p.1 = 1 := by
    change deriv id p.1 = 1
    exact (hasDerivAt_id p.1).deriv
  have hy : deriv (fun y : ℝ => y) p.2.1 = 1 := by
    change deriv id p.2.1 = 1
    exact (hasDerivAt_id p.2.1).deriv
  have hz : deriv (fun z : ℝ => z) p.2.2 = 1 := by
    change deriv id p.2.2 = 1
    exact (hasDerivAt_id p.2.2).deriv
  change deriv (fun x : ℝ => x) p.1 +
      deriv (fun y : ℝ => y) p.2.1 +
        deriv (fun z : ℝ => z) p.2.2 = 3
  rw [hx, hy, hz]
  norm_num

theorem gap3 (p : Vec3) :
    identityDivergence p = 3 := by
  rw [gap1 p, gap2 p]

theorem gap4 (p : Vec3) (hp : p ≠ (0, 0, 0)) :
    radialDivergence p = radialPartialSum p := by
  rfl

theorem gap5 (p : Vec3) (hp : p ≠ (0, 0, 0)) :
    radialPartialSum p =
      (1 / radius p - p.1 ^ 2 / radius p ^ 3) +
        (1 / radius p - p.2.1 ^ 2 / radius p ^ 3) +
        (1 / radius p - p.2.2 ^ 2 / radius p ^ 3) := by
  have hs := sum_sq_pos p hp
  have hgx :
      HasDerivAt
        (fun t : ℝ => t ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2)
        (2 * p.1) p.1 := by
    convert (((hasDerivAt_id p.1).pow 2).add
      (hasDerivAt_const p.1 (p.2.1 ^ 2))).add
        (hasDerivAt_const p.1 (p.2.2 ^ 2)) using 1 <;>
      norm_num <;> ring
  have hgy :
      HasDerivAt
        (fun t : ℝ => p.1 ^ 2 + t ^ 2 + p.2.2 ^ 2)
        (2 * p.2.1) p.2.1 := by
    convert ((hasDerivAt_const p.2.1 (p.1 ^ 2)).add
      ((hasDerivAt_id p.2.1).pow 2)).add
        (hasDerivAt_const p.2.1 (p.2.2 ^ 2)) using 1 <;>
      norm_num <;> ring
  have hgz :
      HasDerivAt
        (fun t : ℝ => p.1 ^ 2 + p.2.1 ^ 2 + t ^ 2)
        (2 * p.2.2) p.2.2 := by
    convert ((hasDerivAt_const p.2.2 (p.1 ^ 2)).add
      (hasDerivAt_const p.2.2 (p.2.1 ^ 2))).add
        ((hasDerivAt_id p.2.2).pow 2) using 1 <;>
      norm_num <;> ring
  have hxpart :
      partialX (fun q => (radialUnitField q).1) p =
        1 / radius p - p.1 ^ 2 / radius p ^ 3 := by
    change deriv
        (fun t : ℝ =>
          (1 / Real.sqrt (t ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2)) * t)
        p.1 =
      1 / Real.sqrt (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2) -
        p.1 ^ 2 /
          Real.sqrt (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2) ^ 3
    exact radial_component_deriv
      (fun t : ℝ => t ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2)
      p.1 (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2) hgx rfl hs
  have hypart :
      partialY (fun q => (radialUnitField q).2.1) p =
        1 / radius p - p.2.1 ^ 2 / radius p ^ 3 := by
    change deriv
        (fun t : ℝ =>
          (1 / Real.sqrt (p.1 ^ 2 + t ^ 2 + p.2.2 ^ 2)) * t)
        p.2.1 =
      1 / Real.sqrt (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2) -
        p.2.1 ^ 2 /
          Real.sqrt (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2) ^ 3
    exact radial_component_deriv
      (fun t : ℝ => p.1 ^ 2 + t ^ 2 + p.2.2 ^ 2)
      p.2.1 (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2) hgy rfl hs
  have hzpart :
      partialZ (fun q => (radialUnitField q).2.2) p =
        1 / radius p - p.2.2 ^ 2 / radius p ^ 3 := by
    change deriv
        (fun t : ℝ =>
          (1 / Real.sqrt (p.1 ^ 2 + p.2.1 ^ 2 + t ^ 2)) * t)
        p.2.2 =
      1 / Real.sqrt (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2) -
        p.2.2 ^ 2 /
          Real.sqrt (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2) ^ 3
    exact radial_component_deriv
      (fun t : ℝ => p.1 ^ 2 + p.2.1 ^ 2 + t ^ 2)
      p.2.2 (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2) hgz rfl hs
  unfold radialPartialSum
  rw [hxpart, hypart, hzpart]

theorem gap6 (p : Vec3) (hp : p ≠ (0, 0, 0)) :
    radialDivergence p =
      (1 / radius p - p.1 ^ 2 / radius p ^ 3) +
        (1 / radius p - p.2.1 ^ 2 / radius p ^ 3) +
        (1 / radius p - p.2.2 ^ 2 / radius p ^ 3) := by
  exact (gap4 p hp).trans (gap5 p hp)

theorem gap7 (p : Vec3) (hp : p ≠ (0, 0, 0)) :
    radialDivergence p =
      3 / radius p -
        (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2) / radius p ^ 3 := by
  rw [gap6 p hp]
  ring

theorem gap8 (p : Vec3) (hp : p ≠ (0, 0, 0)) :
    3 / radius p -
        (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2) / radius p ^ 3 =
      3 / radius p - 1 / radius p := by
  have hs := sum_sq_pos p hp
  have hr0 : radius p ≠ 0 := by
    unfold radius
    exact ne_of_gt (Real.sqrt_pos.2 hs)
  have hrsq :
      radius p ^ 2 = p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 := by
    unfold radius
    exact Real.sq_sqrt (le_of_lt hs)
  rw [← hrsq]
  field_simp [hr0]

theorem gap9 (p : Vec3) (hp : p ≠ (0, 0, 0)) :
    3 / radius p - 1 / radius p = 2 / radius p := by
  ring

theorem gap10 (p : Vec3) (hp : p ≠ (0, 0, 0)) :
    radialDivergence p = 2 / radius p := by
  calc
    radialDivergence p =
        3 / radius p -
          (p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2) / radius p ^ 3 :=
      gap7 p hp
    _ = 3 / radius p - 1 / radius p := gap8 p hp
    _ = 2 / radius p := gap9 p hp

end

end ProofGap.Exercise4427
