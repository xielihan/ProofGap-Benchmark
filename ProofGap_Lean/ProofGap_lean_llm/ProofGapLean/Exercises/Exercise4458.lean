import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Order.IntermediateValue

namespace ProofGap.Exercise4458

noncomputable section

abbrev Vec3 := ℝ × ℝ × ℝ

def dot (p q : Vec3) : ℝ :=
  p.1 * q.1 + p.2.1 * q.2.1 + p.2.2 * q.2.2

def scale (a : ℝ) (p : Vec3) : Vec3 :=
  (a * p.1, a * p.2.1, a * p.2.2)

def radius (p : Vec3) : ℝ :=
  Real.sqrt (dot p p)

def inverseSquareField (m : ℝ) (p : Vec3) : Vec3 :=
  scale (-m / radius p ^ 3) p

def fieldOneForm (m : ℝ) (p v : Vec3) : ℝ :=
  dot (inverseSquareField m p) v

def coordinateOneForm (m : ℝ) (p v : Vec3) : ℝ :=
  (-m / radius p ^ 3) * p.1 * v.1 +
    (-m / radius p ^ 3) * p.2.1 * v.2.1 +
    (-m / radius p ^ 3) * p.2.2 * v.2.2

def squaredRadiusDifferential (p v : Vec3) : ℝ :=
  2 * dot p v

def radialRate (p v : Vec3) : ℝ :=
  dot p v / radius p

def radialOneForm (m : ℝ) (p v : Vec3) : ℝ :=
  (-m / radius p ^ 2) * radialRate p v

def centralPotential (m : ℝ) (p : Vec3) : ℝ :=
  m / radius p

def potentialDifferential (m : ℝ) (p v : Vec3) : ℝ :=
  (-m / radius p ^ 3) * dot p v

def radialPotential (m r : ℝ) : ℝ :=
  m / r

private theorem radius_ne_zero_of_ne (p : Vec3)
    (hp : p ≠ (0, 0, 0)) : radius p ≠ 0 := by
  apply ne_of_gt
  unfold radius
  apply Real.sqrt_pos.2
  rcases p with ⟨x, y, z⟩
  have hxyz : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0 := by
    by_cases hx : x = 0
    · by_cases hy : y = 0
      · right
        right
        intro hz
        apply hp
        simp [hx, hy, hz]
      · exact Or.inr (Or.inl hy)
    · exact Or.inl hx
  simp only [dot, Prod.fst, Prod.snd]
  rcases hxyz with hx | hy | hz
  · nlinarith [mul_self_pos.mpr hx, mul_self_nonneg y, mul_self_nonneg z]
  · nlinarith [mul_self_nonneg x, mul_self_pos.mpr hy, mul_self_nonneg z]
  · nlinarith [mul_self_nonneg x, mul_self_nonneg y, mul_self_pos.mpr hz]

theorem gap1 (m : ℝ) (p v : Vec3) (hp : p ≠ (0, 0, 0)) :
    potentialDifferential m p v = fieldOneForm m p v := by
  unfold potentialDifferential fieldOneForm inverseSquareField scale dot
  ring

theorem gap2 (m : ℝ) (p v : Vec3) (hp : p ≠ (0, 0, 0)) :
    fieldOneForm m p v = coordinateOneForm m p v := by
  unfold fieldOneForm inverseSquareField scale coordinateOneForm dot
  ring

theorem gap3 (m : ℝ) (p v : Vec3) (hp : p ≠ (0, 0, 0)) :
    coordinateOneForm m p v =
      (-m / (2 * radius p ^ 3)) * squaredRadiusDifferential p v := by
  unfold coordinateOneForm squaredRadiusDifferential dot
  field_simp [radius_ne_zero_of_ne p hp]
  <;> ring

theorem gap4 (m : ℝ) (p v : Vec3) (hp : p ≠ (0, 0, 0)) :
    (-m / (2 * radius p ^ 3)) * squaredRadiusDifferential p v =
      radialOneForm m p v := by
  unfold squaredRadiusDifferential radialOneForm radialRate
  field_simp [radius_ne_zero_of_ne p hp]
  <;> ring

theorem gap5 (m r : ℝ) (hr : r ≠ 0) :
    HasDerivAt (radialPotential m) (-m / r ^ 2) r := by
  simpa [radialPotential] using
    (hasDerivAt_const r m).div (hasDerivAt_id r) hr

theorem gap6 (m : ℝ) (p v : Vec3) (hp : p ≠ (0, 0, 0)) :
    potentialDifferential m p v = radialOneForm m p v := by
  calc
    potentialDifferential m p v = fieldOneForm m p v := gap1 m p v hp
    _ = coordinateOneForm m p v := gap2 m p v hp
    _ = (-m / (2 * radius p ^ 3)) * squaredRadiusDifferential p v :=
      gap3 m p v hp
    _ = radialOneForm m p v := gap4 m p v hp

theorem gap7 (m : ℝ) (u : ℝ → ℝ)
    (hu : ∀ r : ℝ, 0 < r → HasDerivAt u (-m / r ^ 2) r) :
    ∃ C : ℝ, ∀ r : ℝ, 0 < r → u r = radialPotential m r + C := by
  have hderiv (x : ℝ) (hx : 0 < x) :
      HasDerivAt (fun t : ℝ => u t - radialPotential m t) 0 x := by
    simpa using (hu x hx).sub (gap5 m x (ne_of_gt hx))
  refine ⟨u 1 - radialPotential m 1, ?_⟩
  intro r hr
  have hdiff :
      DifferentiableOn ℝ (fun x : ℝ => u x - radialPotential m x)
        (Set.Ioo 0 (r + 2)) := by
    intro x hx
    exact (hderiv x hx.1).differentiableAt.differentiableWithinAt
  have hconst :
      u r - radialPotential m r = u 1 - radialPotential m 1 := by
    apply isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo hdiff
    · intro x hx
      exact (hderiv x hx.1).deriv
    · exact ⟨hr, by linarith⟩
    · exact ⟨zero_lt_one, by linarith⟩
  linarith

theorem gap8 (m : ℝ) (u : ℝ → ℝ)
    (hfamily :
      ∃ C : ℝ, ∀ r : ℝ, 0 < r → u r = radialPotential m r + C)
    (hnormalized : u 1 = m) :
    ∀ r : ℝ, 0 < r → u r = radialPotential m r := by
  rcases hfamily with ⟨C, hC⟩
  have hCzero : C = 0 := by
    have h1 := hC 1 zero_lt_one
    rw [hnormalized] at h1
    simp [radialPotential] at h1
    linarith
  intro r hr
  simpa [hCzero] using hC r hr

end

end ProofGap.Exercise4458
