import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise3642

noncomputable section

structure Point3 where
  x : ℝ
  y : ℝ
  z : ℝ
  deriving DecidableEq

def u (p : Point3) : ℝ :=
  p.x ^ 2 + p.y ^ 2 + p.z ^ 2 + 2 * p.x + 4 * p.y - 6 * p.z

def partialX (g : Point3 → ℝ) (p : Point3) : ℝ :=
  deriv (fun x => g ⟨x, p.y, p.z⟩) p.x

def partialY (g : Point3 → ℝ) (p : Point3) : ℝ :=
  deriv (fun y => g ⟨p.x, y, p.z⟩) p.y

def partialZ (g : Point3 → ℝ) (p : Point3) : ℝ :=
  deriv (fun z => g ⟨p.x, p.y, z⟩) p.z

def gradient (g : Point3 → ℝ) (p : Point3) : Point3 :=
  ⟨partialX g p, partialY g p, partialZ g p⟩

def basePoint : Point3 :=
  ⟨-1, -2, 3⟩

def secondVariation (v : Point3) : ℝ :=
  2 * (v.x ^ 2 + v.y ^ 2 + v.z ^ 2)

def PositiveDefiniteSecondVariation : Prop :=
  ∀ v : Point3, v ≠ ⟨0, 0, 0⟩ → 0 < secondVariation v

def IsUniqueGlobalMinimizer
    (g : Point3 → ℝ) (p : Point3) : Prop :=
  (∀ q, g p ≤ g q) ∧ (∀ q, g q = g p → q = p)

def minimumPoints : Set Point3 :=
  {p | ∀ q, u p ≤ u q}

theorem gap1 :
    ∀ p : Point3,
      gradient u p =
        ⟨2 * (p.x + 1), 2 * (p.y + 2), 2 * (p.z - 3)⟩ := by
  intro p
  have hx : partialX u p = 2 * (p.x + 1) := by
    change
      deriv
          (fun x : ℝ =>
            x ^ 2 + p.y ^ 2 + p.z ^ 2 + 2 * x + 4 * p.y - 6 * p.z)
          p.x =
        2 * (p.x + 1)
    have h0 := (hasDerivAt_id p.x).mul (hasDerivAt_id p.x)
    have h1 := h0.add (hasDerivAt_const p.x (p.y ^ 2))
    have h2 := h1.add (hasDerivAt_const p.x (p.z ^ 2))
    have h3 := h2.add ((hasDerivAt_id p.x).const_mul 2)
    have h4 := h3.add (hasDerivAt_const p.x (4 * p.y))
    have h5 := h4.sub (hasDerivAt_const p.x (6 * p.z))
    convert h5.deriv using 1
    · apply congrArg (fun f : ℝ → ℝ => deriv f p.x)
      funext x
      dsimp [id]
      ring
    · dsimp [id]
      ring
  have hy : partialY u p = 2 * (p.y + 2) := by
    change
      deriv
          (fun y : ℝ =>
            p.x ^ 2 + y ^ 2 + p.z ^ 2 + 2 * p.x + 4 * y - 6 * p.z)
          p.y =
        2 * (p.y + 2)
    have h0 := hasDerivAt_const p.y (p.x ^ 2)
    have h1 := h0.add ((hasDerivAt_id p.y).mul (hasDerivAt_id p.y))
    have h2 := h1.add (hasDerivAt_const p.y (p.z ^ 2))
    have h3 := h2.add (hasDerivAt_const p.y (2 * p.x))
    have h4 := h3.add ((hasDerivAt_id p.y).const_mul 4)
    have h5 := h4.sub (hasDerivAt_const p.y (6 * p.z))
    convert h5.deriv using 1
    · apply congrArg (fun f : ℝ → ℝ => deriv f p.y)
      funext y
      dsimp [id]
      ring
    · dsimp [id]
      ring
  have hz : partialZ u p = 2 * (p.z - 3) := by
    change
      deriv
          (fun z : ℝ =>
            p.x ^ 2 + p.y ^ 2 + z ^ 2 + 2 * p.x + 4 * p.y - 6 * z)
          p.z =
        2 * (p.z - 3)
    have h0 := hasDerivAt_const p.z (p.x ^ 2)
    have h1 := h0.add (hasDerivAt_const p.z (p.y ^ 2))
    have h2 := h1.add ((hasDerivAt_id p.z).mul (hasDerivAt_id p.z))
    have h3 := h2.add (hasDerivAt_const p.z (2 * p.x))
    have h4 := h3.add (hasDerivAt_const p.z (4 * p.y))
    have h5 := h4.sub ((hasDerivAt_id p.z).const_mul 6)
    convert h5.deriv using 1
    · apply congrArg (fun f : ℝ → ℝ => deriv f p.z)
      funext z
      dsimp [id]
      ring
    · dsimp [id]
      ring
  simpa only [gradient, hx, hy, hz]

theorem gap2 :
    ∀ p : Point3, gradient u p = ⟨0, 0, 0⟩ ↔ p = basePoint := by
  intro p
  rw [gap1 p]
  constructor
  · intro h
    have hx : 2 * (p.x + 1) = 0 := by
      simpa using congrArg Point3.x h
    have hy : 2 * (p.y + 2) = 0 := by
      simpa using congrArg Point3.y h
    have hz : 2 * (p.z - 3) = 0 := by
      simpa using congrArg Point3.z h
    rcases p with ⟨x, y, z⟩
    dsimp at hx hy hz ⊢
    have ex : x = -1 := by linarith
    have ey : y = -2 := by linarith
    have ez : z = 3 := by linarith
    subst x
    subst y
    subst z
    rfl
  · rintro rfl
    norm_num [basePoint]

theorem gap3 :
    ∀ p : Point3, p ∈ ({basePoint} : Set Point3) →
      partialX u p = 2 * (p.x + 1) ∧ 2 * (p.x + 1) = 0 ∧
      partialY u p = 2 * (p.y + 2) ∧ 2 * (p.y + 2) = 0 ∧
      partialZ u p = 2 * (p.z - 3) ∧ 2 * (p.z - 3) = 0 := by
  intro p hp
  have hp' : p = basePoint := by
    simpa using hp
  subst p
  have hx :
      partialX u basePoint = 2 * (basePoint.x + 1) := by
    simpa [gradient] using congrArg Point3.x (gap1 basePoint)
  have hy :
      partialY u basePoint = 2 * (basePoint.y + 2) := by
    simpa [gradient] using congrArg Point3.y (gap1 basePoint)
  have hz :
      partialZ u basePoint = 2 * (basePoint.z - 3) := by
    simpa [gradient] using congrArg Point3.z (gap1 basePoint)
  exact
    ⟨hx, by norm_num [basePoint],
      hy, by norm_num [basePoint],
      hz, by norm_num [basePoint]⟩

theorem gap4 :
    ∀ v : Point3,
      secondVariation v = 2 * (v.x ^ 2 + v.y ^ 2 + v.z ^ 2) := by
  intro v
  rfl

theorem gap5 :
    ∀ v : Point3, v ≠ ⟨0, 0, 0⟩ →
      0 < 2 * (v.x ^ 2 + v.y ^ 2 + v.z ^ 2) := by
  rintro ⟨x, y, z⟩ hv
  by_contra h
  have hx : x = 0 := by
    nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
  have hy : y = 0 := by
    nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
  have hz : z = 0 := by
    nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
  subst x
  subst y
  subst z
  exact hv rfl

theorem gap6 :
    PositiveDefiniteSecondVariation := by
  intro v hv
  simpa [secondVariation] using gap5 v hv

theorem gap7 :
    IsUniqueGlobalMinimizer u basePoint := by
  have hcomplete (q : Point3) :
      u q = (q.x + 1) ^ 2 + (q.y + 2) ^ 2 + (q.z - 3) ^ 2 - 14 := by
    unfold u
    ring
  have hbase : u basePoint = -14 := by
    norm_num [u, basePoint]
  constructor
  · intro q
    rw [hbase, hcomplete q]
    nlinarith
      [sq_nonneg (q.x + 1), sq_nonneg (q.y + 2),
        sq_nonneg (q.z - 3)]
  · intro q hq
    rw [hcomplete q, hbase] at hq
    have hx : q.x = -1 := by
      nlinarith
        [sq_nonneg (q.x + 1), sq_nonneg (q.y + 2),
          sq_nonneg (q.z - 3)]
    have hy : q.y = -2 := by
      nlinarith
        [sq_nonneg (q.x + 1), sq_nonneg (q.y + 2),
          sq_nonneg (q.z - 3)]
    have hz : q.z = 3 := by
      nlinarith
        [sq_nonneg (q.x + 1), sq_nonneg (q.y + 2),
          sq_nonneg (q.z - 3)]
    rcases q with ⟨x, y, z⟩
    dsimp at hx hy hz ⊢
    subst x
    subst y
    subst z
    rfl

theorem gap8 :
    u basePoint = -14 := by
  norm_num [u, basePoint]

theorem gap9 :
    minimumPoints = {basePoint} := by
  apply Set.ext
  intro p
  simp only [minimumPoints, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro hp
    exact
      (gap7).2 p
        (le_antisymm (hp basePoint) ((gap7).1 p))
  · rintro rfl
    exact (gap7).1

end

end ProofGap.Exercise3642
