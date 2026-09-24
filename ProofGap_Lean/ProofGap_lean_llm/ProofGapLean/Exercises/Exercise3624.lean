import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3624

noncomputable section

def z (p : ℝ × ℝ) : ℝ :=
  p.1 ^ 2 - p.1 * p.2 + p.2 ^ 2 - 2 * p.1 + p.2

def partialX (g : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun x => g (x, p.2)) p.1

def partialY (g : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun y => g (p.1, y)) p.2

def partialXX (g : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun x => partialX g (x, p.2)) p.1

def partialXY (g : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun y => partialX g (p.1, y)) p.2

def partialYY (g : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun y => partialY g (p.1, y)) p.2

def basePoint : ℝ × ℝ :=
  (1, 0)

def hessianA : ℝ :=
  partialXX z basePoint

def hessianB : ℝ :=
  partialXY z basePoint

def hessianC : ℝ :=
  partialYY z basePoint

def hessianDiscriminant : ℝ :=
  hessianA * hessianC - hessianB ^ 2

def IsUniqueGlobalMinimizer
    (g : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : Prop :=
  (∀ q, g p ≤ g q) ∧ (∀ q, g q = g p → q = p)

private theorem partialX_z (p : ℝ × ℝ) : partialX z p = 2 * p.1 - p.2 - 2 := by
  unfold partialX
  let hx := hasDerivAt_id p.1
  have hsq := hx.mul hx
  have hxy := hx.mul_const p.2
  have htwo := hx.const_mul 2
  have h := (((hsq.sub hxy).add_const (p.2 ^ 2)).sub htwo).add_const p.2
  convert h.deriv using 1 <;> simp [z, pow_two] <;> ring

private theorem partialY_z (p : ℝ × ℝ) : partialY z p = -p.1 + 2 * p.2 + 1 := by
  unfold partialY
  let hy := hasDerivAt_id p.2
  have hconst := hasDerivAt_const p.2 (p.1 ^ 2)
  have hxy := hy.const_mul p.1
  have hsq := hy.mul hy
  have h0 := (((hconst.sub hxy).add hsq).sub_const (2 * p.1)).add hy
  have h := h0.add_const 0
  convert h.deriv using 1 <;> simp [z, pow_two] <;> ring

private theorem partialXX_z (p : ℝ × ℝ) : partialXX z p = 2 := by
  unfold partialXX
  have hf : (fun x : ℝ => partialX z (x, p.2)) =
      (fun x : ℝ => 2 * x - p.2 - 2) := by
    funext x
    simpa using partialX_z (x, p.2)
  rw [hf]
  let hx := hasDerivAt_id p.1
  have h := ((hx.const_mul 2).sub_const p.2).sub_const 2
  convert h.deriv using 1 <;> ring

private theorem partialXY_z (p : ℝ × ℝ) : partialXY z p = -1 := by
  unfold partialXY
  have hf : (fun y : ℝ => partialX z (p.1, y)) =
      (fun y : ℝ => 2 * p.1 - y - 2) := by
    funext y
    simpa using partialX_z (p.1, y)
  rw [hf]
  let hy := hasDerivAt_id p.2
  have h := ((hasDerivAt_const p.2 (2 * p.1)).sub hy).sub_const 2
  convert h.deriv using 1 <;> ring

private theorem partialYY_z (p : ℝ × ℝ) : partialYY z p = 2 := by
  unfold partialYY
  have hf : (fun y : ℝ => partialY z (p.1, y)) =
      (fun y : ℝ => -p.1 + 2 * y + 1) := by
    funext y
    simpa using partialY_z (p.1, y)
  rw [hf]
  let hy := hasDerivAt_id p.2
  have h := ((hasDerivAt_const p.2 (-p.1)).add (hy.const_mul 2)).add_const 1
  convert h.deriv using 1 <;> ring

theorem gap1 :
    ∀ p : ℝ × ℝ, p ∈ ({basePoint} : Set (ℝ × ℝ)) →
      partialX z p = 2 * p.1 - p.2 - 2 ∧
      2 * p.1 - p.2 - 2 = 0 ∧
      partialY z p = -p.1 + 2 * p.2 + 1 ∧
      -p.1 + 2 * p.2 + 1 = 0 := by
  intro p hp
  simp only [Set.mem_singleton_iff] at hp
  subst p
  simp [partialX_z, partialY_z, basePoint]

theorem gap2 :
    basePoint = (1, 0) := by
  rfl

theorem gap3 :
    hessianA = partialXX z basePoint := by
  rfl

theorem gap4 :
    partialXX z basePoint = 2 := by
  exact partialXX_z basePoint

theorem gap5 :
    hessianB = partialXY z basePoint := by
  rfl

theorem gap6 :
    partialXY z basePoint = -1 := by
  exact partialXY_z basePoint

theorem gap7 :
    hessianC = partialYY z basePoint := by
  rfl

theorem gap8 :
    partialYY z basePoint = 2 := by
  exact partialYY_z basePoint

theorem gap9 :
    hessianDiscriminant = 3 := by
  norm_num [hessianDiscriminant, hessianA, hessianB, hessianC,
    partialXX_z, partialXY_z, partialYY_z]

theorem gap10 :
    (3 : ℝ) > 0 := by
  norm_num

theorem gap11 :
    hessianDiscriminant > 0 := by
  rw [gap9]
  exact gap10

theorem gap12 :
    IsUniqueGlobalMinimizer z basePoint := by
  constructor
  · rintro ⟨x, y⟩
    have h1 : 0 ≤ (x - 1) ^ 2 := sq_nonneg (x - 1)
    have h2 : 0 ≤ ((x - 1) - y) ^ 2 := sq_nonneg ((x - 1) - y)
    have h3 : 0 ≤ y ^ 2 := sq_nonneg y
    norm_num [z, basePoint]
    nlinarith
  · rintro ⟨x, y⟩ hq
    norm_num [z, basePoint] at hq
    have h1 : 0 ≤ (x - 1) ^ 2 := sq_nonneg (x - 1)
    have h2 : 0 ≤ ((x - 1) - y) ^ 2 := sq_nonneg ((x - 1) - y)
    have h3 : 0 ≤ y ^ 2 := sq_nonneg y
    have hy : y = 0 := by
      nlinarith
    have hx : x = 1 := by
      nlinarith
    simp [basePoint, hx, hy]

theorem gap13 :
    z basePoint = -1 := by
  norm_num [z, basePoint]

end

end ProofGap.Exercise3624
