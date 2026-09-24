import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3651

noncomputable section

structure Point3 where
  x : ℝ
  y : ℝ
  z : ℝ
  deriving DecidableEq

def definingFunction (p : Point3) : ℝ :=
  p.x ^ 2 + p.y ^ 2 + p.z ^ 2 -
    2 * p.x + 2 * p.y - 4 * p.z - 10

def surface : Set Point3 :=
  {p | definingFunction p = 0}

def height (p : Point3) : ℝ :=
  p.z

def gradientF (p : Point3) : Point3 :=
  ⟨p.x - 1, p.y + 1, p.z - 2⟩

def Tangent (p v : Point3) : Prop :=
  (p.x - 1) * v.x + (p.y + 1) * v.y + (p.z - 2) * v.z = 0

def pTop : Point3 :=
  ⟨1, -1, 6⟩

def pBottom : Point3 :=
  ⟨1, -1, -2⟩

def graphSecondVariation (p v : Point3) : ℝ :=
  -((v.x) ^ 2 + (v.y) ^ 2) / (p.z - 2)

def NegativeDefiniteAtTop : Prop :=
  ∀ v : Point3, v.x ≠ 0 ∨ v.y ≠ 0 →
    graphSecondVariation pTop v < 0

def IsUniqueGlobalMaximizer (p : Point3) : Prop :=
  p ∈ surface ∧ (∀ q ∈ surface, height q ≤ height p) ∧
    (∀ q ∈ surface, height q = height p → q = p)

def IsUniqueGlobalMinimizer (p : Point3) : Prop :=
  p ∈ surface ∧ (∀ q ∈ surface, height p ≤ height q) ∧
    (∀ q ∈ surface, height q = height p → q = p)

def maximumPoints : Set Point3 :=
  {p | p ∈ surface ∧ ∀ q ∈ surface, height q ≤ height p}

def minimumPoints : Set Point3 :=
  {p | p ∈ surface ∧ ∀ q ∈ surface, height p ≤ height q}

private theorem surface_centered_eq (p : Point3) (hp : p ∈ surface) :
    (p.x - 1) ^ 2 + (p.y + 1) ^ 2 + (p.z - 2) ^ 2 = 16 := by
  change definingFunction p = 0 at hp
  unfold definingFunction at hp
  nlinarith

theorem gap1 :
    ∀ p : Point3,
      gradientF p = ⟨p.x - 1, p.y + 1, p.z - 2⟩ := by
  intro p
  rfl

theorem gap2 :
    ∀ p ∈ surface, p.x = 1 → p.y = -1 →
      ∀ v : Point3, Tangent p v → v.z = 0 := by
  intro p hp hx hy v hv
  have hs := surface_centered_eq p hp
  have hs' : (p.z - 2) ^ 2 = 16 := by
    simpa [hx, hy] using hs
  have hn : p.z - 2 ≠ 0 := by
    intro hzero
    rw [hzero] at hs'
    norm_num at hs'
  have hprod : (p.z - 2) * v.z = 0 := by
    simpa [Tangent, hx, hy] using hv
  exact (mul_eq_zero.mp hprod).resolve_left hn

theorem gap3 :
    ∀ p ∈ surface, p.x = 1 → p.y = -1 →
      (p.z = 6 ∨ p.z = -2) := by
  intro p hp hx hy
  have hs := surface_centered_eq p hp
  have hs' : (p.z - 2) ^ 2 = 16 := by
    simpa [hx, hy] using hs
  have hfac : (p.z - 6) * (p.z + 2) = 0 := by
    nlinarith [hs']
  rcases mul_eq_zero.mp hfac with h | h
  · left
    linarith
  · right
    linarith

theorem gap4 :
    ∀ p ∈ surface, p.x = 1 → p.y = -1 → p.z ≠ 2 →
      ∀ v : Point3,
        (v.x) ^ 2 + (v.y) ^ 2 +
          (p.z - 2) * graphSecondVariation p v = 0 := by
  intro p hp hx hy hz v
  have hden : p.z - 2 ≠ 0 := sub_ne_zero.mpr hz
  unfold graphSecondVariation
  field_simp [hden] <;> ring

theorem gap5 :
    ∀ v : Point3,
      graphSecondVariation pTop v =
        -(1 / 4 : ℝ) * ((v.x) ^ 2 + (v.y) ^ 2) := by
  intro v
  dsimp [graphSecondVariation, pTop]
  ring

theorem gap6 :
    ∀ v : Point3, v.x ≠ 0 ∨ v.y ≠ 0 →
      -(1 / 4 : ℝ) * ((v.x) ^ 2 + (v.y) ^ 2) < 0 := by
  intro v hv
  rcases hv with hx | hy
  · nlinarith [sq_pos_of_ne_zero hx, sq_nonneg v.y]
  · nlinarith [sq_nonneg v.x, sq_pos_of_ne_zero hy]

theorem gap7 :
    NegativeDefiniteAtTop := by
  unfold NegativeDefiniteAtTop
  intro v hv
  rw [gap5 v]
  exact gap6 v hv

theorem gap8 :
    IsUniqueGlobalMaximizer pTop := by
  unfold IsUniqueGlobalMaximizer
  refine ⟨?_, ?_, ?_⟩
  · change definingFunction pTop = 0
    norm_num [definingFunction, pTop]
  · intro q hq
    change q.z ≤ 6
    have hs := surface_centered_eq q hq
    nlinarith [sq_nonneg (q.x - 1), sq_nonneg (q.y + 1),
      sq_nonneg (q.z - 6)]
  · intro q hq hh
    have hs := surface_centered_eq q hq
    have hz : q.z = 6 := by
      simpa [height, pTop] using hh
    rw [hz] at hs
    norm_num at hs
    have hx : q.x = 1 := by
      nlinarith [sq_nonneg (q.x - 1), sq_nonneg (q.y + 1)]
    have hy : q.y = -1 := by
      nlinarith [sq_nonneg (q.x - 1), sq_nonneg (q.y + 1)]
    rcases q with ⟨x, y, z⟩
    change x = 1 at hx
    change y = -1 at hy
    change z = 6 at hz
    subst x
    subst y
    subst z
    rfl

theorem gap9 :
    height pTop = 6 := by
  rfl

theorem gap10 :
    IsUniqueGlobalMinimizer pBottom := by
  unfold IsUniqueGlobalMinimizer
  refine ⟨?_, ?_, ?_⟩
  · change definingFunction pBottom = 0
    norm_num [definingFunction, pBottom]
  · intro q hq
    change -2 ≤ q.z
    have hs := surface_centered_eq q hq
    nlinarith [sq_nonneg (q.x - 1), sq_nonneg (q.y + 1),
      sq_nonneg (q.z + 2)]
  · intro q hq hh
    have hs := surface_centered_eq q hq
    have hz : q.z = -2 := by
      simpa [height, pBottom] using hh
    rw [hz] at hs
    norm_num at hs
    have hx : q.x = 1 := by
      nlinarith [sq_nonneg (q.x - 1), sq_nonneg (q.y + 1)]
    have hy : q.y = -1 := by
      nlinarith [sq_nonneg (q.x - 1), sq_nonneg (q.y + 1)]
    rcases q with ⟨x, y, z⟩
    change x = 1 at hx
    change y = -1 at hy
    change z = -2 at hz
    subst x
    subst y
    subst z
    rfl

theorem gap11 :
    height pBottom = -2 := by
  rfl

theorem gap12 :
    ∀ p ∈ surface, p.z = 2 →
      p ∉ maximumPoints ∧ p ∉ minimumPoints := by
  intro p hp hz
  constructor
  · intro hmax
    change p ∈ surface ∧ ∀ q ∈ surface, height q ≤ height p at hmax
    have htop : pTop ∈ surface := by
      change definingFunction pTop = 0
      norm_num [definingFunction, pTop]
    have hle := hmax.2 pTop htop
    norm_num [height, pTop, hz] at hle
  · intro hmin
    change p ∈ surface ∧ ∀ q ∈ surface, height p ≤ height q at hmin
    have hbottom : pBottom ∈ surface := by
      change definingFunction pBottom = 0
      norm_num [definingFunction, pBottom]
    have hle := hmin.2 pBottom hbottom
    norm_num [height, pBottom, hz] at hle

theorem gap13 :
    (maximumPoints, minimumPoints) = ({pTop}, {pBottom}) := by
  have htop :
      pTop ∈ surface ∧
        (∀ q ∈ surface, height q ≤ height pTop) ∧
        (∀ q ∈ surface, height q = height pTop → q = pTop) := by
    simpa only [IsUniqueGlobalMaximizer] using gap8
  have hbottom :
      pBottom ∈ surface ∧
        (∀ q ∈ surface, height pBottom ≤ height q) ∧
        (∀ q ∈ surface, height q = height pBottom → q = pBottom) := by
    simpa only [IsUniqueGlobalMinimizer] using gap10
  apply Prod.ext
  · apply Set.ext
    intro p
    constructor
    · intro hp
      change p ∈ surface ∧ (∀ q ∈ surface, height q ≤ height p) at hp
      have heq : height p = height pTop :=
        le_antisymm (htop.2.1 p hp.1) (hp.2 pTop htop.1)
      have hp_eq : p = pTop := htop.2.2 p hp.1 heq
      simpa [hp_eq]
    · intro hp
      have hp_eq : p = pTop := by
        simpa using hp
      subst p
      exact ⟨htop.1, htop.2.1⟩
  · apply Set.ext
    intro p
    constructor
    · intro hp
      change p ∈ surface ∧ (∀ q ∈ surface, height p ≤ height q) at hp
      have heq : height p = height pBottom :=
        le_antisymm (hp.2 pBottom hbottom.1) (hbottom.2.1 p hp.1)
      have hp_eq : p = pBottom := hbottom.2.2 p hp.1 heq
      simpa [hp_eq]
    · intro hp
      have hp_eq : p = pBottom := by
        simpa using hp
      subst p
      exact ⟨hbottom.1, hbottom.2.1⟩

end

end ProofGap.Exercise3651
