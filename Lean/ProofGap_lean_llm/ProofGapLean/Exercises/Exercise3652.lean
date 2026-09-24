import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise3652

noncomputable section

structure Point3 where
  x : ℝ
  y : ℝ
  z : ℝ
  deriving DecidableEq

def definingFunction (p : Point3) : ℝ :=
  p.x ^ 2 + p.y ^ 2 + p.z ^ 2 -
    p.x * p.z - p.y * p.z +
    2 * p.x + 2 * p.y + 2 * p.z - 2

def surface : Set Point3 :=
  {p | definingFunction p = 0}

def height (p : Point3) : ℝ :=
  p.z

def gradientF (p : Point3) : Point3 :=
  ⟨2 * p.x - p.z + 2,
    2 * p.y - p.z + 2,
    2 * p.z - p.x - p.y + 2⟩

def root6 : ℝ :=
  Real.sqrt 6

def pMin : Point3 :=
  ⟨-(3 + root6), -(3 + root6), -(4 + 2 * root6)⟩

def pMax : Point3 :=
  ⟨-(3 - root6), -(3 - root6), 2 * root6 - 4⟩

def HeightCritical (p : Point3) : Prop :=
  p ∈ surface ∧
    2 * p.x - p.z + 2 = 0 ∧
    2 * p.y - p.z + 2 = 0

def heightCriticalPoints : Set Point3 :=
  {p | HeightCritical p}

def graphSecondVariation (p v : Point3) : ℝ :=
  -2 * ((v.x) ^ 2 + (v.y) ^ 2) /
    (2 * p.z - p.x - p.y + 2)

def PositiveDefiniteAtPMin : Prop :=
  ∀ v : Point3, v.x ≠ 0 ∨ v.y ≠ 0 →
    0 < graphSecondVariation pMin v

def IsUniqueGlobalMinimizer (p : Point3) : Prop :=
  p ∈ surface ∧ (∀ q ∈ surface, height p ≤ height q) ∧
    (∀ q ∈ surface, height q = height p → q = p)

def IsUniqueGlobalMaximizer (p : Point3) : Prop :=
  p ∈ surface ∧ (∀ q ∈ surface, height q ≤ height p) ∧
    (∀ q ∈ surface, height q = height p → q = p)

def minimumPoints : Set Point3 :=
  {p | p ∈ surface ∧ ∀ q ∈ surface, height p ≤ height q}

def maximumPoints : Set Point3 :=
  {p | p ∈ surface ∧ ∀ q ∈ surface, height q ≤ height p}

private lemma sqrt6_nonneg : 0 ≤ Real.sqrt 6 := by
  exact Real.sqrt_nonneg 6

private lemma sqrt6_pos : 0 < Real.sqrt 6 := by
  exact Real.sqrt_pos.2 (by norm_num)

private lemma sqrt6_ne : Real.sqrt 6 ≠ 0 :=
  ne_of_gt sqrt6_pos

private lemma sqrt6_sq : (Real.sqrt 6) ^ 2 = 6 := by
  exact Real.sq_sqrt (by norm_num)

private lemma point3_eq {p q : Point3}
    (hx : p.x = q.x) (hy : p.y = q.y) (hz : p.z = q.z) : p = q := by
  cases p
  cases q
  simp_all

private lemma surface_quadratic_identity (p : Point3) (hp : p ∈ surface) :
    (2 * p.x - p.z + 2) ^ 2 +
        (2 * p.y - p.z + 2) ^ 2 +
        2 * (p.z + 4) ^ 2 = 48 := by
  change definingFunction p = 0 at hp
  unfold definingFunction at hp
  nlinarith

private lemma surface_height_bounds (p : Point3) (hp : p ∈ surface) :
    -(4 + 2 * Real.sqrt 6) ≤ p.z ∧
      p.z ≤ 2 * Real.sqrt 6 - 4 := by
  have hid := surface_quadratic_identity p hp
  have hx := sq_nonneg (2 * p.x - p.z + 2)
  have hy := sq_nonneg (2 * p.y - p.z + 2)
  constructor
  · by_contra hn
    have hlt : p.z < -(4 + 2 * Real.sqrt 6) := lt_of_not_ge hn
    have hprod :
        0 < (-(p.z + 4) - 2 * Real.sqrt 6) *
            (-(p.z + 4) + 2 * Real.sqrt 6) := by
      apply mul_pos
      · nlinarith
      · nlinarith [sqrt6_nonneg]
    nlinarith [sqrt6_sq]
  · by_contra hn
    have hlt : 2 * Real.sqrt 6 - 4 < p.z := lt_of_not_ge hn
    have hprod :
        0 < (p.z + 4 - 2 * Real.sqrt 6) *
            (p.z + 4 + 2 * Real.sqrt 6) := by
      apply mul_pos
      · nlinarith
      · nlinarith [sqrt6_nonneg]
    nlinarith [sqrt6_sq]

private lemma pMin_mem_surface : pMin ∈ surface := by
  change definingFunction pMin = 0
  simp only [definingFunction, pMin, root6]
  nlinarith [sqrt6_sq]

private lemma pMax_mem_surface : pMax ∈ surface := by
  change definingFunction pMax = 0
  simp only [definingFunction, pMax, root6]
  nlinarith [sqrt6_sq]

private lemma eq_pMin_of_surface_height
    (p : Point3) (hp : p ∈ surface)
    (hz : p.z = -(4 + 2 * Real.sqrt 6)) : p = pMin := by
  have hid := surface_quadratic_identity p hp
  rw [hz] at hid
  have hy_nonneg :=
    sq_nonneg (2 * p.y - (-(4 + 2 * Real.sqrt 6)) + 2)
  have hx_sq :
      (2 * p.x - (-(4 + 2 * Real.sqrt 6)) + 2) ^ 2 = 0 := by
    nlinarith [sqrt6_sq]
  have hx_zero :
      2 * p.x - (-(4 + 2 * Real.sqrt 6)) + 2 = 0 := by
    rw [pow_two] at hx_sq
    rcases mul_eq_zero.mp hx_sq with h | h
    · exact h
    · exact h
  have hx_nonneg :=
    sq_nonneg (2 * p.x - (-(4 + 2 * Real.sqrt 6)) + 2)
  have hy_sq :
      (2 * p.y - (-(4 + 2 * Real.sqrt 6)) + 2) ^ 2 = 0 := by
    nlinarith [sqrt6_sq]
  have hy_zero :
      2 * p.y - (-(4 + 2 * Real.sqrt 6)) + 2 = 0 := by
    rw [pow_two] at hy_sq
    rcases mul_eq_zero.mp hy_sq with h | h
    · exact h
    · exact h
  apply point3_eq
  · change p.x = -(3 + root6)
    unfold root6
    nlinarith
  · change p.y = -(3 + root6)
    unfold root6
    nlinarith
  · change p.z = -(4 + 2 * root6)
    simpa [root6] using hz

private lemma eq_pMax_of_surface_height
    (p : Point3) (hp : p ∈ surface)
    (hz : p.z = 2 * Real.sqrt 6 - 4) : p = pMax := by
  have hid := surface_quadratic_identity p hp
  rw [hz] at hid
  have hy_nonneg :=
    sq_nonneg (2 * p.y - (2 * Real.sqrt 6 - 4) + 2)
  have hx_sq :
      (2 * p.x - (2 * Real.sqrt 6 - 4) + 2) ^ 2 = 0 := by
    nlinarith [sqrt6_sq]
  have hx_zero :
      2 * p.x - (2 * Real.sqrt 6 - 4) + 2 = 0 := by
    rw [pow_two] at hx_sq
    rcases mul_eq_zero.mp hx_sq with h | h
    · exact h
    · exact h
  have hx_nonneg :=
    sq_nonneg (2 * p.x - (2 * Real.sqrt 6 - 4) + 2)
  have hy_sq :
      (2 * p.y - (2 * Real.sqrt 6 - 4) + 2) ^ 2 = 0 := by
    nlinarith [sqrt6_sq]
  have hy_zero :
      2 * p.y - (2 * Real.sqrt 6 - 4) + 2 = 0 := by
    rw [pow_two] at hy_sq
    rcases mul_eq_zero.mp hy_sq with h | h
    · exact h
    · exact h
  apply point3_eq
  · change p.x = -(3 - root6)
    unfold root6
    nlinarith
  · change p.y = -(3 - root6)
    unfold root6
    nlinarith
  · change p.z = 2 * root6 - 4
    simpa [root6] using hz

private lemma pMin_denominator :
    2 * pMin.z - pMin.x - pMin.y + 2 = -2 * Real.sqrt 6 := by
  dsimp [pMin, root6]
  ring

private lemma pMax_denominator :
    2 * pMax.z - pMax.x - pMax.y + 2 = 2 * Real.sqrt 6 := by
  dsimp [pMax, root6]
  ring

private lemma pMin_denominator_ne :
    2 * pMin.z - pMin.x - pMin.y + 2 ≠ 0 := by
  rw [pMin_denominator]
  nlinarith [sqrt6_pos]

private lemma pMax_denominator_ne :
    2 * pMax.z - pMax.x - pMax.y + 2 ≠ 0 := by
  rw [pMax_denominator]
  nlinarith [sqrt6_pos]

private lemma graphSecondVariation_identity_of_ne
    (p v : Point3)
    (hd : 2 * p.z - p.x - p.y + 2 ≠ 0) :
    2 * (v.x) ^ 2 + 2 * (v.y) ^ 2 +
        (2 * p.z - p.x - p.y + 2) *
          graphSecondVariation p v = 0 := by
  unfold graphSecondVariation
  field_simp [hd]
  <;> ring

theorem gap1 :
    ∀ p : Point3,
      gradientF p =
        ⟨2 * p.x - p.z + 2,
          2 * p.y - p.z + 2,
          2 * p.z - p.x - p.y + 2⟩ := by
  intro p
  rfl

theorem gap2 :
    pMin =
      ⟨-(3 + Real.sqrt 6), -(3 + Real.sqrt 6),
        -(4 + 2 * Real.sqrt 6)⟩ := by
  rfl

theorem gap3 :
    pMax =
      ⟨-(3 - Real.sqrt 6), -(3 - Real.sqrt 6),
        2 * Real.sqrt 6 - 4⟩ := by
  rfl

theorem gap4 :
    heightCriticalPoints = {pMin, pMax} := by
  apply Set.ext
  intro p
  change HeightCritical p ↔ p ∈ ({pMin, pMax} : Set Point3)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hp, hx, hy⟩
    have hid := surface_quadratic_identity p hp
    simp [hx, hy] at hid
    have hzsq : (p.z + 4) ^ 2 = 24 := by
      nlinarith
    have hprod :
        (p.z + 4 + 2 * Real.sqrt 6) *
            (p.z + 4 - 2 * Real.sqrt 6) = 0 := by
      nlinarith [sqrt6_sq]
    rcases mul_eq_zero.mp hprod with hlo | hhi
    · left
      apply eq_pMin_of_surface_height p hp
      nlinarith
    · right
      apply eq_pMax_of_surface_height p hp
      nlinarith
  · rintro (rfl | rfl)
    · refine ⟨pMin_mem_surface, ?_, ?_⟩
      · dsimp [pMin, root6]
        ring
      · dsimp [pMin, root6]
        ring
    · refine ⟨pMax_mem_surface, ?_, ?_⟩
      · dsimp [pMax, root6]
        ring
      · dsimp [pMax, root6]
        ring

theorem gap5 :
    ∀ p : Point3, HeightCritical p →
      ∀ v : Point3,
        2 * (v.x) ^ 2 + 2 * (v.y) ^ 2 +
          (2 * p.z - p.x - p.y + 2) *
            graphSecondVariation p v = 0 := by
  intro p hp v
  have hp' : p ∈ heightCriticalPoints := by
    exact hp
  rw [gap4] at hp'
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp'
  rcases hp' with hp' | hp'
  · subst p
    exact graphSecondVariation_identity_of_ne pMin v pMin_denominator_ne
  · subst p
    exact graphSecondVariation_identity_of_ne pMax v pMax_denominator_ne

theorem gap6 :
    ∀ v : Point3,
      graphSecondVariation pMin v =
        1 / Real.sqrt 6 * ((v.x) ^ 2 + (v.y) ^ 2) := by
  intro v
  unfold graphSecondVariation
  rw [pMin_denominator]
  field_simp [sqrt6_ne]
  <;> ring

theorem gap7 :
    ∀ v : Point3, v.x ≠ 0 ∨ v.y ≠ 0 →
      0 < 1 / Real.sqrt 6 * ((v.x) ^ 2 + (v.y) ^ 2) := by
  intro v hv
  have hsum : 0 < (v.x) ^ 2 + (v.y) ^ 2 := by
    rcases hv with hx | hy
    · have hx2 : 0 < (v.x) ^ 2 := by
        positivity
      nlinarith [sq_nonneg v.y]
    · have hy2 : 0 < (v.y) ^ 2 := by
        positivity
      nlinarith [sq_nonneg v.x]
  have hcoef : 0 < 1 / Real.sqrt 6 := one_div_pos.mpr sqrt6_pos
  exact mul_pos hcoef hsum

theorem gap8 :
    PositiveDefiniteAtPMin := by
  unfold PositiveDefiniteAtPMin
  intro v hv
  rw [gap6 v]
  exact gap7 v hv

theorem gap9 :
    IsUniqueGlobalMinimizer pMin := by
  refine ⟨pMin_mem_surface, ?_, ?_⟩
  · intro q hq
    simpa [height, pMin, root6] using (surface_height_bounds q hq).1
  · intro q hq heq
    apply eq_pMin_of_surface_height q hq
    simpa [height, pMin, root6] using heq

theorem gap10 :
    height pMin = -(4 + 2 * Real.sqrt 6) := by
  rfl

theorem gap11 :
    IsUniqueGlobalMaximizer pMax := by
  refine ⟨pMax_mem_surface, ?_, ?_⟩
  · intro q hq
    simpa [height, pMax, root6] using (surface_height_bounds q hq).2
  · intro q hq heq
    apply eq_pMax_of_surface_height q hq
    simpa [height, pMax, root6] using heq

theorem gap12 :
    height pMax = 2 * Real.sqrt 6 - 4 := by
  rfl

theorem gap13 :
    ∀ p ∈ surface, 2 * p.z - p.x - p.y + 2 = 0 →
      p ∉ maximumPoints ∧ p ∉ minimumPoints := by
  intro p hp hz
  constructor
  · intro hmaximum
    change p ∈ surface ∧
        (∀ q ∈ surface, height q ≤ height p) at hmaximum
    rcases hmaximum with ⟨_, hp_bound⟩
    rcases gap11 with ⟨hpMax, hmax_bound, hmax_unique⟩
    have h₁ : height p ≤ height pMax := hmax_bound p hp
    have h₂ : height pMax ≤ height p := hp_bound pMax hpMax
    have heq : height p = height pMax := le_antisymm h₁ h₂
    have hpeq : p = pMax := hmax_unique p hp heq
    subst p
    exact pMax_denominator_ne hz
  · intro hminimum
    change p ∈ surface ∧
        (∀ q ∈ surface, height p ≤ height q) at hminimum
    rcases hminimum with ⟨_, hp_bound⟩
    rcases gap9 with ⟨hpMin, hmin_bound, hmin_unique⟩
    have h₁ : height pMin ≤ height p := hmin_bound p hp
    have h₂ : height p ≤ height pMin := hp_bound pMin hpMin
    have heq : height p = height pMin := le_antisymm h₂ h₁
    have hpeq : p = pMin := hmin_unique p hp heq
    subst p
    exact pMin_denominator_ne hz

theorem gap14 :
    (maximumPoints, minimumPoints) = ({pMax}, {pMin}) := by
  apply Prod.ext
  · apply Set.ext
    intro p
    change (p ∈ surface ∧ ∀ q ∈ surface, height q ≤ height p) ↔
      p ∈ ({pMax} : Set Point3)
    simp only [Set.mem_singleton_iff]
    constructor
    · rintro ⟨hp, hp_bound⟩
      rcases gap11 with ⟨hpMax, hmax_bound, hmax_unique⟩
      have h₁ : height p ≤ height pMax := hmax_bound p hp
      have h₂ : height pMax ≤ height p := hp_bound pMax hpMax
      exact hmax_unique p hp (le_antisymm h₁ h₂)
    · intro hp
      subst p
      rcases gap11 with ⟨hpMax, hmax_bound, _⟩
      exact ⟨hpMax, hmax_bound⟩
  · apply Set.ext
    intro p
    change (p ∈ surface ∧ ∀ q ∈ surface, height p ≤ height q) ↔
      p ∈ ({pMin} : Set Point3)
    simp only [Set.mem_singleton_iff]
    constructor
    · rintro ⟨hp, hp_bound⟩
      rcases gap9 with ⟨hpMin, hmin_bound, hmin_unique⟩
      have h₁ : height p ≤ height pMin := hp_bound pMin hpMin
      have h₂ : height pMin ≤ height p := hmin_bound p hp
      exact hmin_unique p hp (le_antisymm h₁ h₂)
    · intro hp
      subst p
      rcases gap9 with ⟨hpMin, hmin_bound, _⟩
      exact ⟨hpMin, hmin_bound⟩

end

end ProofGap.Exercise3652
