import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3659

noncomputable section

structure Point3 where
  x : ℝ
  y : ℝ
  z : ℝ
  deriving DecidableEq

def objective (q : Point3) : ℝ :=
  q.x - 2 * q.y + 2 * q.z

def sphere : Set Point3 :=
  {q | q.x ^ 2 + q.y ^ 2 + q.z ^ 2 = 1}

def critical (q : Point3) (lambda : ℝ) : Prop :=
  1 + 2 * lambda * q.x = 0 ∧
    -2 + 2 * lambda * q.y = 0 ∧
    2 + 2 * lambda * q.z = 0 ∧
    q ∈ sphere

def positivePoint : Point3 :=
  ⟨1 / 3, -2 / 3, 2 / 3⟩

def negativePoint : Point3 :=
  ⟨-1 / 3, 2 / 3, -2 / 3⟩

def maximizers : Set Point3 :=
  {q | q ∈ sphere ∧ ∀ r ∈ sphere, objective r ≤ objective q}

def minimizers : Set Point3 :=
  {q | q ∈ sphere ∧ ∀ r ∈ sphere, objective q ≤ objective r}

private theorem objective_le_three (q : Point3) (hq : q ∈ sphere) :
    objective q ≤ 3 := by
  rcases q with ⟨x, y, z⟩
  change x ^ 2 + y ^ 2 + z ^ 2 = 1 at hq
  change x - 2 * y + 2 * z ≤ 3
  nlinarith [sq_nonneg (x - 1 / 3), sq_nonneg (y + 2 / 3),
    sq_nonneg (z - 2 / 3)]

private theorem neg_three_le_objective (q : Point3) (hq : q ∈ sphere) :
    -3 ≤ objective q := by
  rcases q with ⟨x, y, z⟩
  change x ^ 2 + y ^ 2 + z ^ 2 = 1 at hq
  change -3 ≤ x - 2 * y + 2 * z
  nlinarith [sq_nonneg (x + 1 / 3), sq_nonneg (y - 2 / 3),
    sq_nonneg (z + 2 / 3)]

private theorem eq_positivePoint_of_objective_ge_three
    (q : Point3) (hq : q ∈ sphere) (hobj : 3 ≤ objective q) :
    q = positivePoint := by
  rcases q with ⟨x, y, z⟩
  change x ^ 2 + y ^ 2 + z ^ 2 = 1 at hq
  change 3 ≤ x - 2 * y + 2 * z at hobj
  have hx : x = (1 : ℝ) / 3 := by
    nlinarith [sq_nonneg (x - 1 / 3), sq_nonneg (y + 2 / 3),
      sq_nonneg (z - 2 / 3)]
  have hy : y = -(2 : ℝ) / 3 := by
    nlinarith [sq_nonneg (x - 1 / 3), sq_nonneg (y + 2 / 3),
      sq_nonneg (z - 2 / 3)]
  have hz : z = (2 : ℝ) / 3 := by
    nlinarith [sq_nonneg (x - 1 / 3), sq_nonneg (y + 2 / 3),
      sq_nonneg (z - 2 / 3)]
  subst x
  subst y
  subst z
  rfl

private theorem eq_negativePoint_of_objective_le_neg_three
    (q : Point3) (hq : q ∈ sphere) (hobj : objective q ≤ -3) :
    q = negativePoint := by
  rcases q with ⟨x, y, z⟩
  change x ^ 2 + y ^ 2 + z ^ 2 = 1 at hq
  change x - 2 * y + 2 * z ≤ -3 at hobj
  have hx : x = -(1 : ℝ) / 3 := by
    nlinarith [sq_nonneg (x + 1 / 3), sq_nonneg (y - 2 / 3),
      sq_nonneg (z + 2 / 3)]
  have hy : y = (2 : ℝ) / 3 := by
    nlinarith [sq_nonneg (x + 1 / 3), sq_nonneg (y - 2 / 3),
      sq_nonneg (z + 2 / 3)]
  have hz : z = -(2 : ℝ) / 3 := by
    nlinarith [sq_nonneg (x + 1 / 3), sq_nonneg (y - 2 / 3),
      sq_nonneg (z + 2 / 3)]
  subst x
  subst y
  subst z
  rfl

theorem gap1 :
    ∃ P₁ : Point3, P₁ = positivePoint := by
  exact ⟨positivePoint, rfl⟩

theorem gap2 :
    ∃ P₂ : Point3, P₂ = negativePoint := by
  exact ⟨negativePoint, rfl⟩

theorem gap3 :
    objective positivePoint = 3 := by
  norm_num [objective, positivePoint]

theorem gap4 :
    objective negativePoint = -3 := by
  norm_num [objective, negativePoint]

theorem gap5 :
    {q | ∃ lambda, critical q lambda} =
      ({positivePoint, negativePoint} : Set Point3) := by
  ext q
  constructor
  · rintro ⟨lambda, hcrit⟩
    rcases q with ⟨x, y, z⟩
    rcases hcrit with ⟨hx, hy, hz, hs⟩
    change x ^ 2 + y ^ 2 + z ^ 2 = 1 at hs
    have hxl : lambda * x = -(1 : ℝ) / 2 := by
      nlinarith
    have hyl : lambda * y = 1 := by
      nlinarith
    have hzl : lambda * z = -1 := by
      nlinarith
    have hl_sq : lambda ^ 2 = (9 : ℝ) / 4 := by
      calc
        lambda ^ 2 = lambda ^ 2 * (x ^ 2 + y ^ 2 + z ^ 2) := by rw [hs]; ring
        _ = (lambda * x) ^ 2 + (lambda * y) ^ 2 + (lambda * z) ^ 2 := by ring
        _ = (9 : ℝ) / 4 := by rw [hxl, hyl, hzl]; norm_num
    have hl : lambda = (3 : ℝ) / 2 ∨ lambda = -(3 : ℝ) / 2 := by
      rcases le_total 0 lambda with hnonneg | hnonpos
      · left
        nlinarith
      · right
        nlinarith
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases hl with hl | hl
    · right
      have hx' : x = (-1 / 3 : ℝ) := by
        nlinarith [hxl]
      have hy' : y = (2 / 3 : ℝ) := by
        nlinarith [hyl]
      have hz' : z = (-2 / 3 : ℝ) := by
        nlinarith [hzl]
      subst x
      subst y
      subst z
      rfl
    · left
      have hx' : x = (1 / 3 : ℝ) := by
        nlinarith [hxl]
      have hy' : y = (-2 / 3 : ℝ) := by
        nlinarith [hyl]
      have hz' : z = (2 / 3 : ℝ) := by
        nlinarith [hzl]
      subst x
      subst y
      subst z
      rfl
  · intro hq
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl
    · refine ⟨-(3 : ℝ) / 2, ?_⟩
      norm_num [critical, sphere, positivePoint]
    · refine ⟨(3 : ℝ) / 2, ?_⟩
      norm_num [critical, sphere, negativePoint]

theorem gap6 :
    maximizers = ({positivePoint} : Set Point3) := by
  ext q
  change (q ∈ sphere ∧ ∀ r ∈ sphere, objective r ≤ objective q) ↔ q = positivePoint
  constructor
  · rintro ⟨hq, hmax⟩
    have hp : positivePoint ∈ sphere := by
      norm_num [positivePoint, sphere]
    have hge : 3 ≤ objective q := by
      calc
        3 = objective positivePoint := gap3.symm
        _ ≤ objective q := hmax positivePoint hp
    exact eq_positivePoint_of_objective_ge_three q hq hge
  · intro hq
    subst q
    constructor
    · norm_num [positivePoint, sphere]
    · intro r hr
      rw [gap3]
      exact objective_le_three r hr

theorem gap7 :
    objective positivePoint = 3 := by
  exact gap3

theorem gap8 :
    minimizers = ({negativePoint} : Set Point3) := by
  ext q
  change (q ∈ sphere ∧ ∀ r ∈ sphere, objective q ≤ objective r) ↔ q = negativePoint
  constructor
  · rintro ⟨hq, hmin⟩
    have hn : negativePoint ∈ sphere := by
      norm_num [negativePoint, sphere]
    have hle : objective q ≤ -3 := by
      calc
        objective q ≤ objective negativePoint := hmin negativePoint hn
        _ = -3 := gap4
    exact eq_negativePoint_of_objective_le_neg_three q hq hle
  · intro hq
    subst q
    constructor
    · norm_num [negativePoint, sphere]
    · intro r hr
      rw [gap4]
      exact neg_three_le_objective r hr

theorem gap9 :
    objective negativePoint = -3 := by
  exact gap4

end

end ProofGap.Exercise3659
