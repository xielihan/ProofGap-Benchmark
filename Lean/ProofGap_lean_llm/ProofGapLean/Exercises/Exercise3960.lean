import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3960

noncomputable section

def triangle : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1 - p.1}

def square : Set (ℝ × ℝ) :=
  Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1

def xiCoord (x y : ℝ) : ℝ :=
  x + y

def etaCoord (x y : ℝ) : ℝ :=
  if x + y = 0 then 0 else y / (x + y)

def inverseMap (q : ℝ × ℝ) : ℝ × ℝ :=
  (q.1 * (1 - q.2), q.1 * q.2)

theorem gap1 (x y : ℝ) (hp : (x, y) ∈ triangle) :
    0 ≤ x + y := by
  change 0 ≤ x ∧ x ≤ 1 ∧ 0 ≤ y ∧ y ≤ 1 - x at hp
  rcases hp with ⟨hx0, hx1, hy0, hy1⟩
  linarith

theorem gap2 (x y : ℝ) (hp : (x, y) ∈ triangle) :
    x + y ≤ 1 := by
  change 0 ≤ x ∧ x ≤ 1 ∧ 0 ≤ y ∧ y ≤ 1 - x at hp
  rcases hp with ⟨hx0, hx1, hy0, hy1⟩
  linarith

theorem gap3 (x y : ℝ) (hp : (x, y) ∈ triangle) :
    (0 : ℝ) ≤ 1 := by
  exact zero_le_one

theorem gap4 (x y : ℝ) (hp : (x, y) ∈ triangle) :
    0 ≤ xiCoord x y := by
  simpa [xiCoord] using gap1 x y hp

theorem gap5 (x y : ℝ) (hp : (x, y) ∈ triangle) :
    xiCoord x y ≤ 1 := by
  simpa [xiCoord] using gap2 x y hp

theorem gap6 (x y : ℝ) (hp : (x, y) ∈ triangle) :
    (0 : ℝ) ≤ 1 := by
  exact zero_le_one

theorem gap7 (x y : ℝ) (hxi : xiCoord x y ≠ 0) :
    etaCoord x y = y / xiCoord x y := by
  have hsum : x + y ≠ 0 := by
    simpa [xiCoord] using hxi
  simp [etaCoord, xiCoord, hsum]

theorem gap8 (x y : ℝ) (hp : (x, y) ∈ triangle) :
    etaCoord x y ≤ y / (0 + y) := by
  change 0 ≤ x ∧ x ≤ 1 ∧ 0 ≤ y ∧ y ≤ 1 - x at hp
  rcases hp with ⟨hx0, hx1, hy0, hy1⟩
  by_cases hy : y = 0
  · subst y
    simp [etaCoord, xiCoord]
  · have hypos : 0 < y := lt_of_le_of_ne hy0 (Ne.symm hy)
    have hsum : 0 < x + y := by linarith
    have hxi : xiCoord x y ≠ 0 := by
      simpa [xiCoord] using ne_of_gt hsum
    rw [gap7 x y hxi]
    have hden : 0 < 0 + y := by simpa using hypos
    apply (div_le_div_iff₀ hsum hden).2
    nlinarith [mul_nonneg hy0 hx0]

theorem gap9 (x y : ℝ) (hy : 0 < y) :
    y / (0 + y) = 1 := by
  simp [ne_of_gt hy]

theorem gap10 (x y : ℝ) (hp : (x, y) ∈ triangle) :
    etaCoord x y ≤ 1 := by
  change 0 ≤ x ∧ x ≤ 1 ∧ 0 ≤ y ∧ y ≤ 1 - x at hp
  rcases hp with ⟨hx0, hx1, hy0, hy1⟩
  by_cases hy : y = 0
  · subst y
    simp [etaCoord]
  · have hypos : 0 < y := lt_of_le_of_ne hy0 (Ne.symm hy)
    have h := gap8 x y ⟨hx0, hx1, hy0, hy1⟩
    rw [gap9 x y hypos] at h
    exact h

theorem gap11 (x y : ℝ) (hp : (x, y) ∈ triangle) :
    0 ≤ etaCoord x y := by
  change 0 ≤ x ∧ x ≤ 1 ∧ 0 ≤ y ∧ y ≤ 1 - x at hp
  rcases hp with ⟨hx0, hx1, hy0, hy1⟩
  by_cases hsum : x + y = 0
  · simp [etaCoord, hsum]
  · have hsum0 : 0 ≤ x + y := by linarith
    have hsumpos : 0 < x + y := lt_of_le_of_ne hsum0 (Ne.symm hsum)
    simp only [etaCoord, hsum, if_false]
    exact div_nonneg hy0 (le_of_lt hsumpos)

theorem gap12 (x y : ℝ) (hp : (x, y) ∈ triangle) :
    0 ≤ etaCoord x y := by
  exact gap11 x y hp

theorem gap13 (x y : ℝ) (hp : (x, y) ∈ triangle) :
    etaCoord x y ≤ 1 := by
  exact gap10 x y hp

theorem gap14 (x y : ℝ) (hp : (x, y) ∈ triangle) :
    (0 : ℝ) ≤ 1 := by
  exact zero_le_one

theorem gap15 (xi eta : ℝ) (hq : (xi, eta) ∈ square) :
    0 ≤ (inverseMap (xi, eta)).1 + (inverseMap (xi, eta)).2 := by
  change (0 ≤ xi ∧ xi ≤ 1) ∧ (0 ≤ eta ∧ eta ≤ 1) at hq
  rcases hq with ⟨⟨hxi0, hxi1⟩, ⟨heta0, heta1⟩⟩
  change 0 ≤ xi * (1 - eta) + xi * eta
  nlinarith

theorem gap16 (xi eta : ℝ) (hq : (xi, eta) ∈ square) :
    (inverseMap (xi, eta)).1 + (inverseMap (xi, eta)).2 ≤ 1 := by
  change (0 ≤ xi ∧ xi ≤ 1) ∧ (0 ≤ eta ∧ eta ≤ 1) at hq
  rcases hq with ⟨⟨hxi0, hxi1⟩, ⟨heta0, heta1⟩⟩
  change xi * (1 - eta) + xi * eta ≤ 1
  nlinarith

theorem gap17 (xi eta : ℝ) (hq : (xi, eta) ∈ square) :
    (0 : ℝ) ≤ 1 := by
  exact zero_le_one

theorem gap18 (xi eta : ℝ) :
    (inverseMap (xi, eta)).2 = xi * eta := by
  rfl

theorem gap19 (xi eta : ℝ) :
    (inverseMap (xi, eta)).1 = xi * (1 - eta) := by
  rfl

theorem gap20 (xi eta : ℝ) (hq : (xi, eta) ∈ square) :
    0 ≤ (inverseMap (xi, eta)).1 := by
  change (0 ≤ xi ∧ xi ≤ 1) ∧ (0 ≤ eta ∧ eta ≤ 1) at hq
  rcases hq with ⟨⟨hxi0, hxi1⟩, ⟨heta0, heta1⟩⟩
  change 0 ≤ xi * (1 - eta)
  exact mul_nonneg hxi0 (sub_nonneg.mpr heta1)

theorem gap21 (xi eta : ℝ) (hq : (xi, eta) ∈ square) :
    (inverseMap (xi, eta)).1 ≤ 1 := by
  change (0 ≤ xi ∧ xi ≤ 1) ∧ (0 ≤ eta ∧ eta ≤ 1) at hq
  rcases hq with ⟨⟨hxi0, hxi1⟩, ⟨heta0, heta1⟩⟩
  have hfactor : 1 - eta ≤ 1 := by linarith
  have hprod := mul_le_mul_of_nonneg_left hfactor hxi0
  change xi * (1 - eta) ≤ 1
  nlinarith

theorem gap22 (xi eta : ℝ) (hq : (xi, eta) ∈ square) :
    0 ≤ (inverseMap (xi, eta)).2 := by
  change (0 ≤ xi ∧ xi ≤ 1) ∧ (0 ≤ eta ∧ eta ≤ 1) at hq
  rcases hq with ⟨⟨hxi0, hxi1⟩, ⟨heta0, heta1⟩⟩
  change 0 ≤ xi * eta
  exact mul_nonneg hxi0 heta0

theorem gap23 (xi eta : ℝ) (hq : (xi, eta) ∈ square) :
    (inverseMap (xi, eta)).2 ≤ 1 - (inverseMap (xi, eta)).1 := by
  have hsum := gap16 xi eta hq
  linarith

theorem gap24 :
    inverseMap '' square = triangle := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    rcases q with ⟨xi, eta⟩
    change 0 ≤ (inverseMap (xi, eta)).1 ∧
      (inverseMap (xi, eta)).1 ≤ 1 ∧
      0 ≤ (inverseMap (xi, eta)).2 ∧
      (inverseMap (xi, eta)).2 ≤ 1 - (inverseMap (xi, eta)).1
    exact ⟨gap20 xi eta hq, gap21 xi eta hq,
      gap22 xi eta hq, gap23 xi eta hq⟩
  · intro hp
    rcases p with ⟨x, y⟩
    refine ⟨(xiCoord x y, etaCoord x y), ?_, ?_⟩
    · change (0 ≤ xiCoord x y ∧ xiCoord x y ≤ 1) ∧
        (0 ≤ etaCoord x y ∧ etaCoord x y ≤ 1)
      exact ⟨⟨gap4 x y hp, gap5 x y hp⟩,
        ⟨gap12 x y hp, gap13 x y hp⟩⟩
    · by_cases h : xiCoord x y = 0
      · have hsum : x + y = 0 := by simpa [xiCoord] using h
        change 0 ≤ x ∧ x ≤ 1 ∧ 0 ≤ y ∧ y ≤ 1 - x at hp
        rcases hp with ⟨hx0, hx1, hy0, hy1⟩
        have hx : x = 0 := by nlinarith
        have hy : y = 0 := by nlinarith
        subst x
        subst y
        simp [inverseMap, xiCoord, etaCoord]
      · have hsum : x + y ≠ 0 := by simpa [xiCoord] using h
        simp only [inverseMap, xiCoord, etaCoord, hsum, if_false]
        apply Prod.ext
        · change (x + y) * (1 - y / (x + y)) = x
          field_simp [hsum] <;> ring
        · change (x + y) * (y / (x + y)) = y
          field_simp [hsum] <;> ring

theorem gap25 (xi eta : ℝ) (hxi : xi ≠ 0) :
    inverseMap (xi, eta) ∈ triangle ↔ (xi, eta) ∈ square := by
  constructor
  · intro hinv
    change 0 ≤ xi * (1 - eta) ∧
      xi * (1 - eta) ≤ 1 ∧
      0 ≤ xi * eta ∧
      xi * eta ≤ 1 - xi * (1 - eta) at hinv
    rcases hinv with ⟨hx0, hx1, hy0, hy1⟩
    have hsum : xi * (1 - eta) + xi * eta = xi := by ring
    have hxi0 : 0 ≤ xi := by nlinarith
    have hxi1 : xi ≤ 1 := by nlinarith
    have hxipos : 0 < xi := lt_of_le_of_ne hxi0 (Ne.symm hxi)
    have heta0 : 0 ≤ eta := by
      rcases (mul_nonneg_iff.mp hy0) with hgood | hbad
      · exact hgood.2
      · exfalso
        linarith [hbad.1]
    have heta1 : eta ≤ 1 := by
      rcases (mul_nonneg_iff.mp hx0) with hgood | hbad
      · linarith [hgood.2]
      · exfalso
        linarith [hbad.1]
    change (0 ≤ xi ∧ xi ≤ 1) ∧ (0 ≤ eta ∧ eta ≤ 1)
    exact ⟨⟨hxi0, hxi1⟩, ⟨heta0, heta1⟩⟩
  · intro hq
    rw [← gap24]
    exact ⟨(xi, eta), hq, rfl⟩

end

end ProofGap.Exercise3960
