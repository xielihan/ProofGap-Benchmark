import Mathlib

set_option linter.style.longLine false

abbrev V3 := ℝ × ℝ × ℝ

def v3dot (u v : V3) : ℝ := u.1 * v.1 + u.2.1 * v.2.1 + u.2.2 * v.2.2
notation:70 u " ·₃ " v => v3dot u v

def SaPred (a : ℝ) : Set V3 := {p | p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 = 2 * a * p.1}
def SbPred (b : ℝ) : Set V3 := {p | p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 = 2 * b * p.2.1}
def ScPred (c : ℝ) : Set V3 := {p | p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 = 2 * c * p.2.2}

-- exercise: exercise_3561

theorem proof_gap_exercise_3561_1
  (a b c : ℝ) (Sa Sb Sc : Set V3)
  (hSaSub : Sa ⊆ Set.univ) (hSbSub : Sb ⊆ Set.univ) (hScSub : Sc ⊆ Set.univ)
  (hSa : ∀ x y z : ℝ, Sa = SaPred a)
  (hSb : ∀ x y z : ℝ, Sb = SbPred b)
  (hSc : ∀ x y z : ℝ, Sc = ScPred c)
  : ∀ x0 y0 z0 : ℝ, (x0, y0, z0) ∈ Sa ∧ (x0, y0, z0) ∈ Sb ->
      x0 ^ 2 + y0 ^ 2 + z0 ^ 2 = 2 * a * x0 := by
  sorry

theorem proof_gap_exercise_3561_2
  (a b c : ℝ) (Sa Sb Sc : Set V3)
  (hSaSub : Sa ⊆ Set.univ) (hSbSub : Sb ⊆ Set.univ) (hScSub : Sc ⊆ Set.univ)
  (hSa : ∀ x y z : ℝ, Sa = SaPred a) (hSb : ∀ x y z : ℝ, Sb = SbPred b) (hSc : ∀ x y z : ℝ, Sc = ScPred c)
  (h10 : ∀ x0 y0 z0 : ℝ, (x0, y0, z0) ∈ Sa ∧ (x0, y0, z0) ∈ Sb -> x0 ^ 2 + y0 ^ 2 + z0 ^ 2 = 2 * a * x0)
  : ∀ x0 y0 z0 : ℝ, (x0, y0, z0) ∈ Sa ∧ (x0, y0, z0) ∈ Sb ->
      x0 ^ 2 + y0 ^ 2 + z0 ^ 2 = 2 * b * y0 := by
  sorry

theorem proof_gap_exercise_3561_3
  (a b c : ℝ) (Sa Sb Sc : Set V3)
  (hSaSub : Sa ⊆ Set.univ) (hSbSub : Sb ⊆ Set.univ) (hScSub : Sc ⊆ Set.univ)
  (hSa : ∀ x y z : ℝ, Sa = SaPred a) (hSb : ∀ x y z : ℝ, Sb = SbPred b) (hSc : ∀ x y z : ℝ, Sc = ScPred c)
  (h10 : ∀ x0 y0 z0 : ℝ, (x0, y0, z0) ∈ Sa ∧ (x0, y0, z0) ∈ Sb -> x0 ^ 2 + y0 ^ 2 + z0 ^ 2 = 2 * a * x0)
  (h11 : ∀ x0 y0 z0 : ℝ, (x0, y0, z0) ∈ Sa ∧ (x0, y0, z0) ∈ Sb -> x0 ^ 2 + y0 ^ 2 + z0 ^ 2 = 2 * b * y0)
  : ∀ n1 : V3, ∀ x0 y0 z0 : ℝ, (x0, y0, z0) ∈ Sa ∧ (x0, y0, z0) ∈ Sb ->
      n1 = (2 * (x0 - a), 2 * y0, 2 * z0) := by
  sorry

theorem proof_gap_exercise_3561_4
  (a b c : ℝ) (Sa Sb Sc : Set V3)
  (hSaSub : Sa ⊆ Set.univ) (hSbSub : Sb ⊆ Set.univ) (hScSub : Sc ⊆ Set.univ)
  (hSa : ∀ x y z : ℝ, Sa = SaPred a) (hSb : ∀ x y z : ℝ, Sb = SbPred b) (hSc : ∀ x y z : ℝ, Sc = ScPred c)
  (h10 : ∀ x0 y0 z0 : ℝ, (x0, y0, z0) ∈ Sa ∧ (x0, y0, z0) ∈ Sb -> x0 ^ 2 + y0 ^ 2 + z0 ^ 2 = 2 * a * x0)
  (h11 : ∀ x0 y0 z0 : ℝ, (x0, y0, z0) ∈ Sa ∧ (x0, y0, z0) ∈ Sb -> x0 ^ 2 + y0 ^ 2 + z0 ^ 2 = 2 * b * y0)
  (h12 : ∀ n1 : V3, ∀ x0 y0 z0 : ℝ, (x0, y0, z0) ∈ Sa ∧ (x0, y0, z0) ∈ Sb -> n1 = (2 * (x0 - a), 2 * y0, 2 * z0))
  : ∀ n2 : V3, ∀ x0 y0 z0 : ℝ, (x0, y0, z0) ∈ Sa ∧ (x0, y0, z0) ∈ Sb ->
      n2 = (2 * x0, 2 * (y0 - b), 2 * z0) := by
  sorry

theorem proof_gap_exercise_3561_5
  (a b c : ℝ) (Sa Sb Sc : Set V3)
  (hSaSub : Sa ⊆ Set.univ) (hSbSub : Sb ⊆ Set.univ) (hScSub : Sc ⊆ Set.univ)
  (hSa : ∀ x y z : ℝ, Sa = SaPred a) (hSb : ∀ x y z : ℝ, Sb = SbPred b) (hSc : ∀ x y z : ℝ, Sc = ScPred c)
  (h10 : ∀ x0 y0 z0 : ℝ, (x0, y0, z0) ∈ Sa ∧ (x0, y0, z0) ∈ Sb -> x0 ^ 2 + y0 ^ 2 + z0 ^ 2 = 2 * a * x0)
  (h11 : ∀ x0 y0 z0 : ℝ, (x0, y0, z0) ∈ Sa ∧ (x0, y0, z0) ∈ Sb -> x0 ^ 2 + y0 ^ 2 + z0 ^ 2 = 2 * b * y0)
  (h12 : ∀ n1 : V3, ∀ x0 y0 z0 : ℝ, (x0, y0, z0) ∈ Sa ∧ (x0, y0, z0) ∈ Sb -> n1 = (2 * (x0 - a), 2 * y0, 2 * z0))
  (h13 : ∀ n2 : V3, ∀ x0 y0 z0 : ℝ, (x0, y0, z0) ∈ Sa ∧ (x0, y0, z0) ∈ Sb -> n2 = (2 * x0, 2 * (y0 - b), 2 * z0))
  : ∀ n1 n2 : V3, ∀ x0 y0 z0 : ℝ, (x0, y0, z0) ∈ Sa ∧ (x0, y0, z0) ∈ Sb ->
      (n1 ·₃ n2) = 4 * (x0 * (x0 - a) + y0 * (y0 - b) + z0 ^ 2) := by
  sorry

theorem proof_gap_exercise_3561_6
  (a b c : ℝ) (Sa Sb Sc : Set V3)
  (hSaSub : Sa ⊆ Set.univ) (hSbSub : Sb ⊆ Set.univ) (hScSub : Sc ⊆ Set.univ)
  (hSa : ∀ x y z : ℝ, Sa = SaPred a) (hSb : ∀ x y z : ℝ, Sb = SbPred b) (hSc : ∀ x y z : ℝ, Sc = ScPred c)
  (h10 : ∀ x0 y0 z0 : ℝ, (x0, y0, z0) ∈ Sa ∧ (x0, y0, z0) ∈ Sb -> x0 ^ 2 + y0 ^ 2 + z0 ^ 2 = 2 * a * x0)
  (h11 : ∀ x0 y0 z0 : ℝ, (x0, y0, z0) ∈ Sa ∧ (x0, y0, z0) ∈ Sb -> x0 ^ 2 + y0 ^ 2 + z0 ^ 2 = 2 * b * y0)
  (h14 : ∀ n1 n2 : V3, ∀ x0 y0 z0 : ℝ, (x0, y0, z0) ∈ Sa ∧ (x0, y0, z0) ∈ Sb -> (n1 ·₃ n2) = 4 * (x0 * (x0 - a) + y0 * (y0 - b) + z0 ^ 2))
  : ∀ n1 n2 : V3, ∀ x0 y0 z0 : ℝ, (x0, y0, z0) ∈ Sa ∧ (x0, y0, z0) ∈ Sb ->
      (n1 ·₃ n2) = 2 * (x0 ^ 2 + y0 ^ 2 + z0 ^ 2 - 2 * a * x0 + x0 ^ 2 + y0 ^ 2 + z0 ^ 2 - 2 * b * y0) := by
  sorry

theorem proof_gap_exercise_3561_7
  (a b c : ℝ) (Sa Sb Sc : Set V3)
  (hSaSub : Sa ⊆ Set.univ) (hSbSub : Sb ⊆ Set.univ) (hScSub : Sc ⊆ Set.univ)
  (hSa : ∀ x y z : ℝ, Sa = SaPred a) (hSb : ∀ x y z : ℝ, Sb = SbPred b) (hSc : ∀ x y z : ℝ, Sc = ScPred c)
  (h10 : ∀ x0 y0 z0 : ℝ, (x0, y0, z0) ∈ Sa ∧ (x0, y0, z0) ∈ Sb -> x0 ^ 2 + y0 ^ 2 + z0 ^ 2 = 2 * a * x0)
  (h11 : ∀ x0 y0 z0 : ℝ, (x0, y0, z0) ∈ Sa ∧ (x0, y0, z0) ∈ Sb -> x0 ^ 2 + y0 ^ 2 + z0 ^ 2 = 2 * b * y0)
  (h15 : ∀ n1 n2 : V3, ∀ x0 y0 z0 : ℝ, (x0, y0, z0) ∈ Sa ∧ (x0, y0, z0) ∈ Sb -> (n1 ·₃ n2) = 2 * (x0 ^ 2 + y0 ^ 2 + z0 ^ 2 - 2 * a * x0 + x0 ^ 2 + y0 ^ 2 + z0 ^ 2 - 2 * b * y0))
  : ∀ n1 n2 : V3, ∀ x0 y0 z0 : ℝ, (x0, y0, z0) ∈ Sa ∧ (x0, y0, z0) ∈ Sb -> (n1 ·₃ n2) = 0 := by
  sorry

theorem proof_gap_exercise_3561_8
  (a b c : ℝ) (Sa Sb Sc : Set V3)
  (hSaSub : Sa ⊆ Set.univ) (hSbSub : Sb ⊆ Set.univ) (hScSub : Sc ⊆ Set.univ)
  (hSa : ∀ x y z : ℝ, Sa = SaPred a) (hSb : ∀ x y z : ℝ, Sb = SbPred b) (hSc : ∀ x y z : ℝ, Sc = ScPred c)
  (hprev : True)
  : ∀ x0 y0 z0 : ℝ, (x0, y0, z0) ∈ Sa ∧ (x0, y0, z0) ∈ Sc ->
      ((2 * (x0 - a), 2 * y0, 2 * z0) ·₃ (2 * x0, 2 * y0, 2 * (z0 - c))) = 0 := by
  sorry

theorem proof_gap_exercise_3561_9
  (a b c : ℝ) (Sa Sb Sc : Set V3)
  (hSaSub : Sa ⊆ Set.univ) (hSbSub : Sb ⊆ Set.univ) (hScSub : Sc ⊆ Set.univ)
  (hSa : ∀ x y z : ℝ, Sa = SaPred a) (hSb : ∀ x y z : ℝ, Sb = SbPred b) (hSc : ∀ x y z : ℝ, Sc = ScPred c)
  (h17 : ∀ x0 y0 z0 : ℝ, (x0, y0, z0) ∈ Sa ∧ (x0, y0, z0) ∈ Sc ->
      ((2 * (x0 - a), 2 * y0, 2 * z0) ·₃ (2 * x0, 2 * y0, 2 * (z0 - c))) = 0)
  : ∀ x0 y0 z0 : ℝ, (x0, y0, z0) ∈ Sb ∧ (x0, y0, z0) ∈ Sc ->
      ((2 * x0, 2 * (y0 - b), 2 * z0) ·₃ (2 * x0, 2 * y0, 2 * (z0 - c))) = 0 := by
  sorry

theorem proof_gap_exercise_3561_10
  (a b c : ℝ) (Sa Sb Sc : Set V3)
  (hSaSub : Sa ⊆ Set.univ) (hSbSub : Sb ⊆ Set.univ) (hScSub : Sc ⊆ Set.univ)
  (hSa : ∀ x y z : ℝ, Sa = SaPred a) (hSb : ∀ x y z : ℝ, Sb = SbPred b) (hSc : ∀ x y z : ℝ, Sc = ScPred c)
  (h16 : ∀ n1 n2 : V3, ∀ x0 y0 z0 : ℝ, (x0, y0, z0) ∈ Sa ∧ (x0, y0, z0) ∈ Sb -> (n1 ·₃ n2) = 0)
  (h17 : ∀ x0 y0 z0 : ℝ, (x0, y0, z0) ∈ Sa ∧ (x0, y0, z0) ∈ Sc ->
      ((2 * (x0 - a), 2 * y0, 2 * z0) ·₃ (2 * x0, 2 * y0, 2 * (z0 - c))) = 0)
  (h18 : ∀ x0 y0 z0 : ℝ, (x0, y0, z0) ∈ Sb ∧ (x0, y0, z0) ∈ Sc ->
      ((2 * x0, 2 * (y0 - b), 2 * z0) ·₃ (2 * x0, 2 * y0, 2 * (z0 - c))) = 0)
  : ∀ x0 y0 z0 : ℝ,
      (((x0, y0, z0) ∈ Sa ∧ (x0, y0, z0) ∈ Sb) -> ((2 * (x0 - a), 2 * y0, 2 * z0) ·₃ (2 * x0, 2 * (y0 - b), 2 * z0)) = 0) ∧
      (((x0, y0, z0) ∈ Sa ∧ (x0, y0, z0) ∈ Sc) -> ((2 * (x0 - a), 2 * y0, 2 * z0) ·₃ (2 * x0, 2 * y0, 2 * (z0 - c))) = 0) ∧
      (((x0, y0, z0) ∈ Sb ∧ (x0, y0, z0) ∈ Sc) -> ((2 * x0, 2 * (y0 - b), 2 * z0) ·₃ (2 * x0, 2 * y0, 2 * (z0 - c))) = 0) := by
  sorry

theorem proof_gap_exercise_3561_11
  (a b c : ℝ) (Sa Sb Sc : Set V3)
  (hSaSub : Sa ⊆ Set.univ) (hSbSub : Sb ⊆ Set.univ) (hScSub : Sc ⊆ Set.univ)
  (hSa : ∀ x y z : ℝ, Sa = SaPred a) (hSb : ∀ x y z : ℝ, Sb = SbPred b) (hSc : ∀ x y z : ℝ, Sc = ScPred c)
  (h19 : ∀ x0 y0 z0 : ℝ,
      (((x0, y0, z0) ∈ Sa ∧ (x0, y0, z0) ∈ Sb) -> ((2 * (x0 - a), 2 * y0, 2 * z0) ·₃ (2 * x0, 2 * (y0 - b), 2 * z0)) = 0) ∧
      (((x0, y0, z0) ∈ Sa ∧ (x0, y0, z0) ∈ Sc) -> ((2 * (x0 - a), 2 * y0, 2 * z0) ·₃ (2 * x0, 2 * y0, 2 * (z0 - c))) = 0) ∧
      (((x0, y0, z0) ∈ Sb ∧ (x0, y0, z0) ∈ Sc) -> ((2 * x0, 2 * (y0 - b), 2 * z0) ·₃ (2 * x0, 2 * y0, 2 * (z0 - c))) = 0))
  : ∀ x0 y0 z0 : ℝ,
      (((x0, y0, z0) ∈ Sa ∧ (x0, y0, z0) ∈ Sb) -> ((2 * (x0 - a), 2 * y0, 2 * z0) ·₃ (2 * x0, 2 * (y0 - b), 2 * z0)) = 0) ∧
      (((x0, y0, z0) ∈ Sa ∧ (x0, y0, z0) ∈ Sc) -> ((2 * (x0 - a), 2 * y0, 2 * z0) ·₃ (2 * x0, 2 * y0, 2 * (z0 - c))) = 0) ∧
      (((x0, y0, z0) ∈ Sb ∧ (x0, y0, z0) ∈ Sc) -> ((2 * x0, 2 * (y0 - b), 2 * z0) ·₃ (2 * x0, 2 * y0, 2 * (z0 - c))) = 0) := by
  sorry
