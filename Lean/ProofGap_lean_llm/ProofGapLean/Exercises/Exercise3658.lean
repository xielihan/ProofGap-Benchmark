import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import ProofGapLean.Prelude.Elementary
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise3658

noncomputable section

def objective (q : ℝ × ℝ) : ℝ :=
  Real.cos q.1 ^ 2 + Real.cos q.2 ^ 2

def constraint : Set (ℝ × ℝ) :=
  {q | q.1 - q.2 = Real.pi / 4}

def indexedPoint (k : ℤ) : ℝ × ℝ :=
  (Real.pi / 8 + (k : ℝ) * Real.pi / 2,
    -Real.pi / 8 + (k : ℝ) * Real.pi / 2)

def critical (q : ℝ × ℝ) (lambda : ℝ) : Prop :=
  -Real.sin (2 * q.1) + lambda = 0 ∧
    -Real.sin (2 * q.2) - lambda = 0 ∧
    q ∈ constraint

def maximizers : Set (ℝ × ℝ) :=
  {q | q ∈ constraint ∧ ∀ r ∈ constraint, objective r ≤ objective q}

def minimizers : Set (ℝ × ℝ) :=
  {q | q ∈ constraint ∧ ∀ r ∈ constraint, objective q ≤ objective r}

def evenIndexedPoints : Set (ℝ × ℝ) :=
  {q | ∃ k : ℤ, Even k ∧ q = indexedPoint k}

def oddIndexedPoints : Set (ℝ × ℝ) :=
  {q | ∃ k : ℤ, Odd k ∧ q = indexedPoint k}

private theorem constrained_facts (q : ℝ × ℝ) (hq : q ∈ constraint) :
    objective q =
        1 + (Real.cos (2 * q.1) + Real.sin (2 * q.1)) / 2 ∧
      1 - 1 / Real.sqrt 2 ≤ objective q ∧
      objective q ≤ 1 + 1 / Real.sqrt 2 ∧
      ((objective q = 1 + 1 / Real.sqrt 2 ∨
          objective q = 1 - 1 / Real.sqrt 2) →
        Real.cos (2 * q.1) = Real.sin (2 * q.1)) := by
  have hq' : q.2 = q.1 - Real.pi / 4 := by
    change q.1 - q.2 = Real.pi / 4 at hq
    linarith
  have hcos2 :
      Real.cos (2 * q.2) = Real.sin (2 * q.1) := by
    rw [hq']
    rw [show 2 * (q.1 - Real.pi / 4) =
      2 * q.1 - Real.pi / 2 by ring]
    rw [Real.cos_sub, Real.cos_pi_div_two, Real.sin_pi_div_two]
    ring
  have hformula :
      objective q =
        1 + (Real.cos (2 * q.1) + Real.sin (2 * q.1)) / 2 := by
    change Real.cos q.1 ^ 2 + Real.cos q.2 ^ 2 =
      1 + (Real.cos (2 * q.1) + Real.sin (2 * q.1)) / 2
    nlinarith [Real.cos_two_mul q.1, Real.cos_two_mul q.2]
  have hunit :
      Real.sin (2 * q.1) ^ 2 + Real.cos (2 * q.1) ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq (2 * q.1)
  have hsquare :
      (Real.cos (2 * q.1) + Real.sin (2 * q.1)) ^ 2 ≤ 2 := by
    nlinarith [sq_nonneg
      (Real.cos (2 * q.1) - Real.sin (2 * q.1))]
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt_sq : Real.sqrt 2 ^ 2 = 2 := by norm_num
  have hinv : 1 / Real.sqrt 2 = Real.sqrt 2 / 2 := by
    apply (div_eq_iff (ne_of_gt hsqrt)).2
    nlinarith
  have hsum_lower :
      -Real.sqrt 2 ≤
        Real.cos (2 * q.1) + Real.sin (2 * q.1) := by
    nlinarith
  have hsum_upper :
      Real.cos (2 * q.1) + Real.sin (2 * q.1) ≤
        Real.sqrt 2 := by
    nlinarith
  have hlower : 1 - 1 / Real.sqrt 2 ≤ objective q := by
    rw [hformula, hinv]
    linarith
  have hupper : objective q ≤ 1 + 1 / Real.sqrt 2 := by
    rw [hformula, hinv]
    linarith
  have hext :
      (objective q = 1 + 1 / Real.sqrt 2 ∨
          objective q = 1 - 1 / Real.sqrt 2) →
        Real.cos (2 * q.1) = Real.sin (2 * q.1) := by
    intro h
    rcases h with h | h
    · rw [hformula, hinv] at h
      nlinarith [sq_nonneg
        (Real.cos (2 * q.1) - Real.sin (2 * q.1))]
    · rw [hformula, hinv] at h
      nlinarith [sq_nonneg
        (Real.cos (2 * q.1) - Real.sin (2 * q.1))]
  exact ⟨hformula, hlower, hupper, hext⟩

theorem gap1 :
    ∀ k : ℤ, (indexedPoint k).1 =
      Real.pi / 8 + (k : ℝ) * Real.pi / 2 := by
  intro k
  rfl

theorem gap2 :
    ∀ k : ℤ, (indexedPoint k).2 =
      -Real.pi / 8 + (k : ℝ) * Real.pi / 2 := by
  intro k
  rfl

theorem gap3 :
    ∀ k : ℤ, ∃ lambda, critical (indexedPoint k) lambda := by
  intro k
  have htrig :
      Real.sin (2 * (indexedPoint k).1) =
        Real.cos (2 * (indexedPoint k).1) := by
    have hz0 : Real.sin ((k : ℝ) * Real.pi) = 0 :=
      Real.sin_int_mul_pi k
    have hz :
        Real.sin (2 * (indexedPoint k).1 - Real.pi / 4) = 0 := by
      convert hz0 using 1
      rw [gap1]
      ring
    rw [Real.sin_sub, Real.sin_pi_div_four, Real.cos_pi_div_four] at hz
    have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    nlinarith
  have hytrig :
      Real.sin (2 * (indexedPoint k).2) =
        -Real.cos (2 * (indexedPoint k).1) := by
    have hang :
        2 * (indexedPoint k).2 =
          2 * (indexedPoint k).1 - Real.pi / 2 := by
      rw [gap1, gap2]
      ring
    rw [hang, Real.sin_sub, Real.cos_pi_div_two, Real.sin_pi_div_two]
    ring
  have hcon : indexedPoint k ∈ constraint := by
    change
      (Real.pi / 8 + (k : ℝ) * Real.pi / 2) -
          (-Real.pi / 8 + (k : ℝ) * Real.pi / 2) =
        Real.pi / 4
    ring
  refine ⟨Real.sin (2 * (indexedPoint k).1), ?_⟩
  change
    -Real.sin (2 * (indexedPoint k).1) +
          Real.sin (2 * (indexedPoint k).1) = 0 ∧
      -Real.sin (2 * (indexedPoint k).2) -
          Real.sin (2 * (indexedPoint k).1) = 0 ∧
      indexedPoint k ∈ constraint
  constructor
  · ring
  constructor
  · rw [hytrig, htrig]
    ring
  · exact hcon

theorem gap4 :
    ∀ k : ℤ, Even k →
      objective (indexedPoint k) = 1 + 1 / Real.sqrt 2 := by
  intro k hk
  rcases hk with ⟨j, hj⟩
  subst k
  have hcon : indexedPoint (j + j) ∈ constraint := by
    change
      (Real.pi / 8 + ((j + j : ℤ) : ℝ) * Real.pi / 2) -
          (-Real.pi / 8 + ((j + j : ℤ) : ℝ) * Real.pi / 2) =
        Real.pi / 4
    ring
  have ht :
      2 * (indexedPoint (j + j)).1 =
        Real.pi / 4 + (j : ℝ) * (2 * Real.pi) := by
    rw [gap1]
    simp only [Int.cast_add]
    ring
  have hc :
      Real.cos (2 * (indexedPoint (j + j)).1) = Real.sqrt 2 / 2 := by
    rw [ht, Real.cos_add_int_mul_two_pi, Real.cos_pi_div_four]
  have hs :
      Real.sin (2 * (indexedPoint (j + j)).1) = Real.sqrt 2 / 2 := by
    rw [ht, Real.sin_add_int_mul_two_pi, Real.sin_pi_div_four]
  rcases constrained_facts (indexedPoint (j + j)) hcon with
    ⟨hobj, -, -, -⟩
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt_sq : Real.sqrt 2 ^ 2 = 2 := by norm_num
  have hinv : 1 / Real.sqrt 2 = Real.sqrt 2 / 2 := by
    apply (div_eq_iff (ne_of_gt hsqrt)).2
    nlinarith
  rw [hobj, hc, hs, hinv]
  ring

theorem gap5 :
    ∀ k : ℤ, Even k → indexedPoint k ∈ maximizers := by
  intro k hk
  have hcon : indexedPoint k ∈ constraint := by
    change
      (Real.pi / 8 + (k : ℝ) * Real.pi / 2) -
          (-Real.pi / 8 + (k : ℝ) * Real.pi / 2) =
        Real.pi / 4
    ring
  change indexedPoint k ∈ constraint ∧
    ∀ r ∈ constraint, objective r ≤ objective (indexedPoint k)
  refine ⟨hcon, ?_⟩
  intro r hr
  have hupper := (constrained_facts r hr).2.2.1
  rw [gap4 k hk]
  exact hupper

theorem gap6 :
    ∀ k : ℤ, Odd k →
      objective (indexedPoint k) = 1 - 1 / Real.sqrt 2 := by
  intro k hk
  rcases hk with ⟨j, hj⟩
  subst k
  have hcon : indexedPoint (2 * j + 1) ∈ constraint := by
    change
      (Real.pi / 8 + ((2 * j + 1 : ℤ) : ℝ) * Real.pi / 2) -
          (-Real.pi / 8 + ((2 * j + 1 : ℤ) : ℝ) * Real.pi / 2) =
        Real.pi / 4
    ring
  have ht :
      2 * (indexedPoint (2 * j + 1)).1 =
        (Real.pi / 4 + Real.pi) + (j : ℝ) * (2 * Real.pi) := by
    rw [gap1]
    norm_num only [Int.cast_add, Int.cast_mul, Int.cast_one,
      Int.cast_ofNat]
    ring
  have hc :
      Real.cos (2 * (indexedPoint (2 * j + 1)).1) =
        -(Real.sqrt 2 / 2) := by
    rw [ht, Real.cos_add_int_mul_two_pi, Real.cos_add,
      Real.cos_pi_div_four, Real.sin_pi_div_four, Real.cos_pi,
      Real.sin_pi]
    ring
  have hs :
      Real.sin (2 * (indexedPoint (2 * j + 1)).1) =
        -(Real.sqrt 2 / 2) := by
    rw [ht, Real.sin_add_int_mul_two_pi, Real.sin_add,
      Real.sin_pi_div_four, Real.cos_pi_div_four, Real.cos_pi,
      Real.sin_pi]
    ring
  rcases constrained_facts (indexedPoint (2 * j + 1)) hcon with
    ⟨hobj, -, -, -⟩
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt_sq : Real.sqrt 2 ^ 2 = 2 := by norm_num
  have hinv : 1 / Real.sqrt 2 = Real.sqrt 2 / 2 := by
    apply (div_eq_iff (ne_of_gt hsqrt)).2
    nlinarith
  rw [hobj, hc, hs, hinv]
  ring

theorem gap7 :
    ∀ k : ℤ, Odd k → indexedPoint k ∈ minimizers := by
  intro k hk
  have hcon : indexedPoint k ∈ constraint := by
    change
      (Real.pi / 8 + (k : ℝ) * Real.pi / 2) -
          (-Real.pi / 8 + (k : ℝ) * Real.pi / 2) =
        Real.pi / 4
    ring
  change indexedPoint k ∈ constraint ∧
    ∀ r ∈ constraint, objective (indexedPoint k) ≤ objective r
  refine ⟨hcon, ?_⟩
  intro r hr
  have hlower := (constrained_facts r hr).2.1
  rw [gap6 k hk]
  exact hlower

theorem gap8 :
    maximizers = evenIndexedPoints := by
  ext q
  constructor
  · intro hq
    change q ∈ constraint ∧
      ∀ r ∈ constraint, objective r ≤ objective q at hq
    rcases hq with ⟨hqcon, hqmax⟩
    rcases constrained_facts q hqcon with
      ⟨hformula, hlower, hupper, hext⟩
    have hzeroEven : Even (0 : ℤ) := ⟨0, by norm_num⟩
    have hpcon : indexedPoint 0 ∈ constraint := by
      change
        (Real.pi / 8 + ((0 : ℤ) : ℝ) * Real.pi / 2) -
            (-Real.pi / 8 + ((0 : ℤ) : ℝ) * Real.pi / 2) =
          Real.pi / 4
      norm_num
      ring
    have hpval := gap4 0 hzeroEven
    have hcompare := hqmax (indexedPoint 0) hpcon
    have hobj : objective q = 1 + 1 / Real.sqrt 2 := by
      nlinarith
    have htrig :
        Real.cos (2 * q.1) = Real.sin (2 * q.1) :=
      hext (Or.inl hobj)
    have hz : Real.sin (2 * q.1 - Real.pi / 4) = 0 := by
      rw [Real.sin_sub, Real.sin_pi_div_four, Real.cos_pi_div_four]
      have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
      nlinarith
    rw [Real.sin_eq_zero_iff] at hz
    rcases hz with ⟨k, hk⟩
    have hqcon' : q.1 - q.2 = Real.pi / 4 := by
      exact hqcon
    have hqeq : q = indexedPoint k := by
      apply Prod.ext
      · change q.1 = Real.pi / 8 + (k : ℝ) * Real.pi / 2
        linarith
      · change q.2 = -Real.pi / 8 + (k : ℝ) * Real.pi / 2
        linarith
    have hkpar : Even k ∨ Odd k := Int.even_or_odd k
    rcases hkpar with hkeven | hkodd
    · change ∃ k : ℤ, Even k ∧ q = indexedPoint k
      exact ⟨k, hkeven, hqeq⟩
    · have hoddval := gap6 k hkodd
      rw [← hqeq] at hoddval
      have hpos : 0 < 1 / Real.sqrt 2 :=
        one_div_pos.mpr (Real.sqrt_pos.2 (by norm_num))
      nlinarith
  · intro hq
    change ∃ k : ℤ, Even k ∧ q = indexedPoint k at hq
    rcases hq with ⟨k, hk, rfl⟩
    exact gap5 k hk

theorem gap9 :
    minimizers = oddIndexedPoints := by
  ext q
  constructor
  · intro hq
    change q ∈ constraint ∧
      ∀ r ∈ constraint, objective q ≤ objective r at hq
    rcases hq with ⟨hqcon, hqmin⟩
    rcases constrained_facts q hqcon with
      ⟨hformula, hlower, hupper, hext⟩
    have honeOdd : Odd (1 : ℤ) := ⟨0, by norm_num⟩
    have hpcon : indexedPoint 1 ∈ constraint := by
      change
        (Real.pi / 8 + ((1 : ℤ) : ℝ) * Real.pi / 2) -
            (-Real.pi / 8 + ((1 : ℤ) : ℝ) * Real.pi / 2) =
          Real.pi / 4
      norm_num
      ring
    have hpval := gap6 1 honeOdd
    have hcompare := hqmin (indexedPoint 1) hpcon
    have hobj : objective q = 1 - 1 / Real.sqrt 2 := by
      nlinarith
    have htrig :
        Real.cos (2 * q.1) = Real.sin (2 * q.1) :=
      hext (Or.inr hobj)
    have hz : Real.sin (2 * q.1 - Real.pi / 4) = 0 := by
      rw [Real.sin_sub, Real.sin_pi_div_four, Real.cos_pi_div_four]
      have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
      nlinarith
    rw [Real.sin_eq_zero_iff] at hz
    rcases hz with ⟨k, hk⟩
    have hqcon' : q.1 - q.2 = Real.pi / 4 := by
      exact hqcon
    have hqeq : q = indexedPoint k := by
      apply Prod.ext
      · change q.1 = Real.pi / 8 + (k : ℝ) * Real.pi / 2
        linarith
      · change q.2 = -Real.pi / 8 + (k : ℝ) * Real.pi / 2
        linarith
    have hkpar : Even k ∨ Odd k := Int.even_or_odd k
    rcases hkpar with hkeven | hkodd
    · have hevenval := gap4 k hkeven
      rw [← hqeq] at hevenval
      have hpos : 0 < 1 / Real.sqrt 2 :=
        one_div_pos.mpr (Real.sqrt_pos.2 (by norm_num))
      nlinarith
    · change ∃ k : ℤ, Odd k ∧ q = indexedPoint k
      exact ⟨k, hkodd, hqeq⟩
  · intro hq
    change ∃ k : ℤ, Odd k ∧ q = indexedPoint k at hq
    rcases hq with ⟨k, hk, rfl⟩
    exact gap7 k hk

end

end ProofGap.Exercise3658
