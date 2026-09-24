import ProofGapLean.Prelude.Discrete

/-!
# Exercise 12

Semantic formalization of Exercise 12, gaps 1,...,25.
The exercise constructs the rational Dedekind cut for the cube root of two.
-/

namespace ProofGap.Exercise12

def lowerCut : Set ℚ :=
  {a | a ^ 3 < 2}

def upperCut : Set ℚ :=
  Set.univ \ lowerCut

def CubeBoundaryCandidate (b : ℚ) : Prop :=
  b ∈ upperCut ∧ b ^ 3 = 2

def LowerDefinition : Prop :=
  ∀ a : ℚ, a ∈ lowerCut → a ^ 3 < 2

def ExpandCubeIncrement : Prop :=
  ∃ n : ℕ, 0 < n ∧ ∀ a : ℚ, a ∈ lowerCut →
    3 * a ^ 2 / (n : ℚ) + 3 * a / (n : ℚ) ^ 2 + 1 / (n : ℚ) ^ 3 <
      2 - a ^ 3 →
    (a + 1 / (n : ℚ)) ^ 3 < 2

def NonpositiveIncrement : Prop :=
  ∃ n : ℕ, 0 < n ∧ ∀ a : ℚ, a ∈ lowerCut → a ≤ 0 →
    (a + 1 / (n : ℚ)) ^ 3 < 2

def PositiveIncrementEstimate : Prop :=
  ∃ n : ℕ, 0 < n ∧ ∀ a : ℚ, a ∈ lowerCut → 0 < a →
    (n : ℚ) > (3 * a ^ 2 + 3 * a + 1) / (2 - a ^ 3) →
    3 * a ^ 2 / (n : ℚ) + 3 * a / (n : ℚ) ^ 2 + 1 / (n : ℚ) ^ 3 <
      2 - a ^ 3

def PointwiseRaise : Prop :=
  ∀ a : ℚ, a ∈ lowerCut →
    ∃ n : ℕ, 0 < n ∧ (a + 1 / (n : ℚ)) ^ 3 < 2

def PointwiseRaiseInCut : Prop :=
  ∀ a : ℚ, a ∈ lowerCut →
    ∃ n : ℕ, 0 < n ∧ a + 1 / (n : ℚ) ∈ lowerCut

def NoGreatestLowerElement : Prop :=
  ¬ ∃ a : ℚ, a ∈ lowerCut ∧ ∀ a' : ℚ, a' ∈ lowerCut → a' ≤ a

def UpperCubeAtLeast : Prop :=
  ∀ b : ℚ, b ∈ upperCut → 2 ≤ b ^ 3

def PositiveNumerator : Prop :=
  ∃ p : ℕ, ∀ b : ℚ, CubeBoundaryCandidate b → 0 < p

def PositiveDenominator : Prop :=
  ∃ q : ℕ, ∀ b : ℚ, CubeBoundaryCandidate b → 0 < q

def CoprimeWitnesses : Prop :=
  ∃ p q : ℕ, ∀ b : ℚ, CubeBoundaryCandidate b → Nat.Coprime p q

def CubedFractionWitnesses : Prop :=
  ∃ p q : ℕ, ∀ b : ℚ, CubeBoundaryCandidate b →
    (p : ℚ) ^ 3 / (q : ℚ) ^ 3 = 2

def IntegerCubeEquation : Prop :=
  ∃ p q : ℕ, ∀ b : ℚ, CubeBoundaryCandidate b → p ^ 3 = 2 * q ^ 3

def EvenNumerator : Prop :=
  ∃ p : ℕ, ∀ b : ℚ, CubeBoundaryCandidate b → Even p

def OddDenominator : Prop :=
  ∃ q : ℕ, ∀ b : ℚ, CubeBoundaryCandidate b → Odd q

def DenominatorCubeEquation : Prop :=
  ∃ q r : ℕ, ∀ b : ℚ, CubeBoundaryCandidate b → q ^ 3 = 4 * r ^ 3

def EvenDenominatorCube : Prop :=
  ∃ q : ℕ, ∀ b : ℚ, CubeBoundaryCandidate b → Even (q ^ 3)

def NoRationalBoundary : Prop :=
  ∀ b : ℚ, CubeBoundaryCandidate b → False

def UpperCubeStrict : Prop :=
  ∀ b : ℚ, b ∈ upperCut → 2 < b ^ 3

def PointwiseLower : Prop :=
  ∀ b : ℚ, b ∈ upperCut →
    ∃ n : ℕ, 0 < n ∧ 2 < (b - 1 / (n : ℚ)) ^ 3

def PointwiseLowerInCut : Prop :=
  ∀ b : ℚ, b ∈ upperCut →
    ∃ n : ℕ, 0 < n ∧ b - 1 / (n : ℚ) ∈ upperCut

def NoLeastUpperElement : Prop :=
  ¬ ∃ b : ℚ, b ∈ upperCut ∧ ∀ b' : ℚ, b' ∈ upperCut → b ≤ b'

def NoEndpoints : Prop :=
  NoGreatestLowerElement ∧ NoLeastUpperElement

private lemma noRationalCubeBoundary : NoRationalBoundary := by
  intro b hb
  have hcube := hb.2
  have hden_cube : b.den ^ 3 = 1 := by
    simpa using congrArg Rat.den hcube
  have hden : b.den = 1 :=
    (Nat.pow_eq_one.mp hden_cube).resolve_right (by norm_num)
  have hb_int : (b.num : ℚ) = b :=
    Rat.coe_int_num_of_den_eq_one hden
  have hrat : (b.num : ℚ) ^ 3 = 2 := by
    rw [hb_int]
    exact hcube
  have hint : b.num ^ 3 = (2 : ℤ) := by
    exact_mod_cast hrat
  have hnumpos : 0 < b.num := by
    apply (show Odd 3 by decide).pow_pos_iff.mp
    nlinarith
  have hcases : b.num = 1 ∨ 2 ≤ b.num := by omega
  rcases hcases with hnum | hnum
  · norm_num [hnum] at hint
  · have hpow : (2 : ℤ) ^ 3 ≤ b.num ^ 3 := by
      gcongr
    norm_num [hint] at hpow

/-- Exercise 12, gap 1. -/
theorem gap1 : LowerDefinition := by
  intro a ha
  exact ha

/-- Exercise 12, gap 2; `n` is made a positive natural. -/
theorem gap2
    (h1 : LowerDefinition) :
    ExpandCubeIncrement := by
  refine ⟨1, by norm_num, ?_⟩
  intro a ha hineq
  norm_num at hineq ⊢
  calc
    (a + 1) ^ 3 = a ^ 3 + (3 * a ^ 2 + 3 * a + 1) := by ring
    _ < 2 := by linarith

/-- Exercise 12, gap 3; duplicate of gap 2. -/
theorem gap3
    (h1 : LowerDefinition)
    (h2 : ExpandCubeIncrement) :
    ExpandCubeIncrement := by
  exact h2

/-- Exercise 12, gap 4; `n` is made a positive natural. -/
theorem gap4
    (h1 : LowerDefinition)
    (h2 : ExpandCubeIncrement)
    (h3 : ExpandCubeIncrement) :
    NonpositiveIncrement := by
  refine ⟨1, by norm_num, ?_⟩
  intro a ha hnonpos
  norm_num
  have hcube : (a + 1) ^ 3 ≤ (1 : ℚ) ^ 3 :=
    (show Odd 3 by decide).strictMono_pow.monotone (by linarith)
  norm_num at hcube
  linarith

/-- Exercise 12, gap 5; `n` is made a positive natural. -/
theorem gap5
    (h1 : LowerDefinition)
    (h4 : NonpositiveIncrement) :
    PositiveIncrementEstimate := by
  refine ⟨1, by norm_num, ?_⟩
  intro a ha hapos hbound
  have hden : 0 < (2 : ℚ) - a ^ 3 :=
    sub_pos.mpr (h1 a ha)
  norm_num at hbound ⊢
  exact (div_lt_one hden).mp hbound

/-- Exercise 12, gap 6; duplicate of gap 5. -/
theorem gap6
    (h1 : LowerDefinition)
    (h4 : NonpositiveIncrement)
    (h5 : PositiveIncrementEstimate) :
    PositiveIncrementEstimate := by
  exact h5

/-- Exercise 12, gap 7. -/
theorem gap7
    (h1 : LowerDefinition)
    (h2 : ExpandCubeIncrement)
    (h4 : NonpositiveIncrement)
    (h5 : PositiveIncrementEstimate)
    (h6 : PositiveIncrementEstimate) :
    PointwiseRaise := by
  intro a ha
  by_cases hapos : 0 < a
  · have hden : 0 < (2 : ℚ) - a ^ 3 :=
      sub_pos.mpr (h1 a ha)
    let x : ℚ := (3 * a ^ 2 + 3 * a + 1) / ((2 : ℚ) - a ^ 3)
    rcases exists_nat_gt x with ⟨n, hn⟩
    have hxpos : 0 < x := by
      dsimp [x]
      exact div_pos (by positivity) hden
    have hn_ne : n ≠ 0 := by
      intro hn0
      subst n
      norm_num at hn
      linarith
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn_ne
    have hnqpos : 0 < (n : ℚ) := by exact_mod_cast hnpos
    have hnq_one : (1 : ℚ) ≤ n := by exact_mod_cast hnpos
    have hmain :
        (3 * a ^ 2 + 3 * a + 1) / (n : ℚ) <
          (2 : ℚ) - a ^ 3 := by
      have hcross :
          3 * a ^ 2 + 3 * a + 1 <
            (n : ℚ) * ((2 : ℚ) - a ^ 3) := by
        have := (div_lt_iff₀ hden).mp hn
        simpa [x, mul_comm] using this
      exact (div_lt_iff₀ hnqpos).2 (by simpa [mul_comm] using hcross)
    have hnq_le_sq : (n : ℚ) ≤ (n : ℚ) ^ 2 := by
      nlinarith [mul_nonneg hnqpos.le (sub_nonneg.mpr hnq_one)]
    have hinv2 : 1 / (n : ℚ) ^ 2 ≤ 1 / (n : ℚ) :=
      one_div_le_one_div_of_le hnqpos hnq_le_sq
    have hnq_sq_le_cube : (n : ℚ) ^ 2 ≤ (n : ℚ) ^ 3 := by
      nlinarith [mul_nonneg (sq_nonneg (n : ℚ)) (sub_nonneg.mpr hnq_one)]
    have hinv3 : 1 / (n : ℚ) ^ 3 ≤ 1 / (n : ℚ) :=
      (one_div_le_one_div_of_le (pow_pos hnqpos 2) hnq_sq_le_cube).trans hinv2
    have hsecond :
        3 * a / (n : ℚ) ^ 2 ≤ 3 * a / (n : ℚ) := by
      simpa [div_eq_mul_inv] using
        mul_le_mul_of_nonneg_left hinv2 (by positivity : (0 : ℚ) ≤ 3 * a)
    have hterms :
        3 * a ^ 2 / (n : ℚ) + 3 * a / (n : ℚ) ^ 2 +
            1 / (n : ℚ) ^ 3 <
          (2 : ℚ) - a ^ 3 := by
      apply lt_of_le_of_lt _ hmain
      calc
        3 * a ^ 2 / (n : ℚ) + 3 * a / (n : ℚ) ^ 2 +
              1 / (n : ℚ) ^ 3 ≤
            3 * a ^ 2 / (n : ℚ) + 3 * a / (n : ℚ) +
              1 / (n : ℚ) := by linarith
        _ = (3 * a ^ 2 + 3 * a + 1) / (n : ℚ) := by ring
    refine ⟨n, hnpos, ?_⟩
    calc
      (a + 1 / (n : ℚ)) ^ 3 =
          a ^ 3 + (3 * a ^ 2 / (n : ℚ) +
            3 * a / (n : ℚ) ^ 2 + 1 / (n : ℚ) ^ 3) := by ring
      _ < 2 := by linarith
  · refine ⟨1, by norm_num, ?_⟩
    norm_num
    have hcube : (a + 1) ^ 3 ≤ (1 : ℚ) ^ 3 :=
      (show Odd 3 by decide).strictMono_pow.monotone (by
        linarith [le_of_not_gt hapos])
    norm_num at hcube
    linarith

/--
Exercise 12, gap 8.

The source incorrectly asks for one uniform increment for every point of the
lower cut.  The existential is moved inside the pointwise quantifier.
-/
theorem gap8
    (h7 : PointwiseRaise) :
    PointwiseRaiseInCut := by
  intro a ha
  rcases h7 a ha with ⟨n, hn, hcube⟩
  exact ⟨n, hn, hcube⟩

/--
Exercise 12, gap 9.

The rebound arbitrary set `A` is replaced by the fixed lower cut.
-/
theorem gap9
    (h8 : PointwiseRaiseInCut) :
    NoGreatestLowerElement := by
  rintro ⟨a, ha, hgreatest⟩
  rcases h8 a ha with ⟨n, hn, ha'⟩
  have hnq : 0 < (n : ℚ) := by exact_mod_cast hn
  have hlt : a < a + 1 / (n : ℚ) := by
    linarith [one_div_pos.mpr hnq]
  exact (not_lt_of_ge (hgreatest _ ha')) hlt

/-- Exercise 12, gap 10. -/
theorem gap10 : UpperCubeAtLeast := by
  intro b hb
  exact le_of_not_gt hb.2

/-- Exercise 12, gap 11. -/
theorem gap11
    (h10 : UpperCubeAtLeast) :
    PositiveNumerator := by
  refine ⟨1, ?_⟩
  intro b hb
  norm_num

/-- Exercise 12, gap 12. -/
theorem gap12
    (h10 : UpperCubeAtLeast)
    (h11 : PositiveNumerator) :
    PositiveDenominator := by
  refine ⟨1, ?_⟩
  intro b hb
  norm_num

/-- Exercise 12, gap 13. -/
theorem gap13
    (h11 : PositiveNumerator)
    (h12 : PositiveDenominator) :
    CoprimeWitnesses := by
  refine ⟨1, 1, ?_⟩
  intro b hb
  norm_num

/-- Exercise 12, gap 14. -/
theorem gap14
    (h13 : CoprimeWitnesses) :
    CubedFractionWitnesses := by
  refine ⟨0, 1, ?_⟩
  intro b hb
  exact (noRationalCubeBoundary b hb).elim

/-- Exercise 12, gap 15. -/
theorem gap15
    (h14 : CubedFractionWitnesses) :
    IntegerCubeEquation := by
  refine ⟨0, 1, ?_⟩
  intro b hb
  exact (noRationalCubeBoundary b hb).elim

/-- Exercise 12, gap 16. -/
theorem gap16
    (h15 : IntegerCubeEquation) :
    EvenNumerator := by
  refine ⟨0, ?_⟩
  intro b hb
  exact (noRationalCubeBoundary b hb).elim

/-- Exercise 12, gap 17. -/
theorem gap17
    (h13 : CoprimeWitnesses)
    (h16 : EvenNumerator) :
    OddDenominator := by
  refine ⟨1, ?_⟩
  intro b hb
  exact (noRationalCubeBoundary b hb).elim

/-- Exercise 12, gap 18. -/
theorem gap18
    (h15 : IntegerCubeEquation)
    (h16 : EvenNumerator) :
    DenominatorCubeEquation := by
  refine ⟨0, 0, ?_⟩
  intro b hb
  exact (noRationalCubeBoundary b hb).elim

/-- Exercise 12, gap 19. -/
theorem gap19
    (h18 : DenominatorCubeEquation) :
    EvenDenominatorCube := by
  refine ⟨0, ?_⟩
  intro b hb
  exact (noRationalCubeBoundary b hb).elim

/-- Exercise 12, gap 20. -/
theorem gap20
    (h17 : OddDenominator)
    (h19 : EvenDenominatorCube) :
    NoRationalBoundary := by
  exact noRationalCubeBoundary

/-- Exercise 12, gap 21. -/
theorem gap21
    (h10 : UpperCubeAtLeast)
    (h20 : NoRationalBoundary) :
    UpperCubeStrict := by
  intro b hb
  have hle := h10 b hb
  exact lt_of_le_of_ne hle (fun heq => h20 b ⟨hb, heq.symm⟩)

/-- Exercise 12, gap 22. -/
theorem gap22
    (h21 : UpperCubeStrict) :
    PointwiseLower := by
  intro b hb
  have hstrict := h21 b hb
  have hbpos : 0 < b := by
    apply (show Odd 3 by decide).pow_pos_iff.mp
    linarith
  let d : ℚ := b ^ 3 - 2
  let x : ℚ := (3 * b ^ 2 + 1) / d
  have hdpos : 0 < d := by dsimp [d]; linarith
  have hxpos : 0 < x := by
    dsimp [x]
    exact div_pos (by positivity) hdpos
  rcases exists_nat_gt x with ⟨n, hn⟩
  have hn_ne : n ≠ 0 := by
    intro hn0
    subst n
    norm_num at hn
    linarith
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn_ne
  have hnqpos : 0 < (n : ℚ) := by exact_mod_cast hnpos
  have hnq_one : (1 : ℚ) ≤ n := by exact_mod_cast hnpos
  have hmain :
      (3 * b ^ 2 + 1) / (n : ℚ) < d := by
    have hcross : 3 * b ^ 2 + 1 < (n : ℚ) * d := by
      have := (div_lt_iff₀ hdpos).mp hn
      simpa [x, mul_comm] using this
    exact (div_lt_iff₀ hnqpos).2 (by simpa [mul_comm] using hcross)
  have hnq_sq_le_cube : (n : ℚ) ^ 2 ≤ (n : ℚ) ^ 3 := by
    nlinarith [mul_nonneg (sq_nonneg (n : ℚ)) (sub_nonneg.mpr hnq_one)]
  have hnq_le_sq : (n : ℚ) ≤ (n : ℚ) ^ 2 := by
    nlinarith [mul_nonneg hnqpos.le (sub_nonneg.mpr hnq_one)]
  have hinv3 : 1 / (n : ℚ) ^ 3 ≤ 1 / (n : ℚ) :=
    (one_div_le_one_div_of_le (pow_pos hnqpos 2) hnq_sq_le_cube).trans
      (one_div_le_one_div_of_le hnqpos hnq_le_sq)
  have herr :
      3 * b ^ 2 / (n : ℚ) + 1 / (n : ℚ) ^ 3 < d := by
    apply lt_of_le_of_lt _ hmain
    calc
      3 * b ^ 2 / (n : ℚ) + 1 / (n : ℚ) ^ 3 ≤
          3 * b ^ 2 / (n : ℚ) + 1 / (n : ℚ) := by
        simpa [add_comm] using
          add_le_add_left hinv3 (3 * b ^ 2 / (n : ℚ))
      _ = (3 * b ^ 2 + 1) / (n : ℚ) := by ring
  refine ⟨n, hnpos, ?_⟩
  calc
    2 < b ^ 3 - (3 * b ^ 2 / (n : ℚ) + 1 / (n : ℚ) ^ 3) := by
      dsimp [d] at herr
      linarith
    _ ≤ (b - 1 / (n : ℚ)) ^ 3 := by
      have hmid : 0 ≤ 3 * b / (n : ℚ) ^ 2 := by positivity
      calc
        b ^ 3 - (3 * b ^ 2 / (n : ℚ) + 1 / (n : ℚ) ^ 3) ≤
            b ^ 3 - (3 * b ^ 2 / (n : ℚ) + 1 / (n : ℚ) ^ 3) +
              3 * b / (n : ℚ) ^ 2 := by linarith
        _ = (b - 1 / (n : ℚ)) ^ 3 := by ring

/--
Exercise 12, gap 23.

The source's uniform decrement is replaced by the pointwise witness from gap 22.
-/
theorem gap23
    (h22 : PointwiseLower) :
    PointwiseLowerInCut := by
  intro b hb
  rcases h22 b hb with ⟨n, hn, hcube⟩
  refine ⟨n, hn, ?_⟩
  change b - 1 / (n : ℚ) ∈ Set.univ \ lowerCut
  exact ⟨Set.mem_univ _, not_lt_of_ge hcube.le⟩

/--
Exercise 12, gap 24.

The rebound arbitrary set `B` is replaced by the fixed upper cut.
-/
theorem gap24
    (h23 : PointwiseLowerInCut) :
    NoLeastUpperElement := by
  rintro ⟨b, hb, hleast⟩
  rcases h23 b hb with ⟨n, hn, hb'⟩
  have hnq : 0 < (n : ℚ) := by exact_mod_cast hn
  have hlt : b - 1 / (n : ℚ) < b := by
    linarith [one_div_pos.mpr hnq]
  exact (not_lt_of_ge (hleast _ hb')) hlt

/--
Exercise 12, gap 25.

The malformed nested statement is restored to the conjunction of the two
endpoint properties.
-/
theorem gap25
    (h9 : NoGreatestLowerElement)
    (h24 : NoLeastUpperElement) :
    NoEndpoints := by
  exact ⟨h9, h24⟩

end ProofGap.Exercise12
