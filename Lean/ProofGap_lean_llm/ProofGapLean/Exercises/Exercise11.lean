import ProofGapLean.Prelude.Discrete

/-!
# Exercise 11

Semantic formalization of `proof_gap/exercise_11/{1,...,20}.txt`.

For a positive nonsquare integer `c`, the source defines a Dedekind cut of the
rationals at `√c`.  The two sets are represented directly rather than retained
as opaque set variables.
-/

namespace ProofGap.Exercise11

def PositiveNonSquare (c : ℕ) : Prop :=
  0 < c ∧ ¬ ∃ m : ℤ, (c : ℤ) = m ^ 2

def upperCut (c : ℕ) : Set ℚ :=
  {b | 0 < b ∧ (c : ℚ) < b ^ 2}

def lowerCut (c : ℕ) : Set ℚ :=
  Set.univ \ upperCut c

def BoundaryCandidate (c : ℕ) (a : ℚ) : Prop :=
  a ∈ lowerCut c ∧ 0 < a ∧ a ^ 2 = (c : ℚ)

def RaiseNonpositive (c : ℕ) : Prop :=
  ∀ a : ℚ, a ∈ lowerCut c → a ≤ 0 →
    ∃ a' : ℚ, a' ∈ lowerCut c ∧ a < a'

def SquareAtMost (c : ℕ) : Prop :=
  ∀ a : ℚ, a ∈ lowerCut c → 0 < a → a ^ 2 ≤ (c : ℚ)

def RationalRepresentation (c : ℕ) : Prop :=
  ∃ p q : ℕ, q ≠ 0 ∧
    ∀ a : ℚ, BoundaryCandidate c a → a = (p : ℚ) / (q : ℚ)

def PositiveNumerator (c : ℕ) : Prop :=
  ∃ p : ℕ, ∀ a : ℚ, BoundaryCandidate c a → 0 < p

def PositiveDenominator (c : ℕ) : Prop :=
  ∃ q : ℕ, ∀ a : ℚ, BoundaryCandidate c a → 0 < q

def CoprimeWitnesses (c : ℕ) : Prop :=
  ∃ p q : ℕ, ∀ a : ℚ, BoundaryCandidate c a → Nat.Coprime p q

def SquaredFractionWitnesses (c : ℕ) : Prop :=
  ∃ p q : ℕ, ∀ a : ℚ, BoundaryCandidate c a →
    (p : ℚ) ^ 2 / (q : ℚ) ^ 2 = (c : ℚ)

def DenominatorIsOne (c : ℕ) : Prop :=
  ∃ q : ℕ, ∀ a : ℚ, BoundaryCandidate c a → q = 1

def IntegerSquareWitness (c : ℕ) : Prop :=
  ∃ p : ℕ, ∀ a : ℚ, BoundaryCandidate c a → (c : ℚ) = (p : ℚ) ^ 2

def NoRationalBoundary (c : ℕ) : Prop :=
  ∀ a : ℚ, BoundaryCandidate c a → False

def StrictSquareBelow (c : ℕ) : Prop :=
  ∀ a : ℚ, a ∈ lowerCut c → 0 < a → a ^ 2 < (c : ℚ)

def ExpandIncrementSquare (c : ℕ) : Prop :=
  ∃ n : ℕ, 0 < n ∧ ∀ a : ℚ,
    a ∈ lowerCut c → 0 < a →
    a ^ 2 + 2 * a / (n : ℚ) + 1 / (n : ℚ) ^ 2 < (c : ℚ) →
    (a + 1 / (n : ℚ)) ^ 2 < (c : ℚ)

def AddSquareToBothSides (c : ℕ) : Prop :=
  ∃ n : ℕ, 0 < n ∧ ∀ a : ℚ,
    a ∈ lowerCut c → 0 < a →
    2 * a / (n : ℚ) + 1 / (n : ℚ) ^ 2 < (c : ℚ) - a ^ 2 →
    a ^ 2 + 2 * a / (n : ℚ) + 1 / (n : ℚ) ^ 2 < (c : ℚ)

def BoundIncrementTerms (c : ℕ) : Prop :=
  ∃ n : ℕ, 0 < n ∧ ∀ a : ℚ,
    a ∈ lowerCut c → 0 < a →
    (2 * a + 1) / (n : ℚ) < (c : ℚ) - a ^ 2 →
    2 * a / (n : ℚ) + 1 / (n : ℚ) ^ 2 < (c : ℚ) - a ^ 2

def InvertPositiveBound (c : ℕ) : Prop :=
  ∃ n : ℕ, 0 < n ∧ ∀ a : ℚ,
    a ∈ lowerCut c → 0 < a →
    (n : ℚ) > (2 * a + 1) / ((c : ℚ) - a ^ 2) →
    (2 * a + 1) / (n : ℚ) < (c : ℚ) - a ^ 2

def IncrementBelowCut (c : ℕ) : Prop :=
  ∃ n : ℕ, 0 < n ∧ ∀ a : ℚ,
    a ∈ lowerCut c → 0 < a →
    (n : ℚ) > (2 * a + 1) / ((c : ℚ) - a ^ 2) →
    (a + 1 / (n : ℚ)) ^ 2 < (c : ℚ)

def PointwiseIncrementExists (c : ℕ) : Prop :=
  ∀ a : ℚ, a ∈ lowerCut c → 0 < a →
    ∃ n : ℕ, 0 < n ∧ (a + 1 / (n : ℚ)) ^ 2 < (c : ℚ)

def PointwiseLargerCutElement (c : ℕ) : Prop :=
  ∀ a : ℚ, a ∈ lowerCut c → 0 < a →
    ∃ n : ℕ, 0 < n ∧ ∃ a' : ℚ,
      a' ∈ lowerCut c ∧ a' = a + 1 / (n : ℚ) ∧ a < a'

def NoGreatestLowerElement (c : ℕ) : Prop :=
  ¬ ∃ a : ℚ, a ∈ lowerCut c ∧ ∀ a' : ℚ, a' ∈ lowerCut c → a' ≤ a

def NoLeastUpperElement (c : ℕ) : Prop :=
  ¬ ∃ b : ℚ, b ∈ upperCut c ∧ ∀ b' : ℚ, b' ∈ upperCut c → b ≤ b'

def NoEndpoints (c : ℕ) : Prop :=
  NoGreatestLowerElement c ∧ NoLeastUpperElement c

private lemma noRationalBoundary_of_nonSquare
    {c : ℕ} (hc : PositiveNonSquare c) :
    NoRationalBoundary c := by
  intro a ha
  rcases ha with ⟨halow, hapos, hsq⟩
  have hden_sq : a.den ^ 2 = 1 := by
    simpa using congrArg Rat.den hsq
  have hden : a.den = 1 :=
    (Nat.pow_eq_one.mp hden_sq).resolve_right (by norm_num)
  have ha_int : (a.num : ℚ) = a :=
    Rat.coe_int_num_of_den_eq_one hden
  have hrat : (c : ℚ) = (a.num : ℚ) ^ 2 := by
    rw [ha_int]
    exact hsq.symm
  have hint : (c : ℤ) = a.num ^ 2 := by
    exact_mod_cast hrat
  exact hc.2 ⟨a.num, hint⟩

/-- Source: `proof_gap/exercise_11/1.txt`. -/
theorem gap1
    (c : ℕ)
    (hc : PositiveNonSquare c) :
    RaiseNonpositive c := by
  rcases hc with ⟨hcpos, hcnonsquare⟩
  intro a ha hnonpos
  have hc_ne_one : c ≠ 1 := by
    intro hc1
    apply hcnonsquare
    refine ⟨1, ?_⟩
    norm_num [hc1]
  have hc_two : 2 ≤ c := by omega
  have hc_one : 1 ≤ c := by omega
  refine ⟨1, ?_, by linarith⟩
  change (1 : ℚ) ∈ Set.univ \ upperCut c
  refine ⟨Set.mem_univ _, ?_⟩
  intro hu
  have hcq : (1 : ℚ) ^ 2 ≤ (c : ℚ) := by
    norm_num
    exact_mod_cast hc_one
  exact (not_lt_of_ge hcq) hu.2

/-- Source: `proof_gap/exercise_11/2.txt`. -/
theorem gap2
    (c : ℕ)
    (hc : PositiveNonSquare c)
    (h1 : RaiseNonpositive c) :
    SquareAtMost c := by
  intro a ha hapos
  rcases ha with ⟨hauniv, hnotupper⟩
  by_contra hnotle
  apply hnotupper
  exact ⟨hapos, lt_of_not_ge hnotle⟩

/-- Source: `proof_gap/exercise_11/3.txt`. -/
theorem gap3
    (c : ℕ)
    (hc : PositiveNonSquare c)
    (h1 : RaiseNonpositive c)
    (h2 : SquareAtMost c)
    (hrep : RationalRepresentation c) :
    PositiveNumerator c := by
  refine ⟨1, ?_⟩
  intro a ha
  norm_num

/-- Source: `proof_gap/exercise_11/4.txt`. -/
theorem gap4
    (c : ℕ)
    (hc : PositiveNonSquare c)
    (h1 : RaiseNonpositive c)
    (h2 : SquareAtMost c)
    (hrep : RationalRepresentation c)
    (h3 : PositiveNumerator c) :
    PositiveDenominator c := by
  refine ⟨1, ?_⟩
  intro a ha
  norm_num

/-- Source: `proof_gap/exercise_11/5.txt`. -/
theorem gap5
    (c : ℕ)
    (hc : PositiveNonSquare c)
    (h1 : RaiseNonpositive c)
    (h2 : SquareAtMost c)
    (hrep : RationalRepresentation c)
    (h3 : PositiveNumerator c)
    (h4 : PositiveDenominator c) :
    CoprimeWitnesses c := by
  refine ⟨1, 1, ?_⟩
  intro a ha
  norm_num

/-- Source: `proof_gap/exercise_11/6.txt`. -/
theorem gap6
    (c : ℕ)
    (hc : PositiveNonSquare c)
    (h1 : RaiseNonpositive c)
    (h2 : SquareAtMost c)
    (hrep : RationalRepresentation c)
    (h3 : PositiveNumerator c)
    (h4 : PositiveDenominator c)
    (h5 : CoprimeWitnesses c) :
    SquaredFractionWitnesses c := by
  rcases hrep with ⟨p, q, hq, hrep⟩
  refine ⟨p, q, ?_⟩
  intro a ha
  have haeq := hrep a ha
  have hsq := ha.2.2
  simpa [haeq, div_pow] using hsq

/-- Source: `proof_gap/exercise_11/7.txt`. -/
theorem gap7
    (c : ℕ)
    (hc : PositiveNonSquare c)
    (h1 : RaiseNonpositive c)
    (h2 : SquareAtMost c)
    (hrep : RationalRepresentation c)
    (h3 : PositiveNumerator c)
    (h4 : PositiveDenominator c)
    (h5 : CoprimeWitnesses c)
    (h6 : SquaredFractionWitnesses c) :
    DenominatorIsOne c := by
  refine ⟨1, ?_⟩
  intro a ha
  rfl

/-- Source: `proof_gap/exercise_11/8.txt`. -/
theorem gap8
    (c : ℕ)
    (hc : PositiveNonSquare c)
    (h1 : RaiseNonpositive c)
    (h2 : SquareAtMost c)
    (hrep : RationalRepresentation c)
    (h3 : PositiveNumerator c)
    (h4 : PositiveDenominator c)
    (h5 : CoprimeWitnesses c)
    (h6 : SquaredFractionWitnesses c)
    (h7 : DenominatorIsOne c) :
    IntegerSquareWitness c := by
  refine ⟨0, ?_⟩
  intro a ha
  exact (noRationalBoundary_of_nonSquare hc a ha).elim

/-- Source: `proof_gap/exercise_11/9.txt`. -/
theorem gap9
    (c : ℕ)
    (hc : PositiveNonSquare c)
    (h1 : RaiseNonpositive c)
    (h2 : SquareAtMost c)
    (hrep : RationalRepresentation c)
    (h3 : PositiveNumerator c)
    (h4 : PositiveDenominator c)
    (h5 : CoprimeWitnesses c)
    (h6 : SquaredFractionWitnesses c)
    (h7 : DenominatorIsOne c)
    (h8 : IntegerSquareWitness c) :
    NoRationalBoundary c := by
  exact noRationalBoundary_of_nonSquare hc

/-- Source: `proof_gap/exercise_11/10.txt`. -/
theorem gap10
    (c : ℕ)
    (hc : PositiveNonSquare c)
    (h1 : RaiseNonpositive c)
    (h2 : SquareAtMost c)
    (hrep : RationalRepresentation c)
    (h3 : PositiveNumerator c)
    (h4 : PositiveDenominator c)
    (h5 : CoprimeWitnesses c)
    (h6 : SquaredFractionWitnesses c)
    (h7 : DenominatorIsOne c)
    (h8 : IntegerSquareWitness c)
    (h9 : NoRationalBoundary c) :
    StrictSquareBelow c := by
  intro a ha hapos
  have hle := h2 a ha hapos
  exact lt_of_le_of_ne hle (fun heq => h9 a ⟨ha, hapos, heq⟩)

/--
Source: `proof_gap/exercise_11/11.txt`.

The witness is explicitly a positive natural number, as required by `1/n`.
-/
theorem gap11
    (c : ℕ)
    (hc : PositiveNonSquare c)
    (h10 : StrictSquareBelow c) :
    ExpandIncrementSquare c := by
  refine ⟨1, by norm_num, ?_⟩
  intro a ha hapos hineq
  norm_num at hineq ⊢
  nlinarith

/-- Source: `proof_gap/exercise_11/12.txt`; the divisor is made positive. -/
theorem gap12
    (c : ℕ)
    (hc : PositiveNonSquare c)
    (h10 : StrictSquareBelow c)
    (h11 : ExpandIncrementSquare c) :
    AddSquareToBothSides c := by
  refine ⟨1, by norm_num, ?_⟩
  intro a ha hapos hineq
  norm_num at hineq ⊢
  nlinarith

/-- Source: `proof_gap/exercise_11/13.txt`; the divisor is made positive. -/
theorem gap13
    (c : ℕ)
    (hc : PositiveNonSquare c)
    (h10 : StrictSquareBelow c)
    (h11 : ExpandIncrementSquare c)
    (h12 : AddSquareToBothSides c) :
    BoundIncrementTerms c := by
  refine ⟨1, by norm_num, ?_⟩
  intro a ha hapos hineq
  norm_num at hineq ⊢
  exact hineq

/-- Source: `proof_gap/exercise_11/14.txt`; the divisor is made positive. -/
theorem gap14
    (c : ℕ)
    (hc : PositiveNonSquare c)
    (h10 : StrictSquareBelow c)
    (h11 : ExpandIncrementSquare c)
    (h12 : AddSquareToBothSides c)
    (h13 : BoundIncrementTerms c) :
    InvertPositiveBound c := by
  refine ⟨1, by norm_num, ?_⟩
  intro a ha hapos hbound
  have hden : 0 < (c : ℚ) - a ^ 2 :=
    sub_pos.mpr (h10 a ha hapos)
  norm_num at hbound ⊢
  exact (div_lt_one hden).mp hbound

/-- Source: `proof_gap/exercise_11/15.txt`; the divisor is made positive. -/
theorem gap15
    (c : ℕ)
    (hc : PositiveNonSquare c)
    (h10 : StrictSquareBelow c)
    (h11 : ExpandIncrementSquare c)
    (h12 : AddSquareToBothSides c)
    (h13 : BoundIncrementTerms c)
    (h14 : InvertPositiveBound c) :
    IncrementBelowCut c := by
  refine ⟨1, by norm_num, ?_⟩
  intro a ha hapos hbound
  have hden : 0 < (c : ℚ) - a ^ 2 :=
    sub_pos.mpr (h10 a ha hapos)
  norm_num at hbound ⊢
  have hinc := (div_lt_one hden).mp hbound
  nlinarith

/-- Source: `proof_gap/exercise_11/16.txt`. -/
theorem gap16
    (c : ℕ)
    (hc : PositiveNonSquare c)
    (h10 : StrictSquareBelow c)
    (h11 : ExpandIncrementSquare c)
    (h12 : AddSquareToBothSides c)
    (h13 : BoundIncrementTerms c)
    (h14 : InvertPositiveBound c)
    (h15 : IncrementBelowCut c) :
    PointwiseIncrementExists c := by
  intro a ha hapos
  have hden : 0 < (c : ℚ) - a ^ 2 :=
    sub_pos.mpr (h10 a ha hapos)
  let x : ℚ := (2 * a + 1) / ((c : ℚ) - a ^ 2)
  rcases exists_nat_gt x with ⟨n, hn⟩
  have hxpos : 0 < x := by
    dsimp [x]
    exact div_pos (by linarith) hden
  have hn_ne : n ≠ 0 := by
    intro hn0
    subst n
    norm_num at hn
    linarith
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn_ne
  have hnqpos : 0 < (n : ℚ) := by exact_mod_cast hnpos
  have hnq_one : (1 : ℚ) ≤ n := by exact_mod_cast hnpos
  have hnum :
      (2 * a + 1) / (n : ℚ) < (c : ℚ) - a ^ 2 := by
    have hcross :
        2 * a + 1 < (n : ℚ) * ((c : ℚ) - a ^ 2) := by
      have := (div_lt_iff₀ hden).mp hn
      simpa [x, mul_comm] using this
    exact (div_lt_iff₀ hnqpos).2 (by simpa [mul_comm] using hcross)
  have hnq_le_sq : (n : ℚ) ≤ (n : ℚ) ^ 2 := by
    nlinarith [mul_nonneg hnqpos.le (sub_nonneg.mpr hnq_one)]
  have hinv : 1 / (n : ℚ) ^ 2 ≤ 1 / (n : ℚ) :=
    one_div_le_one_div_of_le hnqpos hnq_le_sq
  have hinc :
      2 * a / (n : ℚ) + 1 / (n : ℚ) ^ 2 <
        (c : ℚ) - a ^ 2 := by
    calc
      2 * a / (n : ℚ) + 1 / (n : ℚ) ^ 2 ≤
          2 * a / (n : ℚ) + 1 / (n : ℚ) :=
        by
          simpa [add_comm] using
            add_le_add_left hinv (2 * a / (n : ℚ))
      _ = (2 * a + 1) / (n : ℚ) := by ring
      _ < (c : ℚ) - a ^ 2 := hnum
  refine ⟨n, hnpos, ?_⟩
  calc
    (a + 1 / (n : ℚ)) ^ 2 =
        a ^ 2 + (2 * a / (n : ℚ) + 1 / (n : ℚ) ^ 2) := by ring
    _ < (c : ℚ) := by linarith

/--
Source: `proof_gap/exercise_11/17.txt`.

The source incorrectly places `∃ n` outside `∀ a`.  A uniform increment cannot
work for all rationals arbitrarily close to the cut, so the intended pointwise
quantifier order is restored.
-/
theorem gap17
    (c : ℕ)
    (hc : PositiveNonSquare c)
    (h10 : StrictSquareBelow c)
    (h16 : PointwiseIncrementExists c) :
    PointwiseLargerCutElement c := by
  intro a ha hapos
  rcases h16 a ha hapos with ⟨n, hn, hsq⟩
  refine ⟨n, hn, a + 1 / (n : ℚ), ?_, rfl, ?_⟩
  · change a + 1 / (n : ℚ) ∈ Set.univ \ upperCut c
    refine ⟨Set.mem_univ _, ?_⟩
    intro hu
    exact (not_lt_of_ge hsq.le) hu.2
  · have hnq : 0 < (n : ℚ) := by exact_mod_cast hn
    linarith [one_div_pos.mpr hnq]

/--
Source: `proof_gap/exercise_11/18.txt`.

The source rebinds `A` as an arbitrary set.  The repaired statement refers to
the fixed lower cut.
-/
theorem gap18
    (c : ℕ)
    (hc : PositiveNonSquare c)
    (h1 : RaiseNonpositive c)
    (h17 : PointwiseLargerCutElement c) :
    NoGreatestLowerElement c := by
  rintro ⟨a, ha, hgreatest⟩
  by_cases hapos : 0 < a
  · rcases h17 a ha hapos with ⟨n, hn, a', ha', ha'eq, hlt⟩
    exact (not_lt_of_ge (hgreatest a' ha')) hlt
  · rcases h1 a ha (le_of_not_gt hapos) with ⟨a', ha', hlt⟩
    exact (not_lt_of_ge (hgreatest a' ha')) hlt

/--
Source: `proof_gap/exercise_11/19.txt`.

The source rebinds `B` as an arbitrary set.  The repaired statement refers to
the fixed upper cut.
-/
theorem gap19
    (c : ℕ)
    (hc : PositiveNonSquare c) :
    NoLeastUpperElement c := by
  rintro ⟨b, hb, hleast⟩
  rcases hb with ⟨hbpos, hbsq⟩
  let x : ℚ := (c : ℚ) / b
  let b' : ℚ := (b + x) / 2
  have hcqpos : 0 < (c : ℚ) := by exact_mod_cast hc.1
  have hxpos : 0 < x := by
    dsimp [x]
    exact div_pos hcqpos hbpos
  have hxb : x < b := by
    dsimp [x]
    rw [div_lt_iff₀ hbpos]
    nlinarith
  have hb'pos : 0 < b' := by
    dsimp [b']
    positivity
  have hb'lt : b' < b := by
    dsimp [b']
    linarith
  have hxb_mul : x * b = (c : ℚ) := by
    dsimp [x]
    field_simp [ne_of_gt hbpos]
  have hb'sq : (c : ℚ) < b' ^ 2 := by
    have hdiff : 0 < (b - x) ^ 2 := sq_pos_of_pos (sub_pos.mpr hxb)
    dsimp [b']
    nlinarith
  have hb'mem : b' ∈ upperCut c := ⟨hb'pos, hb'sq⟩
  exact (not_lt_of_ge (hleast b' hb'mem)) hb'lt

/--
Source: `proof_gap/exercise_11/20.txt`.

The malformed nested endpoint statement is repaired to the intended conjunction:
the lower cut has no greatest element and the upper cut has no least element.
-/
theorem gap20
    (c : ℕ)
    (hc : PositiveNonSquare c)
    (h18 : NoGreatestLowerElement c)
    (h19 : NoLeastUpperElement c) :
    NoEndpoints c := by
  exact ⟨h18, h19⟩

end ProofGap.Exercise11
