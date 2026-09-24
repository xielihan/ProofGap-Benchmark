import ProofGapLean.Prelude.Elementary
import ProofGapLean.Prelude.Finite

/-!
# Exercise 10

Semantic formalization of `proof_gap/exercise_10/{1,...,10}.txt`.
The source `sqrtn(2,x)` is the positive real square root `Real.sqrt x`.
-/

namespace ProofGap.Exercise10

noncomputable section

def wallisProduct (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.Icc 1 n,
    (2 * (i : ℝ) - 1) / (2 * (i : ℝ))

def rootBound (n : ℕ) : ℝ :=
  1 / Real.sqrt (2 * (n : ℝ) + 1)

def WallisBound (n : ℕ) : Prop :=
  wallisProduct n < rootBound n

def BaseCase : Prop :=
  ∀ n : ℕ, n = 1 → (1 / 2 : ℝ) < 1 / Real.sqrt 3

def AppendFactor : Prop :=
  ∀ k : ℕ, 0 < k → WallisBound k →
    wallisProduct (k + 1) <
      rootBound k * ((2 * (k : ℝ) + 1) / (2 * (k : ℝ) + 2))

def RationalizeIntermediate : Prop :=
  ∀ k : ℕ, 0 < k → WallisBound k →
    rootBound k * ((2 * (k : ℝ) + 1) / (2 * (k : ℝ) + 2)) =
      Real.sqrt (2 * (k : ℝ) + 1) / (2 * (k : ℝ) + 2)

def SubstituteRationalization : Prop :=
  ∀ k : ℕ, 0 < k → WallisBound k →
    wallisProduct (k + 1) <
      Real.sqrt (2 * (k : ℝ) + 1) / (2 * (k : ℝ) + 2)

def RootComparison : Prop :=
  ∀ k : ℕ, 0 < k → WallisBound k →
    (2 * (k : ℝ) + 1) * (2 * (k : ℝ) + 3) <
      (2 * (k : ℝ) + 2) ^ 2 →
    Real.sqrt (2 * (k : ℝ) + 1) / (2 * (k : ℝ) + 2) <
      1 / Real.sqrt (2 * (k : ℝ) + 3)

def ExpandPolynomialInequality : Prop :=
  ∀ k : ℕ, 0 < k → WallisBound k →
    4 * (k : ℝ) ^ 2 + 8 * (k : ℝ) + 3 <
      4 * (k : ℝ) ^ 2 + 8 * (k : ℝ) + 4 →
    (2 * (k : ℝ) + 1) * (2 * (k : ℝ) + 3) <
      (2 * (k : ℝ) + 2) ^ 2

def ApplyRootComparison : Prop :=
  ∀ k : ℕ, 0 < k → WallisBound k →
    4 * (k : ℝ) ^ 2 + 8 * (k : ℝ) + 3 <
      4 * (k : ℝ) ^ 2 + 8 * (k : ℝ) + 4 →
    Real.sqrt (2 * (k : ℝ) + 1) / (2 * (k : ℝ) + 2) <
      1 / Real.sqrt (2 * (k : ℝ) + 3)

def InductionStep : Prop :=
  ∀ k : ℕ, 0 < k → WallisBound k → WallisBound (k + 1)

def CorrectedFinalBound : Prop :=
  ∀ n : ℕ, 0 < n → WallisBound n

/-- Source: `proof_gap/exercise_10/1.txt`. -/
theorem gap1 : BaseCase := by
  intro n hn
  have hspos : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hslt : Real.sqrt (3 : ℝ) < 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  rw [div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 2) hspos]
  simpa using hslt

/-- Source: `proof_gap/exercise_10/2.txt`. -/
theorem gap2
    (h1 : BaseCase) :
    AppendFactor := by
  intro k hk hbound
  unfold WallisBound at hbound
  have hfactor :
      0 < (2 * (k : ℝ) + 1) / (2 * (k : ℝ) + 2) := by
    positivity
  have hmul := mul_lt_mul_of_pos_right hbound hfactor
  rw [wallisProduct, Finset.prod_Icc_succ_top (by omega)]
  convert hmul using 1 <;>
    simp only [wallisProduct, Nat.cast_add, Nat.cast_one] <;> ring

/-- Source: `proof_gap/exercise_10/3.txt`. -/
theorem gap3
    (h1 : BaseCase)
    (h2 : AppendFactor) :
    RationalizeIntermediate := by
  intro k hk hbound
  unfold rootBound
  have hA : 0 ≤ 2 * (k : ℝ) + 1 := by positivity
  have hs : Real.sqrt (2 * (k : ℝ) + 1) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by positivity))
  have hden : 2 * (k : ℝ) + 2 ≠ 0 := by positivity
  have hsq := Real.sq_sqrt hA
  field_simp [hs, hden]
  nlinarith

/-- Source: `proof_gap/exercise_10/4.txt`. -/
theorem gap4
    (h1 : BaseCase)
    (h2 : AppendFactor)
    (h3 : RationalizeIntermediate) :
    SubstituteRationalization := by
  intro k hk hbound
  rw [← h3 k hk hbound]
  exact h2 k hk hbound

/-- Source: `proof_gap/exercise_10/5.txt`. -/
theorem gap5
    (h1 : BaseCase)
    (h2 : AppendFactor)
    (h3 : RationalizeIntermediate)
    (h4 : SubstituteRationalization) :
    RootComparison := by
  intro k hk hbound hpoly
  let A : ℝ := 2 * (k : ℝ) + 1
  let B : ℝ := 2 * (k : ℝ) + 2
  let C : ℝ := 2 * (k : ℝ) + 3
  change A * C < B ^ 2 at hpoly
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hsC : 0 < Real.sqrt C := Real.sqrt_pos.2 (by
    dsimp [C]
    positivity)
  have hsA_sq : (Real.sqrt A) ^ 2 = A := Real.sq_sqrt hA
  have hsC_sq : (Real.sqrt C) ^ 2 = C := Real.sq_sqrt hC
  have hprod_sq :
      (Real.sqrt A * Real.sqrt C) ^ 2 = A * C := by
    rw [mul_pow, hsA_sq, hsC_sq]
  have hprod_nonneg : 0 ≤ Real.sqrt A * Real.sqrt C := by positivity
  have hprod : Real.sqrt A * Real.sqrt C < B := by
    nlinarith
  change Real.sqrt A / B < 1 / Real.sqrt C
  rw [div_lt_div_iff₀ hB hsC]
  simpa using hprod

/-- Source: `proof_gap/exercise_10/6.txt`. -/
theorem gap6
    (h1 : BaseCase)
    (h2 : AppendFactor)
    (h3 : RationalizeIntermediate)
    (h4 : SubstituteRationalization)
    (h5 : RootComparison) :
    ExpandPolynomialInequality := by
  intro k hk hbound hpoly
  nlinarith

/-- Source: `proof_gap/exercise_10/7.txt`. -/
theorem gap7
    (h1 : BaseCase)
    (h2 : AppendFactor)
    (h3 : RationalizeIntermediate)
    (h4 : SubstituteRationalization)
    (h5 : RootComparison)
    (h6 : ExpandPolynomialInequality) :
    ApplyRootComparison := by
  intro k hk hbound hpoly
  exact h5 k hk hbound (h6 k hk hbound hpoly)

/-- Source: `proof_gap/exercise_10/8.txt`. -/
theorem gap8
    (h1 : BaseCase)
    (h2 : AppendFactor)
    (h3 : RationalizeIntermediate)
    (h4 : SubstituteRationalization)
    (h5 : RootComparison)
    (h6 : ExpandPolynomialInequality)
    (h7 : ApplyRootComparison) :
    InductionStep := by
  intro k hk hbound
  have hroot := h7 k hk hbound (by nlinarith)
  have hstep := (h4 k hk hbound).trans hroot
  unfold WallisBound rootBound
  convert hstep using 1 <;> norm_num <;> ring

/--
Source: `proof_gap/exercise_10/9.txt`.

The unrestricted source goal is false at `n=0`: both sides equal one.  The
positive-index condition used by the base case and induction step is restored.
-/
theorem gap9
    (h1 : BaseCase)
    (h2 : AppendFactor)
    (h3 : RationalizeIntermediate)
    (h4 : SubstituteRationalization)
    (h5 : RootComparison)
    (h6 : ExpandPolynomialInequality)
    (h7 : ApplyRootComparison)
    (h8 : InductionStep) :
    CorrectedFinalBound := by
  intro n
  induction n with
  | zero =>
      intro hn
      omega
  | succ k ih =>
      intro hn
      by_cases hk : k = 0
      · subst k
        convert h1 1 rfl using 1 <;>
          norm_num [WallisBound, wallisProduct, rootBound] <;> ring
      · exact h8 k (by omega) (ih (by omega))

/--
Source: `proof_gap/exercise_10/10.txt`.

This duplicates gap 9 and uses the same repaired positive-index domain.
-/
theorem gap10
    (h1 : BaseCase)
    (h2 : AppendFactor)
    (h3 : RationalizeIntermediate)
    (h4 : SubstituteRationalization)
    (h5 : RootComparison)
    (h6 : ExpandPolynomialInequality)
    (h7 : ApplyRootComparison)
    (h8 : InductionStep)
    (h9 : CorrectedFinalBound) :
    CorrectedFinalBound := by
  exact h9

end

end ProofGap.Exercise10
