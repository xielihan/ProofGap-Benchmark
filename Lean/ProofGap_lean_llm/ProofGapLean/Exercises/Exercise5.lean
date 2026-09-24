import ProofGapLean.Prelude.Discrete

/-!
# Exercise 5

Semantic formalization of Exercise 5, gaps 1,...,10.

The source function `A(a,n)` is the step-`h` falling factorial
`∏ i=0,...,n-1 (a-i*h)`.  The notation `C(n)^m` is the binomial coefficient
`Nat.choose n m`, cast to `ℝ`.
-/

namespace ProofGap.Exercise5

def falling (h a : ℝ) (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.range n, (a - (i : ℝ) * h)

def convolution (h a b : ℝ) (n : ℕ) : ℝ :=
  ∑ m ∈ Finset.range (n + 1),
    (Nat.choose n m : ℝ) * falling h a (n - m) * falling h b m

def GeneralizedBinomial (h a b : ℝ) (n : ℕ) : Prop :=
  falling h (a + b) n = convolution h a b n

def DefiningEquation (h : ℝ) : Prop :=
  ∀ a : ℝ, ∀ n : ℕ,
    falling h a n = ∏ i ∈ Finset.range n, (a - (i : ℝ) * h)

def ZeroFactorial (h : ℝ) : Prop :=
  ∀ a : ℝ, falling h a 0 = 1

def BaseValue (h : ℝ) : Prop :=
  ∀ n : ℕ, ∀ a b : ℝ, n = 1 → falling h (a + b) 1 = a + b

def BaseConvolution (h : ℝ) : Prop :=
  ∀ n : ℕ, ∀ a b : ℝ, n = 1 → convolution h a b 1 = a + b

def FallingRecurrence (h : ℝ) : Prop :=
  ∀ a b : ℝ, ∀ k : ℕ, 0 < k → GeneralizedBinomial h a b k →
    falling h (a + b) (k + 1) =
      falling h (a + b) k * (a + b - (k : ℝ) * h)

def SubstituteInductionHypothesis (h : ℝ) : Prop :=
  ∀ a b : ℝ, ∀ k : ℕ, 0 < k → GeneralizedBinomial h a b k →
    falling h (a + b) (k + 1) =
      (a + b - (k : ℝ) * h) * convolution h a b k

def ExpandedSuccessorConvolution (h : ℝ) : Prop :=
  ∀ a b : ℝ, ∀ k : ℕ, 0 < k → GeneralizedBinomial h a b k →
    falling h (a + b) (k + 1) = convolution h a b (k + 1)

def PositiveGeneralizedBinomial (h : ℝ) : Prop :=
  ∀ a b : ℝ, ∀ n : ℕ, 0 < n → GeneralizedBinomial h a b n

def ZeroStepPowerLaw (h : ℝ) : Prop :=
  ∀ a : ℝ, ∀ n : ℕ, h = 0 → falling h a n = a ^ n

def OrdinaryBinomialAtZeroStep (h : ℝ) : Prop :=
  ∀ a b : ℝ, ∀ n : ℕ, h = 0 →
    (a + b) ^ n =
      ∑ m ∈ Finset.range (n + 1),
        (Nat.choose n m : ℝ) * a ^ (n - m) * b ^ m

private theorem falling_succ (h a : ℝ) (n : ℕ) :
    falling h a (n + 1) = falling h a n * (a - (n : ℝ) * h) := by
  simp [falling, Finset.prod_range_succ]

private theorem convolution_eq_commuted_sum (h a b : ℝ) (n : ℕ) :
    convolution h a b n =
      ∑ i ∈ Finset.range (n + 1),
        (Nat.choose n i : ℝ) * (falling h b i * falling h a (n - i)) := by
  simp only [convolution]
  apply Finset.sum_congr rfl
  intro i hi
  ring

private theorem convolution_succ (h a b : ℝ) (n : ℕ) :
    convolution h a b (n + 1) =
      (a + b - (n : ℝ) * h) * convolution h a b n := by
  rw [convolution_eq_commuted_sum, convolution_eq_commuted_sum]
  calc
    (∑ i ∈ Finset.range (n + 1 + 1),
        (Nat.choose (n + 1) i : ℝ) *
          (falling h b i * falling h a (n + 1 - i))) =
        (∑ i ∈ Finset.range (n + 1),
          (Nat.choose n i : ℝ) *
            (falling h b i * falling h a (n + 1 - i))) +
        ∑ i ∈ Finset.range (n + 1),
          (Nat.choose n i : ℝ) *
            (falling h b (i + 1) * falling h a (n - i)) := by
      simpa [Nat.add_assoc] using
        (Finset.sum_choose_succ_mul
          (R := ℝ)
          (fun i j => falling h b i * falling h a j)
          n)
    _ = (a + b - (n : ℝ) * h) *
        ∑ i ∈ Finset.range (n + 1),
          (Nat.choose n i : ℝ) *
            (falling h b i * falling h a (n - i)) := by
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have hi_le : i ≤ n := by
        simpa [Finset.mem_range, Nat.lt_succ_iff] using hi
      have hsub : n + 1 - i = (n - i) + 1 := by
        omega
      rw [hsub, falling_succ h a (n - i), falling_succ h b i]
      have hcast : ((n - i : ℕ) : ℝ) + (i : ℝ) = (n : ℝ) := by
        exact_mod_cast Nat.sub_add_cancel hi_le
      rw [← hcast]
      ring

/-- Exercise 5, gap 1. -/
theorem gap1
    (h : ℝ)
    (h1 : DefiningEquation h)
    (h2 : ZeroFactorial h) :
    BaseValue h := by
  intro n a b hn
  subst n
  simp [falling]

/-- Exercise 5, gap 2. -/
theorem gap2
    (h : ℝ)
    (h1 : DefiningEquation h)
    (h2 : ZeroFactorial h)
    (h3 : BaseValue h) :
    BaseConvolution h := by
  intro n a b hn
  subst n
  norm_num [convolution, falling, Finset.sum_range_succ, Finset.prod_range_succ]

/-- Exercise 5, gap 3. -/
theorem gap3
    (h : ℝ)
    (h1 : DefiningEquation h)
    (h2 : ZeroFactorial h)
    (h3 : BaseValue h)
    (h4 : BaseConvolution h) :
    FallingRecurrence h := by
  intro a b k hk hGB
  exact falling_succ h (a + b) k

/-- Exercise 5, gap 4. -/
theorem gap4
    (h : ℝ)
    (h1 : DefiningEquation h)
    (h2 : ZeroFactorial h)
    (h3 : BaseValue h)
    (h4 : BaseConvolution h)
    (h5 : FallingRecurrence h) :
    SubstituteInductionHypothesis h := by
  intro a b k hk hGB
  rw [h5 a b k hk hGB, hGB]
  ring

/--
Exercise 5, gap 5.

The displayed first, second, penultimate, and final terms separated by an
ellipsis are represented by the complete successor convolution.
-/
theorem gap5
    (h : ℝ)
    (h1 : DefiningEquation h)
    (h2 : ZeroFactorial h)
    (h3 : BaseValue h)
    (h4 : BaseConvolution h)
    (h5 : FallingRecurrence h)
    (h6 : SubstituteInductionHypothesis h) :
    ExpandedSuccessorConvolution h := by
  intro a b k hk hGB
  calc
    falling h (a + b) (k + 1) =
        (a + b - (k : ℝ) * h) * convolution h a b k :=
      h6 a b k hk hGB
    _ = convolution h a b (k + 1) := (convolution_succ h a b k).symm

/--
Exercise 5, gap 6.

This is the summation-notation version of gap 5 and therefore has the same
semantic proposition.
-/
theorem gap6
    (h : ℝ)
    (h1 : DefiningEquation h)
    (h2 : ZeroFactorial h)
    (h3 : BaseValue h)
    (h4 : BaseConvolution h)
    (h5 : FallingRecurrence h)
    (h6 : SubstituteInductionHypothesis h)
    (h7 : ExpandedSuccessorConvolution h) :
    ExpandedSuccessorConvolution h := by
  exact h7

/-- Exercise 5, gap 7. -/
theorem gap7
    (h : ℝ)
    (h1 : DefiningEquation h)
    (h2 : ZeroFactorial h)
    (h3 : BaseValue h)
    (h4 : BaseConvolution h)
    (h5 : FallingRecurrence h)
    (h6 : SubstituteInductionHypothesis h)
    (h7 : ExpandedSuccessorConvolution h)
    (h8 : ExpandedSuccessorConvolution h) :
    PositiveGeneralizedBinomial h := by
  intro a b n hn
  have hbase : GeneralizedBinomial h a b 1 := by
    change falling h (a + b) 1 = convolution h a b 1
    calc
      falling h (a + b) 1 = a + b := h3 1 a b rfl
      _ = convolution h a b 1 := (h4 1 a b rfl).symm
  exact Nat.le_induction
    hbase
    (fun k hk ih => h8 a b k hk ih)
    n
    hn

/-- Exercise 5, gap 8. -/
theorem gap8
    (h : ℝ)
    (h1 : DefiningEquation h)
    (h2 : ZeroFactorial h)
    (h3 : BaseValue h)
    (h4 : BaseConvolution h)
    (h5 : FallingRecurrence h)
    (h6 : SubstituteInductionHypothesis h)
    (h7 : ExpandedSuccessorConvolution h)
    (h8 : ExpandedSuccessorConvolution h)
    (h9 : PositiveGeneralizedBinomial h) :
    ZeroStepPowerLaw h := by
  intro a n hh
  subst h
  simp [falling]

/-- Exercise 5, gap 9. -/
theorem gap9
    (h : ℝ)
    (h1 : DefiningEquation h)
    (h2 : ZeroFactorial h)
    (h3 : BaseValue h)
    (h4 : BaseConvolution h)
    (h5 : FallingRecurrence h)
    (h6 : SubstituteInductionHypothesis h)
    (h7 : ExpandedSuccessorConvolution h)
    (h8 : ExpandedSuccessorConvolution h)
    (h9 : PositiveGeneralizedBinomial h)
    (h10 : ZeroStepPowerLaw h) :
    OrdinaryBinomialAtZeroStep h := by
  intro a b n hh
  subst h
  cases n with
  | zero =>
      simp
  | succ n =>
      have hGB := h9 a b (n + 1) (by omega)
      change falling 0 (a + b) (n + 1) = convolution 0 a b (n + 1) at hGB
      have hpower (x : ℝ) (m : ℕ) : falling 0 x m = x ^ m :=
        h10 x m rfl
      simpa only [convolution, hpower] using hGB

/--
Exercise 5, gap 10.

The goal repeats the generalized binomial identity from gap 7.
-/
theorem gap10
    (h : ℝ)
    (h1 : DefiningEquation h)
    (h2 : ZeroFactorial h)
    (h3 : BaseValue h)
    (h4 : BaseConvolution h)
    (h5 : FallingRecurrence h)
    (h6 : SubstituteInductionHypothesis h)
    (h7 : ExpandedSuccessorConvolution h)
    (h8 : ExpandedSuccessorConvolution h)
    (h9 : PositiveGeneralizedBinomial h)
    (h10 : ZeroStepPowerLaw h)
    (h11 : OrdinaryBinomialAtZeroStep h) :
    PositiveGeneralizedBinomial h := by
  exact h9

end ProofGap.Exercise5
