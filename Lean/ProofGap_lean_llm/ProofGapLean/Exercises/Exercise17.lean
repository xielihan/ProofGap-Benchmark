import ProofGapLean.Prelude.Elementary

/-!
# Exercise 17

Semantic formalization of `proof_gap/exercise_17/{1,...,6}.txt`.
All three source sets consist of rational numbers.  They are embedded into
`ℝ` before applying `sSup` and `sInf`, because `ℚ` is not conditionally
complete.
-/

namespace ProofGap.Exercise17

/-- The image in `ℝ` of the rational set `{q | q² < 2}`. -/
def E : Set ℝ :=
  {x | ∃ q : ℚ, x = (q : ℝ) ∧ q ^ 2 < 2}

/--
The rational lower set from the source: every nonpositive rational, together
with the positive rationals whose square is below two.
-/
def A : Set ℝ :=
  {x | ∃ q : ℚ, x = (q : ℝ) ∧ (q ≤ 0 ∨ (0 < q ∧ q ^ 2 < 2))}

/-- The complement of `A` within the embedded rational numbers. -/
def B : Set ℝ :=
  Set.range (fun q : ℚ => (q : ℝ)) \ A

/--
The reflected rational upper set: every nonnegative rational, together with
the negative rationals whose square is below two.
-/
def BPrime : Set ℝ :=
  {x | ∃ q : ℚ, x = (q : ℝ) ∧ (0 ≤ q ∨ (q < 0 ∧ q ^ 2 < 2))}

/-- The complement of `BPrime` within the embedded rational numbers. -/
def APrime : Set ℝ :=
  Set.range (fun q : ℚ => (q : ℝ)) \ BPrime

private lemma isLUB_E_sqrtTwo : IsLUB E (Real.sqrt 2) := by
  have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hssq : (Real.sqrt 2) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  constructor
  · rintro x ⟨q, rfl, hq⟩
    have hqreal : ((q : ℝ) ^ 2) < 2 := by exact_mod_cast hq
    by_cases hqnonpos : (q : ℝ) ≤ 0
    · linarith
    · nlinarith
  · intro M hupper
    by_contra hnot
    have hMlt : M < Real.sqrt 2 := lt_of_not_ge hnot
    have hmax : max M 0 < Real.sqrt 2 := max_lt hMlt hspos
    rcases exists_rat_btwn hmax with ⟨q, hqmax, hqsqrt⟩
    have hqpos : (0 : ℝ) < q :=
      (le_max_right M 0).trans_lt hqmax
    have hqreal : ((q : ℝ) ^ 2) < 2 := by nlinarith
    have hqrat : q ^ 2 < (2 : ℚ) := by exact_mod_cast hqreal
    have hqmem : (q : ℝ) ∈ E := ⟨q, rfl, hqrat⟩
    have hqle := hupper hqmem
    linarith [lt_of_le_of_lt (le_max_left M 0) hqmax]

private lemma isLUB_A_sqrtTwo : IsLUB A (Real.sqrt 2) := by
  have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hssq : (Real.sqrt 2) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  constructor
  · rintro x ⟨q, rfl, hqnonpos | ⟨hqpos, hq⟩⟩
    · have : (q : ℝ) ≤ 0 := by exact_mod_cast hqnonpos
      linarith
    · have hqreal : ((q : ℝ) ^ 2) < 2 := by exact_mod_cast hq
      have hqposreal : (0 : ℝ) < q := by exact_mod_cast hqpos
      nlinarith
  · intro M hupper
    by_contra hnot
    have hMlt : M < Real.sqrt 2 := lt_of_not_ge hnot
    have hmax : max M 0 < Real.sqrt 2 := max_lt hMlt hspos
    rcases exists_rat_btwn hmax with ⟨q, hqmax, hqsqrt⟩
    have hqpos : (0 : ℝ) < q :=
      (le_max_right M 0).trans_lt hqmax
    have hqreal : ((q : ℝ) ^ 2) < 2 := by nlinarith
    have hqposrat : (0 : ℚ) < q := by exact_mod_cast hqpos
    have hqrat : q ^ 2 < (2 : ℚ) := by exact_mod_cast hqreal
    have hqmem : (q : ℝ) ∈ A := ⟨q, rfl, Or.inr ⟨hqposrat, hqrat⟩⟩
    have hqle := hupper hqmem
    linarith [lt_of_le_of_lt (le_max_left M 0) hqmax]

private lemma isGLB_E_negSqrtTwo : IsGLB E (-Real.sqrt 2) := by
  have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hssq : (Real.sqrt 2) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  constructor
  · rintro x ⟨q, rfl, hq⟩
    have hqreal : ((q : ℝ) ^ 2) < 2 := by exact_mod_cast hq
    by_cases hqnonneg : 0 ≤ (q : ℝ)
    · linarith
    · nlinarith
  · intro M hlower
    by_contra hnot
    have hMgt : -Real.sqrt 2 < M := lt_of_not_ge hnot
    have hmin : -Real.sqrt 2 < min M 0 :=
      lt_min hMgt (neg_lt_zero.mpr hspos)
    rcases exists_rat_btwn hmin with ⟨q, hqnegroot, hqmin⟩
    have hqneg : (q : ℝ) < 0 :=
      hqmin.trans_le (min_le_right M 0)
    have hqreal : ((q : ℝ) ^ 2) < 2 := by nlinarith
    have hqrat : q ^ 2 < (2 : ℚ) := by exact_mod_cast hqreal
    have hqmem : (q : ℝ) ∈ E := ⟨q, rfl, hqrat⟩
    have hMle := hlower hqmem
    linarith [hqmin.trans_le (min_le_left M 0)]

private lemma isGLB_BPrime_negSqrtTwo : IsGLB BPrime (-Real.sqrt 2) := by
  have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hssq : (Real.sqrt 2) ^ 2 = 2 :=
    Real.sq_sqrt (by norm_num)
  constructor
  · rintro x ⟨q, rfl, hqnonneg | ⟨hqneg, hq⟩⟩
    · have : (0 : ℝ) ≤ q := by exact_mod_cast hqnonneg
      linarith
    · have hqreal : ((q : ℝ) ^ 2) < 2 := by exact_mod_cast hq
      have hqnegreal : (q : ℝ) < 0 := by exact_mod_cast hqneg
      nlinarith
  · intro M hlower
    by_contra hnot
    have hMgt : -Real.sqrt 2 < M := lt_of_not_ge hnot
    have hmin : -Real.sqrt 2 < min M 0 :=
      lt_min hMgt (neg_lt_zero.mpr hspos)
    rcases exists_rat_btwn hmin with ⟨q, hqnegroot, hqmin⟩
    have hqneg : (q : ℝ) < 0 :=
      hqmin.trans_le (min_le_right M 0)
    have hqreal : ((q : ℝ) ^ 2) < 2 := by nlinarith
    have hqnegrat : q < (0 : ℚ) := by exact_mod_cast hqneg
    have hqrat : q ^ 2 < (2 : ℚ) := by exact_mod_cast hqreal
    have hqmem : (q : ℝ) ∈ BPrime :=
      ⟨q, rfl, Or.inr ⟨hqnegrat, hqrat⟩⟩
    have hMle := hlower hqmem
    linarith [hqmin.trans_le (min_le_left M 0)]

/-- Source: `proof_gap/exercise_17/1.txt`. -/
theorem gap1 :
    sSup E = sSup A := by
  have hEne : E.Nonempty := ⟨0, 0, by norm_num, by norm_num⟩
  have hAne : A.Nonempty := ⟨0, 0, by norm_num, Or.inl le_rfl⟩
  exact (isLUB_E_sqrtTwo.csSup_eq hEne).trans
    (isLUB_A_sqrtTwo.csSup_eq hAne).symm

/-- Source: `proof_gap/exercise_17/2.txt`. -/
theorem gap2
    (h1 : sSup E = sSup A) :
    sSup A = Real.sqrt 2 := by
  have hAne : A.Nonempty := ⟨0, 0, by norm_num, Or.inl le_rfl⟩
  exact isLUB_A_sqrtTwo.csSup_eq hAne

/-- Source: `proof_gap/exercise_17/3.txt`. -/
theorem gap3
    (h1 : sSup E = sSup A)
    (h2 : sSup A = Real.sqrt 2) :
    sSup E = Real.sqrt 2 := by
  exact h1.trans h2

/-- Source: `proof_gap/exercise_17/4.txt`. -/
theorem gap4
    (h1 : sSup E = sSup A)
    (h2 : sSup A = Real.sqrt 2)
    (h3 : sSup E = Real.sqrt 2) :
    sInf E = sInf BPrime := by
  have hEne : E.Nonempty := ⟨0, 0, by norm_num, by norm_num⟩
  have hBne : BPrime.Nonempty := ⟨0, 0, by norm_num, Or.inl le_rfl⟩
  exact (isGLB_E_negSqrtTwo.csInf_eq hEne).trans
    (isGLB_BPrime_negSqrtTwo.csInf_eq hBne).symm

/-- Source: `proof_gap/exercise_17/5.txt`. -/
theorem gap5
    (h4 : sInf E = sInf BPrime) :
    sInf BPrime = -Real.sqrt 2 := by
  have hBne : BPrime.Nonempty := ⟨0, 0, by norm_num, Or.inl le_rfl⟩
  exact isGLB_BPrime_negSqrtTwo.csInf_eq hBne

/-- Source: `proof_gap/exercise_17/6.txt`. -/
theorem gap6
    (h4 : sInf E = sInf BPrime)
    (h5 : sInf BPrime = -Real.sqrt 2) :
    sInf E = -Real.sqrt 2 := by
  exact h4.trans h5

end ProofGap.Exercise17
