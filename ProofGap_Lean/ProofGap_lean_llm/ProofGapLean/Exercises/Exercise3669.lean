import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise3669

noncomputable section

open scoped BigOperators

def objective {n : ℕ} (alpha : Fin n → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i, alpha i / x i

def constraint {n : ℕ} (beta : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 < x i) ∧ ∑ i, beta i * x i = 1}

def critical {n : ℕ} (alpha beta x : Fin n → ℝ) (lambda : ℝ) : Prop :=
  (∀ i, -(alpha i / x i ^ 2) + lambda * beta i = 0) ∧
    x ∈ constraint beta

def normalization {n : ℕ} (alpha beta : Fin n → ℝ) : ℝ :=
  ∑ j, Real.sqrt (alpha j * beta j)

def candidate {n : ℕ} (alpha beta : Fin n → ℝ) : Fin n → ℝ :=
  fun i => Real.sqrt (alpha i / beta i) * (normalization alpha beta)⁻¹

def secondVariation {n : ℕ}
    (alpha x dx : Fin n → ℝ) : ℝ :=
  2 * ∑ i, alpha i / x i ^ 3 * dx i ^ 2

def minimizers {n : ℕ}
    (alpha beta : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {x | x ∈ constraint beta ∧
    ∀ y ∈ constraint beta, objective alpha x ≤ objective alpha y}

private lemma _sqrt_ratio_identities {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Real.sqrt (a / b) * b = Real.sqrt (a * b) ∧
      a / Real.sqrt (a / b) = Real.sqrt (a * b) := by
  have hq : 0 < Real.sqrt (a / b) := Real.sqrt_pos.2 (div_pos ha hb)
  have hq2 : Real.sqrt (a / b) ^ 2 = a / b :=
    Real.sq_sqrt (le_of_lt (div_pos ha hb))
  have hr2 : Real.sqrt (a * b) ^ 2 = a * b :=
    Real.sq_sqrt (le_of_lt (mul_pos ha hb))
  have hqb : Real.sqrt (a / b) ^ 2 * b = a := by
    rw [hq2]
    field_simp [ne_of_gt hb]
  have hsquares :
      (Real.sqrt (a / b) * b) ^ 2 = Real.sqrt (a * b) ^ 2 := by
    rw [mul_pow, hr2]
    nlinarith
  have hfirst : Real.sqrt (a / b) * b = Real.sqrt (a * b) := by
    have hleft : 0 ≤ Real.sqrt (a / b) * b :=
      mul_nonneg (Real.sqrt_nonneg _) (le_of_lt hb)
    have hright : 0 ≤ Real.sqrt (a * b) := Real.sqrt_nonneg _
    nlinarith
  refine ⟨hfirst, ?_⟩
  calc
    a / Real.sqrt (a / b) =
        (Real.sqrt (a / b) ^ 2 * b) / Real.sqrt (a / b) := by rw [hqb]
    _ = Real.sqrt (a / b) * b := by
      field_simp [ne_of_gt hq]
    _ = Real.sqrt (a * b) := hfirst

private lemma _sqrt_ratio_cross {a b y : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hy : 0 < y) :
    Real.sqrt (a / y) * Real.sqrt (b * y) = Real.sqrt (a * b) := by
  have hu2 : Real.sqrt (a / y) ^ 2 = a / y :=
    Real.sq_sqrt (le_of_lt (div_pos ha hy))
  have hv2 : Real.sqrt (b * y) ^ 2 = b * y :=
    Real.sq_sqrt (le_of_lt (mul_pos hb hy))
  have hr2 : Real.sqrt (a * b) ^ 2 = a * b :=
    Real.sq_sqrt (le_of_lt (mul_pos ha hb))
  have hsquares :
      (Real.sqrt (a / y) * Real.sqrt (b * y)) ^ 2 =
        Real.sqrt (a * b) ^ 2 := by
    rw [mul_pow, hu2, hv2, hr2]
    field_simp [ne_of_gt hy]
  have hleft : 0 ≤ Real.sqrt (a / y) * Real.sqrt (b * y) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hright : 0 ≤ Real.sqrt (a * b) := Real.sqrt_nonneg _
  nlinarith

private lemma _normalization_pos {n : ℕ} (hn : 0 < n)
    (alpha beta : Fin n → ℝ) (ha : ∀ i, 0 < alpha i)
    (hb : ∀ i, 0 < beta i) : 0 < normalization alpha beta := by
  unfold normalization
  apply Finset.sum_pos
  · intro i _
    exact Real.sqrt_pos.2 (mul_pos (ha i) (hb i))
  · let i : Fin n := ⟨0, hn⟩
    exact ⟨i, Finset.mem_univ i⟩

private lemma _candidate_constraint {n : ℕ} (hn : 0 < n)
    (alpha beta : Fin n → ℝ) (ha : ∀ i, 0 < alpha i)
    (hb : ∀ i, 0 < beta i) :
    candidate alpha beta ∈ constraint beta := by
  have hN := _normalization_pos hn alpha beta ha hb
  constructor
  · intro i
    unfold candidate
    exact mul_pos (Real.sqrt_pos.2 (div_pos (ha i) (hb i)))
      (inv_pos.2 hN)
  · unfold candidate
    calc
      (∑ i, beta i *
          (Real.sqrt (alpha i / beta i) * (normalization alpha beta)⁻¹)) =
          ∑ i, Real.sqrt (alpha i * beta i) *
            (normalization alpha beta)⁻¹ := by
              apply Finset.sum_congr rfl
              intro i _
              rw [← mul_assoc, mul_comm (beta i),
                (_sqrt_ratio_identities (ha i) (hb i)).1]
      _ = normalization alpha beta * (normalization alpha beta)⁻¹ := by
            unfold normalization
            rw [Finset.sum_mul]
      _ = 1 := mul_inv_cancel₀ (ne_of_gt hN)

private lemma _candidate_objective {n : ℕ} (hn : 0 < n)
    (alpha beta : Fin n → ℝ) (ha : ∀ i, 0 < alpha i)
    (hb : ∀ i, 0 < beta i) :
    objective alpha (candidate alpha beta) = normalization alpha beta ^ 2 := by
  have hN := _normalization_pos hn alpha beta ha hb
  unfold objective candidate
  calc
    (∑ i, alpha i /
        (Real.sqrt (alpha i / beta i) * (normalization alpha beta)⁻¹)) =
        ∑ i, normalization alpha beta * Real.sqrt (alpha i * beta i) := by
          apply Finset.sum_congr rfl
          intro i _
          have hq : 0 < Real.sqrt (alpha i / beta i) :=
            Real.sqrt_pos.2 (div_pos (ha i) (hb i))
          rw [← (_sqrt_ratio_identities (ha i) (hb i)).2]
          field_simp [ne_of_gt hN, ne_of_gt hq]
    _ = normalization alpha beta *
        ∑ i, Real.sqrt (alpha i * beta i) := by rw [Finset.mul_sum]
    _ = normalization alpha beta ^ 2 := by
          unfold normalization
          ring

private lemma _candidate_critical {n : ℕ} (hn : 0 < n)
    (alpha beta : Fin n → ℝ) (ha : ∀ i, 0 < alpha i)
    (hb : ∀ i, 0 < beta i) :
    critical alpha beta (candidate alpha beta)
      (normalization alpha beta ^ 2) := by
  have hN := _normalization_pos hn alpha beta ha hb
  constructor
  · intro i
    have hq2 : Real.sqrt (alpha i / beta i) ^ 2 =
        alpha i / beta i :=
      Real.sq_sqrt (le_of_lt (div_pos (ha i) (hb i)))
    unfold candidate
    rw [mul_pow, hq2]
    field_simp [ne_of_gt hN, ne_of_gt (ha i), ne_of_gt (hb i)]
    <;> ring
  · exact _candidate_constraint hn alpha beta ha hb

private lemma _objective_difference {n : ℕ}
    (alpha beta y : Fin n → ℝ) (ha : ∀ i, 0 < alpha i)
    (hb : ∀ i, 0 < beta i) (hy : y ∈ constraint beta) :
    objective alpha y - normalization alpha beta ^ 2 =
      ∑ i, (Real.sqrt (alpha i / y i) -
        normalization alpha beta * Real.sqrt (beta i * y i)) ^ 2 := by
  let N := normalization alpha beta
  change objective alpha y - N ^ 2 =
    ∑ i, (Real.sqrt (alpha i / y i) -
      N * Real.sqrt (beta i * y i)) ^ 2
  have hweighted : ∑ i, N ^ 2 * (beta i * y i) = N ^ 2 := by
    rw [← Finset.mul_sum, hy.2, mul_one]
  have hnormal : ∑ i, 2 * N * Real.sqrt (alpha i * beta i) = 2 * N ^ 2 := by
    rw [← Finset.mul_sum]
    change 2 * N * N = 2 * N ^ 2
    ring
  calc
    objective alpha y - N ^ 2 = objective alpha y + N ^ 2 - 2 * N ^ 2 := by ring
    _ = (∑ i, alpha i / y i) +
          (∑ i, N ^ 2 * (beta i * y i)) -
          (∑ i, 2 * N * Real.sqrt (alpha i * beta i)) := by
            rw [hweighted, hnormal]
            rfl
    _ = ∑ i, (alpha i / y i + N ^ 2 * (beta i * y i) -
          2 * N * Real.sqrt (alpha i * beta i)) := by
            rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    _ = ∑ i, (Real.sqrt (alpha i / y i) -
          N * Real.sqrt (beta i * y i)) ^ 2 := by
            apply Finset.sum_congr rfl
            intro i _
            have hu2 : Real.sqrt (alpha i / y i) ^ 2 = alpha i / y i :=
              Real.sq_sqrt (le_of_lt (div_pos (ha i) (hy.1 i)))
            have hv2 : Real.sqrt (beta i * y i) ^ 2 = beta i * y i :=
              Real.sq_sqrt (le_of_lt (mul_pos (hb i) (hy.1 i)))
            have hcross := _sqrt_ratio_cross (ha i) (hb i) (hy.1 i)
            rw [show
              (Real.sqrt (alpha i / y i) -
                N * Real.sqrt (beta i * y i)) ^ 2 =
                Real.sqrt (alpha i / y i) ^ 2 +
                  N ^ 2 * Real.sqrt (beta i * y i) ^ 2 -
                  2 * N *
                    (Real.sqrt (alpha i / y i) *
                      Real.sqrt (beta i * y i)) by ring]
            rw [hu2, hv2, hcross]

theorem gap1 {n : ℕ} (alpha beta x : Fin n → ℝ) (lambda : ℝ)
    (ha : ∀ i, 0 < alpha i) (hb : ∀ i, 0 < beta i)
    (hcrit : critical alpha beta x lambda) :
    ∀ i, x i = candidate alpha beta i := by
  intro i
  rcases hcrit with ⟨hstat, hxpos, hcon⟩
  have hlambda : 0 < lambda := by
    have hquot : 0 < alpha i / x i ^ 2 :=
      div_pos (ha i) (pow_pos (hxpos i) 2)
    have hi := hstat i
    have hprod : 0 < lambda * beta i := by linarith
    rcases (mul_pos_iff.mp hprod) with h | h
    · exact h.1
    · exact False.elim ((not_lt_of_ge (le_of_lt (hb i))) h.2)
  have hsqrtlambda : 0 < Real.sqrt lambda := Real.sqrt_pos.2 hlambda
  have hscale : ∀ j, Real.sqrt lambda * x j = Real.sqrt (alpha j / beta j) := by
    intro j
    have hj := hstat j
    have hxjne : x j ≠ 0 := ne_of_gt (hxpos j)
    have hbj : beta j ≠ 0 := ne_of_gt (hb j)
    have hq2 : Real.sqrt (alpha j / beta j) ^ 2 = alpha j / beta j :=
      Real.sq_sqrt (le_of_lt (div_pos (ha j) (hb j)))
    have hl2 : Real.sqrt lambda ^ 2 = lambda :=
      Real.sq_sqrt (le_of_lt hlambda)
    have heq : lambda * beta j * x j ^ 2 = alpha j := by
      field_simp [hxjne] at hj
      nlinarith
    have hsquares :
        (Real.sqrt lambda * x j) ^ 2 =
          Real.sqrt (alpha j / beta j) ^ 2 := by
      rw [mul_pow, hl2, hq2]
      field_simp [hbj]
      nlinarith [heq]
    have hleft : 0 ≤ Real.sqrt lambda * x j :=
      mul_nonneg (Real.sqrt_nonneg _) (le_of_lt (hxpos j))
    have hright : 0 ≤ Real.sqrt (alpha j / beta j) := Real.sqrt_nonneg _
    nlinarith
  have hnormalization : normalization alpha beta = Real.sqrt lambda := by
    unfold normalization
    calc
      (∑ j, Real.sqrt (alpha j * beta j)) =
          ∑ j, Real.sqrt (alpha j / beta j) * beta j := by
            apply Finset.sum_congr rfl
            intro j _
            symm
            exact (_sqrt_ratio_identities (ha j) (hb j)).1
      _ = ∑ j, (Real.sqrt lambda * x j) * beta j := by
            apply Finset.sum_congr rfl
            intro j _
            rw [hscale j]
      _ = Real.sqrt lambda * ∑ j, beta j * x j := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
      _ = Real.sqrt lambda := by rw [hcon, mul_one]
  unfold candidate
  rw [hnormalization]
  have hi := hscale i
  field_simp [ne_of_gt hsqrtlambda]
  nlinarith

theorem gap2 {n : ℕ} (hn : 0 < n) (alpha beta : Fin n → ℝ)
    (ha : ∀ i, 0 < alpha i) (hb : ∀ i, 0 < beta i) :
    {x | ∃ lambda, critical alpha beta x lambda} =
      ({candidate alpha beta} : Set (Fin n → ℝ)) := by
  ext x
  constructor
  · rintro ⟨lambda, hcritical⟩
    have hx : x = candidate alpha beta := by
      funext i
      exact gap1 alpha beta x lambda ha hb hcritical i
    simpa [hx]
  · intro hx
    have hx' : x = candidate alpha beta := by simpa using hx
    subst x
    exact ⟨normalization alpha beta ^ 2,
      _candidate_critical hn alpha beta ha hb⟩

theorem gap3 {n : ℕ} (alpha x dx : Fin n → ℝ) :
    secondVariation alpha x dx =
      2 * ∑ i, alpha i / x i ^ 3 * dx i ^ 2 := by
  rfl

theorem gap4 {n : ℕ} (alpha x dx : Fin n → ℝ)
    (ha : ∀ i, 0 < alpha i) (hx : ∀ i, 0 < x i)
    (hdx : dx ≠ 0) :
    secondVariation alpha x dx > 0 := by
  unfold secondVariation
  have hexists : ∃ i, dx i ≠ 0 := by
    by_contra h
    apply hdx
    funext i
    by_contra hi
    exact h ⟨i, hi⟩
  rcases hexists with ⟨i, hi⟩
  have hnonneg : ∀ j,
      0 ≤ alpha j / x j ^ 3 * dx j ^ 2 := by
    intro j
    exact mul_nonneg
      (le_of_lt (div_pos (ha j) (pow_pos (hx j) 3)))
      (sq_nonneg (dx j))
  have hterm : 0 < alpha i / x i ^ 3 * dx i ^ 2 :=
    mul_pos (div_pos (ha i) (pow_pos (hx i) 3))
      (sq_pos_of_ne_zero hi)
  have hle :
      alpha i / x i ^ 3 * dx i ^ 2 ≤
        ∑ j, alpha j / x j ^ 3 * dx j ^ 2 :=
    Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ i)
  have hsum : 0 < ∑ j, alpha j / x j ^ 3 * dx j ^ 2 :=
    lt_of_lt_of_le hterm hle
  exact mul_pos (by norm_num) hsum

theorem gap5 {n : ℕ} (hn : 0 < n) (alpha x : Fin n → ℝ)
    (ha : ∀ i, 0 < alpha i) (hx : ∀ i, 0 < x i) :
    ∃ dx : Fin n → ℝ, secondVariation alpha x dx > 0 := by
  let i : Fin n := ⟨0, hn⟩
  refine ⟨fun _ => 1, gap4 alpha x (fun _ => 1) ha hx ?_⟩
  intro hzero
  have hi := congrFun hzero i
  norm_num at hi

theorem gap6 {n : ℕ} (hn : 0 < n) (alpha beta : Fin n → ℝ)
    (ha : ∀ i, 0 < alpha i) (hb : ∀ i, 0 < beta i) :
    minimizers alpha beta =
      ({candidate alpha beta} : Set (Fin n → ℝ)) := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hxconstraint, hxminimal⟩
    have hcconstraint := _candidate_constraint hn alpha beta ha hb
    have hcobjective := _candidate_objective hn alpha beta ha hb
    have hdiff := _objective_difference alpha beta x ha hb hxconstraint
    have hsumnonneg :
        0 ≤ ∑ i, (Real.sqrt (alpha i / x i) -
          normalization alpha beta * Real.sqrt (beta i * x i)) ^ 2 := by
      apply Finset.sum_nonneg
      intro i _
      exact sq_nonneg _
    have hobjective_ge :
        normalization alpha beta ^ 2 ≤ objective alpha x := by
      nlinarith
    have hobjective_le :
        objective alpha x ≤ normalization alpha beta ^ 2 := by
      rw [← hcobjective]
      exact hxminimal (candidate alpha beta) hcconstraint
    have hobjective_eq :
        objective alpha x = normalization alpha beta ^ 2 :=
      le_antisymm hobjective_le hobjective_ge
    have hsumzero :
        (∑ i, (Real.sqrt (alpha i / x i) -
          normalization alpha beta * Real.sqrt (beta i * x i)) ^ 2) = 0 := by
      nlinarith
    have heach : ∀ i ∈ Finset.univ,
        (Real.sqrt (alpha i / x i) -
          normalization alpha beta * Real.sqrt (beta i * x i)) ^ 2 = 0 := by
      apply (Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
        sq_nonneg (Real.sqrt (alpha i / x i) -
          normalization alpha beta * Real.sqrt (beta i * x i)))).mp
      exact hsumzero
    have hcritical :
        critical alpha beta x (normalization alpha beta ^ 2) := by
      constructor
      · intro i
        have hi := heach i (Finset.mem_univ i)
        have hroot : Real.sqrt (alpha i / x i) =
            normalization alpha beta * Real.sqrt (beta i * x i) := by
          nlinarith
        have hu2 : Real.sqrt (alpha i / x i) ^ 2 = alpha i / x i :=
          Real.sq_sqrt
            (le_of_lt (div_pos (ha i) (hxconstraint.1 i)))
        have hv2 : Real.sqrt (beta i * x i) ^ 2 = beta i * x i :=
          Real.sq_sqrt
            (le_of_lt (mul_pos (hb i) (hxconstraint.1 i)))
        have hsquare0 :
            Real.sqrt (alpha i / x i) ^ 2 =
              (normalization alpha beta * Real.sqrt (beta i * x i)) ^ 2 := by
          exact congrArg (fun z : ℝ => z ^ 2) hroot
        have hsquare :
            alpha i / x i =
              normalization alpha beta ^ 2 * (beta i * x i) := by
          rw [hu2, mul_pow, hv2] at hsquare0
          exact hsquare0
        have hxne : x i ≠ 0 := ne_of_gt (hxconstraint.1 i)
        field_simp [hxne] at hsquare ⊢
        nlinarith [hsquare]
      · exact hxconstraint
    have hxcandidate : x = candidate alpha beta := by
      funext i
      exact gap1 alpha beta x (normalization alpha beta ^ 2)
        ha hb hcritical i
    simpa [hxcandidate]
  · intro hx
    have hx' : x = candidate alpha beta := by simpa using hx
    subst x
    constructor
    · exact _candidate_constraint hn alpha beta ha hb
    · intro y hy
      have hdiff := _objective_difference alpha beta y ha hb hy
      have hsumnonneg :
          0 ≤ ∑ i, (Real.sqrt (alpha i / y i) -
            normalization alpha beta * Real.sqrt (beta i * y i)) ^ 2 := by
        apply Finset.sum_nonneg
        intro i _
        exact sq_nonneg _
      rw [_candidate_objective hn alpha beta ha hb]
      nlinarith

theorem gap7 {n : ℕ} (hn : 0 < n) (alpha beta : Fin n → ℝ)
    (ha : ∀ i, 0 < alpha i) (hb : ∀ i, 0 < beta i) :
    objective alpha (candidate alpha beta) =
      normalization alpha beta ^ 2 := by
  exact _candidate_objective hn alpha beta ha hb

end

end ProofGap.Exercise3669
