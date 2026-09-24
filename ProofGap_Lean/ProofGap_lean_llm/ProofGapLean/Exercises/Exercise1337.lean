import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise1337

noncomputable section

def HasLimitAtTop (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f Filter.atTop (nhds L)

def quotient (a n x : ℝ) : ℝ := Real.rpow x n / Real.exp (a * x)

def integerStage (a : ℝ) (n j : ℕ) (x : ℝ) : ℝ :=
  ((Nat.factorial n : ℝ) / (Nat.factorial (n - j) : ℝ)) *
    x ^ (n - j) / (a ^ j * Real.exp (a * x))

def IsPositiveInteger (n : ℝ) : Prop :=
  ∃ k : ℕ, 1 ≤ k ∧ n = k

private theorem monomialScaledExpLimit
    (a c d : ℝ) (m : ℕ) (ha : 0 < a) (hd : d ≠ 0) :
    HasLimitAtTop
      (fun x => c * x ^ m / (d * Real.exp (a * x))) 0 := by
  unfold HasLimitAtTop
  have hscale :
      Filter.Tendsto (fun x : ℝ => a * x) Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop.2 ?_
    intro b
    exact (Filter.eventually_ge_atTop (b / a)).mono fun x hx => by
      simpa [mul_comm] using (div_le_iff₀ ha).1 hx
  have hbase :
      Filter.Tendsto
        (fun x : ℝ => (a * x) ^ m * Real.exp (-(a * x)))
        Filter.atTop (nhds 0) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero m).comp hscale
  have hconst :
      Filter.Tendsto (fun _ : ℝ => c / (d * a ^ m)) Filter.atTop
        (nhds (c / (d * a ^ m))) :=
    tendsto_const_nhds
  have h :
      Filter.Tendsto
        (fun x : ℝ =>
          (c / (d * a ^ m)) *
            ((a * x) ^ m * Real.exp (-(a * x))))
        Filter.atTop (nhds 0) := by
    simpa using hconst.mul hbase
  refine h.congr' (Filter.Eventually.of_forall ?_)
  intro x
  rw [mul_pow, Real.exp_neg]
  field_simp [ha.ne', hd]

theorem gap1 (a : ℝ) (n : ℕ) (ha : 0 < a) (hn : 1 ≤ n) :
    HasLimitAtTop (fun x => x ^ n / Real.exp (a * x)) 0 ↔
      HasLimitAtTop (integerStage a n 1) 0 := by
  constructor
  · intro _
    change HasLimitAtTop
      (fun x =>
        ((Nat.factorial n : ℝ) / (Nat.factorial (n - 1) : ℝ)) *
          x ^ (n - 1) / (a ^ 1 * Real.exp (a * x))) 0
    exact
      monomialScaledExpLimit a
        ((Nat.factorial n : ℝ) / (Nat.factorial (n - 1) : ℝ))
        (a ^ 1) (n - 1) ha (pow_ne_zero _ ha.ne')
  · intro _
    simpa using
      (monomialScaledExpLimit a 1 1 n ha (one_ne_zero : (1 : ℝ) ≠ 0))

theorem gap2 (a : ℝ) (n : ℕ) (ha : 0 < a) (hn : 1 ≤ n) :
    ∀ j < n, HasLimitAtTop (integerStage a n j) 0 ↔
      HasLimitAtTop (integerStage a n (j + 1)) 0 := by
  intro j hj
  constructor
  · intro _
    simpa [integerStage] using
      (monomialScaledExpLimit a
        ((Nat.factorial n : ℝ) / (Nat.factorial (n - (j + 1)) : ℝ))
        (a ^ (j + 1)) (n - (j + 1)) ha (pow_ne_zero _ ha.ne'))
  · intro _
    simpa [integerStage] using
      (monomialScaledExpLimit a
        ((Nat.factorial n : ℝ) / (Nat.factorial (n - j) : ℝ))
        (a ^ j) (n - j) ha (pow_ne_zero _ ha.ne'))

theorem gap3 (a : ℝ) (n : ℕ) (ha : 0 < a) (hn : 1 ≤ n) :
    HasLimitAtTop (integerStage a n n) 0 ↔
      HasLimitAtTop
        (fun x => (Nat.factorial n : ℝ) / (a ^ n * Real.exp (a * x))) 0 := by
  constructor
  · intro _
    simpa using
      (monomialScaledExpLimit a (Nat.factorial n : ℝ) (a ^ n) 0 ha
        (pow_ne_zero _ ha.ne'))
  · intro _
    change HasLimitAtTop
      (fun x =>
        ((Nat.factorial n : ℝ) / (Nat.factorial (n - n) : ℝ)) *
          x ^ (n - n) / (a ^ n * Real.exp (a * x))) 0
    exact
      monomialScaledExpLimit a
        ((Nat.factorial n : ℝ) / (Nat.factorial (n - n) : ℝ))
        (a ^ n) (n - n) ha (pow_ne_zero _ ha.ne')

theorem gap4 (a : ℝ) (n : ℕ) (ha : 0 < a) :
    HasLimitAtTop
      (fun x => (Nat.factorial n : ℝ) / (a ^ n * Real.exp (a * x))) 0 := by
  simpa using
    (monomialScaledExpLimit a (Nat.factorial n : ℝ) (a ^ n) 0 ha
      (pow_ne_zero _ ha.ne'))

theorem gap5 (a : ℝ) (n : ℕ) (ha : 0 < a) :
    HasLimitAtTop (fun x => x ^ n / Real.exp (a * x)) 0 := by
  simpa using
    (monomialScaledExpLimit a 1 1 n ha (one_ne_zero : (1 : ℝ) ≠ 0))

theorem gap6 (n : ℝ) (hn : 0 < n) (hni : ¬ IsPositiveInteger n) :
    (⌊n⌋₊ : ℝ) < n := by
  have hle : (⌊n⌋₊ : ℝ) ≤ n := Nat.floor_le (le_of_lt hn)
  refine lt_of_le_of_ne hle ?_
  intro heq
  apply hni
  refine ⟨⌊n⌋₊, ?_, heq.symm⟩
  refine Nat.one_le_iff_ne_zero.mpr ?_
  intro hk
  have hn0 : n = 0 := by
    simpa [hk] using heq.symm
  exact (ne_of_gt hn) hn0

theorem gap7 (n : ℝ) (hn : 0 < n) (hni : ¬ IsPositiveInteger n) :
    n < (⌊n⌋₊ : ℝ) + 1 := by
  simpa using (Nat.lt_floor_add_one n)

theorem gap8 (n : ℝ) (hn : 0 < n) (hni : ¬ IsPositiveInteger n) :
    (⌊n⌋₊ : ℝ) < (⌊n⌋₊ : ℝ) + 1 := by
  simpa using
    (lt_add_of_pos_right (⌊n⌋₊ : ℝ) (zero_lt_one : (0 : ℝ) < 1))

theorem gap9 (a n x : ℝ) (ha : 0 < a) (hn : 0 < n)
    (hni : ¬ IsPositiveInteger n) (hx : 1 < x) :
    x ^ ⌊n⌋₊ / Real.exp (a * x) < quotient a n x := by
  have hx0 : 0 ≤ x := le_of_lt (lt_trans zero_lt_one hx)
  have hp :
      Real.rpow x (⌊n⌋₊ : ℝ) < Real.rpow x n :=
    (Real.strictMono_rpow_of_base_gt_one hx) (gap6 n hn hni)
  have hp' : x ^ ⌊n⌋₊ < Real.rpow x n := by
    simpa [Real.rpow_natCast, hx0] using hp
  unfold quotient
  exact (div_lt_div_iff_of_pos_right (Real.exp_pos (a * x))).2 hp'

theorem gap10 (a n x : ℝ) (ha : 0 < a) (hn : 0 < n)
    (hni : ¬ IsPositiveInteger n) (hx : 1 < x) :
    quotient a n x < x ^ (⌊n⌋₊ + 1) / Real.exp (a * x) := by
  have he : n < ((⌊n⌋₊ + 1 : ℕ) : ℝ) := by
    simpa using (gap7 n hn hni)
  have hp :
      Real.rpow x n < Real.rpow x ((⌊n⌋₊ + 1 : ℕ) : ℝ) :=
    (Real.strictMono_rpow_of_base_gt_one hx) he
  have hp' : Real.rpow x n < x ^ (⌊n⌋₊ + 1) := by
    rw [← Real.rpow_natCast]
    exact hp
  unfold quotient
  exact (div_lt_div_iff_of_pos_right (Real.exp_pos (a * x))).2 hp'

theorem gap11 (a n x : ℝ) (ha : 0 < a) (hn : 0 < n)
    (hni : ¬ IsPositiveInteger n) (hx : 1 < x) :
    x ^ ⌊n⌋₊ / Real.exp (a * x) <
      x ^ (⌊n⌋₊ + 1) / Real.exp (a * x) := by
  exact (gap9 a n x ha hn hni hx).trans (gap10 a n x ha hn hni hx)

theorem gap12 (a n : ℝ) (ha : 0 < a) (hn : 0 < n)
    (hni : ¬ IsPositiveInteger n) :
    HasLimitAtTop (fun x => x ^ ⌊n⌋₊ / Real.exp (a * x)) 0 := by
  simpa using (gap5 a ⌊n⌋₊ ha)

theorem gap13 (a n : ℝ) (ha : 0 < a) (hn : 0 < n)
    (hni : ¬ IsPositiveInteger n) :
    HasLimitAtTop (fun x => x ^ (⌊n⌋₊ + 1) / Real.exp (a * x)) 0 := by
  simpa using (gap5 a (⌊n⌋₊ + 1) ha)

theorem gap14 (a n : ℝ) (ha : 0 < a) (hn : 0 < n)
    (hni : ¬ IsPositiveInteger n) :
    HasLimitAtTop (quotient a n) 0 := by
  have hlo :
      ∀ᶠ x : ℝ in Filter.atTop,
        x ^ ⌊n⌋₊ / Real.exp (a * x) ≤ quotient a n x :=
    (Filter.eventually_gt_atTop (1 : ℝ)).mono fun x hx =>
      le_of_lt (gap9 a n x ha hn hni hx)
  have hup :
      ∀ᶠ x : ℝ in Filter.atTop,
        quotient a n x ≤ x ^ (⌊n⌋₊ + 1) / Real.exp (a * x) :=
    (Filter.eventually_gt_atTop (1 : ℝ)).mono fun x hx =>
      le_of_lt (gap10 a n x ha hn hni hx)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (gap12 a n ha hn hni) (gap13 a n ha hn hni) hlo hup

theorem gap15 (a n : ℝ) (ha : 0 < a) (hn : 0 < n) :
    HasLimitAtTop (quotient a n) 0 := by
  by_cases hni : IsPositiveInteger n
  · rcases hni with ⟨k, hk, rfl⟩
    have h := gap5 a k ha
    unfold quotient
    refine h.congr' ((Filter.eventually_ge_atTop (0 : ℝ)).mono ?_)
    intro x hx
    simp [Real.rpow_natCast, hx]
  · exact gap14 a n ha hn hni

end

end ProofGap.Exercise1337
