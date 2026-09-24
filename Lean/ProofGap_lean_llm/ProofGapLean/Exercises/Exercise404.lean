import ProofGapLean.Prelude.Core

namespace ProofGap.Exercise404

noncomputable section

def HasLimitAtInfinity (f : ℝ → ℝ) (b : ℝ) : Prop :=
  ∀ ε > 0, ∃ N > 0, ∀ x, N < |x| → |f x - b| < ε

def HasLimitAtNegInfinity (f : ℝ → ℝ) (b : ℝ) : Prop :=
  ∀ ε > 0, ∃ N > 0, ∀ x, x < -N → |f x - b| < ε

def HasLimitAtPosInfinity (f : ℝ → ℝ) (b : ℝ) : Prop :=
  ∀ ε > 0, ∃ N > 0, ∀ x, N < x → |f x - b| < ε

def g (x : ℝ) : ℝ := 1 / x

/-- Source: `proof_gap/exercise_404/1.txt`. -/
private theorem reciprocal_hasLimitAtInfinity : HasLimitAtInfinity g 0 := by
  intro ε hε
  refine ⟨1 / ε, one_div_pos.mpr hε, ?_⟩
  intro x hx
  have hxabs : 0 < |x| := lt_trans (one_div_pos.mpr hε) hx
  change |1 / x - 0| < ε
  rw [sub_zero, abs_div, abs_one]
  apply (div_lt_iff₀ hxabs).2
  have hprod : 1 < |x| * ε := (div_lt_iff₀ hε).1 hx
  simpa [mul_comm] using hprod

theorem gap1 : ∀ f : ℝ → ℝ, ∀ b,
    HasLimitAtInfinity f b ↔
      ∀ ε > 0, ∃ N > 0, ∀ x, N < |x| → |f x - b| < ε := by
  intro f b
  rfl

/-- Source: `proof_gap/exercise_404/2.txt`. -/
theorem gap2 : ∀ f : ℝ → ℝ, ∀ b,
    HasLimitAtNegInfinity f b ↔
      ∀ ε > 0, ∃ N > 0, ∀ x, x < -N → |f x - b| < ε := by
  intro f b
  rfl

/-- Source: `proof_gap/exercise_404/3.txt`. -/
theorem gap3 : ∀ f : ℝ → ℝ, ∀ b,
    HasLimitAtPosInfinity f b ↔
      ∀ ε > 0, ∃ N > 0, ∀ x, N < x → |f x - b| < ε := by
  intro f b
  rfl

/-- Source: `proof_gap/exercise_404/4.txt`; define the previously free example `g(x)=1/x`. -/
theorem gap4 :
    HasLimitAtNegInfinity g 0 ↔ HasLimitAtPosInfinity g 0 := by
  have hall : HasLimitAtInfinity g 0 := reciprocal_hasLimitAtInfinity
  constructor
  · intro _
    intro ε hε
    rcases hall ε hε with ⟨N, hN, hlim⟩
    refine ⟨N, hN, ?_⟩
    intro x hx
    apply hlim x
    have hxpos : 0 < x := lt_trans hN hx
    simpa [abs_of_pos hxpos] using hx
  · intro _
    intro ε hε
    rcases hall ε hε with ⟨N, hN, hlim⟩
    refine ⟨N, hN, ?_⟩
    intro x hx
    apply hlim x
    have hxneg : x < 0 := lt_trans hx (neg_lt_zero.mpr hN)
    rw [abs_of_neg hxneg]
    simpa using (neg_lt_neg hx)

/-- Source: `proof_gap/exercise_404/5.txt`; define the previously free example `g(x)=1/x`. -/
theorem gap5 :
    HasLimitAtPosInfinity g 0 ↔ HasLimitAtInfinity g 0 := by
  constructor
  · intro _
    exact reciprocal_hasLimitAtInfinity
  · intro hall
    intro ε hε
    rcases hall ε hε with ⟨N, hN, hlim⟩
    refine ⟨N, hN, ?_⟩
    intro x hx
    apply hlim x
    have hxpos : 0 < x := lt_trans hN hx
    simpa [abs_of_pos hxpos] using hx

/-- Source: `proof_gap/exercise_404/6.txt`; define the previously free example `g(x)=1/x`. -/
theorem gap6 : HasLimitAtInfinity g 0 := by
  exact reciprocal_hasLimitAtInfinity

/-- Source: `proof_gap/exercise_404/7.txt`; define the previously free example `g(x)=1/x`. -/
theorem gap7 : HasLimitAtNegInfinity g 0 := by
  intro ε hε
  rcases reciprocal_hasLimitAtInfinity ε hε with ⟨N, hN, hlim⟩
  refine ⟨N, hN, ?_⟩
  intro x hx
  apply hlim x
  have hxneg : x < 0 := lt_trans hx (neg_lt_zero.mpr hN)
  rw [abs_of_neg hxneg]
  simpa using (neg_lt_neg hx)

end

end ProofGap.Exercise404
