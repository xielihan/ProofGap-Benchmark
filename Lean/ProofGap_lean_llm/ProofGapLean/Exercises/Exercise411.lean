import ProofGapLean.Prelude.Sequences
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise411

noncomputable section

def f (x : ℝ) : ℝ := (x ^ 2 - 1) / (2 * x ^ 2 - x - 1)
def factored (x : ℝ) : ℝ :=
  ((x - 1) * (x + 1)) / ((2 * x + 1) * (x - 1))
def cancelled (x : ℝ) : ℝ := (x + 1) / (2 * x + 1)
def normalized (x : ℝ) : ℝ :=
  (1 - 1 / x ^ 2) / (2 - 1 / x - 1 / x ^ 2)

def HasLimitAt (g : ℝ → ℝ) (a L : ℝ) : Prop :=
  Filter.Tendsto g (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds L)
def HasLimitAtInfinity (g : ℝ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ N > 0, ∀ x, N < |x| → |g x - L| < ε

/-- Source: `proof_gap/exercise_411/1.txt`. -/
private theorem f_hasLimitAtInfinity_half :
    HasLimitAtInfinity f (1 / 2) := by
  unfold HasLimitAtInfinity
  intro ε hε
  have hinv : 0 < (1 / ε : ℝ) := one_div_pos.mpr hε
  refine ⟨1 / ε + 2, by linarith, ?_⟩
  intro x hx
  have habs : 1 < |x| := by
    linarith
  have hx1 : x ≠ 1 := by
    intro h
    subst x
    norm_num at habs
  have hxsub : x - 1 ≠ 0 := sub_ne_zero.mpr hx1
  have hxden : 2 * x + 1 ≠ 0 := by
    intro h
    have hxval : x = -(1 / 2 : ℝ) := by
      linarith
    rw [hxval] at habs
    norm_num at habs
  have hfactor : 2 * x ^ 2 - x - 1 = (2 * x + 1) * (x - 1) := by
    ring
  have hnum : x ^ 2 - 1 = (x + 1) * (x - 1) := by
    ring
  have hcancel : f x = cancelled x := by
    unfold f cancelled
    rw [hnum, hfactor]
    exact mul_div_mul_right (x + 1) (2 * x + 1) hxsub
  have hxden' : 1 + x * 2 ≠ 0 := by
    intro h
    apply hxden
    linarith
  have hinvcancel :
      (1 + x * 2) * (1 + x * 2)⁻¹ = (1 : ℝ) :=
    mul_inv_cancel₀ hxden'
  have hdiff : f x - 1 / 2 = 1 / (2 * (2 * x + 1)) := by
    rw [hcancel]
    unfold cancelled
    field_simp [hxden, hxden']
    ring_nf at hinvcancel ⊢
    linarith
  have hqbound : 1 / ε < 2 * |2 * x + 1| := by
    rcases le_total 0 x with hxpos | hxneg
    · have hxp : 1 / ε + 2 < x := by
        simpa [abs_of_nonneg hxpos] using hx
      rw [abs_of_nonneg (by linarith : 0 ≤ 2 * x + 1)]
      linarith
    · have hxn : 1 / ε + 2 < -x := by
        simpa [abs_of_nonpos hxneg] using hx
      have hlinear : 2 * x + 1 ≤ 0 := by
        linarith
      rw [abs_of_nonpos hlinear]
      linarith
  have hqpos : 0 < 2 * |2 * x + 1| := lt_trans hinv hqbound
  have hprod : 1 < ε * (2 * |2 * x + 1|) := by
    have h' : 1 < (2 * |2 * x + 1|) * ε :=
      (div_lt_iff₀ hε).mp hqbound
    simpa [mul_comm] using h'
  have hrecip : 1 / (2 * |2 * x + 1|) < ε :=
    (div_lt_iff₀ hqpos).2 hprod
  rw [hdiff, abs_div, abs_one, abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact hrecip

theorem gap1 : HasLimitAt f 0 ((-1) / (-1)) := by
  unfold HasLimitAt
  have hc : ContinuousAt f 0 := by
    unfold f
    exact ((continuousAt_id.pow 2).sub continuousAt_const).div
      (((continuousAt_const.mul (continuousAt_id.pow 2)).sub
        continuousAt_id).sub continuousAt_const) (by norm_num)
  simpa [f] using hc.tendsto.mono_left inf_le_left

/-- Source: `proof_gap/exercise_411/2.txt`. -/
theorem gap2 : ((-1 : ℝ) / (-1)) = 1 := by
  norm_num

/-- Source: `proof_gap/exercise_411/3.txt`. -/
theorem gap3 : HasLimitAt f 0 1 := by
  simpa using gap1

/-- Source: `proof_gap/exercise_411/4.txt`. -/
theorem gap4 : HasLimitAt f 1 (2 / 3) ↔ HasLimitAt factored 1 (2 / 3) := by
  have h : f = factored := by
    funext x
    unfold f factored
    congr 1 <;> ring
  rw [h]

/-- Source: `proof_gap/exercise_411/5.txt`. -/
theorem gap5 : HasLimitAt factored 1 (2 / 3) ↔
    HasLimitAt cancelled 1 (2 / 3) := by
  have heq : factored =ᶠ[nhdsWithin 1 ({1} : Set ℝ)ᶜ] cancelled := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx1 : x ≠ 1 := by
      simpa using hx
    have hxsub : x - 1 ≠ 0 := sub_ne_zero.mpr hx1
    unfold factored cancelled
    rw [mul_comm (x - 1) (x + 1)]
    exact mul_div_mul_right (x + 1) (2 * x + 1) hxsub
  change
    Filter.map factored (nhdsWithin 1 ({1} : Set ℝ)ᶜ) ≤ nhds (2 / 3 : ℝ) ↔
      Filter.map cancelled (nhdsWithin 1 ({1} : Set ℝ)ᶜ) ≤ nhds (2 / 3 : ℝ)
  rw [Filter.map_congr heq]

/-- Source: `proof_gap/exercise_411/6.txt`. -/
theorem gap6 : HasLimitAt cancelled 1 (2 / 3) := by
  unfold HasLimitAt
  have hc : ContinuousAt cancelled 1 := by
    unfold cancelled
    exact (continuousAt_id.add continuousAt_const).div
      ((continuousAt_const.mul continuousAt_id).add continuousAt_const)
      (by norm_num)
  have hsub : nhdsWithin (1 : ℝ) ({1} : Set ℝ)ᶜ ≤ nhds (1 : ℝ) :=
    inf_le_left
  have ht : Filter.Tendsto cancelled
      (nhdsWithin (1 : ℝ) ({1} : Set ℝ)ᶜ) (nhds (cancelled 1)) :=
    hc.tendsto.mono_left hsub
  convert ht using 1 <;> norm_num [cancelled]

/-- Source: `proof_gap/exercise_411/7.txt`. -/
theorem gap7 : HasLimitAt f 1 (2 / 3) := by
  exact gap4.mpr (gap5.mpr gap6)

/-- Source: `proof_gap/exercise_411/8.txt`. -/
theorem gap8 : HasLimitAtInfinity f (1 / 2) ↔
    HasLimitAtInfinity normalized (1 / 2) := by
  have heq : ∀ x : ℝ, x ≠ 0 → f x = normalized x := by
    intro x hx0
    have hn : 1 - 1 / x ^ 2 = (x ^ 2 - 1) / x ^ 2 := by
      field_simp [hx0] <;> ring
    have hd : 2 - 1 / x - 1 / x ^ 2 =
        (2 * x ^ 2 - x - 1) / x ^ 2 := by
      field_simp [hx0] <;> ring
    unfold f normalized
    rw [hn, hd]
    by_cases hD : 2 * x ^ 2 - x - 1 = 0
    · simp [hD]
    · field_simp [hx0, hD]
  unfold HasLimitAtInfinity
  constructor
  · intro h ε hε
    obtain ⟨N, hN, hbound⟩ := h ε hε
    refine ⟨N, hN, ?_⟩
    intro x hx
    have hx0 : x ≠ 0 := by
      intro hzero
      subst x
      have : (0 : ℝ) < |(0 : ℝ)| := lt_trans hN hx
      norm_num at this
    simpa [heq x hx0] using hbound x hx
  · intro h ε hε
    obtain ⟨N, hN, hbound⟩ := h ε hε
    refine ⟨N, hN, ?_⟩
    intro x hx
    have hx0 : x ≠ 0 := by
      intro hzero
      subst x
      have : (0 : ℝ) < |(0 : ℝ)| := lt_trans hN hx
      norm_num at this
    simpa [← heq x hx0] using hbound x hx

/-- Source: `proof_gap/exercise_411/9.txt`. -/
theorem gap9 : HasLimitAtInfinity normalized (1 / 2) := by
  exact gap8.mp f_hasLimitAtInfinity_half

/-- Source: `proof_gap/exercise_411/10.txt`. -/
theorem gap10 : HasLimitAtInfinity f (1 / 2) := by
  exact f_hasLimitAtInfinity_half

end

end ProofGap.Exercise411
