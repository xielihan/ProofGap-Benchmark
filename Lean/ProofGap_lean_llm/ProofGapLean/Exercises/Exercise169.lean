import ProofGapLean.Prelude.Elementary
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise169

noncomputable section

def lg (x : ℝ) : ℝ := Real.log x / Real.log 10
def arg (x : ℝ) : ℝ := lg (x / 10)
def domain : Set ℝ := {x | 0 < x ∧ -1 ≤ arg x ∧ arg x ≤ 1}
def y (x : ℝ) : ℝ := Real.arcsin (arg x)
def valueSet : Set ℝ := {t | ∃ x ∈ domain, t = y x}

/-- Source: `proof_gap/exercise_169/1.txt`. -/
theorem gap1 : ∀ x : ℝ, x ∈ domain → 1 / 10 ≤ x / 10 := by
  intro x hx
  have hxdivpos : 0 < x / 10 := by
    have := hx.1
    positivity
  have hlog10 : 0 < Real.log 10 := Real.log_pos (by norm_num)
  have hlog :
      Real.log (1 / 10 : ℝ) ≤ Real.log (x / 10) := by
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one]
    have hmul := (le_div_iff₀ hlog10).1 hx.2.1
    linarith
  exact (Real.log_le_log_iff (by norm_num) hxdivpos).1 hlog

/-- Source: `proof_gap/exercise_169/2.txt`. -/
theorem gap2 : ∀ x : ℝ, x ∈ domain → x / 10 ≤ 10 := by
  intro x hx
  by_cases hz : x / 10 ≤ 0
  · linarith
  · have hzpos : 0 < x / 10 := lt_of_not_ge hz
    have hlog10 : 0 < Real.log 10 := Real.log_pos (by norm_num)
    have hlog : Real.log (x / 10) ≤ Real.log 10 := by
      have h := hx.2.2
      unfold arg lg at h
      have hmul := (div_le_iff₀ hlog10).1 h
      simpa only [one_mul] using hmul
    exact (Real.log_le_log_iff hzpos (by norm_num)).1 hlog

/-- Source: `proof_gap/exercise_169/3.txt`. -/
theorem gap3 : (1 / 10 : ℝ) ≤ 10 := by
  norm_num

/-- Source: `proof_gap/exercise_169/4.txt`. -/
theorem gap4 : ∀ x : ℝ, x ∈ domain → 1 ≤ x := by
  intro x hx
  linarith [gap1 x hx]

/-- Source: `proof_gap/exercise_169/5.txt`. -/
theorem gap5 : ∀ x : ℝ, x ∈ domain → x ≤ 100 := by
  intro x hx
  have h := gap2 x hx
  linarith

/-- Source: `proof_gap/exercise_169/6.txt`. -/
theorem gap6 : (1 : ℝ) ≤ 100 := by
  norm_num

/-- Source: `proof_gap/exercise_169/7.txt`. -/
theorem gap7 : ∀ x : ℝ, 0 < x → -1 ≤ arg x → arg x ≤ 1 → x ∈ domain := by
  intro x hxpos hxlo hxhi
  exact ⟨hxpos, hxlo, hxhi⟩

/-- Source: `proof_gap/exercise_169/8.txt`. -/
theorem gap8 : domain = Set.Icc 1 100 := by
  ext x
  constructor
  · intro hx
    exact ⟨gap4 x hx, gap5 x hx⟩
  · rintro ⟨hxlo, hxhi⟩
    have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hxlo
    have hxdivpos : 0 < x / 10 := by positivity
    have hlog10 : 0 < Real.log 10 := Real.log_pos (by norm_num)
    have hdivlo : (1 / 10 : ℝ) ≤ x / 10 := by linarith
    have hdivhi : x / 10 ≤ (10 : ℝ) := by linarith
    have hloglo :
        Real.log (1 / 10 : ℝ) ≤ Real.log (x / 10) :=
      (Real.log_le_log_iff (by norm_num) hxdivpos).2 hdivlo
    have hloghi : Real.log (x / 10) ≤ Real.log 10 :=
      (Real.log_le_log_iff hxdivpos (by norm_num)).2 hdivhi
    apply gap7 x hxpos
    · unfold arg lg
      rw [le_div_iff₀ hlog10]
      rw [Real.log_div (by norm_num) (by norm_num), Real.log_one] at hloglo
      linarith
    · unfold arg lg
      rw [div_le_iff₀ hlog10]
      simpa only [one_mul] using hloghi

/-- Source: `proof_gap/exercise_169/9.txt`; remove the shadowed existential y. -/
theorem gap9 : valueSet = Set.Icc (-Real.pi / 2) (Real.pi / 2) := by
  ext t
  constructor
  · rintro ⟨x, hxdom, rfl⟩
    unfold y
    constructor
    · linarith [Real.neg_pi_div_two_le_arcsin (arg x)]
    · exact Real.arcsin_le_pi_div_two _
  · rintro ⟨htlo, hthi⟩
    let x : ℝ := 10 * Real.rpow 10 (Real.sin t)
    have hxdiv : x / 10 = Real.rpow 10 (Real.sin t) := by
      dsimp [x]
      ring
    have harg : arg x = Real.sin t := by
      unfold arg lg
      rw [hxdiv]
      change Real.log ((10 : ℝ) ^ Real.sin t) / Real.log 10 = Real.sin t
      rw [Real.log_rpow (by norm_num : (0 : ℝ) < 10)]
      have hlog10 : Real.log 10 ≠ 0 :=
        ne_of_gt (Real.log_pos (by norm_num))
      field_simp [hlog10]
    have hxdom : x ∈ domain := by
      exact gap7 x (by dsimp [x]; positivity)
        (by rw [harg]; exact Real.neg_one_le_sin t)
        (by rw [harg]; exact Real.sin_le_one t)
    refine ⟨x, hxdom, ?_⟩
    unfold y
    rw [harg]
    have htlo' : -(Real.pi / 2) ≤ t := by linarith
    exact (Real.arcsin_sin htlo' hthi).symm

end

end ProofGap.Exercise169
