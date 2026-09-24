import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise203

noncomputable section

def targetDomain : Set ℝ := Set.Ioo 0 1
def sinDomain : Set ℝ := {x | Real.sin x ∈ targetDomain}
def logDomain : Set ℝ := {x | 0 < x ∧ Real.log x ∈ targetDomain}
def floorRatio (x : ℝ) : ℝ := (⌊x⌋ : ℤ) / x
def floorRatioDomain : Set ℝ := {x | floorRatio x ∈ targetDomain}

/-- Source: `proof_gap/exercise_203/1.txt`; positivity is a composite-domain condition. -/
theorem gap1 : ∀ x : ℝ, x ∈ sinDomain → 0 < Real.sin x := by
  intro x hx
  exact hx.1

/-- Source: `proof_gap/exercise_203/2.txt`. -/
theorem gap2 : ∀ x : ℝ, x ∈ sinDomain → Real.sin x < 1 := by
  intro x hx
  exact hx.2

/-- Source: `proof_gap/exercise_203/3.txt`. -/
theorem gap3 : (0 : ℝ) < 1 := by
  norm_num

private theorem sin_pos_iff_exists_int_interval (x : ℝ) :
    0 < Real.sin x ↔ ∃ k : ℤ,
      2 * (k : ℝ) * Real.pi < x ∧
        x < Real.pi + 2 * (k : ℝ) * Real.pi := by
  constructor
  · intro hsin
    let k : ℤ := ⌊x / (2 * Real.pi)⌋
    have hden : 0 < 2 * Real.pi := by positivity
    have hk_le : (k : ℝ) ≤ x / (2 * Real.pi) := Int.floor_le _
    have hk_lt : x / (2 * Real.pi) < (k : ℝ) + 1 :=
      Int.lt_floor_add_one _
    have hleft : (k : ℝ) * (2 * Real.pi) ≤ x :=
      (le_div_iff₀ hden).mp hk_le
    have hright : x < ((k : ℝ) + 1) * (2 * Real.pi) :=
      (div_lt_iff₀ hden).mp hk_lt
    let r : ℝ := x - (k : ℝ) * (2 * Real.pi)
    have hr_nonneg : 0 ≤ r := by
      dsimp [r]
      linarith
    have hr_two_pi : r < 2 * Real.pi := by
      dsimp [r]
      nlinarith [Real.pi_pos]
    have hperiod : Real.sin r = Real.sin x := by
      dsimp [r]
      exact Real.sin_sub_int_mul_two_pi x k
    have hsinr : 0 < Real.sin r := by
      rw [hperiod]
      exact hsin
    have hr_pos : 0 < r := by
      apply lt_of_le_of_ne hr_nonneg
      intro hr
      have hx_eq : x = (k : ℝ) * (2 * Real.pi) := by
        dsimp [r] at hr
        linarith
      have hzero : Real.sin x = 0 := by
        rw [hx_eq]
        simpa using Real.sin_int_mul_two_pi_sub 0 k
      linarith
    have hr_pi : r < Real.pi := by
      by_contra hnot
      have hpi_le : Real.pi ≤ r := le_of_not_gt hnot
      have hr_ne_pi : r ≠ Real.pi := by
        intro hr
        have hzero : Real.sin r = 0 := by
          rw [hr]
          exact Real.sin_pi
        linarith
      have hpi_lt : Real.pi < r :=
        lt_of_le_of_ne hpi_le (Ne.symm hr_ne_pi)
      have hsneg :
          Real.sin (r - (1 : ℤ) * (2 * Real.pi)) < 0 :=
        Real.sin_neg_of_neg_of_neg_pi_lt
          (by norm_num; linarith)
          (by norm_num; linarith)
      have hsperiod :
          Real.sin (r - (1 : ℤ) * (2 * Real.pi)) =
            Real.sin r :=
        Real.sin_sub_int_mul_two_pi r 1
      rw [hsperiod] at hsneg
      linarith
    refine ⟨k, ?_, ?_⟩
    · dsimp [r] at hr_pos
      nlinarith
    · dsimp [r] at hr_pi
      nlinarith
  · rintro ⟨k, hleft, hright⟩
    have hrpos :
        0 < x - (k : ℝ) * (2 * Real.pi) := by
      nlinarith
    have hrpi :
        x - (k : ℝ) * (2 * Real.pi) < Real.pi := by
      nlinarith
    have hsin := Real.sin_pos_of_pos_of_lt_pi hrpos hrpi
    calc
      0 < Real.sin (x - (k : ℝ) * (2 * Real.pi)) := hsin
      _ = Real.sin x := Real.sin_sub_int_mul_two_pi x k

/-- Source: `proof_gap/exercise_203/4.txt`; k is existential for each x, not outside the set equality. -/
theorem gap4 :
    sinDomain =
      {x : ℝ | ∃ k : ℤ,
        2 * (k : ℝ) * Real.pi < x ∧
        x < Real.pi + 2 * (k : ℝ) * Real.pi ∧
        x ≠ ((4 * (k : ℝ) + 1) / 2) * Real.pi} := by
  apply Set.ext
  intro x
  simp only [sinDomain, targetDomain, Set.mem_setOf_eq, Set.mem_Ioo]
  constructor
  · rintro ⟨hspos, hslt⟩
    rcases (sin_pos_iff_exists_int_interval x).mp hspos with
      ⟨k, hleft, hright⟩
    refine ⟨k, hleft, hright, ?_⟩
    intro hx
    have harg :
        Real.pi / 2 + (k : ℝ) * (2 * Real.pi) = x := by
      rw [hx]
      ring
    have hsone : Real.sin x = 1 :=
      Real.sin_eq_one_iff.mpr ⟨k, harg⟩
    linarith
  · rintro ⟨k, hleft, hright, hne⟩
    have hspos : 0 < Real.sin x :=
      (sin_pos_iff_exists_int_interval x).mpr ⟨k, hleft, hright⟩
    refine ⟨hspos, lt_of_le_of_ne (Real.sin_le_one x) ?_⟩
    intro hsone
    rcases Real.sin_eq_one_iff.mp hsone with ⟨j, hj⟩
    have hkjR : (k : ℝ) < (j : ℝ) + 1 := by
      nlinarith [Real.pi_pos]
    have hjkR : (j : ℝ) < (k : ℝ) + 1 := by
      nlinarith [Real.pi_pos]
    have hkj : k < j + 1 := by exact_mod_cast hkjR
    have hjk : j < k + 1 := by exact_mod_cast hjkR
    have hjk_eq : j = k := by omega
    apply hne
    calc
      x = Real.pi / 2 + (j : ℝ) * (2 * Real.pi) := hj.symm
      _ = ((4 * (k : ℝ) + 1) / 2) * Real.pi := by
        rw [hjk_eq]
        ring

/-- Source: `proof_gap/exercise_203/5.txt`; positivity is conditional. -/
theorem gap5 : ∀ x : ℝ, x ∈ logDomain → 0 < Real.log x := by
  intro x hx
  exact hx.2.1

/-- Source: `proof_gap/exercise_203/6.txt`. -/
theorem gap6 : ∀ x : ℝ, x ∈ logDomain → Real.log x < 1 := by
  intro x hx
  exact hx.2.2

/-- Source: `proof_gap/exercise_203/7.txt`. -/
theorem gap7 : (0 : ℝ) < 1 := by
  norm_num

/-- Source: `proof_gap/exercise_203/8.txt`. -/
theorem gap8 : logDomain = Set.Ioo 1 (Real.exp 1) := by
  ext x
  constructor
  · rintro ⟨hxpos, hlogpos, hloglt⟩
    exact ⟨(Real.log_pos_iff hxpos.le).1 hlogpos,
      (Real.log_lt_iff_lt_exp hxpos).1 hloglt⟩
  · rintro ⟨hxone, hxexp⟩
    have hxpos : 0 < x := lt_trans (by norm_num) hxone
    exact ⟨hxpos, (Real.log_pos_iff hxpos.le).2 hxone,
      (Real.log_lt_iff_lt_exp hxpos).2 hxexp⟩

/-- Source: `proof_gap/exercise_203/9.txt`; positivity is conditional. -/
theorem gap9 : ∀ x : ℝ, x ∈ floorRatioDomain → 0 < floorRatio x := by
  intro x hx
  exact hx.1

/-- Source: `proof_gap/exercise_203/10.txt`. -/
theorem gap10 : ∀ x : ℝ, x ∈ floorRatioDomain → floorRatio x < 1 := by
  intro x hx
  exact hx.2

/-- Source: `proof_gap/exercise_203/11.txt`. -/
theorem gap11 : (0 : ℝ) < 1 := by
  norm_num

/-- Source: `proof_gap/exercise_203/12.txt`; express nonintegrality without a mismatched natural-number set. -/
theorem gap12 :
    floorRatioDomain = {x : ℝ | 1 < x ∧ x ≠ (⌊x⌋ : ℤ)} := by
  apply Set.ext
  intro x
  simp only [floorRatioDomain, floorRatio, targetDomain,
    Set.mem_setOf_eq, Set.mem_Ioo]
  let z : ℝ := (⌊x⌋ : ℤ)
  have hzle : z ≤ x := Int.floor_le x
  have hxlt : x < z + 1 := Int.lt_floor_add_one x
  constructor
  · rintro ⟨hpos, hlt⟩
    rcases div_pos_iff.mp hpos with ⟨hzpos, hxpos⟩ | ⟨hzneg, hxneg⟩
    · have hzlt : z < x := (div_lt_one hxpos).mp hlt
      have hzi : (1 : ℤ) ≤ ⌊x⌋ := by
        exact_mod_cast hzpos
      have hzone : 1 ≤ z := by
        change (1 : ℝ) ≤ ((⌊x⌋ : ℤ) : ℝ)
        exact_mod_cast hzi
      exact ⟨lt_of_le_of_lt hzone hzlt, by
        change x ≠ z
        exact ne_of_gt hzlt⟩
    · have hxltz : x < z := (div_lt_one_of_neg hxneg).mp hlt
      linarith
  · rintro ⟨hxone, hxne⟩
    have hxpos : 0 < x := by linarith
    have hzlt : z < x := lt_of_le_of_ne hzle (Ne.symm hxne)
    have hzpos : 0 < z := by linarith
    exact ⟨div_pos hzpos hxpos, (div_lt_one hxpos).mpr hzlt⟩

end

end ProofGap.Exercise203
