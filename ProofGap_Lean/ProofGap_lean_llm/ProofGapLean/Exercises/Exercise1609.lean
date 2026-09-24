import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1609

noncomputable section

def curve (x : ℝ) := Real.log x
def objective (x : ℝ) := (1 + x ^ 2) ^ 3 / x ^ 2
def powThreeHalves (u : ℝ) := u * Real.sqrt u
def curvatureRadius (x : ℝ) := powThreeHalves (1 + x ^ 2) / |x|
def optimizer : ℝ := 1 / Real.sqrt 2
def Optimal (x : ℝ) : Prop :=
  x ∈ Set.Ioi 0 ∧ ∀ x' ∈ Set.Ioi (0 : ℝ), objective x ≤ objective x'

private theorem sqrtTwoPosAux1609 : 0 < Real.sqrt 2 := by
  exact Real.sqrt_pos.2 (by norm_num)

private theorem sqrtTwoSqAux1609 : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by
  simpa using (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2))

private theorem optimizerPosAux1609 : 0 < optimizer := by
  unfold optimizer
  exact one_div_pos.mpr sqrtTwoPosAux1609

private theorem optimizerSqAux1609 : optimizer ^ 2 = (1 : ℝ) / 2 := by
  unfold optimizer
  rw [div_pow, sqrtTwoSqAux1609]
  norm_num

theorem gap1 (x : ℝ) (hx : 0 < x) :
    deriv curve x = 1 / x := by
  change deriv Real.log x = 1 / x
  simpa only [one_div] using (Real.hasDerivAt_log hx.ne').deriv
theorem gap2 (x : ℝ) (hx : 0 < x) :
    deriv (deriv curve) x = -(1 / x ^ 2) := by
  have heq : deriv curve =ᶠ[nhds x] (fun y : ℝ => 1 / y) :=
    (eventually_gt_nhds hx).mono (fun y hy => gap1 y hy)
  have hrecip :
      HasDerivAt (fun y : ℝ => 1 / y) (-(1 / x ^ 2)) x := by
    convert (hasDerivAt_const x (1 : ℝ)).div (hasDerivAt_id x) hx.ne' using 1 <;>
      simp only [id_eq] <;>
      field_simp [hx.ne'] <;>
      ring
  calc
    deriv (deriv curve) x = deriv (fun y : ℝ => 1 / y) x := heq.deriv_eq
    _ = -(1 / x ^ 2) := hrecip.deriv
theorem gap3 (x : ℝ) (hx : 0 < x) :
    curvatureRadius x = powThreeHalves (1 + x ^ 2) / |x| := by
  rfl
theorem gap4 (x : ℝ) (hx : 0 < x) :
    deriv objective x =
      2 * (1 + x ^ 2) ^ 2 * (2 * x ^ 2 - 1) / x ^ 3 := by
  have hden : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    convert (hasDerivAt_id x).pow 2 using 1 <;>
      simp [id_eq] <;>
      ring
  have hinner :
      HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * x) x := by
    convert (hasDerivAt_const x (1 : ℝ)).add hden using 1 <;>
      simp only [Pi.add_apply, zero_add]
  have hnum :
      HasDerivAt (fun y : ℝ => (1 + y ^ 2) ^ 3)
        (3 * (1 + x ^ 2) ^ 2 * (2 * x)) x := by
    simpa [Pi.pow_apply] using hinner.pow 3
  have hquot := hnum.div hden (pow_ne_zero 2 hx.ne')
  unfold objective
  convert hquot.deriv using 1
  field_simp [hx.ne']
  ring
theorem gap5 (x : ℝ) :
    deriv objective x = 0 ∧ 0 < x ↔ x = optimizer := by
  constructor
  · rintro ⟨hd, hx⟩
    rw [gap4 x hx] at hd
    rcases div_eq_zero_iff.mp hd with hnum | hden
    · have hbase : 0 < (1 + x ^ 2) ^ 2 := by positivity
      have hfactor : 2 * x ^ 2 - 1 = 0 := by
        rcases mul_eq_zero.mp hnum with hcoeff | hfactor
        · exact ((mul_ne_zero (by norm_num) (ne_of_gt hbase)) hcoeff).elim
        · exact hfactor
      have hprodSq : (x * Real.sqrt 2) ^ 2 = 1 := by
        calc
          (x * Real.sqrt 2) ^ 2 = x ^ 2 * (Real.sqrt 2) ^ 2 := by ring
          _ = 1 := by
            rw [sqrtTwoSqAux1609]
            nlinarith [hfactor]
      have hprod : x * Real.sqrt 2 = 1 := by
        nlinarith [hprodSq, mul_pos hx sqrtTwoPosAux1609]
      unfold optimizer
      exact (eq_div_iff (ne_of_gt sqrtTwoPosAux1609)).2 hprod
    · exact ((pow_ne_zero 3 hx.ne') hden).elim
  · rintro rfl
    constructor
    · rw [gap4 optimizer optimizerPosAux1609]
      have hfactor : 2 * optimizer ^ 2 - 1 = 0 := by
        nlinarith [optimizerSqAux1609]
      rw [hfactor]
      simp
    · exact optimizerPosAux1609
theorem gap6 (x : ℝ) (hx : x ∈ ({optimizer} : Set ℝ)) :
    deriv objective x = 0 ∧ 0 < x := by
  have hxeq : x = optimizer := by
    simpa only [Set.mem_singleton_iff] using hx
  exact (gap5 x).2 hxeq
theorem gap7 (x : ℝ) (hx : 0 < x) (hxo : x < optimizer) :
    deriv objective x < 0 := by
  have hsquares : x ^ 2 < optimizer ^ 2 := by
    have hp : 0 < (optimizer - x) * (optimizer + x) :=
      mul_pos (sub_pos.mpr hxo) (add_pos optimizerPosAux1609 hx)
    nlinarith [hp]
  have hfactor : 2 * x ^ 2 - 1 < 0 := by
    nlinarith [optimizerSqAux1609, hsquares]
  rw [gap4 x hx]
  have hcoeff : 0 < 2 * (1 + x ^ 2) ^ 2 := by positivity
  exact div_neg_of_neg_of_pos
    (mul_neg_of_pos_of_neg hcoeff hfactor) (pow_pos hx 3)
theorem gap8 (x : ℝ) (hxo : optimizer < x) :
    deriv objective x > 0 := by
  have hx : 0 < x := lt_trans optimizerPosAux1609 hxo
  have hsquares : optimizer ^ 2 < x ^ 2 := by
    have hp : 0 < (x - optimizer) * (x + optimizer) :=
      mul_pos (sub_pos.mpr hxo) (add_pos hx optimizerPosAux1609)
    nlinarith [hp]
  have hfactor : 0 < 2 * x ^ 2 - 1 := by
    nlinarith [optimizerSqAux1609, hsquares]
  rw [gap4 x hx]
  have hcoeff : 0 < 2 * (1 + x ^ 2) ^ 2 := by positivity
  exact div_pos (mul_pos hcoeff hfactor) (pow_pos hx 3)
theorem gap9 : Optimal optimizer := by
  refine ⟨optimizerPosAux1609, ?_⟩
  intro x hx
  have hxSq : 0 < x ^ 2 := pow_pos hx 2
  calc
    objective optimizer = (27 : ℝ) / 4 := by
      unfold objective
      rw [optimizerSqAux1609]
      norm_num
    _ ≤ objective x := by
      unfold objective
      apply (le_div_iff₀ hxSq).2
      have hid :
          4 * (1 + x ^ 2) ^ 3 - 27 * x ^ 2 =
            (2 * x ^ 2 - 1) ^ 2 * (x ^ 2 + 4) := by
        ring
      have hnonneg : 0 ≤ 4 * (1 + x ^ 2) ^ 3 - 27 * x ^ 2 := by
        rw [hid]
        exact mul_nonneg (sq_nonneg _) (by nlinarith [sq_nonneg x])
      nlinarith [hnonneg]
theorem gap10 : curve optimizer = -(Real.log 2 / 2) := by
  have hprod : Real.sqrt 2 * Real.sqrt 2 = (2 : ℝ) := by
    simpa [pow_two] using sqrtTwoSqAux1609
  have hlog := Real.log_mul
    (ne_of_gt sqrtTwoPosAux1609) (ne_of_gt sqrtTwoPosAux1609)
  rw [hprod] at hlog
  unfold curve optimizer
  rw [one_div, Real.log_inv]
  linarith [hlog]
theorem gap11 :
    (optimizer, curve optimizer) =
      (1 / Real.sqrt 2, -(Real.log 2 / 2)) ∧ Optimal optimizer := by
  constructor
  · apply Prod.ext
    · rfl
    · exact gap10
  · exact gap9

end
end ProofGap.Exercise1609
