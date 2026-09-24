import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise653_2

noncomputable section

def p (x : ℝ) : ℝ := Real.sqrt (1 + x) - Real.sqrt (1 - x)

/-- Source: `proof_gap/exercise_653_2/1.txt`; the algebraic identity requires `x≠0`. -/
private theorem p_div_eq_near_zero (x : ℝ) (hx : x ≠ 0)
    (hlo : -1 < x) (hhi : x < 1) :
    p x / x = 2 / (Real.sqrt (1 + x) + Real.sqrt (1 - x)) := by
  have hplus : 0 ≤ 1 + x := by linarith
  have hminus : 0 ≤ 1 - x := by linarith
  have hsplus : (Real.sqrt (1 + x)) ^ 2 = 1 + x :=
    Real.sq_sqrt hplus
  have hsminus : (Real.sqrt (1 - x)) ^ 2 = 1 - x :=
    Real.sq_sqrt hminus
  have ha0 : 0 ≤ Real.sqrt (1 + x) := Real.sqrt_nonneg _
  have hb0 : 0 ≤ Real.sqrt (1 - x) := Real.sqrt_nonneg _
  have hden : Real.sqrt (1 + x) + Real.sqrt (1 - x) ≠ 0 := by
    intro hzero
    nlinarith [hsplus, hsminus]
  unfold p
  field_simp [hx, hden]
  all_goals nlinarith [hsplus, hsminus]

theorem gap1 (x : ℝ) (hx : x ≠ 0) (hlo : -1 < x) (hhi : x < 1) :
    p x / x = 2 / (Real.sqrt (1 + x) + Real.sqrt (1 - x)) := by
  exact p_div_eq_near_zero x hx hlo hhi

/-- Source: `proof_gap/exercise_653_2/2.txt`. -/
theorem gap2 :
    Filter.Tendsto
      (fun x : ℝ => 2 / (Real.sqrt (1 + x) + Real.sqrt (1 - x)))
      (nhds 0) (nhds 1) := by
  have hplus : Continuous (fun x : ℝ => Real.sqrt (1 + x)) :=
    Real.continuous_sqrt.comp (continuous_const.add continuous_id)
  have hminus : Continuous (fun x : ℝ => Real.sqrt (1 - x)) :=
    Real.continuous_sqrt.comp (continuous_const.sub continuous_id)
  have hcont :
      ContinuousAt
        (fun x : ℝ => 2 / (Real.sqrt (1 + x) + Real.sqrt (1 - x))) 0 :=
    (continuousAt_const : ContinuousAt (fun _ : ℝ => (2 : ℝ)) 0).div
      (hplus.add hminus).continuousAt (by norm_num)
  change
    Filter.Tendsto
      (fun x : ℝ => 2 / (Real.sqrt (1 + x) + Real.sqrt (1 - x)))
      (nhds 0)
      (nhds
        (2 / (Real.sqrt (1 + (0 : ℝ)) + Real.sqrt (1 - (0 : ℝ)))))
    at hcont
  norm_num at hcont
  exact hcont

/-- Source: `proof_gap/exercise_653_2/3.txt`. -/
theorem gap3 :
    Filter.Tendsto (fun x : ℝ => p x / x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
  have hbase :
      Filter.Tendsto
        (fun x : ℝ => 2 / (Real.sqrt (1 + x) + Real.sqrt (1 - x)))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) :=
    gap2.mono_left
      (show nhdsWithin 0 ({0} : Set ℝ)ᶜ ≤ nhds 0 from inf_le_left)
  have hI : ∀ᶠ x : ℝ in nhds 0, x ∈ Set.Ioo (-1 : ℝ) 1 :=
    isOpen_Ioo.mem_nhds (by constructor <;> norm_num)
  have hI' :
      ∀ᶠ x : ℝ in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
        x ∈ Set.Ioo (-1 : ℝ) 1 :=
    hI.filter_mono
      (show nhdsWithin 0 ({0} : Set ℝ)ᶜ ≤ nhds 0 from inf_le_left)
  refine hbase.congr' ?_
  filter_upwards [hI', self_mem_nhdsWithin] with x hxI hxmem
  exact
    (p_div_eq_near_zero x (by simpa using hxmem) hxI.1 hxI.2).symm

/-- Source: `proof_gap/exercise_653_2/4.txt`. -/
theorem gap4 :
    Asymptotics.IsEquivalent (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
      p (fun x : ℝ => x) := by
  change
    (fun x : ℝ => p x - x) =o[nhdsWithin 0 ({0} : Set ℝ)ᶜ]
      (fun x : ℝ => x)
  have hone :
      Filter.Tendsto (fun _ : ℝ => (1 : ℝ))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) :=
    tendsto_const_nhds
  have ht :
      Filter.Tendsto (fun x : ℝ => p x / x - 1)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
    simpa using gap3.sub hone
  have hnorm :
      Filter.Tendsto (fun x : ℝ => ‖p x / x - 1‖)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
    simpa using ht.norm
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have hratio :
      ∀ᶠ x : ℝ in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
        ‖p x / x - 1‖ < c :=
    (tendsto_order.1 hnorm).2 c hc
  filter_upwards [hratio, self_mem_nhdsWithin] with x hxratio hxmem
  have hx0 : x ≠ 0 := by simpa using hxmem
  have hid : p x - x = (p x / x - 1) * x := by
    field_simp [hx0]
  rw [hid, norm_mul]
  exact mul_le_mul_of_nonneg_right (le_of_lt hxratio) (norm_nonneg x)

/-- Source: `proof_gap/exercise_653_2/5.txt`; unpack the singleton pair. -/
theorem gap5 (C : ℝ) (n : ℕ) (h : (C, n) = (1, 1)) :
    Asymptotics.IsEquivalent (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
      p (fun x => C * x ^ n) := by
  have hC : C = 1 := congrArg Prod.fst h
  have hn : n = 1 := congrArg Prod.snd h
  subst C
  subst n
  simpa using gap4

end

end ProofGap.Exercise653_2
