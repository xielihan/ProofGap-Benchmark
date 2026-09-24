import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise543

noncomputable section

def powSelf (x : ℝ) : ℝ := Real.rpow x x
def original (a x : ℝ) : ℝ := (powSelf x - powSelf a) / (x - a)
def expFactor (a x : ℝ) : ℝ :=
  powSelf a *
    ((Real.exp (x * Real.log x - a * Real.log a) - 1) /
      (x * Real.log x - a * Real.log a)) *
    ((x * Real.log x - a * Real.log a) / (x - a))
def logQuotient (a x : ℝ) : ℝ :=
  (x * Real.log x - a * Real.log a) / (x - a)
def splitLog (a x : ℝ) : ℝ :=
  (x * Real.log x - x * Real.log a) / (x - a) + Real.log a
def normalized (a x : ℝ) : ℝ :=
  (x / a) * (Real.log (1 + (x - a) / a) / ((x - a) / a)) + Real.log a
def expQuotient (a x : ℝ) : ℝ :=
  (Real.exp (x * Real.log x - a * Real.log a) - 1) /
    (x * Real.log x - a * Real.log a)
def HasLimitAt (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds L)

/-- Source: `proof_gap/exercise_543/1.txt`; restrict logarithms and denominators to their domain. -/
private theorem tendsto_id_from_punctured (a : ℝ) :
    Filter.Tendsto (fun x : ℝ => x)
      (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds a) := by
  exact
    (continuousAt_id : ContinuousAt (fun x : ℝ => x) a).mono_left inf_le_left

theorem gap1 (a x : ℝ) (ha : 0 < a) (hx : 0 < x) (hxa : x ≠ a) :
    original a x = expFactor a x := by
  have hpowx : powSelf x = Real.exp (x * Real.log x) := by
    simp [powSelf, Real.rpow_def_of_pos hx, mul_comm]
  have hpowa : powSelf a = Real.exp (a * Real.log a) := by
    simp [powSelf, Real.rpow_def_of_pos ha, mul_comm]
  by_cases hd : x * Real.log x - a * Real.log a = 0
  · have hp : powSelf x = powSelf a := by
      rw [hpowx, hpowa, sub_eq_zero.mp hd]
    simp [original, expFactor, hp, hd]
  · have hexp :
        Real.exp (x * Real.log x) =
          Real.exp (a * Real.log a) *
            Real.exp (x * Real.log x - a * Real.log a) := by
      calc
        Real.exp (x * Real.log x) =
            Real.exp (a * Real.log a +
              (x * Real.log x - a * Real.log a)) := by
                congr 1
                ring
        _ = Real.exp (a * Real.log a) *
              Real.exp (x * Real.log x - a * Real.log a) :=
                Real.exp_add _ _
    unfold original expFactor
    rw [hpowx, hpowa, hexp]
    field_simp [hd, sub_ne_zero.mpr hxa]

/-- Source: `proof_gap/exercise_543/2.txt`; replace the malformed premise `x→a` by a pointwise punctured-domain identity. -/
theorem gap2 (a x : ℝ) (ha : 0 < a) (hx : 0 < x) (hxa : x ≠ a) :
    logQuotient a x = splitLog a x := by
  unfold logQuotient splitLog
  field_simp [sub_ne_zero.mpr hxa]
  ring

/-- Source: `proof_gap/exercise_543/3.txt`; make the punctured-domain identity explicit. -/
theorem gap3 (a x : ℝ) (ha : 0 < a) (hx : 0 < x) (hxa : x ≠ a) :
    splitLog a x = normalized a x := by
  have harg : 1 + (x - a) / a = x / a := by
    field_simp [ha.ne']
    ring
  unfold splitLog normalized
  rw [harg, Real.log_div hx.ne' ha.ne']
  field_simp [ha.ne', sub_ne_zero.mpr hxa]

/-- Source: `proof_gap/exercise_543/4.txt`; remove the shadowing outer quantifier. -/
theorem gap4 (a : ℝ) (ha : 0 < a) :
    HasLimitAt (normalized a) a (1 + Real.log a) := by
  have hid := tendsto_id_from_punctured a
  have hy :
      Filter.Tendsto (fun x : ℝ => x / a)
        (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds 1) := by
    convert hid.div_const a using 1
    simp [ha.ne']
  have hyne :
      ∀ᶠ x in nhdsWithin a ({a} : Set ℝ)ᶜ, x / a ≠ 1 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx
    intro h
    apply hx
    exact (div_eq_one_iff_eq ha.ne').mp h
  have hypunct :
      Filter.Tendsto (fun x : ℝ => x / a)
        (nhdsWithin a ({a} : Set ℝ)ᶜ)
        (nhdsWithin 1 ({1} : Set ℝ)ᶜ) := by
    refine tendsto_nhdsWithin_iff.2 ⟨hy, ?_⟩
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hyne
  have hslope :=
    (Real.hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto_slope
  change
    Filter.Tendsto
      (fun y : ℝ => (y - 1)⁻¹ • (Real.log y - Real.log 1))
      (nhdsWithin 1 ({1} : Set ℝ)ᶜ) (nhds ((1 : ℝ)⁻¹)) at hslope
  have harg (x : ℝ) : 1 + (x - a) / a = x / a := by
    field_simp [ha.ne']
    ring
  have hden (x : ℝ) : (x - a) / a = x / a - 1 := by
    field_simp [ha.ne']
  have hconst :
      Filter.Tendsto (fun _ : ℝ => Real.log a)
        (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds (Real.log a)) :=
    tendsto_const_nhds
  have hlim :
      Filter.Tendsto
        (fun x : ℝ =>
          (x / a) * (Real.log (x / a) / (x / a - 1)) + Real.log a)
        (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds (1 + Real.log a)) := by
    simpa [Real.log_one, div_eq_mul_inv, mul_comm] using
      (hy.mul (hslope.comp hypunct)).add hconst
  unfold HasLimitAt
  refine hlim.congr' (Filter.Eventually.of_forall (fun x => ?_))
  unfold normalized
  rw [harg x, hden x]

/-- Source: `proof_gap/exercise_543/5.txt`; remove the malformed `x→a` premise. -/
theorem gap5 (a : ℝ) (ha : 0 < a) :
    1 + Real.log a = Real.log (Real.exp 1 * a) := by
  rw [Real.log_mul (Real.exp_ne_zero 1) ha.ne', Real.log_exp]

/-- Source: `proof_gap/exercise_543/6.txt`; state the limit directly. -/
theorem gap6 (a : ℝ) (ha : 0 < a) :
    HasLimitAt (logQuotient a) a (Real.log (Real.exp 1 * a)) := by
  rw [← gap5 a ha]
  have hid := tendsto_id_from_punctured a
  have hpos : ∀ᶠ x in nhdsWithin a ({a} : Set ℝ)ᶜ, 0 < x := by
    have hmem := hid.eventually (isOpen_Ioi.mem_nhds ha)
    simpa only [Set.mem_Ioi] using hmem
  apply (gap4 a ha).congr'
  filter_upwards [hpos, self_mem_nhdsWithin] with x hx hmem
  have hxa : x ≠ a := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hmem
  calc
    normalized a x = splitLog a x := (gap3 a x ha hx hxa).symm
    _ = logQuotient a x := (gap2 a x ha hx hxa).symm

/-- Source: `proof_gap/exercise_543/7.txt`. -/
theorem gap7 (a : ℝ) (ha : 0 < a) :
    HasLimitAt (expQuotient a) a 1 := by
  have hid := tendsto_id_from_punctured a
  have hpos : ∀ᶠ x in nhdsWithin a ({a} : Set ℝ)ᶜ, 0 < x := by
    have hmem := hid.eventually (isOpen_Ioi.mem_nhds ha)
    simpa only [Set.mem_Ioi] using hmem
  have hlog :
      Filter.Tendsto Real.log
        (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds (Real.log a)) :=
    (Real.continuousAt_log ha.ne').tendsto.mono_left inf_le_left
  have hconst :
      Filter.Tendsto (fun _ : ℝ => a * Real.log a)
        (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds (a * Real.log a)) :=
    tendsto_const_nhds
  have hdlim :
      Filter.Tendsto
        (fun x : ℝ => x * Real.log x - a * Real.log a)
        (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds 0) := by
    simpa using (hid.mul hlog).sub hconst
  have hq :
      HasLimitAt (logQuotient a) a (1 + Real.log a) := by
    rw [gap5 a ha]
    exact gap6 a ha
  have hdnz :
      ∀ᶠ x in nhdsWithin a ({a} : Set ℝ)ᶜ,
        x * Real.log x - a * Real.log a ≠ 0 := by
    by_cases hc : 1 + Real.log a = 0
    · filter_upwards [hpos, self_mem_nhdsWithin] with x hx hmem
      have hxa : x ≠ a := by
        simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hmem
      let y : ℝ := x / a
      have hy : 0 < y := by
        dsimp [y]
        exact div_pos hx ha
      have hyne : y ≠ 1 := by
        intro h
        apply hxa
        exact (div_eq_one_iff_eq ha.ne').mp h
      have hlogne : -Real.log y ≠ 0 := by
        intro h
        have hl : Real.log y = 0 := by
          linarith
        apply hyne
        calc
          y = Real.exp (Real.log y) := (Real.exp_log hy).symm
          _ = 1 := by rw [hl]; simp
      have he := Real.add_one_lt_exp hlogne
      have hexp : Real.exp (-Real.log y) = 1 / y := by
        rw [Real.exp_neg, Real.exp_log hy]
        simp only [one_div]
      rw [hexp] at he
      have hmul := mul_lt_mul_of_pos_left he hy
      have hycancel : y * (1 / y) = 1 := by
        field_simp [hy.ne']
      rw [hycancel] at hmul
      have hcore : 0 < y * Real.log y - y + 1 := by
        nlinarith [hmul]
      have hloga : Real.log a = -1 := by
        linarith
      have hxy : x = a * y := by
        dsimp [y]
        field_simp [ha.ne']
      have hlogdiv : Real.log y = Real.log x - Real.log a := by
        dsimp [y]
        exact Real.log_div hx.ne' ha.ne'
      have hlogx : Real.log x = Real.log y + Real.log a := by
        linarith
      have hdident :
          x * Real.log x - a * Real.log a =
            a * (y * Real.log y - y + 1) := by
        calc
          x * Real.log x - a * Real.log a =
              x * (Real.log y + Real.log a) - a * Real.log a := by
                rw [hlogx]
          _ = (a * y) * (Real.log y + Real.log a) -
                a * Real.log a := by
                rw [hxy]
          _ = a * (y * Real.log y - y + 1) := by
                rw [hloga]
                ring
      have hdpos : 0 < x * Real.log x - a * Real.log a := by
        rw [hdident]
        exact mul_pos ha hcore
      exact hdpos.ne'
    · have hopen :
          ({0} : Set ℝ)ᶜ ∈ nhds (1 + Real.log a) :=
        isOpen_compl_singleton.mem_nhds
          (by
            simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hc)
      have hqne :
          ∀ᶠ x in nhdsWithin a ({a} : Set ℝ)ᶜ,
            logQuotient a x ≠ 0 := by
        have hmem := hq hopen
        simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hmem
      filter_upwards [hqne] with x hxq
      intro hd
      apply hxq
      unfold logQuotient
      rw [hd]
      simp
  have hdpunct :
      Filter.Tendsto
        (fun x : ℝ => x * Real.log x - a * Real.log a)
        (nhdsWithin a ({a} : Set ℝ)ᶜ)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) := by
    refine tendsto_nhdsWithin_iff.2 ⟨hdlim, ?_⟩
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hdnz
  have hexpslope := (Real.hasDerivAt_exp 0).tendsto_slope
  change
    Filter.Tendsto
      (fun z : ℝ => (z - 0)⁻¹ • (Real.exp z - Real.exp 0))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (Real.exp 0)) at hexpslope
  have hcomp :
      Filter.Tendsto
        ((fun z : ℝ => (z - 0)⁻¹ • (Real.exp z - Real.exp 0)) ∘
          (fun x : ℝ => x * Real.log x - a * Real.log a))
        (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds 1) := by
    simpa only [Real.exp_zero] using hexpslope.comp hdpunct
  unfold HasLimitAt
  refine hcomp.congr' (Filter.Eventually.of_forall (fun x => ?_))
  simp [expQuotient, Function.comp_apply, div_eq_mul_inv, mul_comm]

/-- Source: `proof_gap/exercise_543/8.txt`. -/
theorem gap8 (a : ℝ) (ha : 0 < a) :
    HasLimitAt (original a) a (powSelf a * Real.log (Real.exp 1 * a)) := by
  have hconst :
      Filter.Tendsto (fun _ : ℝ => powSelf a)
        (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds (powSelf a)) :=
    tendsto_const_nhds
  have hfactor :
      HasLimitAt (expFactor a) a
        (powSelf a * Real.log (Real.exp 1 * a)) := by
    simpa [HasLimitAt, expFactor, expQuotient, logQuotient] using
      (hconst.mul (gap7 a ha)).mul (gap6 a ha)
  have hid := tendsto_id_from_punctured a
  have hpos : ∀ᶠ x in nhdsWithin a ({a} : Set ℝ)ᶜ, 0 < x := by
    have hmem := hid.eventually (isOpen_Ioi.mem_nhds ha)
    simpa only [Set.mem_Ioi] using hmem
  apply hfactor.congr'
  filter_upwards [hpos, self_mem_nhdsWithin] with x hx hmem
  have hxa : x ≠ a := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hmem
  exact (gap1 a x ha hx hxa).symm

end

end ProofGap.Exercise543
