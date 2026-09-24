import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise516

noncomputable section

def original (a₁ a₂ b₁ b₂ x : ℝ) : ℝ :=
  Real.rpow ((a₁ * x + b₁) / (a₂ * x + b₂)) x
def factored (a₁ a₂ b₁ b₂ x : ℝ) : ℝ :=
  Real.rpow (a₁ / a₂) x *
    Real.rpow ((x + b₁ / a₁) / (x + b₂ / a₂)) x
def shiftDifference (a₁ a₂ b₁ b₂ : ℝ) : ℝ := b₁ / a₁ - b₂ / a₂
def exponentialForm (a₁ a₂ b₁ b₂ x : ℝ) : ℝ :=
  let d := shiftDifference a₁ a₂ b₁ b₂
  Real.rpow (a₁ / a₂) x *
    Real.rpow (1 + 1 / ((x + b₂ / a₂) / d))
      (((x + b₂ / a₂) / d) * d - b₂ / a₂)
def equalSlopeForm (a b₁ b₂ x : ℝ) : ℝ :=
  let d := (b₁ - b₂) / a
  Real.rpow (1 + 1 / ((x + b₂ / a) / d))
    (((x + b₂ / a) / d) * d - b₂ / a)

/-- Source: `proof_gap/exercise_516/1.txt`; state the factorization on a sufficiently large positive tail. -/
private theorem tendsto_shifted_one_add_rpow (c v : ℝ) :
    Filter.Tendsto (fun x : ℝ => Real.rpow (1 + c / (x + v)) x)
      Filter.atTop (nhds (Real.exp c)) := by
  by_cases hc : c = 0
  · subst c
    simp
  have hshift : Filter.Tendsto (fun x : ℝ => x + v)
      Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop.2
    intro b
    exact Filter.eventually_atTop.2
      ⟨b - v, fun x hx => by linarith⟩
  have hinv :
      Filter.Tendsto (fun x : ℝ => (x + v)⁻¹)
        Filter.atTop (nhds 0) := by
    simpa only [Function.comp_apply] using tendsto_inv_atTop_zero.comp hshift
  have hz :
      Filter.Tendsto (fun x : ℝ => c / (x + v))
        Filter.atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_const_nhds.mul hinv :
        Filter.Tendsto (fun x : ℝ => c * (x + v)⁻¹)
          Filter.atTop (nhds (c * 0)))
  have hden : ∀ᶠ x : ℝ in Filter.atTop, 0 < x + v := by
    exact Filter.eventually_atTop.2
      ⟨-v + 1, fun x hx => by linarith⟩
  have hzne : ∀ᶠ x : ℝ in Filter.atTop, c / (x + v) ≠ 0 := by
    filter_upwards [hden] with x hx
    exact div_ne_zero hc (ne_of_gt hx)
  have hzWithin :
      Filter.Tendsto (fun x : ℝ => c / (x + v))
        Filter.atTop (nhdsWithin 0 ({0}ᶜ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨hz, ?_⟩
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hzne
  have hslope :
      Filter.Tendsto (fun z : ℝ => Real.log (1 + z) / z)
        (nhdsWithin 0 ({0}ᶜ)) (nhds 1) := by
    simpa only [Real.log_one, sub_zero, inv_one, one_smul, smul_eq_mul,
      div_eq_mul_inv, add_comm, mul_comm] using
      (Real.hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto_slope_zero
  have hs :
      Filter.Tendsto
        (fun x : ℝ => Real.log (1 + c / (x + v)) / (c / (x + v)))
        Filter.atTop (nhds 1) :=
    hslope.comp hzWithin
  have hrem :
      Filter.Tendsto (fun x : ℝ => (c * v) * (x + v)⁻¹)
        Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul hinv :
        Filter.Tendsto (fun x : ℝ => (c * v) * (x + v)⁻¹)
          Filter.atTop (nhds ((c * v) * 0)))
  have hscale' :
      Filter.Tendsto (fun x : ℝ => c - (c * v) * (x + v)⁻¹)
        Filter.atTop (nhds c) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hrem
  have hscale :
      Filter.Tendsto (fun x : ℝ => x * (c / (x + v)))
        Filter.atTop (nhds c) := by
    apply hscale'.congr'
    filter_upwards [hden] with x hx
    rw [div_eq_mul_inv]
    field_simp [ne_of_gt hx] <;> ring_nf
  have hproduct :
      Filter.Tendsto
        (fun x : ℝ =>
          (Real.log (1 + c / (x + v)) / (c / (x + v))) *
            (x * (c / (x + v))))
        Filter.atTop (nhds c) := by
    simpa only [one_mul] using hs.mul hscale
  have hlogmul :
      Filter.Tendsto (fun x : ℝ => Real.log (1 + c / (x + v)) * x)
        Filter.atTop (nhds c) := by
    apply hproduct.congr'
    filter_upwards [hzne] with x hx
    have hcancel : ∀ L z t : ℝ, z ≠ 0 →
        (L / z) * (t * z) = L * t := by
      intro L z t hz0
      field_simp [hz0] <;> ring_nf
    exact hcancel (Real.log (1 + c / (x + v))) (c / (x + v)) x hx
  have hexp :
      Filter.Tendsto
        (fun x : ℝ => Real.exp (Real.log (1 + c / (x + v)) * x))
        Filter.atTop (nhds (Real.exp c)) :=
    Real.continuous_exp.continuousAt.tendsto.comp hlogmul
  have hbase :
      Filter.Tendsto (fun x : ℝ => 1 + c / (x + v))
        Filter.atTop (nhds 1) := by
    simpa only [add_zero] using tendsto_const_nhds.add hz
  have hpos : ∀ᶠ x : ℝ in Filter.atTop, 0 < 1 + c / (x + v) := by
    exact hbase.eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))
  apply hexp.congr'
  filter_upwards [hpos] with x hx
  exact (Real.rpow_def_of_pos hx x).symm

theorem gap1 (a₁ a₂ b₁ b₂ : ℝ) (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) :
    ∃ X : ℝ, ∀ x > X, original a₁ a₂ b₁ b₂ x = factored a₁ a₂ b₁ b₂ x := by
  let X := max (-(b₁ / a₁)) (-(b₂ / a₂))
  refine ⟨X, ?_⟩
  intro x hx
  have hx₁ : 0 < x + b₁ / a₁ := by
    have hle : -(b₁ / a₁) ≤ X := le_max_left _ _
    linarith
  have hx₂ : 0 < x + b₂ / a₂ := by
    have hle : -(b₂ / a₂) ≤ X := le_max_right _ _
    linarith
  have haff₁ : a₁ * x + b₁ = a₁ * (x + b₁ / a₁) := by
    field_simp [ne_of_gt ha₁]
  have haff₂ : a₂ * x + b₂ = a₂ * (x + b₂ / a₂) := by
    field_simp [ne_of_gt ha₂]
  have hbase :
      (a₁ * x + b₁) / (a₂ * x + b₂) =
        (a₁ / a₂) * ((x + b₁ / a₁) / (x + b₂ / a₂)) := by
    rw [haff₁, haff₂]
    field_simp [ne_of_gt ha₁, ne_of_gt ha₂, ne_of_gt hx₂] <;> ring
  have hq : 0 ≤ a₁ / a₂ := le_of_lt (div_pos ha₁ ha₂)
  have hs : 0 ≤ (x + b₁ / a₁) / (x + b₂ / a₂) :=
    le_of_lt (div_pos hx₁ hx₂)
  have hm :
      Real.rpow
          ((a₁ / a₂) * ((x + b₁ / a₁) / (x + b₂ / a₂))) x =
        Real.rpow (a₁ / a₂) x *
          Real.rpow ((x + b₁ / a₁) / (x + b₂ / a₂)) x :=
    Real.mul_rpow hq hs
  rw [original, factored, hbase]
  exact hm

/-- Source: `proof_gap/exercise_516/2.txt`; require the substitution divisor to be nonzero and work on a tail. -/
theorem gap2 (a₁ a₂ b₁ b₂ : ℝ) (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (hd : shiftDifference a₁ a₂ b₁ b₂ ≠ 0) :
    ∃ X : ℝ, ∀ x > X,
      original a₁ a₂ b₁ b₂ x = exponentialForm a₁ a₂ b₁ b₂ x := by
  rcases gap1 a₁ a₂ b₁ b₂ ha₁ ha₂ with ⟨X, hX⟩
  have hd' : b₁ / a₁ - b₂ / a₂ ≠ 0 := by
    simpa only [shiftDifference] using hd
  refine ⟨max X (-(b₂ / a₂)), ?_⟩
  intro x hx
  have hxX : X < x := lt_of_le_of_lt (le_max_left _ _) hx
  have hxv : 0 < x + b₂ / a₂ := by
    have hv : -(b₂ / a₂) ≤ max X (-(b₂ / a₂)) := le_max_right _ _
    linarith
  have hu : x + b₂ / a₂ ≠ 0 := ne_of_gt hxv
  have halgBase : ∀ p q t : ℝ, t + q ≠ 0 → p - q ≠ 0 →
      (t + p) / (t + q) = 1 + 1 / ((t + q) / (p - q)) := by
    intro p q t htu hpq
    field_simp [htu, hpq] <;> ring
  have halgExponent : ∀ q d t : ℝ, d ≠ 0 →
      ((t + q) / d) * d - q = t := by
    intro q d t hd0
    field_simp [hd0] <;> ring
  have hbase :
      (x + b₁ / a₁) / (x + b₂ / a₂) =
        1 + 1 / ((x + b₂ / a₂) / (b₁ / a₁ - b₂ / a₂)) :=
    halgBase (b₁ / a₁) (b₂ / a₂) x hu hd'
  have hexponent :
      ((x + b₂ / a₂) / (b₁ / a₁ - b₂ / a₂)) *
          (b₁ / a₁ - b₂ / a₂) - b₂ / a₂ = x :=
    halgExponent (b₂ / a₂) (b₁ / a₁ - b₂ / a₂) x hd'
  rw [hX x hxX]
  unfold factored exponentialForm shiftDifference
  dsimp
  exact congrArg (fun z => Real.rpow (a₁ / a₂) x * z)
    (congrArg₂ Real.rpow hbase hexponent.symm)

/-- Source: `proof_gap/exercise_516/3.txt`; require both displayed divisors to be nonzero. -/
theorem gap3 (a b₁ b₂ : ℝ) (ha : 0 < a) (hb : b₁ ≠ b₂) :
    ∃ X : ℝ, ∀ x > X,
      original a a b₁ b₂ x = equalSlopeForm a b₁ b₂ x := by
  have hd : shiftDifference a a b₁ b₂ ≠ 0 := by
    unfold shiftDifference
    intro hzero
    apply hb
    apply sub_eq_zero.mp
    calc
      b₁ - b₂ = a * (b₁ / a - b₂ / a) := by
        field_simp [ne_of_gt ha]
      _ = 0 := by rw [hzero, mul_zero]
  rcases gap2 a a b₁ b₂ ha ha hd with ⟨X, hX⟩
  refine ⟨X, ?_⟩
  intro x hx
  rw [hX x hx]
  have hdEq : b₁ / a - b₂ / a = (b₁ - b₂) / a := by
    field_simp [ne_of_gt ha]
  dsimp [exponentialForm, equalSlopeForm, shiftDifference]
  rw [div_self (ne_of_gt ha), hdEq]
  simp

/-- Source: `proof_gap/exercise_516/4.txt`. -/
theorem gap4 (a b₁ b₂ : ℝ) (ha : 0 < a) :
    Filter.Tendsto (original a a b₁ b₂) Filter.atTop
      (nhds (Real.exp ((b₁ - b₂) / a))) := by
  have hlim := tendsto_shifted_one_add_rpow ((b₁ - b₂) / a) (b₂ / a)
  have hdEq : b₁ / a - b₂ / a = (b₁ - b₂) / a := by
    field_simp [ne_of_gt ha]
  have heq :
      (fun x : ℝ => Real.rpow
        (1 + ((b₁ - b₂) / a) / (x + b₂ / a)) x) =ᶠ[Filter.atTop]
        original a a b₁ b₂ := by
    refine Filter.eventually_atTop.2 ⟨-(b₂ / a) + 1, ?_⟩
    intro x hx
    have hxv : 0 < x + b₂ / a := by linarith
    have hu : x + b₂ / a ≠ 0 := ne_of_gt hxv
    have halg : ∀ p q t : ℝ, t + q ≠ 0 →
        (t + p) / (t + q) = 1 + (p - q) / (t + q) := by
      intro p q t htu
      field_simp [htu] <;> ring
    have hnormalized :
        (x + b₁ / a) / (x + b₂ / a) =
          1 + ((b₁ - b₂) / a) / (x + b₂ / a) := by
      rw [← hdEq]
      exact halg (b₁ / a) (b₂ / a) x hu
    have haff₁ : a * x + b₁ = a * (x + b₁ / a) := by
      field_simp [ne_of_gt ha]
    have haff₂ : a * x + b₂ = a * (x + b₂ / a) := by
      field_simp [ne_of_gt ha]
    have hratio :
        (a * x + b₁) / (a * x + b₂) =
          (x + b₁ / a) / (x + b₂ / a) := by
      rw [haff₁, haff₂]
      field_simp [ne_of_gt ha, hu]
    unfold original
    apply congrArg (fun z => Real.rpow z x)
    rw [hratio, hnormalized]
  exact hlim.congr' heq

/-- Source: `proof_gap/exercise_516/5.txt`. -/
theorem gap5 (a₁ a₂ : ℝ) (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (h : a₁ < a₂) :
    0 < a₁ / a₂ := by
  exact div_pos ha₁ ha₂

/-- Source: `proof_gap/exercise_516/6.txt`. -/
theorem gap6 (a₁ a₂ : ℝ) (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (h : a₁ < a₂) :
    a₁ / a₂ < 1 := by
  exact (div_lt_one ha₂).2 h

/-- Source: `proof_gap/exercise_516/7.txt`. -/
theorem gap7 (a₁ a₂ : ℝ) (h : a₁ < a₂) : (0 : ℝ) < 1 := by
  norm_num

/-- Source: `proof_gap/exercise_516/8.txt`. -/
theorem gap8 (a₁ a₂ : ℝ) (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (h : a₁ < a₂) :
    Filter.Tendsto (fun x : ℝ => Real.rpow (a₁ / a₂) x)
      Filter.atTop (nhds 0) := by
  have hq : 0 < a₁ / a₂ := gap5 a₁ a₂ ha₁ ha₂ h
  have hq1 : a₁ / a₂ < 1 := gap6 a₁ a₂ ha₁ ha₂ h
  have hlog : Real.log (a₁ / a₂) < 0 := Real.log_neg hq hq1
  have hlin :
      Filter.Tendsto (fun x : ℝ => Real.log (a₁ / a₂) * x)
        Filter.atTop Filter.atBot := by
    apply Filter.tendsto_atBot.2
    intro B
    refine Filter.eventually_atTop.2
      ⟨B / Real.log (a₁ / a₂), ?_⟩
    intro x hx
    have hm := mul_le_mul_of_nonpos_left hx (le_of_lt hlog)
    have hc :
        Real.log (a₁ / a₂) * (B / Real.log (a₁ / a₂)) = B := by
      field_simp [ne_of_lt hlog]
    rw [hc] at hm
    exact hm
  have hexp :
      Filter.Tendsto
        (fun x : ℝ => Real.exp (Real.log (a₁ / a₂) * x))
        Filter.atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp hlin
  apply hexp.congr'
  exact Filter.Eventually.of_forall (fun x =>
    (Real.rpow_def_of_pos hq x).symm)

/-- Source: `proof_gap/exercise_516/9.txt`. -/
theorem gap9 (a₁ a₂ b₁ b₂ : ℝ) (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) :
    Filter.Tendsto
      (fun x : ℝ => Real.rpow ((x + b₁ / a₁) / (x + b₂ / a₂)) x)
      Filter.atTop (nhds (Real.exp (b₁ / a₁ - b₂ / a₂))) := by
  have hnormalized :
      Filter.Tendsto
        (fun x : ℝ => Real.rpow ((x + b₁ / a₁) / (x + b₂ / a₂)) x)
        Filter.atTop
        (nhds (Real.exp ((b₁ / a₁ - b₂ / a₂) / (1 : ℝ)))) := by
    apply (gap4 (1 : ℝ) (b₁ / a₁) (b₂ / a₂) (by norm_num)).congr'
    exact Filter.Eventually.of_forall (fun x => by
      simp only [original, one_mul])
  simpa only [div_one] using hnormalized

/-- Source: `proof_gap/exercise_516/10.txt`. -/
theorem gap10 (a₁ a₂ b₁ b₂ : ℝ) (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (h : a₁ < a₂) :
    Filter.Tendsto (original a₁ a₂ b₁ b₂) Filter.atTop (nhds 0) := by
  have hp := gap8 a₁ a₂ ha₁ ha₂ h
  have hr := gap9 a₁ a₂ b₁ b₂ ha₁ ha₂
  have hf :
      Filter.Tendsto (factored a₁ a₂ b₁ b₂) Filter.atTop (nhds 0) := by
    simpa only [factored, zero_mul] using hp.mul hr
  rcases gap1 a₁ a₂ b₁ b₂ ha₁ ha₂ with ⟨X, hX⟩
  have heq :
      factored a₁ a₂ b₁ b₂ =ᶠ[Filter.atTop]
        original a₁ a₂ b₁ b₂ := by
    refine Filter.eventually_atTop.2 ⟨X + 1, ?_⟩
    intro x hx
    exact (hX x (by linarith)).symm
  exact hf.congr' heq

/-- Source: `proof_gap/exercise_516/11.txt`. -/
theorem gap11 (a₁ a₂ : ℝ) (ha₂ : 0 < a₂) (h : a₂ < a₁) :
    1 < a₁ / a₂ := by
  exact (one_lt_div ha₂).2 h

/-- Source: `proof_gap/exercise_516/12.txt`. -/
theorem gap12 (a₁ a₂ : ℝ) (ha₂ : 0 < a₂) (h : a₂ < a₁) :
    Filter.Tendsto (fun x : ℝ => Real.rpow (a₁ / a₂) x)
      Filter.atTop Filter.atTop := by
  have hq : 1 < a₁ / a₂ := gap11 a₁ a₂ ha₂ h
  have hlog : 0 < Real.log (a₁ / a₂) := Real.log_pos hq
  have hlin :
      Filter.Tendsto (fun x : ℝ => Real.log (a₁ / a₂) * x)
        Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop.2
    intro B
    refine Filter.eventually_atTop.2
      ⟨B / Real.log (a₁ / a₂), ?_⟩
    intro x hx
    have hm := mul_le_mul_of_nonneg_left hx (le_of_lt hlog)
    have hc :
        Real.log (a₁ / a₂) * (B / Real.log (a₁ / a₂)) = B := by
      field_simp [ne_of_gt hlog]
    rw [hc] at hm
    exact hm
  have hexp :
      Filter.Tendsto
        (fun x : ℝ => Real.exp (Real.log (a₁ / a₂) * x))
        Filter.atTop Filter.atTop :=
    Real.tendsto_exp_atTop.comp hlin
  have hqpos : 0 < a₁ / a₂ := lt_trans (by norm_num) hq
  apply hexp.congr'
  exact Filter.Eventually.of_forall (fun x =>
    (Real.rpow_def_of_pos hqpos x).symm)

/-- Source: `proof_gap/exercise_516/13.txt`. -/
theorem gap13 (a₁ a₂ b₁ b₂ : ℝ) (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (h : a₂ < a₁) :
    Filter.Tendsto (original a₁ a₂ b₁ b₂) Filter.atTop Filter.atTop := by
  have hp := gap12 a₁ a₂ ha₂ h
  have hr := gap9 a₁ a₂ b₁ b₂ ha₁ ha₂
  let c : ℝ := Real.exp (b₁ / a₁ - b₂ / a₂) / 2
  have hc : 0 < c := by
    dsimp only [c]
    exact div_pos (Real.exp_pos _) (by norm_num)
  have hcLim : c < Real.exp (b₁ / a₁ - b₂ / a₂) := by
    dsimp only [c]
    nlinarith [Real.exp_pos (b₁ / a₁ - b₂ / a₂)]
  have hf :
      Filter.Tendsto (factored a₁ a₂ b₁ b₂)
        Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop.2
    intro B
    let T : ℝ := max 1 (B / c + 1)
    have hpEv : ∀ᶠ x in Filter.atTop,
        T ≤ Real.rpow (a₁ / a₂) x := by
      apply hp.eventually
      exact Filter.eventually_atTop.2 ⟨T, fun y hy => hy⟩
    have hrEv : ∀ᶠ x in Filter.atTop,
        c < Real.rpow ((x + b₁ / a₁) / (x + b₂ / a₂)) x := by
      apply hr.eventually
      exact Ioi_mem_nhds hcLim
    filter_upwards [hpEv, hrEv] with x hpx hrx
    unfold factored
    have hp0 : 0 < Real.rpow (a₁ / a₂) x := by
      have hT : 1 ≤ T := le_max_left _ _
      linarith
    have hpB : B / c < Real.rpow (a₁ / a₂) x := by
      have hT : B / c + 1 ≤ T := le_max_right _ _
      linarith
    have hcancel : (B / c) * c = B := by
      field_simp [ne_of_gt hc]
    have hBc : B < Real.rpow (a₁ / a₂) x * c := by
      have hm := mul_lt_mul_of_pos_right hpB hc
      rw [hcancel] at hm
      exact hm
    calc
      B ≤ Real.rpow (a₁ / a₂) x * c := le_of_lt hBc
      _ ≤ Real.rpow (a₁ / a₂) x *
          Real.rpow ((x + b₁ / a₁) / (x + b₂ / a₂)) x :=
        mul_le_mul_of_nonneg_left (le_of_lt hrx) (le_of_lt hp0)
  rcases gap1 a₁ a₂ b₁ b₂ ha₁ ha₂ with ⟨X, hX⟩
  have heq :
      factored a₁ a₂ b₁ b₂ =ᶠ[Filter.atTop]
        original a₁ a₂ b₁ b₂ := by
    refine Filter.eventually_atTop.2 ⟨X + 1, ?_⟩
    intro x hx
    exact (hX x (by linarith)).symm
  exact hf.congr' heq

/-- Source: `proof_gap/exercise_516/14.txt`; encode the three-valued case distinction by three typed implications. -/
theorem gap14 (a₁ a₂ b₁ b₂ : ℝ) (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) :
    (a₁ = a₂ →
      Filter.Tendsto (original a₁ a₂ b₁ b₂) Filter.atTop
        (nhds (Real.exp ((b₁ - b₂) / a₁)))) ∧
    (a₁ < a₂ →
      Filter.Tendsto (original a₁ a₂ b₁ b₂) Filter.atTop (nhds 0)) ∧
    (a₂ < a₁ →
      Filter.Tendsto (original a₁ a₂ b₁ b₂) Filter.atTop Filter.atTop) := by
  constructor
  · intro heq
    subst a₂
    exact gap4 a₁ b₁ b₂ ha₁
  constructor
  · intro hlt
    exact gap10 a₁ a₂ b₁ b₂ ha₁ ha₂ hlt
  · intro hgt
    exact gap13 a₁ a₂ b₁ b₂ ha₁ ha₂ hgt

end

end ProofGap.Exercise516
