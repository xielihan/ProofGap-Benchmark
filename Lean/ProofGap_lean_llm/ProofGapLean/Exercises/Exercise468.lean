import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise468

noncomputable section

def x₁ (b c a : ℝ) : ℝ := (-b + Real.sqrt (b ^ 2 - 4 * a * c)) / (2 * a)
def x₂ (b c a : ℝ) : ℝ := (-b - Real.sqrt (b ^ 2 - 4 * a * c)) / (2 * a)
def conjugateForm (b c a : ℝ) : ℝ :=
  ((-b + Real.sqrt (b ^ 2 - 4 * a * c)) *
      (-b - Real.sqrt (b ^ 2 - 4 * a * c))) /
    (2 * a * (-b - Real.sqrt (b ^ 2 - 4 * a * c)))
def reciprocalForm (b c a : ℝ) : ℝ :=
  -2 * c / (b + Real.sqrt (b ^ 2 - 4 * a * c))
def HasLimitAtZero (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds L)
def DivergesInAbsAtZero (f : ℝ → ℝ) : Prop :=
  Filter.Tendsto (fun a => |f a|) (nhdsWithin 0 ({0} : Set ℝ)ᶜ) Filter.atTop

/-- Source: `proof_gap/exercise_468/1.txt`. -/
private lemma eventually_discriminant_nonneg (b c : ℝ) (hb : 0 < b) :
    ∀ᶠ a in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
      0 ≤ b ^ 2 - 4 * a * c := by
  let δ : ℝ := b ^ 2 / (4 * (|c| + 1))
  have hb2 : 0 < b ^ 2 := by
    nlinarith
  have hcden : 0 < 4 * (|c| + 1) := by
    nlinarith [abs_nonneg c]
  have hδ : 0 < δ := by
    dsimp [δ]
    exact div_pos hb2 hcden
  have hball_nhds :
      ∀ᶠ a in nhds (0 : ℝ), a ∈ Metric.ball (0 : ℝ) δ :=
    Metric.ball_mem_nhds 0 hδ
  have hball :
      ∀ᶠ a in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
        a ∈ Metric.ball (0 : ℝ) δ :=
    hball_nhds.filter_mono inf_le_left
  filter_upwards [hball] with a ha
  have haabs : |a| < δ := by
    simpa [Real.dist_eq] using ha
  have hprod : |a| * (4 * (|c| + 1)) < b ^ 2 := by
    exact (lt_div_iff₀ hcden).mp (by simpa [δ] using haabs)
  have hacabs : 4 * a * c ≤ 4 * (|a| * |c|) := by
    have h := le_abs_self (a * c)
    rw [abs_mul] at h
    nlinarith
  nlinarith [hprod, hacabs, abs_nonneg a, abs_nonneg c]

private lemma eventually_forms (b c : ℝ) (hb : 0 < b) :
    ∀ᶠ a in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
      x₁ b c a = conjugateForm b c a ∧
        conjugateForm b c a = reciprocalForm b c a := by
  have hdisc := eventually_discriminant_nonneg b c hb
  have hpunct :
      ∀ᶠ a in nhdsWithin 0 ({0} : Set ℝ)ᶜ, a ∈ ({0} : Set ℝ)ᶜ :=
    self_mem_nhdsWithin
  filter_upwards [hdisc, hpunct] with a hd ha_mem
  have ha0 : a ≠ 0 := by
    simpa using ha_mem
  have hsnonneg :
      0 ≤ Real.sqrt (b ^ 2 - 4 * a * c) :=
    Real.sqrt_nonneg _
  have hminus :
      -b - Real.sqrt (b ^ 2 - 4 * a * c) ≠ 0 := by
    nlinarith
  have hplus :
      b + Real.sqrt (b ^ 2 - 4 * a * c) ≠ 0 := by
    nlinarith
  constructor
  · unfold x₁ conjugateForm
    field_simp [ha0, hminus] <;> ring
  · have hsquare :
        (Real.sqrt (b ^ 2 - 4 * a * c)) ^ 2 =
          b ^ 2 - 4 * a * c :=
      Real.sq_sqrt hd
    have hprod :
        (-b + Real.sqrt (b ^ 2 - 4 * a * c)) *
            (-b - Real.sqrt (b ^ 2 - 4 * a * c)) =
          4 * a * c := by
      nlinarith [hsquare]
    unfold conjugateForm reciprocalForm
    rw [hprod]
    field_simp [ha0, hminus, hplus] <;> ring

theorem gap1 (b c a : ℝ) : x₁ b c a =
    (-b + Real.sqrt (b ^ 2 - 4 * a * c)) / (2 * a) := by
  rfl

/-- Source: `proof_gap/exercise_468/2.txt`. -/
theorem gap2 (b c a : ℝ) : x₂ b c a =
    (-b - Real.sqrt (b ^ 2 - 4 * a * c)) / (2 * a) := by
  rfl

/-- Source: `proof_gap/exercise_468/3.txt`; the two-sided signed infinite limit is replaced by divergence in absolute value. -/
theorem gap3 (b c : ℝ) (hb : 0 < b) : DivergesInAbsAtZero (x₂ b c) := by
  unfold DivergesInAbsAtZero
  refine Filter.tendsto_atTop.2 ?_
  intro M
  let δ : ℝ := b / (2 * (|M| + 1))
  have hM : 0 < |M| + 1 := by
    nlinarith [abs_nonneg M]
  have hdenM : 0 < 2 * (|M| + 1) := by
    nlinarith
  have hδ : 0 < δ := by
    dsimp [δ]
    exact div_pos hb hdenM
  have hball_nhds :
      ∀ᶠ a in nhds (0 : ℝ), a ∈ Metric.ball (0 : ℝ) δ :=
    Metric.ball_mem_nhds 0 hδ
  have hball :
      ∀ᶠ a in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
        a ∈ Metric.ball (0 : ℝ) δ :=
    hball_nhds.filter_mono inf_le_left
  have hpunct :
      ∀ᶠ a in nhdsWithin 0 ({0} : Set ℝ)ᶜ, a ∈ ({0} : Set ℝ)ᶜ :=
    self_mem_nhdsWithin
  filter_upwards [hball, hpunct] with a ha ha_mem
  have ha0 : a ≠ 0 := by
    simpa using ha_mem
  have haabs : |a| < δ := by
    simpa [Real.dist_eq] using ha
  have hsmallprod : |a| * (2 * (|M| + 1)) < b := by
    exact (lt_div_iff₀ hdenM).mp (by simpa [δ] using haabs)
  have hdena : 0 < 2 * |a| := by
    have : 0 < |a| := abs_pos.mpr ha0
    nlinarith
  have hratio : |M| + 1 < b / (2 * |a|) := by
    apply (lt_div_iff₀ hdena).2
    nlinarith [hsmallprod]
  have hsqrt :
      0 ≤ Real.sqrt (b ^ 2 - 4 * a * c) :=
    Real.sqrt_nonneg _
  have hnum_nonpos :
      -b - Real.sqrt (b ^ 2 - 4 * a * c) ≤ 0 := by
    linarith
  have hnum :
      b ≤ |-b - Real.sqrt (b ^ 2 - 4 * a * c)| := by
    rw [abs_of_nonpos hnum_nonpos]
    linarith
  have hquot :
      b / (2 * |a|) ≤
        |-b - Real.sqrt (b ^ 2 - 4 * a * c)| / (2 * |a|) :=
    div_le_div_of_nonneg_right hnum (le_of_lt hdena)
  have hfinal :
      M ≤ |-b - Real.sqrt (b ^ 2 - 4 * a * c)| / (2 * |a|) := by
    apply le_of_lt
    calc
      M ≤ |M| := le_abs_self M
      _ < |M| + 1 := by linarith
      _ < b / (2 * |a|) := hratio
      _ ≤ |-b - Real.sqrt (b ^ 2 - 4 * a * c)| / (2 * |a|) := hquot
  simpa [x₂, abs_div, abs_mul,
    abs_of_nonneg (show (0 : ℝ) ≤ 2 by linarith)] using hfinal

/-- Source: `proof_gap/exercise_468/4.txt`; rationalize the finite root. -/
theorem gap4 (b c L : ℝ) (hb : 0 < b) :
    HasLimitAtZero (x₁ b c) L ↔ HasLimitAtZero (conjugateForm b c) L := by
  unfold HasLimitAtZero
  have heq :
      x₁ b c =ᶠ[nhdsWithin 0 ({0} : Set ℝ)ᶜ] conjugateForm b c := by
    filter_upwards [eventually_forms b c hb] with a ha
    exact ha.1
  constructor
  · intro h
    exact Filter.Tendsto.congr' heq h
  · intro h
    exact Filter.Tendsto.congr' heq.symm h

/-- Source: `proof_gap/exercise_468/5.txt`. -/
theorem gap5 (b c L : ℝ) (hb : 0 < b) :
    HasLimitAtZero (conjugateForm b c) L ↔
      HasLimitAtZero (reciprocalForm b c) L := by
  unfold HasLimitAtZero
  have heq :
      conjugateForm b c =ᶠ[nhdsWithin 0 ({0} : Set ℝ)ᶜ]
        reciprocalForm b c := by
    filter_upwards [eventually_forms b c hb] with a ha
    exact ha.2
  constructor
  · intro h
    exact Filter.Tendsto.congr' heq h
  · intro h
    exact Filter.Tendsto.congr' heq.symm h

/-- Source: `proof_gap/exercise_468/6.txt`. -/
theorem gap6 (b c : ℝ) (hb : 0 < b) :
    HasLimitAtZero (reciprocalForm b c) (-c / b) := by
  unfold HasLimitAtZero
  have hpoly :
      ContinuousAt (fun a : ℝ => b ^ 2 - 4 * a * c) 0 := by
    exact continuousAt_const.sub
      ((continuousAt_const.mul continuousAt_id).mul continuousAt_const)
  have hsqrt :
      ContinuousAt (fun a : ℝ => Real.sqrt (b ^ 2 - 4 * a * c)) 0 := by
    exact Real.continuous_sqrt.continuousAt.comp hpoly
  have hden :
      b + Real.sqrt (b ^ 2 - 4 * (0 : ℝ) * c) ≠ 0 := by
    simp only [mul_zero, zero_mul, sub_zero, Real.sqrt_sq_eq_abs,
      abs_of_pos hb]
    nlinarith
  have hrec : ContinuousAt (reciprocalForm b c) 0 := by
    unfold reciprocalForm
    exact (continuousAt_const.mul continuousAt_const).div
      (continuousAt_const.add hsqrt) hden
  have hval : reciprocalForm b c 0 = -c / b := by
    unfold reciprocalForm
    simp only [mul_zero, zero_mul, sub_zero, Real.sqrt_sq_eq_abs,
      abs_of_pos hb]
    field_simp [ne_of_gt hb] <;> ring
  rw [← hval]
  exact hrec.tendsto.mono_left inf_le_left

/-- Source: `proof_gap/exercise_468/7.txt`. -/
theorem gap7 (b c : ℝ) (hb : 0 < b) :
    HasLimitAtZero (x₁ b c) (-c / b) := by
  apply (gap4 b c (-c / b) hb).2
  apply (gap5 b c (-c / b) hb).2
  exact gap6 b c hb

/-- Source: `proof_gap/exercise_468/8.txt`; restore the missing sign hypothesis and use two-sided absolute divergence. -/
theorem gap8 (b c : ℝ) (hb : 0 < b) : DivergesInAbsAtZero (x₂ b c) := by
  exact gap3 b c hb

/-- Source: `proof_gap/exercise_468/9.txt`; restore the missing hypothesis `0 < b`. -/
theorem gap9 (b c : ℝ) (hb : 0 < b) :
    HasLimitAtZero (x₁ b c) (-c / b) := by
  exact gap7 b c hb

end

end ProofGap.Exercise468
