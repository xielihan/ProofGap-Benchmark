import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise577

noncomputable section

def u (x : ℝ) : ℝ := Real.sqrt (x ^ 2 + x)
def v (x : ℝ) : ℝ := Real.sqrt (x ^ 2 - x)
def difference (x : ℝ) : ℝ := Real.sinh (u x) - Real.sinh (v x)
def productForm (x : ℝ) : ℝ :=
  2 * Real.sinh ((u x - v x) / 2) * Real.cosh ((u x + v x) / 2)
def rootDifference (x : ℝ) : ℝ := u x - v x
def rationalized (x : ℝ) : ℝ := 2 * x / (u x + v x)
def normalizedDifference (x : ℝ) : ℝ :=
  2 / (Real.sqrt (1 + 1 / x) + Real.sqrt (1 - 1 / x))
def coshRatio (x : ℝ) : ℝ := Real.cosh ((u x + v x) / 2) / Real.cosh x
def expRatio (x : ℝ) : ℝ :=
  (Real.exp ((u x + v x) / 2) + Real.exp (-(u x + v x) / 2)) /
    (Real.exp x + Real.exp (-x))
def final (x : ℝ) : ℝ := difference x / Real.cosh x
def HasLimitAtPosInfinity (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f Filter.atTop (nhds L)

/-- Exercise 577, gap 1; restrict the radicals to the intended tail `x≥1`. -/
private theorem roots_scaled (x : ℝ) (hx : 1 ≤ x) :
    u x = x * Real.sqrt (1 + 1 / x) ∧
      v x = x * Real.sqrt (1 - 1 / x) := by
  have hx0 : 0 ≤ x := le_trans zero_le_one hx
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hxne : x ≠ 0 := ne_of_gt hxpos
  have hp : 0 ≤ 1 + 1 / x := by
    have hi : 0 < 1 / x := one_div_pos.mpr hxpos
    linarith
  have hm : 0 ≤ 1 - 1 / x := by
    exact sub_nonneg.mpr ((div_le_one hxpos).2 hx)
  have hargp : 0 ≤ x ^ 2 + x := by
    nlinarith [sq_nonneg x]
  have hargm : 0 ≤ x ^ 2 - x := by
    have h := mul_nonneg hx0 (sub_nonneg.mpr hx)
    nlinarith
  have hu_sq : (u x) ^ 2 = x ^ 2 + x := by
    simpa [u] using Real.sq_sqrt hargp
  have hv_sq : (v x) ^ 2 = x ^ 2 - x := by
    simpa [v] using Real.sq_sqrt hargm
  have hsp : (Real.sqrt (1 + 1 / x)) ^ 2 = 1 + 1 / x :=
    Real.sq_sqrt hp
  have hsm : (Real.sqrt (1 - 1 / x)) ^ 2 = 1 - 1 / x :=
    Real.sq_sqrt hm
  have hscaledp :
      (x * Real.sqrt (1 + 1 / x)) ^ 2 = x ^ 2 + x := by
    calc
      (x * Real.sqrt (1 + 1 / x)) ^ 2 =
          x ^ 2 * (Real.sqrt (1 + 1 / x)) ^ 2 := by ring
      _ = x ^ 2 * (1 + 1 / x) := by rw [hsp]
      _ = x ^ 2 + x := by
        field_simp [hxne]
  have hscaledm :
      (x * Real.sqrt (1 - 1 / x)) ^ 2 = x ^ 2 - x := by
    calc
      (x * Real.sqrt (1 - 1 / x)) ^ 2 =
          x ^ 2 * (Real.sqrt (1 - 1 / x)) ^ 2 := by ring
      _ = x ^ 2 * (1 - 1 / x) := by rw [hsm]
      _ = x ^ 2 - x := by
        field_simp [hxne]
  have hu0 : 0 ≤ u x := Real.sqrt_nonneg _
  have hv0 : 0 ≤ v x := Real.sqrt_nonneg _
  have hsup0 : 0 ≤ x * Real.sqrt (1 + 1 / x) :=
    mul_nonneg hx0 (Real.sqrt_nonneg _)
  have hsum0 : 0 ≤ x * Real.sqrt (1 - 1 / x) :=
    mul_nonneg hx0 (Real.sqrt_nonneg _)
  constructor <;> nlinarith

private theorem root_offsets (x : ℝ) (hx : 1 ≤ x) :
    u x - x = 1 / (Real.sqrt (1 + 1 / x) + 1) ∧
      v x - x = -(1 / (Real.sqrt (1 - 1 / x) + 1)) := by
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hxne : x ≠ 0 := ne_of_gt hxpos
  have hp : 0 ≤ 1 + 1 / x := by
    have hi : 0 < 1 / x := one_div_pos.mpr hxpos
    linarith
  have hm : 0 ≤ 1 - 1 / x := by
    exact sub_nonneg.mpr ((div_le_one hxpos).2 hx)
  obtain ⟨hu, hv⟩ := roots_scaled x hx
  have hsp : (Real.sqrt (1 + 1 / x)) ^ 2 = 1 + 1 / x :=
    Real.sq_sqrt hp
  have hsm : (Real.sqrt (1 - 1 / x)) ^ 2 = 1 - 1 / x :=
    Real.sq_sqrt hm
  have hdp : Real.sqrt (1 + 1 / x) + 1 ≠ 0 := by
    have hs := Real.sqrt_nonneg (1 + 1 / x)
    nlinarith
  have hdm : Real.sqrt (1 - 1 / x) + 1 ≠ 0 := by
    have hs := Real.sqrt_nonneg (1 - 1 / x)
    nlinarith
  have hpalg :
      x * ((Real.sqrt (1 + 1 / x)) ^ 2 - 1) = 1 := by
    rw [hsp]
    field_simp [hxne]
    ring
  have hmalg :
      x * ((Real.sqrt (1 - 1 / x)) ^ 2 - 1) = -1 := by
    rw [hsm]
    field_simp [hxne]
    ring
  constructor
  · rw [hu]
    apply (eq_div_iff hdp).2
    calc
      (x * Real.sqrt (1 + 1 / x) - x) *
          (Real.sqrt (1 + 1 / x) + 1) =
          x * ((Real.sqrt (1 + 1 / x)) ^ 2 - 1) := by ring
      _ = 1 := hpalg
  · rw [hv]
    have hnegdiv :
        -(1 / (Real.sqrt (1 - 1 / x) + 1)) =
          (-1) / (Real.sqrt (1 - 1 / x) + 1) := by
      ring
    rw [hnegdiv]
    apply (eq_div_iff hdm).2
    calc
      (x * Real.sqrt (1 - 1 / x) - x) *
          (Real.sqrt (1 - 1 / x) + 1) =
          x * ((Real.sqrt (1 - 1 / x)) ^ 2 - 1) := by ring
      _ = -1 := hmalg

theorem gap1 (x : ℝ) (hx : 1 ≤ x) : difference x = productForm x := by
  unfold difference productForm
  let a : ℝ := (u x - v x) / 2
  let b : ℝ := (u x + v x) / 2
  have hu : u x = a + b := by
    dsimp [a, b]
    ring
  have hv : v x = -(a - b) := by
    dsimp [a, b]
    ring
  calc
    Real.sinh (u x) - Real.sinh (v x) =
        Real.sinh (a + b) + Real.sinh (a - b) := by
          rw [hu, hv]
          simp only [Real.sinh_neg]
          ring
    _ = 2 * Real.sinh a * Real.cosh b := by
      rw [Real.sinh_add, Real.sinh_sub]
      ring
    _ = 2 * Real.sinh ((u x - v x) / 2) *
          Real.cosh ((u x + v x) / 2) := by
      rfl

/-- Exercise 577, gap 2; restrict the radicals to `x≥1`. -/
theorem gap2 (x : ℝ) (hx : 1 ≤ x) : rootDifference x = rationalized x := by
  have hx0 : 0 ≤ x := le_trans zero_le_one hx
  have hplus : 0 ≤ x ^ 2 + x := by
    nlinarith [sq_nonneg x]
  have hminus : 0 ≤ x ^ 2 - x := by
    have hm := mul_nonneg hx0 (sub_nonneg.mpr hx)
    nlinarith
  have hu_sq : (u x) ^ 2 = x ^ 2 + x := by
    simpa [u] using Real.sq_sqrt hplus
  have hv_sq : (v x) ^ 2 = x ^ 2 - x := by
    simpa [v] using Real.sq_sqrt hminus
  have hu_pos : 0 < u x := by
    simpa [u] using
      (Real.sqrt_pos.2 (by nlinarith [sq_nonneg x] : 0 < x ^ 2 + x))
  have hsum : u x + v x ≠ 0 := by
    have hv0 : 0 ≤ v x := Real.sqrt_nonneg _
    nlinarith
  unfold rootDifference rationalized
  apply (eq_div_iff hsum).2
  nlinarith

/-- Exercise 577, gap 3; require `x≥1` before dividing by `x`. -/
theorem gap3 (x : ℝ) (hx : 1 ≤ x) :
    rationalized x = normalizedDifference x := by
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hxne : x ≠ 0 := ne_of_gt hxpos
  obtain ⟨hu, hv⟩ := roots_scaled x hx
  have hp : 0 < 1 + 1 / x := by
    have hi : 0 < 1 / x := one_div_pos.mpr hxpos
    linarith
  have hden :
      Real.sqrt (1 + 1 / x) + Real.sqrt (1 - 1 / x) ≠ 0 := by
    have hspos : 0 < Real.sqrt (1 + 1 / x) := Real.sqrt_pos.2 hp
    have hs0 : 0 ≤ Real.sqrt (1 - 1 / x) := Real.sqrt_nonneg _
    nlinarith
  unfold rationalized normalizedDifference
  rw [hu, hv]
  field_simp [hxne, hden] <;> ring

/-- Exercise 577, gap 4. -/
theorem gap4 : HasLimitAtPosInfinity normalizedDifference 1 := by
  unfold HasLimitAtPosInfinity
  have hinv :
      Filter.Tendsto (fun x : ℝ => 1 / x) Filter.atTop (nhds 0) := by
    simpa [one_div] using
      (tendsto_inv_atTop_zero :
        Filter.Tendsto (fun x : ℝ => x⁻¹) Filter.atTop (nhds 0))
  have hsplus :
      Filter.Tendsto (fun x : ℝ => Real.sqrt (1 + 1 / x))
        Filter.atTop (nhds 1) := by
    simpa using
      (Real.continuous_sqrt.continuousAt.tendsto.comp
        ((tendsto_const_nhds :
            Filter.Tendsto (fun _ : ℝ => (1 : ℝ)) Filter.atTop (nhds 1)).add hinv))
  have hsminus :
      Filter.Tendsto (fun x : ℝ => Real.sqrt (1 - 1 / x))
        Filter.atTop (nhds 1) := by
    simpa using
      (Real.continuous_sqrt.continuousAt.tendsto.comp
        ((tendsto_const_nhds :
            Filter.Tendsto (fun _ : ℝ => (1 : ℝ)) Filter.atTop (nhds 1)).sub hinv))
  have hlim :=
    ((tendsto_const_nhds :
        Filter.Tendsto (fun _ : ℝ => (2 : ℝ)) Filter.atTop (nhds 2)).div
      (hsplus.add hsminus) (by norm_num : (1 + 1 : ℝ) ≠ 0))
  norm_num at hlim
  apply hlim.congr'
  apply Filter.Eventually.of_forall
  intro x
  simp [normalizedDifference, one_div]

/-- Exercise 577, gap 5. -/
theorem gap5 : HasLimitAtPosInfinity rootDifference 1 := by
  unfold HasLimitAtPosInfinity at *
  have heq :
      (fun x => normalizedDifference x) =ᶠ[Filter.atTop]
        (fun x => rootDifference x) := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x hx
    exact ((gap2 x hx).trans (gap3 x hx)).symm
  exact gap4.congr' heq

/-- Exercise 577, gap 6; restrict the radical identity to `x≥1`. -/
theorem gap6 (x : ℝ) (hx : 1 ≤ x) : coshRatio x = expRatio x := by
  have hden : Real.exp x + Real.exp (-x) ≠ 0 := by
    have h1 := Real.exp_pos x
    have h2 := Real.exp_pos (-x)
    nlinarith
  unfold coshRatio expRatio
  simp only [Real.cosh_eq]
  field_simp [hden] <;> ring

/-- Exercise 577, gap 7. -/
theorem gap7 : HasLimitAtPosInfinity expRatio 1 := by
  unfold HasLimitAtPosInfinity
  have hinv :
      Filter.Tendsto (fun x : ℝ => 1 / x) Filter.atTop (nhds 0) := by
    simpa [one_div] using
      (tendsto_inv_atTop_zero :
        Filter.Tendsto (fun x : ℝ => x⁻¹) Filter.atTop (nhds 0))
  have hsplus :
      Filter.Tendsto (fun x : ℝ => Real.sqrt (1 + 1 / x))
        Filter.atTop (nhds 1) := by
    simpa using
      (Real.continuous_sqrt.continuousAt.tendsto.comp
        ((tendsto_const_nhds :
            Filter.Tendsto (fun _ : ℝ => (1 : ℝ)) Filter.atTop (nhds 1)).add hinv))
  have hsminus :
      Filter.Tendsto (fun x : ℝ => Real.sqrt (1 - 1 / x))
        Filter.atTop (nhds 1) := by
    simpa using
      (Real.continuous_sqrt.continuousAt.tendsto.comp
        ((tendsto_const_nhds :
            Filter.Tendsto (fun _ : ℝ => (1 : ℝ)) Filter.atTop (nhds 1)).sub hinv))
  have hpRec :
      Filter.Tendsto
        (fun x : ℝ => 1 / (Real.sqrt (1 + 1 / x) + 1))
        Filter.atTop (nhds (1 / 2 : ℝ)) := by
    have hlim :=
      ((tendsto_const_nhds :
          Filter.Tendsto (fun _ : ℝ => (1 : ℝ)) Filter.atTop (nhds 1)).div
        (hsplus.add tendsto_const_nhds)
        (by norm_num : (1 + 1 : ℝ) ≠ 0))
    norm_num at hlim
    apply hlim.congr'
    apply Filter.Eventually.of_forall
    intro x
    simp [one_div]
  have hmRec :
      Filter.Tendsto
        (fun x : ℝ => 1 / (Real.sqrt (1 - 1 / x) + 1))
        Filter.atTop (nhds (1 / 2 : ℝ)) := by
    have hlim :=
      ((tendsto_const_nhds :
          Filter.Tendsto (fun _ : ℝ => (1 : ℝ)) Filter.atTop (nhds 1)).div
        (hsminus.add tendsto_const_nhds)
        (by norm_num : (1 + 1 : ℝ) ≠ 0))
    norm_num at hlim
    apply hlim.congr'
    apply Filter.Eventually.of_forall
    intro x
    simp [one_div]
  have hq :
      Filter.Tendsto
        (fun x : ℝ =>
          (1 / (Real.sqrt (1 + 1 / x) + 1) -
            1 / (Real.sqrt (1 - 1 / x) + 1)) / 2)
        Filter.atTop (nhds 0) := by
    simpa using (hpRec.sub hmRec).div_const 2
  have hoffset :
      Filter.Tendsto
        (fun x : ℝ => (u x + v x) / 2 - x)
        Filter.atTop (nhds 0) := by
    have heq :
        (fun x : ℝ =>
          (1 / (Real.sqrt (1 + 1 / x) + 1) -
            1 / (Real.sqrt (1 - 1 / x) + 1)) / 2) =ᶠ[Filter.atTop]
          (fun x : ℝ => (u x + v x) / 2 - x) := by
      filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x hx
      obtain ⟨hu, hv⟩ := root_offsets x hx
      rw [show (u x + v x) / 2 - x =
          ((u x - x) + (v x - x)) / 2 by ring, hu, hv]
      ring
    exact hq.congr' heq
  have hmidTop :
      Filter.Tendsto (fun x : ℝ => (u x + v x) / 2)
        Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop.2 ?_
    intro b
    have hoffLower :
        ∀ᶠ x in Filter.atTop, -1 < (u x + v x) / 2 - x :=
      hoffset.eventually (Ioi_mem_nhds (by norm_num : (-1 : ℝ) < 0))
    filter_upwards
      [Filter.eventually_ge_atTop (b + 1), hoffLower] with x hx hlow
    nlinarith
  have hsumTop :
      Filter.Tendsto (fun x : ℝ => (u x + v x) / 2 + x)
        Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop.2 ?_
    intro b
    filter_upwards
      [hmidTop.eventually (Filter.eventually_ge_atTop b),
        Filter.eventually_ge_atTop (0 : ℝ)] with x hmid hx
    nlinarith
  have hnegSum :
      Filter.Tendsto (fun x : ℝ => -(u x + v x) / 2 - x)
        Filter.atTop Filter.atBot := by
    refine Filter.tendsto_atBot.2 ?_
    intro b
    filter_upwards
      [hsumTop.eventually (Filter.eventually_ge_atTop (-b))] with x hx
    nlinarith
  have hnegTwo :
      Filter.Tendsto (fun x : ℝ => -x - x)
        Filter.atTop Filter.atBot := by
    refine Filter.tendsto_atBot.2 ?_
    intro b
    filter_upwards [Filter.eventually_ge_atTop (-b / 2)] with x hx
    nlinarith
  have hExpOffset :
      Filter.Tendsto
        (fun x : ℝ => Real.exp ((u x + v x) / 2 - x))
        Filter.atTop (nhds 1) := by
    simpa using Real.continuous_exp.continuousAt.tendsto.comp hoffset
  have hExpNegSum :
      Filter.Tendsto
        (fun x : ℝ => Real.exp (-(u x + v x) / 2 - x))
        Filter.atTop (nhds 0) := by
    exact Real.tendsto_exp_atBot.comp hnegSum
  have hExpNegTwo :
      Filter.Tendsto (fun x : ℝ => Real.exp (-x - x))
        Filter.atTop (nhds 0) := by
    exact Real.tendsto_exp_atBot.comp hnegTwo
  have hquot :
      Filter.Tendsto
        (fun x : ℝ =>
          (Real.exp ((u x + v x) / 2 - x) +
              Real.exp (-(u x + v x) / 2 - x)) /
            (1 + Real.exp (-x - x)))
        Filter.atTop (nhds 1) := by
    have hlim :=
      ((hExpOffset.add hExpNegSum).div
        ((tendsto_const_nhds :
            Filter.Tendsto (fun _ : ℝ => (1 : ℝ)) Filter.atTop (nhds 1)).add
          hExpNegTwo) (by norm_num : (1 + 0 : ℝ) ≠ 0))
    norm_num at hlim
    simpa using hlim
  have heq :
      (fun x : ℝ =>
        (Real.exp ((u x + v x) / 2 - x) +
            Real.exp (-(u x + v x) / 2 - x)) /
          (1 + Real.exp (-x - x))) =ᶠ[Filter.atTop]
        (fun x => expRatio x) := by
    apply Filter.Eventually.of_forall
    intro x
    have hden : Real.exp x + Real.exp (-x) ≠ 0 := by
      have h1 := Real.exp_pos x
      have h2 := Real.exp_pos (-x)
      nlinarith
    unfold expRatio
    simp only [Real.exp_sub]
    field_simp [Real.exp_ne_zero, hden] <;> ring
  exact hquot.congr' heq

/-- Exercise 577, gap 8. -/
theorem gap8 : HasLimitAtPosInfinity coshRatio 1 := by
  unfold HasLimitAtPosInfinity at *
  have heq :
      (fun x => expRatio x) =ᶠ[Filter.atTop]
        (fun x => coshRatio x) := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x hx
    exact (gap6 x hx).symm
  exact gap7.congr' heq

/-- Exercise 577, gap 9. -/
theorem gap9 : HasLimitAtPosInfinity final (2 * Real.sinh (1 / 2)) := by
  unfold HasLimitAtPosInfinity at *
  have hhalf :
      Filter.Tendsto (fun x : ℝ => rootDifference x / 2)
        Filter.atTop (nhds (1 / 2 : ℝ)) := by
    simpa using gap5.div_const 2
  have hsinh :
      Filter.Tendsto (fun x : ℝ => Real.sinh (rootDifference x / 2))
        Filter.atTop (nhds (Real.sinh (1 / 2))) := by
    exact Real.continuous_sinh.continuousAt.tendsto.comp hhalf
  have hproduct :
      Filter.Tendsto
        (fun x : ℝ => 2 * Real.sinh (rootDifference x / 2) * coshRatio x)
        Filter.atTop (nhds (2 * Real.sinh (1 / 2))) := by
    simpa using
      ((tendsto_const_nhds :
          Filter.Tendsto (fun _ : ℝ => (2 : ℝ)) Filter.atTop (nhds 2)).mul
        hsinh |>.mul gap8)
  have heq :
      (fun x : ℝ => 2 * Real.sinh (rootDifference x / 2) * coshRatio x) =ᶠ[Filter.atTop]
        (fun x => final x) := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x hx
    have hcosh : Real.cosh x ≠ 0 := ne_of_gt (Real.cosh_pos x)
    unfold final
    rw [gap1 x hx]
    unfold productForm coshRatio rootDifference
    field_simp [hcosh] <;> ring
  exact hproduct.congr' heq

end

end ProofGap.Exercise577
