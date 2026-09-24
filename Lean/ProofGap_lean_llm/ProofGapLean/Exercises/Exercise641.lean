import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Order.Filter.AtTopBot.Ring

namespace ProofGap.Exercise641

noncomputable section

def oscillationOn (f : ℝ → ℝ) (k : ℝ) : ℝ :=
  sSup {d : ℝ | ∃ x ∈ Set.Icc (-k) k, ∃ y ∈ Set.Icc (-k) k,
    d = |f x - f y|}
def oscillationAt (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto (fun n : ℕ => oscillationOn f (1 / ((n : ℝ) + 1)))
    Filter.atTop (nhds L)
def unboundedOscillationOn (f : ℝ → ℝ) (k : ℝ) : Prop :=
  ∀ M : ℝ, ∃ x ∈ Set.Icc (-k) k, ∃ y ∈ Set.Icc (-k) k,
    M < |f x - f y|

def f₁ (x : ℝ) : ℝ := Real.sin (1 / x)
def f₂ (x : ℝ) : ℝ := 1 / x ^ 2 * Real.cos (1 / x) ^ 2
def f₃ (x : ℝ) : ℝ := x * (2 + Real.sin (1 / x))
def f₄ (x : ℝ) : ℝ := (1 / Real.pi) * Real.arctan (1 / x)
def f₅ (x : ℝ) : ℝ := |Real.sin x| / x
def f₆ (x : ℝ) : ℝ := 1 / (1 + Real.exp (1 / x))
def f₇ (x : ℝ) : ℝ := Real.rpow (1 + |x|) (1 / x)

private theorem oscillationOn_eq_of_upper_of_approx
    (f : ℝ → ℝ) (k L : ℝ)
    (hupper : ∀ x ∈ Set.Icc (-k) k, ∀ y ∈ Set.Icc (-k) k,
      |f x - f y| ≤ L)
    (happrox : ∀ a < L, ∃ x ∈ Set.Icc (-k) k, ∃ y ∈ Set.Icc (-k) k,
      a < |f x - f y|) :
    oscillationOn f k = L := by
  let s : Set ℝ := {d : ℝ | ∃ x ∈ Set.Icc (-k) k, ∃ y ∈ Set.Icc (-k) k,
    d = |f x - f y|}
  have hsne : s.Nonempty := by
    obtain ⟨x, hx, y, hy, -⟩ := happrox (L - 1) (by linarith)
    exact ⟨|f x - f y|, x, hx, y, hy, rfl⟩
  have hsbdd : BddAbove s := by
    refine ⟨L, ?_⟩
    rintro d ⟨x, hx, y, hy, rfl⟩
    exact hupper x hx y hy
  unfold oscillationOn
  change sSup s = L
  apply le_antisymm
  · exact csSup_le hsne fun d hd => by
      rcases hd with ⟨x, hx, y, hy, rfl⟩
      exact hupper x hx y hy
  · by_contra h
    have hslt : sSup s < L := lt_of_not_ge h
    obtain ⟨x, hx, y, hy, hxy⟩ := happrox (sSup s) hslt
    exact (not_lt_of_ge (le_csSup hsbdd ⟨x, hx, y, hy, rfl⟩)) hxy

private theorem oscillationOn_bounds_of_pair_bound
    (f : ℝ → ℝ) (k L : ℝ) (hk : 0 ≤ k)
    (hupper : ∀ x ∈ Set.Icc (-k) k, ∀ y ∈ Set.Icc (-k) k,
      |f x - f y| ≤ L) :
    0 ≤ oscillationOn f k ∧ oscillationOn f k ≤ L ∧
      ∀ x ∈ Set.Icc (-k) k, ∀ y ∈ Set.Icc (-k) k,
        |f x - f y| ≤ oscillationOn f k := by
  let s : Set ℝ := {d : ℝ | ∃ x ∈ Set.Icc (-k) k, ∃ y ∈ Set.Icc (-k) k,
    d = |f x - f y|}
  have hzero : (0 : ℝ) ∈ s := by
    refine ⟨0, ⟨by linarith, hk⟩, 0, ⟨by linarith, hk⟩, ?_⟩
    simp
  have hbdd : BddAbove s := by
    refine ⟨L, ?_⟩
    rintro d ⟨x, hx, y, hy, rfl⟩
    exact hupper x hx y hy
  have hnonneg : 0 ≤ sSup s := le_csSup hbdd hzero
  have hle : sSup s ≤ L := csSup_le ⟨0, hzero⟩ fun d hd => by
    rcases hd with ⟨x, hx, y, hy, rfl⟩
    exact hupper x hx y hy
  unfold oscillationOn
  change 0 ≤ sSup s ∧ sSup s ≤ L ∧ _
  refine ⟨hnonneg, hle, ?_⟩
  intro x hx y hy
  exact le_csSup hbdd ⟨x, hx, y, hy, rfl⟩

private theorem exists_f₁_eq_one (k : ℝ) (hk : 0 < k) :
    ∃ x ∈ Set.Icc (-k) k, f₁ x = 1 := by
  obtain ⟨n : ℕ, hn⟩ :=
    exists_nat_gt ((1 / k - Real.pi / 2) / (2 * Real.pi))
  let t : ℝ := Real.pi / 2 + (n : ℝ) * (2 * Real.pi)
  have htwo_pi : 0 < 2 * Real.pi := by positivity
  have ht_large : 1 / k < t := by
    dsimp [t]
    have := (div_lt_iff₀ htwo_pi).mp hn
    linarith
  have ht : 0 < t := lt_trans (one_div_pos.mpr hk) ht_large
  have hxpos : 0 < 1 / t := one_div_pos.mpr ht
  have hxle : 1 / t ≤ k := by
    apply (div_le_iff₀ ht).2
    have := (div_lt_iff₀ hk).1 ht_large
    nlinarith
  refine ⟨1 / t, ⟨by linarith, hxle⟩, ?_⟩
  have hinv : 1 / (1 / t) = t := by field_simp
  rw [f₁, hinv]
  dsimp [t]
  rw [Real.sin_add_nat_mul_two_pi, Real.sin_pi_div_two]

/-- Exercise 641, gap 1; require a positive neighborhood radius. -/
theorem gap1 (k : ℝ) (hk : 0 < k) : oscillationOn f₁ k = 2 := by
  apply oscillationOn_eq_of_upper_of_approx
  · intro x hx y hy
    calc
      |f₁ x - f₁ y| ≤ |f₁ x| + |f₁ y| := abs_sub _ _
      _ ≤ 1 + 1 := add_le_add (by simpa [f₁] using Real.abs_sin_le_one (1 / x))
        (by simpa [f₁] using Real.abs_sin_le_one (1 / y))
      _ = 2 := by norm_num
  · intro a ha
    obtain ⟨x, hx, hfx⟩ := exists_f₁_eq_one k hk
    have hneg_mem : -x ∈ Set.Icc (-k) k := by
      constructor <;> linarith [hx.1, hx.2]
    refine ⟨x, hx, -x, hneg_mem, ?_⟩
    have hsin : Real.sin x⁻¹ = 1 := by
      simpa [f₁, one_div] using hfx
    have hneg : f₁ (-x) = -1 := by
      simp [f₁, one_div, hsin]
    rw [hfx, hneg]
    norm_num at ha ⊢
    exact ha

/-- Exercise 641, gap 2. -/
theorem gap2 : oscillationAt f₁ 2 := by
  unfold oscillationAt
  have heq : (fun n : ℕ => oscillationOn f₁ (1 / ((n : ℝ) + 1))) =
      fun _ : ℕ => (2 : ℝ) := by
    funext n
    apply gap1
    positivity
  rw [heq]
  exact tendsto_const_nhds

/-- Exercise 641, gap 3; express `+∞` as unbounded oscillation. -/
theorem gap3 (k : ℝ) (hk : 0 < k) : unboundedOscillationOn f₂ k := by
  intro M
  obtain ⟨n : ℕ, hn⟩ :=
    exists_nat_gt
      (max ((1 / k) / (2 * Real.pi)) ((max M 1) / (2 * Real.pi)))
  let t : ℝ := (n : ℝ) * (2 * Real.pi)
  have htwo_pi : 0 < 2 * Real.pi := by positivity
  have ht_inv : 1 / k < t := by
    dsimp [t]
    have h := lt_of_le_of_lt (le_max_left _ _) hn
    exact (div_lt_iff₀ htwo_pi).1 h
  have ht_big : max M 1 < t := by
    dsimp [t]
    have h := lt_of_le_of_lt (le_max_right _ _) hn
    exact (div_lt_iff₀ htwo_pi).1 h
  have ht : 0 < t := lt_trans (by positivity : 0 < 1 / k) ht_inv
  have hxpos : 0 < 1 / t := by positivity
  have hxle : 1 / t ≤ k := by
    apply (div_le_iff₀ ht).2
    have := (div_lt_iff₀ hk).1 ht_inv
    nlinarith
  refine ⟨1 / t, ⟨by linarith, hxle⟩, 0, ⟨by linarith, by linarith⟩, ?_⟩
  have hinv : 1 / (1 / t) = t := by field_simp
  have hcos : Real.cos t = 1 := by
    dsimp [t]
    rw [Real.cos_nat_mul_two_pi]
  simp [f₂, hinv, hcos]
  have hM : M < t := lt_of_le_of_lt (le_max_left _ _) ht_big
  have htone : 1 < t := lt_of_le_of_lt (le_max_right _ _) ht_big
  nlinarith

/-- Exercise 641, gap 4; express divergence of local oscillation to `+∞`. -/
theorem gap4 :
    ∀ k > 0, unboundedOscillationOn f₂ k := by
  exact gap3

private theorem f₃_abs_le (k x : ℝ) (hk : 0 ≤ k)
    (hx : x ∈ Set.Icc (-k) k) : |f₃ x| ≤ 3 * k := by
  have hxabs : |x| ≤ k := (abs_le).2 hx
  have hsin : |Real.sin (1 / x)| ≤ 1 := Real.abs_sin_le_one _
  calc
    |f₃ x| = |x| * |2 + Real.sin (1 / x)| := by simp [f₃, abs_mul]
    _ ≤ |x| * (2 + |Real.sin (1 / x)|) :=
      mul_le_mul_of_nonneg_left (by
        simpa using abs_add_le (2 : ℝ) (Real.sin (1 / x))) (abs_nonneg _)
    _ ≤ k * 3 := by
      apply mul_le_mul hxabs
      · linarith
      · positivity
      · exact hk
    _ = 3 * k := by ring

/-- Exercise 641, gap 5; require a positive radius. -/
theorem gap5 (k : ℝ) (hk : 0 < k) :
    4 * k ≤ oscillationOn f₃ k := by
  have hb := oscillationOn_bounds_of_pair_bound f₃ k (6 * k) hk.le
    (fun x hx y hy => by
      calc
        |f₃ x - f₃ y| ≤ |f₃ x| + |f₃ y| := abs_sub _ _
        _ ≤ 3 * k + 3 * k :=
          add_le_add (f₃_abs_le k x hk.le hx) (f₃_abs_le k y hk.le hy)
        _ = 6 * k := by ring)
  have hpair := hb.2.2 k ⟨by linarith, le_rfl⟩ (-k) ⟨le_rfl, by linarith⟩
  have heq : |f₃ k - f₃ (-k)| = 4 * k := by
    have hdiff : f₃ k - f₃ (-k) = 4 * k := by
      unfold f₃
      simp only [one_div, inv_neg, Real.sin_neg]
      ring
    rw [hdiff, abs_of_pos (by positivity)]
  simpa [heq] using hpair

/-- Exercise 641, gap 6. -/
theorem gap6 (k : ℝ) : 3 * k - k = 2 * k := by
  ring

private theorem oscillationOn_f₃_bounds (k : ℝ) (hk : 0 ≤ k) :
    0 ≤ oscillationOn f₃ k ∧ oscillationOn f₃ k ≤ 6 * k := by
  let s : Set ℝ := {d : ℝ | ∃ x ∈ Set.Icc (-k) k, ∃ y ∈ Set.Icc (-k) k,
    d = |f₃ x - f₃ y|}
  have hzero : (0 : ℝ) ∈ s := by
    refine ⟨0, ⟨by linarith, hk⟩, 0, ⟨by linarith, hk⟩, ?_⟩
    simp [f₃]
  have hupper : ∀ d ∈ s, d ≤ 6 * k := by
    rintro d ⟨x, hx, y, hy, rfl⟩
    calc
      |f₃ x - f₃ y| ≤ |f₃ x| + |f₃ y| := abs_sub _ _
      _ ≤ 3 * k + 3 * k := add_le_add (f₃_abs_le k x hk hx) (f₃_abs_le k y hk hy)
      _ = 6 * k := by ring
  have hbdd : BddAbove s := ⟨6 * k, hupper⟩
  unfold oscillationOn
  change 0 ≤ sSup s ∧ sSup s ≤ 6 * k
  exact ⟨le_csSup hbdd hzero, csSup_le ⟨0, hzero⟩ hupper⟩

/-- Exercise 641, gap 7. -/
theorem gap7 : oscillationAt f₃ 0 := by
  unfold oscillationAt
  apply squeeze_zero'
  · exact Filter.Eventually.of_forall fun n =>
      (oscillationOn_f₃_bounds (1 / ((n : ℝ) + 1)) (by positivity)).1
  · exact Filter.Eventually.of_forall fun n =>
      (oscillationOn_f₃_bounds (1 / ((n : ℝ) + 1)) (by positivity)).2
  · simpa using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1))
          Filter.atTop (nhds 0)).const_mul 6

/-- Exercise 641, gap 8; the finite-radius endpoint formula in the source is not the supremum, so state its limiting role. -/
theorem gap8 :
    Filter.Tendsto
      (fun k : ℝ => (1 / Real.pi) *
        (Real.arctan (1 / k) - Real.arctan (1 / (-k))))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have hinv :
      Filter.Tendsto (fun k : ℝ => 1 / k)
        (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop := by
    simpa [one_div] using
      (tendsto_inv_nhdsGT_zero : Filter.Tendsto (fun k : ℝ => k⁻¹)
        (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop)
  have hinv_neg :
      Filter.Tendsto (fun k : ℝ => 1 / (-k))
        (nhdsWithin 0 (Set.Ioi 0)) Filter.atBot := by
    have h := Filter.tendsto_neg_atTop_atBot.comp hinv
    simpa [Function.comp_def, one_div] using h
  have hpos :
      Filter.Tendsto (fun k : ℝ => Real.arctan (1 / k))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.pi / 2)) :=
    (tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop).comp hinv
  have hneg :
      Filter.Tendsto (fun k : ℝ => Real.arctan (1 / (-k)))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (-(Real.pi / 2))) :=
    (tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atBot).comp hinv_neg
  have hcalc :
      (1 / Real.pi) * (Real.pi / 2 - (-(Real.pi / 2))) = (1 : ℝ) := by
    have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    field_simp
    norm_num
  simpa only [hcalc] using (hpos.sub hneg).const_mul (1 / Real.pi)

/-- Exercise 641, gap 9. -/
theorem gap9 (k : ℝ) (hk : k ≠ 0) :
    (1 / Real.pi) * (Real.arctan (1 / k) - Real.arctan (1 / (-k))) =
      (2 / Real.pi) * Real.arctan (1 / k) := by
  rw [show (1 / (-k) : ℝ) = -(1 / k) by field_simp]
  rw [Real.arctan_neg]
  ring

private theorem f₄_pair_le_one (x y : ℝ) : |f₄ x - f₄ y| ≤ 1 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hxlo : -(1 / 2 : ℝ) ≤ f₄ x := by
    rw [f₄, one_div_mul_eq_div]
    apply (le_div_iff₀ hpi).2
    have h := (Real.neg_pi_div_two_lt_arctan (1 / x)).le
    linarith
  have hxhi : f₄ x ≤ (1 / 2 : ℝ) := by
    rw [f₄, one_div_mul_eq_div]
    apply (div_le_iff₀ hpi).2
    have h := (Real.arctan_lt_pi_div_two (1 / x)).le
    linarith
  have hylo : -(1 / 2 : ℝ) ≤ f₄ y := by
    rw [f₄, one_div_mul_eq_div]
    apply (le_div_iff₀ hpi).2
    have h := (Real.neg_pi_div_two_lt_arctan (1 / y)).le
    linarith
  have hyhi : f₄ y ≤ (1 / 2 : ℝ) := by
    rw [f₄, one_div_mul_eq_div]
    apply (div_le_iff₀ hpi).2
    have h := (Real.arctan_lt_pi_div_two (1 / y)).le
    linarith
  rw [abs_le]
  constructor <;> linarith

/-- Exercise 641, gap 10. -/
theorem gap10 : oscillationAt f₄ 1 := by
  unfold oscillationAt
  let r : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hr0 : Filter.Tendsto r Filter.atTop (nhds 0) := by
    simpa [r] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1))
          Filter.atTop (nhds 0))
  have hrpos : ∀ᶠ n : ℕ in Filter.atTop, r n ∈ Set.Ioi 0 :=
    Filter.Eventually.of_forall fun n => by simp [r]; positivity
  have hr : Filter.Tendsto r Filter.atTop (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.2 ⟨hr0, hrpos⟩
  have hlower :
      Filter.Tendsto (fun n : ℕ => |f₄ (r n) - f₄ (-(r n))|)
        Filter.atTop (nhds 1) := by
    have h := gap8.abs.comp hr
    convert h using 1
    · ext n
      simp only [Function.comp_apply, f₄, one_div, inv_neg]
      ring
    · norm_num
  have hlow_le : ∀ᶠ n : ℕ in Filter.atTop,
      |f₄ (r n) - f₄ (-(r n))| ≤ oscillationOn f₄ (r n) := by
    filter_upwards with n
    have hrn : 0 ≤ r n := by simp [r]; positivity
    have hb := oscillationOn_bounds_of_pair_bound f₄ (r n) 1 hrn
      (fun x _ y _ => f₄_pair_le_one x y)
    apply hb.2.2
    · constructor <;> linarith
    · constructor <;> linarith
  have hupp : ∀ᶠ n : ℕ in Filter.atTop, oscillationOn f₄ (r n) ≤ 1 := by
    filter_upwards with n
    exact (oscillationOn_bounds_of_pair_bound f₄ (r n) 1
      (by simp [r]; positivity) (fun x _ y _ => f₄_pair_le_one x y)).2.1
  have hone : Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (nhds 1) :=
    tendsto_const_nhds
  simpa [r] using Filter.Tendsto.squeeze' hlower hone hlow_le hupp

/-- Exercise 641, gap 11; require a positive radius. -/
theorem gap11 (k : ℝ) (hk : 0 < k) : oscillationOn f₅ k = 2 := by
  apply oscillationOn_eq_of_upper_of_approx
  · intro x hx y hy
    have habs (z : ℝ) : |f₅ z| ≤ 1 := by
      by_cases hz : z = 0
      · simp [hz, f₅]
      · rw [f₅, abs_div, abs_abs]
        apply (div_le_iff₀ (abs_pos.mpr hz)).2
        simpa using (Real.abs_sin_le_abs : |Real.sin z| ≤ |z|)
    calc
      |f₅ x - f₅ y| ≤ |f₅ x| + |f₅ y| := abs_sub _ _
      _ ≤ 1 + 1 := add_le_add (habs x) (habs y)
      _ = 2 := by norm_num
  · intro a ha
    have hlim :
        Filter.Tendsto (fun x : ℝ => 2 * |Real.sinc x|)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 2) := by
      have h :=
        ((Real.continuous_sinc.tendsto 0).abs.const_mul 2).mono_left
          (show nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhds 0 from inf_le_left)
      simpa using h
    have haev : ∀ᶠ x : ℝ in nhdsWithin 0 (Set.Ioi 0),
        a < 2 * |Real.sinc x| :=
      hlim.eventually (Ioi_mem_nhds ha)
    have hkev : ∀ᶠ x : ℝ in nhdsWithin 0 (Set.Ioi 0), x < k :=
      Filter.Eventually.filter_mono inf_le_left (Iio_mem_nhds hk)
    have hposev : ∀ᶠ x : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < x := by
      simpa using (self_mem_nhdsWithin : ∀ᶠ x : ℝ in nhdsWithin 0 (Set.Ioi 0),
        x ∈ Set.Ioi 0)
    obtain ⟨x, hax, hxk, hxpos⟩ := (haev.and (hkev.and hposev)).exists
    have hx0 : x ≠ 0 := ne_of_gt hxpos
    have hxmem : x ∈ Set.Icc (-k) k := ⟨by linarith, le_of_lt hxk⟩
    have hnegmem : -x ∈ Set.Icc (-k) k := ⟨by linarith, by linarith⟩
    have hfpos : f₅ x = |Real.sinc x| := by
      rw [f₅, Real.sinc_of_ne_zero hx0, abs_div, abs_of_pos hxpos]
    have hfneg : f₅ (-x) = -|Real.sinc x| := by
      rw [show f₅ (-x) = -f₅ x by
        rw [f₅, f₅]
        simp only [Real.sin_neg, abs_neg]
        ring, hfpos]
    refine ⟨x, hxmem, -x, hnegmem, ?_⟩
    rw [hfpos, hfneg, sub_neg_eq_add, ← two_mul, abs_of_nonneg (by positivity)]
    exact hax

/-- Exercise 641, gap 12. -/
theorem gap12 : oscillationAt f₅ 2 := by
  unfold oscillationAt
  have heq : (fun n : ℕ => oscillationOn f₅ (1 / ((n : ℝ) + 1))) =
      fun _ : ℕ => (2 : ℝ) := by
    funext n
    apply gap11
    positivity
  rw [heq]
  exact tendsto_const_nhds

/-- Exercise 641, gap 13; correct the finite-radius formula to a one-sided endpoint span used in the limit. -/
theorem gap13 :
    Filter.Tendsto
      (fun k : ℝ => |1 / (1 + Real.exp (1 / k)) -
        1 / (1 + Real.exp (-(1 / k)))|)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have hinv :
      Filter.Tendsto (fun k : ℝ => 1 / k)
        (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop := by
    simpa [one_div] using
      (tendsto_inv_nhdsGT_zero : Filter.Tendsto (fun k : ℝ => k⁻¹)
        (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop)
  have hexp_top :
      Filter.Tendsto (fun k : ℝ => Real.exp (1 / k))
        (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop :=
    Real.tendsto_exp_atTop.comp hinv
  have hfirst :
      Filter.Tendsto (fun k : ℝ => 1 / (1 + Real.exp (1 / k)))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have hden : Filter.Tendsto (fun k : ℝ => 1 + Real.exp (1 / k))
        (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop :=
      tendsto_const_nhds.add_atTop hexp_top
    simpa [one_div] using tendsto_inv_atTop_zero.comp hden
  have hexp_bot :
    Filter.Tendsto (fun k : ℝ => Real.exp (-(1 / k)))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    Real.tendsto_exp_atBot.comp (Filter.tendsto_neg_atTop_atBot.comp hinv)
  have hsecond :
      Filter.Tendsto (fun k : ℝ => 1 / (1 + Real.exp (-(1 / k))))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    have hadd := (tendsto_const_nhds (x := (1 : ℝ))).add hexp_bot
    simpa [one_div] using hadd.inv₀ (by norm_num : (1 : ℝ) + 0 ≠ 0)
  convert (hfirst.sub hsecond).abs using 1 <;> norm_num

private theorem f₆_pair_le_one (x y : ℝ) : |f₆ x - f₆ y| ≤ 1 := by
  have hunit (z : ℝ) : 0 ≤ f₆ z ∧ f₆ z ≤ 1 := by
    have hden : 0 < 1 + Real.exp (1 / z) := by positivity
    constructor
    · rw [f₆]
      positivity
    · rw [f₆, div_le_iff₀ hden]
      linarith [Real.exp_pos (1 / z)]
  have hx := hunit x
  have hy := hunit y
  rw [abs_le]
  constructor <;> linarith

/-- Exercise 641, gap 14. -/
theorem gap14 : oscillationAt f₆ 1 := by
  unfold oscillationAt
  let r : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hr0 : Filter.Tendsto r Filter.atTop (nhds 0) := by
    simpa [r] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1))
          Filter.atTop (nhds 0))
  have hrpos : ∀ᶠ n : ℕ in Filter.atTop, r n ∈ Set.Ioi 0 :=
    Filter.Eventually.of_forall fun n => by simp [r]; positivity
  have hr : Filter.Tendsto r Filter.atTop (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.2 ⟨hr0, hrpos⟩
  have hlower :
      Filter.Tendsto (fun n : ℕ => |f₆ (r n) - f₆ (-(r n))|)
        Filter.atTop (nhds 1) := by
    have h := gap13.comp hr
    convert h using 1
    ext n
    simp only [Function.comp_apply, f₆, one_div, inv_neg]
  have hlow_le : ∀ᶠ n : ℕ in Filter.atTop,
      |f₆ (r n) - f₆ (-(r n))| ≤ oscillationOn f₆ (r n) := by
    filter_upwards with n
    have hb := oscillationOn_bounds_of_pair_bound f₆ (r n) 1
      (by simp [r]; positivity) (fun x _ y _ => f₆_pair_le_one x y)
    apply hb.2.2
    · constructor <;> simp [r] <;> positivity
    · constructor <;> simp [r] <;> positivity
  have hupp : ∀ᶠ n : ℕ in Filter.atTop, oscillationOn f₆ (r n) ≤ 1 := by
    filter_upwards with n
    exact (oscillationOn_bounds_of_pair_bound f₆ (r n) 1
      (by simp [r]; positivity) (fun x _ y _ => f₆_pair_le_one x y)).2.1
  simpa [r] using Filter.Tendsto.squeeze' hlower tendsto_const_nhds hlow_le hupp

/-- Exercise 641, gap 15; correct the finite-radius formula to the endpoint span whose limit is used. -/
theorem gap15 :
    Filter.Tendsto
      (fun k : ℝ => Real.rpow (1 + k) (1 / k) -
        Real.rpow (1 + k) (-(1 / k)))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Real.exp 1 - Real.exp (-1))) := by
  have hinv :
      Filter.Tendsto (fun k : ℝ => 1 / k)
        (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop := by
    simpa [one_div] using
      (tendsto_inv_nhdsGT_zero : Filter.Tendsto (fun k : ℝ => k⁻¹)
        (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop)
  have hpos :
      Filter.Tendsto (fun k : ℝ => Real.rpow (1 + k) (1 / k))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.exp 1)) := by
    have h := (Real.tendsto_one_add_div_rpow_exp 1).comp hinv
    convert h using 1
    ext k
    simp only [one_div]
    congr 1
    field_simp
  have hneg :
      Filter.Tendsto (fun k : ℝ => Real.rpow (1 + k) (-(1 / k)))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.exp (-1))) := by
    have h := hpos.inv₀ (Real.exp_ne_zero 1)
    have heq :
        (fun k : ℝ => (Real.rpow (1 + k) (1 / k))⁻¹) =ᶠ[
          nhdsWithin 0 (Set.Ioi 0)]
        (fun k : ℝ => Real.rpow (1 + k) (-(1 / k))) := by
      filter_upwards [self_mem_nhdsWithin] with k hk
      have hkpos : 0 < k := by simpa using hk
      exact (Real.rpow_neg (by positivity) (1 / k)).symm
    simpa only [Real.exp_neg] using h.congr' heq
  exact hpos.sub hneg

private theorem f₇_value_bounds (x : ℝ) :
    Real.exp (-1) ≤ f₇ x ∧ f₇ x ≤ Real.exp 1 := by
  by_cases hx0 : x = 0
  · subst x
    have hlo : Real.exp (-1) ≤ Real.exp 0 :=
      Real.exp_le_exp.mpr (by norm_num)
    have hhi : Real.exp 0 ≤ Real.exp 1 :=
      Real.exp_le_exp.mpr (by norm_num)
    simpa [f₇] using ⟨hlo, hhi⟩
  have hbase : 0 < 1 + |x| := by positivity
  change Real.exp (-1) ≤ Real.rpow (1 + |x|) (1 / x) ∧
    Real.rpow (1 + |x|) (1 / x) ≤ Real.exp 1
  rw [Real.rpow_eq_pow]
  rw [Real.rpow_def_of_pos hbase (1 / x)]
  constructor <;> rw [Real.exp_le_exp]
  · by_cases hx : 0 < x
    · have hlog : 0 ≤ Real.log (1 + |x|) :=
        Real.log_nonneg (by linarith [abs_nonneg x])
      have hinv : 0 ≤ 1 / x := by positivity
      nlinarith [mul_nonneg hlog hinv]
    · have hxneg : x < 0 := lt_of_le_of_ne (le_of_not_gt hx) hx0
      have habs : |x| = -x := abs_of_neg hxneg
      have hlog_upper : Real.log (1 + |x|) ≤ -x := by
        have h := Real.log_le_sub_one_of_pos hbase
        simpa [habs] using h
      have hq : Real.log (1 + |x|) / (-x) ≤ 1 := by
        apply (div_le_iff₀ (neg_pos.mpr hxneg)).2
        simpa using hlog_upper
      have heq :
          Real.log (1 + |x|) * (1 / x) =
            -(Real.log (1 + |x|) / (-x)) := by
        field_simp
      rw [heq]
      linarith
  · by_cases hx : 0 < x
    · have habs : |x| = x := abs_of_pos hx
      have hlog_upper : Real.log (1 + |x|) ≤ x := by
        have h := Real.log_le_sub_one_of_pos hbase
        simpa [habs] using h
      have hq : Real.log (1 + |x|) / x ≤ 1 := by
        apply (div_le_iff₀ hx).2
        simpa using hlog_upper
      simpa [div_eq_mul_inv, one_div] using hq
    · have hxneg : x < 0 := lt_of_le_of_ne (le_of_not_gt hx) hx0
      have hlog : 0 ≤ Real.log (1 + |x|) :=
        Real.log_nonneg (by linarith [abs_nonneg x])
      have hinv : 1 / x ≤ 0 := by
        exact (one_div_nonpos.mpr hxneg.le)
      have hprod := mul_nonpos_of_nonneg_of_nonpos hlog hinv
      linarith

private theorem f₇_pair_le_span (x y : ℝ) :
    |f₇ x - f₇ y| ≤ Real.exp 1 - Real.exp (-1) := by
  have hx := f₇_value_bounds x
  have hy := f₇_value_bounds y
  rw [abs_le]
  constructor <;> linarith

/-- Exercise 641, gap 16. -/
theorem gap16 : oscillationAt f₇ (Real.exp 1 - Real.exp (-1)) := by
  unfold oscillationAt
  let r : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let L : ℝ := Real.exp 1 - Real.exp (-1)
  have hL : 0 < L := by
    dsimp [L]
    exact sub_pos.mpr (Real.exp_lt_exp.mpr (by norm_num))
  have hr0 : Filter.Tendsto r Filter.atTop (nhds 0) := by
    simpa [r] using
      (tendsto_one_div_add_atTop_nhds_zero_nat :
        Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1))
          Filter.atTop (nhds 0))
  have hrpos : ∀ᶠ n : ℕ in Filter.atTop, r n ∈ Set.Ioi 0 :=
    Filter.Eventually.of_forall fun n => by simp [r]; positivity
  have hr : Filter.Tendsto r Filter.atTop (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.2 ⟨hr0, hrpos⟩
  have hlower :
      Filter.Tendsto (fun n : ℕ => |f₇ (r n) - f₇ (-(r n))|)
        Filter.atTop (nhds L) := by
    have h := gap15.abs.comp hr
    convert h using 1
    · ext n
      have hrn : 0 < r n := by simp [r]; positivity
      simp only [Function.comp_apply, f₇, abs_of_pos hrn, abs_neg,
        one_div, inv_neg]
    · simpa [L, abs_of_pos hL]
  have hlow_le : ∀ᶠ n : ℕ in Filter.atTop,
      |f₇ (r n) - f₇ (-(r n))| ≤ oscillationOn f₇ (r n) := by
    filter_upwards with n
    have hb := oscillationOn_bounds_of_pair_bound f₇ (r n) L
      (by simp [r]; positivity) (fun x _ y _ => by simpa [L] using f₇_pair_le_span x y)
    apply hb.2.2
    · constructor <;> simp [r] <;> positivity
    · constructor <;> simp [r] <;> positivity
  have hupp : ∀ᶠ n : ℕ in Filter.atTop, oscillationOn f₇ (r n) ≤ L := by
    filter_upwards with n
    exact (oscillationOn_bounds_of_pair_bound f₇ (r n) L
      (by simp [r]; positivity)
      (fun x _ y _ => by simpa [L] using f₇_pair_le_span x y)).2.1
  have hconst : Filter.Tendsto (fun _ : ℕ => L) Filter.atTop (nhds L) :=
    tendsto_const_nhds
  simpa [r, L] using Filter.Tendsto.squeeze' hlower hconst hlow_le hupp

end

end ProofGap.Exercise641
