import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise551

noncomputable section

def original (a b x : ℝ) : ℝ :=
  (Real.rpow (x + a) (x + a) * Real.rpow (x + b) (x + b)) /
    Real.rpow (x + a + b) (2 * x + a + b)
def normalized (a b x : ℝ) : ℝ :=
  (Real.rpow (1 + a / x) (x + a) * Real.rpow (1 + b / x) (x + b)) /
    Real.rpow (1 + (a + b) / x) (2 * x + a + b)
def HasLimitAtPosInfinity (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f Filter.atTop (nhds L)

/-- Exercise 551, gap 1; interpret the unsigned infinity as the positive tail where real powers are defined. -/
private theorem original_eventuallyEq_normalized (a b : ℝ) :
    original a b =ᶠ[Filter.atTop] normalized a b := by
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ),
    Filter.eventually_gt_atTop (-a), Filter.eventually_gt_atTop (-b),
    Filter.eventually_gt_atTop (-(a + b))] with x hx0 hxa hxb hab
  have hxa_pos : 0 < x + a := by linarith
  have hxb_pos : 0 < x + b := by linarith
  have hab_pos : 0 < x + a + b := by linarith
  have ha_ratio : 1 + a / x = (x + a) / x := by
    field_simp [hx0.ne']
  have hb_ratio : 1 + b / x = (x + b) / x := by
    field_simp [hx0.ne']
  have hab_ratio : 1 + (a + b) / x = (x + a + b) / x := by
    field_simp [hx0.ne']
    ring
  have ha_pos : 0 < 1 + a / x := by
    rw [ha_ratio]
    exact div_pos hxa_pos hx0
  have hb_pos : 0 < 1 + b / x := by
    rw [hb_ratio]
    exact div_pos hxb_pos hx0
  have hc_pos : 0 < 1 + (a + b) / x := by
    rw [hab_ratio]
    exact div_pos hab_pos hx0
  have hxa_factor : x + a = x * (1 + a / x) := by
    field_simp [hx0.ne']
  have hxb_factor : x + b = x * (1 + b / x) := by
    field_simp [hx0.ne']
  have hab_factor : x + a + b = x * (1 + (a + b) / x) := by
    field_simp [hx0.ne']
    ring
  have hrpa :
      Real.rpow (x + a) (x + a) =
        Real.rpow x (x + a) * Real.rpow (1 + a / x) (x + a) := by
    calc
      Real.rpow (x + a) (x + a) =
          Real.rpow (x * (1 + a / x)) (x + a) := by rw [hxa_factor]
      _ = _ := Real.mul_rpow (le_of_lt hx0) (le_of_lt ha_pos)
  have hrpb :
      Real.rpow (x + b) (x + b) =
        Real.rpow x (x + b) * Real.rpow (1 + b / x) (x + b) := by
    calc
      Real.rpow (x + b) (x + b) =
          Real.rpow (x * (1 + b / x)) (x + b) := by rw [hxb_factor]
      _ = _ := Real.mul_rpow (le_of_lt hx0) (le_of_lt hb_pos)
  have hrpc :
      Real.rpow (x + a + b) (2 * x + a + b) =
        Real.rpow x (2 * x + a + b) *
          Real.rpow (1 + (a + b) / x) (2 * x + a + b) := by
    calc
      Real.rpow (x + a + b) (2 * x + a + b) =
          Real.rpow (x * (1 + (a + b) / x)) (2 * x + a + b) := by
            rw [hab_factor]
      _ = _ := Real.mul_rpow (le_of_lt hx0) (le_of_lt hc_pos)
  unfold original normalized
  rw [hrpa, hrpb, hrpc]
  let X1 : ℝ := Real.rpow x (x + a)
  let X2 : ℝ := Real.rpow x (x + b)
  let X3 : ℝ := Real.rpow x (2 * x + a + b)
  let A : ℝ := Real.rpow (1 + a / x) (x + a)
  let B : ℝ := Real.rpow (1 + b / x) (x + b)
  let C : ℝ := Real.rpow (1 + (a + b) / x) (2 * x + a + b)
  change ((X1 * A) * (X2 * B)) / (X3 * C) = (A * B) / C
  have hX : X1 * X2 = X3 := by
    dsimp [X1, X2, X3]
    rw [← Real.rpow_add hx0]
    congr 1 <;> ring
  have hX3 : X3 ≠ 0 := by
    dsimp [X3]
    exact ne_of_gt (Real.rpow_pos_of_pos hx0 _)
  have hC : C ≠ 0 := by
    dsimp [C]
    exact ne_of_gt (Real.rpow_pos_of_pos hc_pos _)
  calc
    ((X1 * A) * (X2 * B)) / (X3 * C) =
        ((X1 * X2) * (A * B)) / (X3 * C) := by ring
    _ = (X3 * (A * B)) / (X3 * C) := by rw [hX]
    _ = (A * B) / C := by
      field_simp [hX3, hC]

private theorem tendsto_mul_log_one_add_div (c : ℝ) :
    Filter.Tendsto
      (fun x : ℝ => x * Real.log (1 + c / x)) Filter.atTop (nhds c) := by
  by_cases hc : c = 0
  · subst c
    simp
  · have hinv :
        Filter.Tendsto (fun x : ℝ => x⁻¹) Filter.atTop (nhds 0) :=
        tendsto_inv_atTop_zero
    have hdiv0 :
        Filter.Tendsto (fun x : ℝ => c / x) Filter.atTop (nhds 0) := by
      simpa [div_eq_mul_inv] using
        (tendsto_const_nhds.mul hinv)
    have hdiv :
        Filter.Tendsto (fun x : ℝ => c / x) Filter.atTop (nhdsWithin 0 {0}ᶜ) := by
      refine tendsto_nhdsWithin_iff.2 ⟨hdiv0, ?_⟩
      filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using
        (div_ne_zero hc hx.ne')
    have hinner : HasDerivAt (fun t : ℝ => 1 + t) 1 0 := by
      simpa using
        ((hasDerivAt_const (x := (0 : ℝ)) (c := (1 : ℝ))).add
          (hasDerivAt_id (x := (0 : ℝ))))
    have houter : HasDerivAt Real.log 1 (1 : ℝ) := by
      simpa using Real.hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0)
    have houter_at_inner :
        HasDerivAt Real.log 1 ((fun t : ℝ => 1 + t) 0) := by
      simpa only [add_zero] using houter
    have hderiv : HasDerivAt (fun t : ℝ => Real.log (1 + t)) 1 0 := by
      simpa [Function.comp_def] using houter_at_inner.comp (0 : ℝ) hinner
    have hratio0 :
        Filter.Tendsto
          (fun t : ℝ => (Real.log (1 + t) - Real.log (1 + 0)) / (t - 0))
          (nhdsWithin 0 {0}ᶜ) (nhds 1) := by
      simpa [div_eq_mul_inv, smul_eq_mul, mul_comm] using
        hderiv.tendsto_slope_zero
    have hratio :
        Filter.Tendsto
          (fun x : ℝ => Real.log (1 + c / x) / (c / x)) Filter.atTop
          (nhds 1) := by
      simpa using hratio0.comp hdiv
    have hprod :
        Filter.Tendsto
          (fun x : ℝ => (Real.log (1 + c / x) / (c / x)) * c)
          Filter.atTop (nhds c) := by
      simpa using hratio.mul tendsto_const_nhds
    have heq :
        (fun x : ℝ => x * Real.log (1 + c / x)) =ᶠ[Filter.atTop]
          (fun x : ℝ => (Real.log (1 + c / x) / (c / x)) * c) := by
      filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
      field_simp [hc, hx.ne']
    exact hprod.congr' (Filter.EventuallyEq.symm heq)

private theorem tendsto_rpow_one_add_div_linear (c k d : ℝ) :
    Filter.Tendsto
      (fun x : ℝ => Real.rpow (1 + c / x) (k * x + d)) Filter.atTop
      (nhds (Real.exp (k * c))) := by
  have hinv :
      Filter.Tendsto (fun x : ℝ => x⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  have hdiv0 :
      Filter.Tendsto (fun x : ℝ => c / x) Filter.atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds.mul hinv)
  have hone :
      Filter.Tendsto (fun x : ℝ => 1 + c / x) Filter.atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add hdiv0
  have hlog :
      Filter.Tendsto (fun x : ℝ => Real.log (1 + c / x)) Filter.atTop
        (nhds 0) := by
    simpa using
      (Real.continuousAt_log one_ne_zero).tendsto.comp hone
  have h1 :
      Filter.Tendsto
        (fun x : ℝ => k * (x * Real.log (1 + c / x))) Filter.atTop
        (nhds (k * c)) :=
    tendsto_const_nhds.mul (tendsto_mul_log_one_add_div c)
  have h2 :
      Filter.Tendsto
        (fun x : ℝ => d * Real.log (1 + c / x)) Filter.atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hlog
  have hsum :
      Filter.Tendsto
        (fun x : ℝ =>
          k * (x * Real.log (1 + c / x)) +
            d * Real.log (1 + c / x)) Filter.atTop
        (nhds (k * c)) := by
    simpa using h1.add h2
  have hargEq :
      (fun x : ℝ => Real.log (1 + c / x) * (k * x + d)) =ᶠ[Filter.atTop]
        (fun x : ℝ =>
          k * (x * Real.log (1 + c / x)) +
            d * Real.log (1 + c / x)) :=
    Filter.Eventually.of_forall (by intro x; ring)
  have harg :
      Filter.Tendsto
        (fun x : ℝ => Real.log (1 + c / x) * (k * x + d)) Filter.atTop
        (nhds (k * c)) := by
    exact hsum.congr' (Filter.EventuallyEq.symm hargEq)
  have hexp :
      Filter.Tendsto
        (fun x : ℝ => Real.exp (Real.log (1 + c / x) * (k * x + d)))
        Filter.atTop (nhds (Real.exp (k * c))) :=
    Real.continuous_exp.continuousAt.tendsto.comp harg
  have hpos : ∀ᶠ x : ℝ in Filter.atTop, 0 < 1 + c / x := by
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ),
      Filter.eventually_gt_atTop |c|] with x hx habs
    have hneg : -x < c := by linarith [neg_abs_le c]
    have hcdiv : -1 < c / x := by
      apply (lt_div_iff₀ hx).2
      simpa using hneg
    linarith
  have heq :
      (fun x : ℝ => Real.rpow (1 + c / x) (k * x + d)) =ᶠ[Filter.atTop]
        (fun x : ℝ =>
          Real.exp (Real.log (1 + c / x) * (k * x + d))) := by
    filter_upwards [hpos] with x hx
    exact Real.rpow_def_of_pos hx (k * x + d)
  exact hexp.congr' (Filter.EventuallyEq.symm heq)

theorem gap1 (a b L : ℝ) :
    HasLimitAtPosInfinity (original a b) L ↔
      HasLimitAtPosInfinity (normalized a b) L := by
  change
    Filter.Tendsto (original a b) Filter.atTop (nhds L) ↔
      Filter.Tendsto (normalized a b) Filter.atTop (nhds L)
  constructor
  · intro h
    exact h.congr' (original_eventuallyEq_normalized a b)
  · intro h
    exact h.congr'
      (Filter.EventuallyEq.symm (original_eventuallyEq_normalized a b))

/-- Exercise 551, gap 2; retain the correct exponents `x+a`, `x+b`, and `2x+a+b`. -/
theorem gap2 (a b : ℝ) :
    HasLimitAtPosInfinity (normalized a b)
      ((Real.exp a * Real.exp b) / Real.exp (2 * (a + b))) := by
  have ha :
      Filter.Tendsto
        (fun x : ℝ => Real.rpow (1 + a / x) (x + a)) Filter.atTop
        (nhds (Real.exp a)) := by
    simpa using tendsto_rpow_one_add_div_linear a 1 a
  have hb :
      Filter.Tendsto
        (fun x : ℝ => Real.rpow (1 + b / x) (x + b)) Filter.atTop
        (nhds (Real.exp b)) := by
    simpa using tendsto_rpow_one_add_div_linear b 1 b
  have hab :
      Filter.Tendsto
        (fun x : ℝ =>
          Real.rpow (1 + (a + b) / x) (2 * x + a + b)) Filter.atTop
        (nhds (Real.exp (2 * (a + b)))) := by
    simpa [add_assoc] using
      tendsto_rpow_one_add_div_linear (a + b) 2 (a + b)
  exact (ha.mul hb).div hab (Real.exp_ne_zero _)

/-- Exercise 551, gap 3. -/
theorem gap3 (a b : ℝ) :
    (Real.exp a * Real.exp b) / Real.exp (2 * (a + b)) =
      Real.exp (-(a + b)) := by
  rw [← Real.exp_add, ← Real.exp_sub]
  congr 1
  ring

/-- Exercise 551, gap 4; use the corrected normalized expression. -/
theorem gap4 (a b : ℝ) :
    HasLimitAtPosInfinity (normalized a b) (Real.exp (-(a + b))) := by
  rw [← gap3 a b]
  exact gap2 a b

end

end ProofGap.Exercise551
